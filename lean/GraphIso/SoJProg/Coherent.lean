module

public import GraphIso.SoJProg.Data
public import GraphIso.Toolkit.Labels

/-!
# Coherent Split-or-Johnson on data

One level of milestone 11's Coherent Split-or-Johnson (`cohSoj`,
`GraphIso/SplitJohnson/CoherentDef.lean`) on data, for the programs of stage 14c
(`PLAN-14.md` §7 item 8). The points are `Fin m`; `C₁` and `C₂` are duplicate-free lists of
points; the colouring is given by a function `f : ℕ → ℕ → ℕ` that agrees on `Fin m` with the
`m × m` array `c` (`colOf m c`). The programs read `f` from the rows of `c`.

* **The data model** (`cohSojD`), with the helpers `offColsD`, `compD` (components by `|S|`
  closure steps, as `comp`), `disconnD`, `minD`, `colsD`, `twinOK` (the `good` test, through
  twin classes for the `violet` edges), `compPart`, `colPartD`, `primLeaf`. `cohSoj` makes at
  most one choice, so its data is a tree of depth at most one (`DTree`): a leaf, or a node with
  its list of options and the leaf at every option.
* **Leaves on data** (`LeafD`): tag `0` is `part ⟨col, blk⟩` with arrays indexed by points; tag
  `1` is `bip W₁ W₂ (bipEdge c g)`, the cells of `W₂` listed, the edge colour `g`.
* **Decoding** (`decodeTree`, `decode_cohSojD`): the data tree decodes to the model,
  `decodeTree m c (cohSojD f m C₁ C₂) = cohSoj (setOf m C₁) (setOf m C₂) (colOf m c)`, with
  `R = Fin m`. Milestone 11 applies `cohSoj` on `R = α ⊕ Finset α`; stage 14d numbers the points
  of that sum consecutively and transports along the numbering.
* **Results** (`ResD`, `toRes`, `decodeRes`): a leaf is `(false, [], #[o])`; a node is
  `(true, options, leaves)` with the leaf at every point `y < m`, so decoding is exact on all of
  `Fin m` (`decodeRes_toRes`). The programs read the colouring as `fA (offsArr m) c`, which agrees
  with `colOf m c` on `Fin m` (`fA_offsArr`); `decodeRes_cohSojD` combines the two.
* **Programs** (`cohSojProg m c C₁ C₂` and its pieces `cs…Prog`, no backend calls): each piece
  has a `RunsWithin` spec with an explicit cost polynomial in a bound `N` on `m`, `|C₁|`, `|C₂|`
  (`RunsWithin.cohSojProg`: cost `cohSojCost (m + |C₁| + |C₂|)`, at most `903 (N + 1)^7` by
  `cohSojCost_le`); `wf_cohSojProg` is well-formedness. The cost bounds hold for all inputs;
  only the decoding needs `C₁`, `C₂` duplicate-free with entries below `m`.
* **Edges of a `bip` leaf**: `bipEdgeProg` computes the edge predicate `bipEdgeD` of a point and
  a listed cell (`bipEdgeD_eq`: it is `bipEdge (colOf m c) g`), at cost `6 |B| + 1`;
  `bipRelProg` materializes the whole relation as the Boolean array `bipRelD` indexed by
  `x * |W₂| + j`, and `relOf_bipRelD` shows that `relOf m W₂` of it is `bipEdge` on every
  listed cell (distinct cells, points below `m`), at cost `bipRelCost`.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.Coherent GraphIso.SplitJohnson

/-! ### The data model -/

section Model

variable (f : ℕ → ℕ → ℕ)

/-- The colours of pairs of distinct points of `S`, with repetitions. -/
def offColsD (S : List ℕ) : List ℕ :=
  S.flatMap fun u => (S.filter fun v => v != u).map fun v => f u v

/-- One closure step of the component computation: add the points of `S` adjacent in colour
`r` to a point of `T`. -/
def compStepD (S : List ℕ) (r : ℕ) (T : List ℕ) : List ℕ :=
  T ++ S.filter fun y => !(T.contains y) && T.any fun x => f x y == r || f y x == r

/-- The component of `x` in the colour-`r` graph on `S` (empty if `x ∉ S`): `|S|` closure
steps, as `comp`. -/
def compD (S : List ℕ) (r x : ℕ) : List ℕ :=
  (compStepD f S r)^[S.length] (if S.contains x then [x] else [])

/-- The colours of `S` whose graphs are disconnected. -/
def disconnD (S : List ℕ) : List ℕ :=
  (offColsD f S).filter fun r => S.any fun x => S.any fun y => !((compD f S r x).contains y)

/-- The least element of a nonempty list (`0` for the empty list). -/
def minD : List ℕ → ℕ
  | [] => 0
  | a :: l => l.foldl min a

/-- The colours of `C₁ × C₂`, with repetitions. -/
def colsD (C₁ C₂ : List ℕ) : List ℕ := C₁.flatMap fun x => C₂.map fun w => f x w

/-- The `good` test of a block `B`: no twin class of `C₁` for the `g`-edges into `B` has more
than `|C₁|/2` points. -/
def twinOK (C₁ B : List ℕ) (g : ℕ) : Bool :=
  C₁.all fun x =>
    decide (2 * (C₁.filter fun x' => B.all fun y => (f x y == g) == (f x' y == g)).length ≤
      C₁.length)

end Model

/-- Leaf data: `(tag, (col, blk), (W₁, W₂, g))`. Tag `0` is `part ⟨col, blk⟩`; any other tag is
`bip W₁ W₂ (bipEdge c g)`. -/
abbrev LeafD := ℕ × ((Array ℕ × Array (List ℕ)) × (List ℕ × (List (List ℕ) × ℕ)))

/-- A `part` leaf. -/
def partLeaf (col : Array ℕ) (blk : Array (List ℕ)) : LeafD := (0, (col, blk), ([], [], 0))

/-- A `bip` leaf. -/
def bipLeaf (W₁ : List ℕ) (W₂ : List (List ℕ)) (g : ℕ) : LeafD :=
  (1, (#[], #[]), (W₁, W₂, g))

/-- Trees of depth at most one on data: a leaf, or a node with its options and a leaf for every
point. -/
inductive DTree
  | leaf : Option LeafD → DTree
  | node : List ℕ → (ℕ → Option LeafD) → DTree

section Model

variable (f : ℕ → ℕ → ℕ)

/-- The colored partition of `S` into the components of colour `r`, with one colour. -/
def compPart (m : ℕ) (S : List ℕ) (r : ℕ) : LeafD :=
  partLeaf (Array.replicate m 0) ((List.range m).map (compD f S r)).toArray

/-- The colouring `x ↦ f x w` of `S`, each colour class as one block. -/
def colPartD (m : ℕ) (S : List ℕ) (w : ℕ) : LeafD :=
  partLeaf ((List.range m).map fun x => f x w).toArray
    ((List.range m).map fun x => S.filter fun y => f y w == f x w).toArray

/-- The colours `k` with more than `|C₁|/2` points `x` such that `f x w = k`, for some
`w ∈ C₂` (the imprimitive case). -/
def bigImpD (C₁ C₂ : List ℕ) : List ℕ :=
  (colsD f C₁ C₂).filter fun k =>
    C₂.any fun w => decide (C₁.length < 2 * (C₁.filter fun x => f x w == k).length)

/-- The options of the imprimitive case: the points whose component passes the `good` test. -/
def goodOptsD (C₁ C₂ : List ℕ) (red violet : ℕ) : List ℕ :=
  C₂.filter fun y => twinOK f C₁ (compD f C₂ red y) violet

/-- The colours of `C₁ × C₂` other than `g`. -/
def otherColsD (C₁ C₂ : List ℕ) (g : ℕ) : List ℕ := (colsD f C₁ C₂).filter fun k => k != g

/-- The colours `k` with more than `|C₁|/2` points `x` such that `f x y = k` (the primitive
case). -/
def bigPrimD (C₁ C₂ : List ℕ) (y : ℕ) : List ℕ :=
  (colsD f C₁ C₂).filter fun k => decide (C₁.length < 2 * (C₁.filter fun x => f x y == k).length)

/-- The colours `b` of `X[C₂]` of positive degree at `y` below `|C₂|/2`. -/
def bluesD (C₂ : List ℕ) (y : ℕ) : List ℕ :=
  (offColsD f C₂).filter fun b =>
    decide (0 < (C₂.filter fun z => f y z == b).length ∧
      2 * (C₂.filter fun z => f y z == b).length < C₂.length)

/-- The leaf at `y` when `X[C₂]` is primitive. -/
def primLeaf (m : ℕ) (C₁ C₂ : List ℕ) (y : ℕ) : Option LeafD :=
  match bigPrimD f C₁ C₂ y with
  | v₀ :: vs =>
    match bluesD f C₂ y with
    | b₀ :: bs =>
      some (bipLeaf (C₁.filter fun x => f x y == minD (v₀ :: vs))
        ((C₂.filter fun z => f y z == minD (b₀ :: bs)).map fun z => [z]) (minD (v₀ :: vs)))
    | [] => none
  | [] => some (colPartD f m C₁ y)

/-- The branch where `X[C₂]` is imprimitive, with `red` its least disconnected colour. -/
def imprimTree (m : ℕ) (C₁ C₂ : List ℕ) (red : ℕ) : DTree :=
  match bigImpD f C₁ C₂ with
  | v₀ :: vs =>
    match goodOptsD f C₁ C₂ red (minD (v₀ :: vs)) with
    | _ :: _ =>
      .node (goodOptsD f C₁ C₂ red (minD (v₀ :: vs))) fun y =>
        some (bipLeaf C₁ ((compD f C₂ red y).map fun z => [z]) (minD (v₀ :: vs)))
    | [] =>
      match otherColsD f C₁ C₂ (minD (v₀ :: vs)) with
      | g₀ :: gs => .leaf (some (bipLeaf C₁ (C₂.map (compD f C₂ red)) (minD (g₀ :: gs))))
      | [] => .leaf none
  | [] => .node C₂ fun w => some (colPartD f m C₁ w)

/-- **Coherent Split-or-Johnson on data.** -/
def cohSojD (m : ℕ) (C₁ C₂ : List ℕ) : DTree :=
  match disconnD f C₁ with
  | r :: rs => .leaf (some (compPart f m C₁ (minD (r :: rs))))
  | [] =>
    match disconnD f C₂ with
    | r :: rs => imprimTree f m C₁ C₂ (minD (r :: rs))
    | [] => .node C₂ fun y => primLeaf f m C₁ C₂ y

end Model

/-! ### Decoding -/

/-- Decode leaf data. -/
def decodeLeaf (m : ℕ) (c : Array ℕ) : Option LeafD → Option (CohOut (Fin m))
  | none => none
  | some (tag, (col, blk), (W₁, W₂, g)) =>
    if tag = 0 then some (.part ⟨fun x => get col x.val, fun x => setOf m (blk.getD x.val [])⟩)
    else some (.bip (setOf m W₁) (famOf m W₂) (bipEdge (colOf m c) g))

/-- Decode a data tree. -/
def decodeTree (m : ℕ) (c : Array ℕ) : DTree → CTree (Fin m) (Option (CohOut (Fin m)))
  | .leaf o => .leaf (decodeLeaf m c o)
  | .node opts k => .node (setOf m opts) fun y => .leaf (decodeLeaf m c (k y.val))

/-! ### Decoding lemmas -/

section DecodeLemmas

variable {m : ℕ}

theorem setOf_filter (l : List ℕ) (p : ℕ → Bool) :
    setOf m (l.filter p) = (setOf m l).filter fun x => p x.val = true := by
  ext x
  simp [mem_setOf, List.mem_filter]

theorem setOf_append (l l' : List ℕ) : setOf m (l ++ l') = setOf m l ∪ setOf m l' := by
  ext x
  simp [mem_setOf]

theorem card_filter_setOf {l : List ℕ} (hl : l.Nodup) (hlm : ∀ x ∈ l, x < m)
    (p : ℕ → Bool) : ((setOf m l).filter fun x => p x.val = true).card = (l.filter p).length := by
  rw [← setOf_filter, card_setOf (hl.filter p)]
  intro x hx
  exact hlm x (List.mem_of_mem_filter hx)

theorem foldl_min_mem : ∀ (l : List ℕ) (a : ℕ), l.foldl min a ∈ a :: l
  | [], a => by simp
  | b :: l, a => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 (foldl_min_mem l (min a b)) with h | h
    · rw [h]
      rcases Nat.le_total a b with hab | hab
      · rw [Nat.min_eq_left hab]
        exact List.mem_cons_self
      · rw [Nat.min_eq_right hab]
        exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem foldl_min_le : ∀ (l : List ℕ) (a : ℕ), ∀ y ∈ a :: l, l.foldl min a ≤ y
  | [], a, y, hy => by
    simp only [List.mem_singleton] at hy
    simp [hy]
  | b :: l, a, y, hy => by
    rw [List.foldl_cons]
    have h := foldl_min_le l (min a b)
    rcases List.mem_cons.1 hy with rfl | hy
    · exact (h _ List.mem_cons_self).trans (Nat.min_le_left _ _)
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact (h _ List.mem_cons_self).trans (Nat.min_le_right _ _)
      · exact h y (List.mem_cons_of_mem _ hy)

theorem minD_cons_mem (a : ℕ) (l : List ℕ) : minD (a :: l) ∈ a :: l := foldl_min_mem l a

theorem minD_cons_le (a : ℕ) (l : List ℕ) : ∀ y ∈ a :: l, minD (a :: l) ≤ y :=
  foldl_min_le l a

/-- The least element of a nonempty list is its `Finset` minimum. -/
theorem min'_eq_minD {s : Finset ℕ} {a : ℕ} {l : List ℕ} (hs : s = (a :: l).toFinset)
    (h : s.Nonempty) : s.min' h = minD (a :: l) := by
  subst hs
  apply le_antisymm
  · exact Finset.min'_le _ _ (List.mem_toFinset.2 (minD_cons_mem a l))
  · exact Finset.le_min' _ _ _ fun y hy => minD_cons_le a l y (List.mem_toFinset.1 hy)

theorem nonempty_toFinset_iff {l : List ℕ} : l.toFinset.Nonempty ↔ l ≠ [] := by
  rw [Finset.nonempty_iff_ne_empty, Ne, List.toFinset_eq_empty_iff]

variable {f : ℕ → ℕ → ℕ} {c : Array ℕ}

/-- **The off-diagonal colours.** -/
theorem offCols_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ}
    (hS : ∀ x ∈ S, x < m) : offCols (setOf m S) (colOf m c) = (offColsD f S).toFinset := by
  ext k
  simp only [offCols, Finset.mem_image, Finset.mem_filter, Finset.mem_product, mem_setOf,
    offColsD, List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_filter, bne_iff_ne,
    ne_eq]
  constructor
  · rintro ⟨⟨u, v⟩, ⟨⟨hu, hv⟩, huv⟩, rfl⟩
    refine ⟨u.val, hu, v.val, ⟨hv, fun h => huv (Fin.ext h.symm)⟩, ?_⟩
    rw [hf]
  · rintro ⟨u, hu, v, ⟨hv, huv⟩, rfl⟩
    refine ⟨(⟨u, hS u hu⟩, ⟨v, hS v hv⟩), ⟨⟨hu, hv⟩, fun h => huv ?_⟩, ?_⟩
    · exact (congrArg Fin.val h).symm
    · exact (hf ⟨u, hS u hu⟩ ⟨v, hS v hv⟩).symm

theorem compStepD_lt {S : List ℕ} (hS : ∀ x ∈ S, x < m) (r : ℕ) {T : List ℕ}
    (hT : ∀ x ∈ T, x < m) : ∀ x ∈ compStepD f S r T, x < m := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · exact hT x h
  · exact hS x (List.mem_of_mem_filter h)

/-- **One closure step.** -/
theorem compStep_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ}
    (r : ℕ) {T : List ℕ} (hT : ∀ x ∈ T, x < m) :
    compStep (setOf m S) (colOf m c) r (setOf m T) = setOf m (compStepD f S r T) := by
  ext y
  simp only [compStep, compStepD, Finset.mem_union, Finset.mem_filter, mem_setOf,
    List.mem_append, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq,
    List.any_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro (h | ⟨hy, x, hx, hxy⟩)
    · exact Or.inl h
    · by_cases hyT : y.val ∈ T
      · exact Or.inl hyT
      · refine Or.inr ⟨hy, ?_, x.val, hx, ?_⟩
        · rw [List.any_eq_false]
          intro z hz e
          simp only [beq_iff_eq] at e
          exact hyT (e ▸ hz)
        · rw [hf, hf]
          exact hxy
  · rintro (h | ⟨hy, -, x, hx, hxy⟩)
    · exact Or.inl h
    · refine Or.inr ⟨hy, ⟨x, hT x hx⟩, hx, ?_⟩
      have e₁ := hf ⟨x, hT x hx⟩ y
      have e₂ := hf y ⟨x, hT x hx⟩
      simp only at e₁ e₂
      rw [← e₁, ← e₂]
      exact hxy

/-- **Components.** -/
theorem comp_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ} (hSn : S.Nodup)
    (hS : ∀ x ∈ S, x < m) (r : ℕ) (x : Fin m) :
    comp (setOf m S) (colOf m c) r x = setOf m (compD f S r x.val) := by
  have hstart : (if x ∈ setOf m S then ({x} : Finset (Fin m)) else ∅) =
      setOf m (if S.contains x.val then [x.val] else []) := by
    ext y
    by_cases hx : x.val ∈ S
    · have hx' : x ∈ setOf m S := mem_setOf.2 hx
      simp [hx', hx, mem_setOf, Fin.ext_iff]
    · have hx' : x ∉ setOf m S := fun h => hx (mem_setOf.1 h)
      simp [hx', hx, mem_setOf]
  have hlt : ∀ y ∈ (if S.contains x.val then [x.val] else []), y < m := by
    intro y hy
    split_ifs at hy with h
    · simp only [List.mem_singleton] at hy
      exact hy ▸ x.isLt
    · simp at hy
  have key : ∀ (n : ℕ) (T : List ℕ), (∀ y ∈ T, y < m) →
      (compStep (setOf m S) (colOf m c) r)^[n] (setOf m T) =
        setOf m ((compStepD f S r)^[n] T) ∧ ∀ y ∈ (compStepD f S r)^[n] T, y < m := by
    intro n
    induction n with
    | zero => intro T hT; exact ⟨rfl, hT⟩
    | succ n ih =>
      intro T hT
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, compStep_eq hf r hT]
      exact ih _ (compStepD_lt hS r hT)
  unfold comp compD
  rw [card_setOf hSn hS, hstart]
  exact (key _ _ hlt).1

theorem compD_lt {S : List ℕ} (hS : ∀ x ∈ S, x < m) (r x : ℕ) : ∀ y ∈ compD f S r x, y < m := by
  have key : ∀ (n : ℕ) (T : List ℕ), (∀ y ∈ T, y < m) → ∀ y ∈ (compStepD f S r)^[n] T, y < m := by
    intro n
    induction n with
    | zero => intro T hT; exact hT
    | succ n ih =>
      intro T hT
      rw [Function.iterate_succ_apply]
      exact ih _ (compStepD_lt hS r hT)
  apply key
  intro y hy
  split_ifs at hy with h
  · simp only [List.mem_singleton] at hy
    exact hy ▸ hS x (List.contains_iff_mem.1 h)
  · simp at hy

/-- **The disconnected colours.** -/
theorem disconn_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ} (hSn : S.Nodup)
    (hS : ∀ x ∈ S, x < m) : disconn (setOf m S) (colOf m c) = (disconnD f S).toFinset := by
  rw [disconn, offCols_eq hf hS]
  ext r
  simp only [Finset.mem_filter, List.mem_toFinset, disconnD, List.mem_filter, List.any_eq_true,
    Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨x, hx, hne⟩
    refine ⟨x.val, mem_setOf.1 hx, ?_⟩
    by_contra hall
    push Not at hall
    apply hne
    refine Finset.Subset.antisymm (comp_subset _ _ _ _) fun y hy => ?_
    rw [comp_eq hf hSn hS, mem_setOf]
    obtain ⟨z, hz, e⟩ := hall y.val (mem_setOf.1 hy)
    exact e ▸ hz
  · rintro ⟨x, hx, y, hy, hyc⟩
    refine ⟨⟨x, hS x hx⟩, mem_setOf.2 hx, fun h => ?_⟩
    have : (⟨y, hS y hy⟩ : Fin m) ∈ comp (setOf m S) (colOf m c) r ⟨x, hS x hx⟩ := by
      rw [h]
      exact mem_setOf.2 hy
    rw [comp_eq hf hSn hS, mem_setOf] at this
    exact hyc y this rfl

/-- **The colours of `C₁ × C₂`.** -/
theorem cols_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) {C₁ C₂ : List ℕ}
    (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) :
    (setOf m C₁ ×ˢ setOf m C₂).image (fun p => colOf m c p.1 p.2) =
      (colsD f C₁ C₂).toFinset := by
  ext k
  simp only [Finset.mem_image, Finset.mem_product, mem_setOf, colsD, List.mem_toFinset,
    List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨⟨x, w⟩, ⟨hx, hw⟩, rfl⟩
    exact ⟨x.val, hx, w.val, hw, hf x w⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨(⟨x, h₁ x hx⟩, ⟨w, h₂ w hw⟩), ⟨hx, hw⟩, (hf ⟨x, h₁ x hx⟩ ⟨w, h₂ w hw⟩).symm⟩

end DecodeLemmas

/-! ### Decoding the leaves and the branches -/

section DecodeLeaves

variable {m : ℕ} {f : ℕ → ℕ → ℕ} {c : Array ℕ}

theorem getD_toArray_range {α : Type*} (g : ℕ → α) (d : α) {x : ℕ} (hx : x < m) :
    ((List.range m).map g).toArray.getD x d = g x := by
  simp [Array.getD, hx]

theorem get_replicate_zero (x : ℕ) : get (Array.replicate m 0) x = 0 := by
  unfold get
  simp only [Array.getD]
  split <;> simp

theorem decode_compPart (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ}
    (hSn : S.Nodup) (hS : ∀ x ∈ S, x < m) (r : ℕ) :
    decodeLeaf m c (some (compPart f m S r)) =
      some (.part ⟨fun _ => 0, comp (setOf m S) (colOf m c) r⟩) := by
  simp only [decodeLeaf, compPart, partLeaf, ↓reduceIte, Option.some.injEq, CohOut.part.injEq,
    CPart.mk.injEq]
  constructor
  · funext x
    exact get_replicate_zero x.val
  · funext x
    rw [getD_toArray_range _ _ x.isLt, comp_eq hf hSn hS]

theorem decode_colPartD (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ} (w : Fin m) :
    decodeLeaf m c (some (colPartD f m S w.val)) =
      some (.part (colPart (setOf m S) fun x => colOf m c x w)) := by
  simp only [decodeLeaf, colPartD, partLeaf, colPart, ↓reduceIte, Option.some.injEq,
    CohOut.part.injEq, CPart.mk.injEq]
  constructor
  · funext x
    unfold get
    rw [getD_toArray_range _ _ x.isLt, hf]
  · funext x
    rw [getD_toArray_range _ _ x.isLt, setOf_filter]
    ext y
    simp only [Finset.mem_filter, beq_iff_eq, hf]

theorem decode_bipLeaf (W₁ : List ℕ) (W₂ : List (List ℕ)) (g : ℕ) :
    decodeLeaf m c (some (bipLeaf W₁ W₂ g)) =
      some (.bip (setOf m W₁) (famOf m W₂) (bipEdge (colOf m c) g)) := by
  simp [decodeLeaf, bipLeaf]

theorem famOf_singletons {L : List ℕ} (hL : ∀ x ∈ L, x < m) :
    famOf m (L.map fun z => [z]) = (setOf m L).image singleton := by
  ext s
  simp only [famOf, List.map_map, List.mem_toFinset, List.mem_map, Function.comp_apply,
    Finset.mem_image, mem_setOf]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨⟨z, hL z hz⟩, hz, ?_⟩
    ext y
    simp [mem_setOf, Fin.ext_iff]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.val, hy, ?_⟩
    ext x
    simp [mem_setOf, Fin.ext_iff]

theorem famOf_comp (hf : ∀ u v : Fin m, f u v = colOf m c u v) {S : List ℕ} (hSn : S.Nodup)
    (hS : ∀ x ∈ S, x < m) (r : ℕ) :
    famOf m (S.map (compD f S r)) = (setOf m S).image (comp (setOf m S) (colOf m c) r) := by
  ext B
  simp only [famOf, List.map_map, List.mem_toFinset, List.mem_map, Function.comp_apply,
    Finset.mem_image, mem_setOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hS y hy⟩, hy, comp_eq hf hSn hS r _⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.val, hy, (comp_eq hf hSn hS r y).symm⟩

theorem card_filter_col (hf : ∀ u v : Fin m, f u v = colOf m c u v) {C : List ℕ}
    (hn : C.Nodup) (h : ∀ x ∈ C, x < m) (w : Fin m) (k : ℕ) :
    ((setOf m C).filter fun x => colOf m c x w = k).card =
      (C.filter fun x => f x w.val == k).length := by
  rw [← card_filter_setOf hn h]
  congr 1
  ext x
  simp [hf]

theorem card_filter_row (hf : ∀ u v : Fin m, f u v = colOf m c u v) {C : List ℕ}
    (hn : C.Nodup) (h : ∀ x ∈ C, x < m) (y : Fin m) (k : ℕ) :
    ((setOf m C).filter fun z => colOf m c y z = k).card =
      (C.filter fun z => f y.val z == k).length := by
  rw [← card_filter_setOf hn h]
  congr 1
  ext x
  simp [hf]

variable {C₁ C₂ : List ℕ}

/-- The model's `big` colours (for any decision procedure of the bounded existential: the
model's, elaborated for a generic `R`, need not be the one found at `Fin m`). -/
theorem bigImp_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) {inst : DecidablePred fun k =>
      ∃ w ∈ setOf m C₂, (setOf m C₁).card <
        2 * ((setOf m C₁).filter fun x => colOf m c x w = k).card} :
    @Finset.filter _ (fun k => ∃ w ∈ setOf m C₂, (setOf m C₁).card <
        2 * ((setOf m C₁).filter fun x => colOf m c x w = k).card) inst
      ((setOf m C₁ ×ˢ setOf m C₂).image (fun p => colOf m c p.1 p.2)) =
      (bigImpD f C₁ C₂).toFinset := by
  rw [cols_eq hf h₁ h₂]
  ext k
  simp only [Finset.mem_filter, List.mem_toFinset, bigImpD, List.mem_filter, List.any_eq_true,
    decide_eq_true_eq]
  refine and_congr_right fun _ => ?_
  rw [card_setOf hn₁ h₁]
  constructor
  · rintro ⟨w, hw, h⟩
    refine ⟨w.val, mem_setOf.1 hw, ?_⟩
    rwa [card_filter_col hf hn₁ h₁] at h
  · rintro ⟨w, hw, h⟩
    refine ⟨⟨w, h₂ w hw⟩, mem_setOf.2 hw, ?_⟩
    rwa [card_filter_col hf hn₁ h₁]

theorem bigPrim_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) (y : Fin m) :
    ((setOf m C₁ ×ˢ setOf m C₂).image (fun p => colOf m c p.1 p.2)).filter (fun k =>
      (setOf m C₁).card < 2 * ((setOf m C₁).filter fun x => colOf m c x y = k).card) =
      (bigPrimD f C₁ C₂ y.val).toFinset := by
  rw [cols_eq hf h₁ h₂]
  ext k
  simp only [Finset.mem_filter, List.mem_toFinset, bigPrimD, List.mem_filter, decide_eq_true_eq]
  rw [card_setOf hn₁ h₁, card_filter_col hf hn₁ h₁]

theorem otherCols_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) (h₁ : ∀ x ∈ C₁, x < m)
    (h₂ : ∀ x ∈ C₂, x < m) (g : ℕ) :
    ((setOf m C₁ ×ˢ setOf m C₂).image (fun p => colOf m c p.1 p.2)).erase g =
      (otherColsD f C₁ C₂ g).toFinset := by
  rw [cols_eq hf h₁ h₂]
  ext k
  simp only [Finset.mem_erase, List.mem_toFinset, otherColsD, List.mem_filter, bne_iff_ne,
    ne_eq]
  tauto

theorem blues_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₂ : C₂.Nodup)
    (h₂ : ∀ x ∈ C₂, x < m) (y : Fin m) :
    (offCols (setOf m C₂) (colOf m c)).filter (fun b =>
      0 < ((setOf m C₂).filter fun z => colOf m c y z = b).card ∧
        2 * ((setOf m C₂).filter fun z => colOf m c y z = b).card < (setOf m C₂).card) =
      (bluesD f C₂ y.val).toFinset := by
  rw [offCols_eq hf h₂]
  ext k
  simp only [Finset.mem_filter, List.mem_toFinset, bluesD, List.mem_filter, decide_eq_true_eq]
  rw [card_setOf hn₂ h₂, card_filter_row hf hn₂ h₂]

theorem twinCls_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v)
    {B : List ℕ} (hB : ∀ y ∈ B, y < m) (g : ℕ) (x : Fin m) :
    twinCls (setOf m C₁) (setOf m B) (fun x y => decide (colOf m c x y = g)) x =
      setOf m (C₁.filter fun x' => B.all fun y => (f x.val y == g) == (f x' y == g)) := by
  ext x'
  simp only [twinCls, Finset.mem_filter, mem_setOf, List.mem_filter, List.all_eq_true]
  refine and_congr_right fun hx' => ?_
  constructor
  · intro h y hy
    have := h ⟨y, hB y hy⟩ hy
    rw [← hf, ← hf] at this
    simpa [Bool.decide_iff_dist, decide_eq_decide] using this
  · intro h y hy
    have := h y.val hy
    rw [← hf, ← hf]
    simpa [decide_eq_decide] using this

theorem twinOK_iff (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (h₁ : ∀ x ∈ C₁, x < m) {B : List ℕ} (hB : ∀ y ∈ B, y < m) (g : ℕ) :
    (∀ x ∈ setOf m C₁, 2 * (twinCls (setOf m C₁) (setOf m B)
        (fun x y => decide (colOf m c x y = g)) x).card ≤ (setOf m C₁).card) ↔
      twinOK f C₁ B g = true := by
  simp only [twinOK, List.all_eq_true, decide_eq_true_eq]
  rw [card_setOf hn₁ h₁]
  have hcard : ∀ x : Fin m, (twinCls (setOf m C₁) (setOf m B)
      (fun x y => decide (colOf m c x y = g)) x).card =
      (C₁.filter fun x' => B.all fun y => (f x.val y == g) == (f x' y == g)).length := by
    intro x
    rw [twinCls_eq hf hB, card_setOf (hn₁.filter _)]
    intro z hz
    exact h₁ z (List.mem_of_mem_filter hz)
  constructor
  · intro h x hx
    have := h ⟨x, h₁ x hx⟩ (mem_setOf.2 hx)
    rwa [hcard] at this
  · intro h x hx
    rw [hcard]
    exact h x.val (mem_setOf.1 hx)

end DecodeLeaves

/-! ### The data tree decodes to the model -/

section DecodeMain

variable {m : ℕ} {f : ℕ → ℕ → ℕ} {c : Array ℕ} {C₁ C₂ : List ℕ}

theorem good_iff (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (hn₂ : C₂.Nodup) (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) (red g : ℕ) (y : Fin m) :
    (∀ x ∈ setOf m C₁, 2 * (twinCls (setOf m C₁) (comp (setOf m C₂) (colOf m c) red y)
        (fun x y => decide (colOf m c x y = g)) x).card ≤ (setOf m C₁).card) ↔
      twinOK f C₁ (compD f C₂ red y.val) g = true := by
  rw [comp_eq hf hn₂ h₂]
  exact twinOK_iff hf hn₁ h₁ (compD_lt h₂ red y.val) g

/-- The model's `good` blocks (for any decision procedure of the bounded universal, as in
`bigImp_eq`). -/
theorem mem_good_iff (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (hn₂ : C₂.Nodup) (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) (red g : ℕ) (y : Fin m)
    (hy : y ∈ setOf m C₂) {inst : DecidablePred fun B => ∀ x ∈ setOf m C₁,
      2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
        (setOf m C₁).card} :
    comp (setOf m C₂) (colOf m c) red y ∈ @Finset.filter _ (fun B => ∀ x ∈ setOf m C₁,
        2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
          (setOf m C₁).card) inst ((setOf m C₂).image (comp (setOf m C₂) (colOf m c) red)) ↔
      twinOK f C₁ (compD f C₂ red y.val) g = true := by
  rw [Finset.mem_filter, ← good_iff hf hn₁ hn₂ h₁ h₂]
  exact and_iff_right (Finset.mem_image_of_mem _ hy)

theorem goodOpts_eq (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (hn₂ : C₂.Nodup) (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) (red g : ℕ)
    {inst : DecidablePred fun B => ∀ x ∈ setOf m C₁,
      2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
        (setOf m C₁).card}
    {inst' : DecidablePred fun y => comp (setOf m C₂) (colOf m c) red y ∈
      @Finset.filter _ (fun B => ∀ x ∈ setOf m C₁,
        2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
          (setOf m C₁).card) inst ((setOf m C₂).image (comp (setOf m C₂) (colOf m c) red))} :
    @Finset.filter _ (fun y => comp (setOf m C₂) (colOf m c) red y ∈
      @Finset.filter _ (fun B => ∀ x ∈ setOf m C₁,
        2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
          (setOf m C₁).card) inst ((setOf m C₂).image (comp (setOf m C₂) (colOf m c) red)))
      inst' (setOf m C₂) = setOf m (goodOptsD f C₁ C₂ red g) := by
  ext y
  rw [Finset.mem_filter, goodOptsD]
  constructor
  · rintro ⟨hy, hg⟩
    exact mem_setOf.2 (List.mem_filter.2
      ⟨mem_setOf.1 hy, (mem_good_iff hf hn₁ hn₂ h₁ h₂ red g y hy).1 hg⟩)
  · intro hy
    obtain ⟨hy2, hg⟩ := List.mem_filter.1 (mem_setOf.1 hy)
    exact ⟨mem_setOf.2 hy2, (mem_good_iff hf hn₁ hn₂ h₁ h₂ red g y (mem_setOf.2 hy2)).2 hg⟩

theorem good_nonempty_iff (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (hn₂ : C₂.Nodup) (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) (red g : ℕ)
    {inst : DecidablePred fun B => ∀ x ∈ setOf m C₁,
      2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
        (setOf m C₁).card} :
    (@Finset.filter _ (fun B => ∀ x ∈ setOf m C₁,
        2 * (twinCls (setOf m C₁) B (fun x y => decide (colOf m c x y = g)) x).card ≤
          (setOf m C₁).card) inst
      ((setOf m C₂).image (comp (setOf m C₂) (colOf m c) red))).Nonempty ↔
      goodOptsD f C₁ C₂ red g ≠ [] := by
  constructor
  · rintro ⟨B, hB⟩
    obtain ⟨hBi, -⟩ := Finset.mem_filter.1 hB
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hBi
    have hy' : y.val ∈ goodOptsD f C₁ C₂ red g :=
      List.mem_filter.2 ⟨mem_setOf.1 hy, (mem_good_iff hf hn₁ hn₂ h₁ h₂ red g y hy).1 hB⟩
    intro e
    rw [e] at hy'
    simp at hy'
  · intro hne
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨hy2, hg⟩ := List.mem_filter.1 hy
    exact ⟨_, (mem_good_iff hf hn₁ hn₂ h₁ h₂ red g ⟨y, h₂ y hy2⟩ (mem_setOf.2 hy2)).2 hg⟩

/-- **Coherent Split-or-Johnson on data decodes to the model** (`R = Fin m`). -/
theorem decode_cohSojD (hf : ∀ u v : Fin m, f u v = colOf m c u v) (hn₁ : C₁.Nodup)
    (hn₂ : C₂.Nodup) (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) :
    decodeTree m c (cohSojD f m C₁ C₂) = cohSoj (setOf m C₁) (setOf m C₂) (colOf m c) := by
  have hd₁ := disconn_eq hf hn₁ h₁
  have hd₂ := disconn_eq hf hn₂ h₂
  unfold cohSoj cohSojD
  dsimp only
  rcases e₁ : disconnD f C₁ with _ | ⟨r, rs⟩
  · rw [e₁] at hd₁
    rcases e₂ : disconnD f C₂ with _ | ⟨r₂, rs₂⟩
    · rw [e₂] at hd₂
      dsimp only
      split
      · rename_i hne
        rw [hd₁] at hne
        simp at hne
      split
      · rename_i hne
        rw [hd₂] at hne
        simp at hne
      simp only [decodeTree]
      congr 1
      funext y
      have hbp := bigPrim_eq hf hn₁ h₁ h₂ y
      have hbl := blues_eq hf hn₂ h₂ y
      simp only [primLeaf]
      rcases eb : bigPrimD f C₁ C₂ y.val with _ | ⟨v₀, vs⟩
      · rw [eb] at hbp
        dsimp only
        split
        · rename_i hv
          rw [hbp] at hv
          simp at hv
        · exact congrArg CTree.leaf (decode_colPartD hf y)
      · rw [eb] at hbp
        rcases ebl : bluesD f C₂ y.val with _ | ⟨b₀, bs⟩
        · rw [ebl] at hbl
          dsimp only
          split
          · split
            · rename_i hb
              rw [hbl] at hb
              simp at hb
            · rfl
          · rename_i hv
            rw [hbp] at hv
            simp at hv
        · rw [ebl] at hbl
          dsimp only
          split
          · rename_i hv
            split
            · rename_i hb
              rw [min'_eq_minD hbp hv, min'_eq_minD hbl hb, decode_bipLeaf, setOf_filter,
                famOf_singletons (fun z hz => h₂ z (List.mem_of_mem_filter hz)), setOf_filter]
              congr 3
              · ext x
                simp [hf]
              · ext z
                simp [hf]
            · rename_i hb
              rw [hbl] at hb
              simp at hb
          · rename_i hv
            rw [hbp] at hv
            simp at hv
    · rw [e₂] at hd₂
      dsimp only
      split
      · rename_i hne
        rw [hd₁] at hne
        simp at hne
      split
      swap
      · rename_i hne
        rw [hd₂] at hne
        simp at hne
      rename_i hne
      rw [min'_eq_minD hd₂ hne]
      simp only [imprimTree]
      rcases eb : bigImpD f C₁ C₂ with _ | ⟨v₀, vs⟩
      · dsimp only
        split
        · rename_i hv
          rw [bigImp_eq hf hn₁ h₁ h₂, eb] at hv
          simp at hv
        · simp only [decodeTree]
          congr 1
          funext w
          exact congrArg CTree.leaf (decode_colPartD hf w)
      · dsimp only
        have hbi := fun i => (bigImp_eq hf hn₁ h₁ h₂ (inst := i)).trans (congrArg _ eb)
        have hgn := fun i =>
          good_nonempty_iff hf hn₁ hn₂ h₁ h₂ (minD (r₂ :: rs₂)) (minD (v₀ :: vs)) (inst := i)
        have hoc := otherCols_eq hf h₁ h₂ (minD (v₀ :: vs)) (C₂ := C₂)
        rcases eg : goodOptsD f C₁ C₂ (minD (r₂ :: rs₂)) (minD (v₀ :: vs)) with _ | ⟨y₀, ys⟩
        · rcases eo : otherColsD f C₁ C₂ (minD (v₀ :: vs)) with _ | ⟨g₀, gs⟩
          · rw [eo] at hoc
            dsimp only
            split
            · rename_i hv
              rw [min'_eq_minD (hbi _) hv]
              split
              · rename_i hg
                exact absurd ((hgn _).1 hg) (by rw [eg]; simp)
              · split
                · rename_i hg'
                  rw [hoc] at hg'
                  simp at hg'
                · rfl
            · rename_i hv
              rw [hbi] at hv
              simp at hv
          · rw [eo] at hoc
            dsimp only
            split
            · rename_i hv
              rw [min'_eq_minD (hbi _) hv]
              split
              · rename_i hg
                exact absurd ((hgn _).1 hg) (by rw [eg]; simp)
              · split
                · rename_i hg'
                  simp only [decodeTree]
                  rw [min'_eq_minD hoc hg', decode_bipLeaf, famOf_comp hf hn₂ h₂]
                · rename_i hg'
                  rw [hoc] at hg'
                  simp at hg'
            · rename_i hv
              rw [hbi] at hv
              simp at hv
        · dsimp only
          split
          · rename_i hv
            rw [min'_eq_minD (hbi _) hv]
            split
            · simp only [decodeTree]
              rw [goodOpts_eq hf hn₁ hn₂ h₁ h₂, eg]
              congr 1
              funext y
              rw [decode_bipLeaf, famOf_singletons (compD_lt h₂ _ _), comp_eq hf hn₂ h₂]
            · rename_i hg
              exact absurd ((hgn _).2 (by rw [eg]; simp)) hg
          · rename_i hv
            rw [hbi] at hv
            simp at hv
  · rw [e₁] at hd₁
    dsimp only
    split
    · rename_i hne
      rw [min'_eq_minD hd₁ hne]
      simp only [decodeTree]
      rw [decode_compPart hf hn₁ h₁]
    · rename_i hne
      rw [hd₁] at hne
      simp at hne

end DecodeMain

/-! ### Results and the colouring read from the array -/

section Results

/-- The result of a program: a leaf (`false`, `[]`, `#[o]`) or a node (`true`, the options,
the leaves at all points `y < m`). -/
abbrev ResD := Bool × (List ℕ × Array (Option LeafD))

/-- The result of a data tree; a node lists its leaves at all points below `m`. -/
def toRes (m : ℕ) : DTree → ResD
  | .leaf o => (false, [], #[o])
  | .node opts k => (true, opts, ((List.range m).map k).toArray)

/-- Decoding a result. -/
def decodeRes (m : ℕ) (c : Array ℕ) : ResD → CTree (Fin m) (Option (CohOut (Fin m)))
  | (false, _, arr) => .leaf (decodeLeaf m c (arr.getD 0 none))
  | (true, opts, arr) => .node (setOf m opts) fun y => .leaf (decodeLeaf m c (arr.getD y.val none))

theorem decodeRes_toRes (m : ℕ) (c : Array ℕ) (t : DTree) :
    decodeRes m c (toRes m t) = decodeTree m c t := by
  cases t with
  | leaf o => rfl
  | node opts k =>
    simp only [toRes, decodeRes, decodeTree]
    congr 1
    funext y
    simp [Array.getD_eq_getD_getElem?, y.isLt]

/-- The row offsets `u m` for `u < m`. -/
def offsArr (m : ℕ) : Array ℕ := ((List.range m).map (· * m)).toArray

/-- The colouring read from the array `c` with the row offsets `offs`. -/
def fA (offs c : Array ℕ) (u v : ℕ) : ℕ := get c (get offs u + v)

theorem fA_offsArr (m : ℕ) (c : Array ℕ) (u v : Fin m) :
    fA (offsArr m) c u v = colOf m c u v := by
  simp [fA, offsArr, colOf, get, Array.getD_eq_getD_getElem?, u.isLt]

/-- **The data result decodes to the model** (`R = Fin m`). -/
theorem decodeRes_cohSojD {m : ℕ} {c : Array ℕ} {C₁ C₂ : List ℕ} (hn₁ : C₁.Nodup)
    (hn₂ : C₂.Nodup) (h₁ : ∀ x ∈ C₁, x < m) (h₂ : ∀ x ∈ C₂, x < m) :
    decodeRes m c (toRes m (cohSojD (fA (offsArr m) c) m C₁ C₂)) =
      cohSoj (setOf m C₁) (setOf m C₂) (colOf m c) := by
  rw [decodeRes_toRes, decode_cohSojD (fA_offsArr m c) hn₁ hn₂ h₁ h₂]

end Results

/-! ### Programs -/

/-- Leaves on data as a type of the cost language (`LeafD`). -/
abbrev cohLeafTy : Cost.Ty :=
  .prod .nat (.prod (.prod (.array .nat) (.array (.list .nat)))
    (.prod (.list .nat) (.prod (.list (.list .nat)) .nat)))

/-- Results as a type of the cost language (`ResD`). -/
abbrev cohResTy : Cost.Ty := .prod .bool (.prod (.list .nat) (.array (.option cohLeafTy)))

section Programs

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The row offsets `u m` for `u < m`, by a fold (the cost language has no multiplication). -/
def csOffsProg (m : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range m) fun is =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nil =>
  .bind (.op2 .pair z nil) fun st₀ =>
  .bind (.foldList is st₀ fun st _ =>
      .bind (.op1 .fst st) fun off => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .cons off acc) fun acc' => .bind (.op2 .add off m) fun off' =>
      .op2 .pair off' acc') fun fin =>
  .bind (.op1 .snd fin) fun racc => .bind (.op1 .reverse racc) fun l => .op1 .arrayOfList l

/-- The colour of `(u, v)`: the entry `offs[u] + v` of `c` (`fA`). -/
def csColProg (offs c : var (.array .nat)) (u v : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .arrayGet offs u) fun o => .bind (.op2 .add o v) fun i => .op2 .arrayGet c i

/-- Membership of `y` in `xs`. -/
def csMemProg (xs : var (.list .nat)) (y : var .nat) : Prog S rec var .bool :=
  anyList xs fun x => .op2 .natEq y x

/-- Equality of Booleans. -/
def csBeqProg (p q : var .bool) : Prog S rec var .bool :=
  .bind (.op2 .and p q) fun both => .bind (.op1 .not p) fun np => .bind (.op1 .not q) fun nq =>
  .bind (.op2 .and np nq) fun neither => .op2 .or both neither

/-- `xs.flatMap F` for lists of numbers: map, then concatenate. -/
def csFlatMap {a' : Ty} (xs : var (.list a')) (f : var a' → Prog S rec var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (mapList xs f) fun rows => .bind (.op1 .reverse rows) fun rr =>
  .bind (.op0 .nil) fun nil => .foldList rr nil fun acc row => .op2 .append row acc

/-- `offColsD`. -/
def csOffColsProg (offs c : var (.array .nat)) (ps : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  csFlatMap ps fun u =>
    .bind (Toolkit.filterList ps fun v => .bind (.op2 .natEq v u) fun e => .op1 .not e) fun T =>
    mapList T fun v => csColProg offs c u v

/-- `compStepD`. -/
def csCompStepProg (offs c : var (.array .nat)) (ps : var (.list .nat)) (r : var .nat)
    (T : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (Toolkit.filterList ps fun y =>
      .bind (csMemProg T y) fun inT => .bind (.op1 .not inT) fun out =>
      .bind (anyList T fun x =>
          .bind (csColProg offs c x y) fun a => .bind (.op2 .natEq a r) fun ea =>
          .bind (csColProg offs c y x) fun b => .bind (.op2 .natEq b r) fun eb =>
          .op2 .or ea eb) fun adj =>
      .op2 .and out adj) fun new =>
  .op2 .append T new

/-- `compD`: `|ps|` closure steps. -/
def csCompProg (offs c : var (.array .nat)) (ps : var (.list .nat)) (r x : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (csMemProg ps x) fun inS =>
  .bind (.ite inS (.bind (.op0 .nil) fun nil => .op2 .cons x nil) (.op0 .nil)) fun T₀ =>
  .bind (.op1 .length ps) fun n => .bind (.op1 .range n) fun is =>
  .foldList is T₀ fun T _ => csCompStepProg offs c ps r T

/-- `disconnD`. -/
def csDisconnProg (offs c : var (.array .nat)) (ps : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (csOffColsProg offs c ps) fun cols =>
  Toolkit.filterList cols fun r => anyList ps fun x =>
    .bind (csCompProg offs c ps r x) fun T => anyList ps fun y =>
      .bind (csMemProg T y) fun b => .op1 .not b

/-- `colsD`. -/
def csColsProg (offs c : var (.array .nat)) (C₁ C₂ : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  csFlatMap C₁ fun x => mapList C₂ fun w => csColProg offs c x w

/-- Whether more than half of the `n₁` points `x ∈ C₁` have colour `k` to `w`. -/
def csMajProg (offs c : var (.array .nat)) (n₁ : var .nat) (C₁ : var (.list .nat))
    (w k : var .nat) : Prog S rec var .bool :=
  .bind (Toolkit.countList C₁ fun x => .bind (csColProg offs c x w) fun a => .op2 .natEq a k)
    fun cnt => .bind (.op2 .add cnt cnt) fun d => .op2 .natLt n₁ d

/-- `bigImpD`, from the colours `cols = colsD`. -/
def csBigImpProg (offs c : var (.array .nat)) (C₁ C₂ cols : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .length C₁) fun n₁ =>
  Toolkit.filterList cols fun k => anyList C₂ fun w => csMajProg offs c n₁ C₁ w k

/-- `bigPrimD`, from the colours `cols = colsD`. -/
def csBigPrimProg (offs c : var (.array .nat)) (C₁ cols : var (.list .nat)) (y : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .length C₁) fun n₁ => Toolkit.filterList cols fun k => csMajProg offs c n₁ C₁ y k

/-- `otherColsD`, from the colours `cols = colsD`. -/
def csOtherColsProg (cols : var (.list .nat)) (g : var .nat) : Prog S rec var (.list .nat) :=
  Toolkit.filterList cols fun k => .bind (.op2 .natEq k g) fun e => .op1 .not e

/-- `bluesD`, from the colours `oc₂ = offColsD C₂`. -/
def csBluesProg (offs c : var (.array .nat)) (C₂ oc₂ : var (.list .nat)) (y : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .length C₂) fun n₂ =>
  Toolkit.filterList oc₂ fun b =>
    .bind (Toolkit.countList C₂ fun z => .bind (csColProg offs c y z) fun a => .op2 .natEq a b)
      fun cnt =>
    .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .natLt z cnt) fun pos =>
    .bind (.op2 .add cnt cnt) fun d => .bind (.op2 .natLt d n₂) fun small => .op2 .and pos small

/-- `twinOK`. -/
def csTwinOKProg (offs c : var (.array .nat)) (C₁ B : var (.list .nat)) (g : var .nat) :
    Prog S rec var .bool :=
  .bind (.op1 .length C₁) fun n₁ =>
  allList C₁ fun x =>
    .bind (Toolkit.countList C₁ fun x' => allList B fun y =>
        .bind (csColProg offs c x y) fun a => .bind (.op2 .natEq a g) fun ea =>
        .bind (csColProg offs c x' y) fun b => .bind (.op2 .natEq b g) fun eb =>
        csBeqProg ea eb) fun cnt =>
    .bind (.op2 .add cnt cnt) fun d => .bind (.op2 .natLt n₁ d) fun lt => .op1 .not lt

/-- `goodOptsD`. -/
def csGoodOptsProg (offs c : var (.array .nat)) (C₁ C₂ : var (.list .nat)) (red violet : var .nat) :
    Prog S rec var (.list .nat) :=
  Toolkit.filterList C₂ fun y =>
    .bind (csCompProg offs c C₂ red y) fun B => csTwinOKProg offs c C₁ B violet

/-- `partLeaf`. -/
def csPartLeafProg (col : var (.array .nat)) (blk : var (.array (.list .nat))) :
    Prog S rec var cohLeafTy :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .pair col blk) fun cb =>
  .bind (.op0 .nil) fun w₁ => .bind (.op0 .nil) fun w₂ => .bind (.op2 .pair w₂ z) fun wg =>
  .bind (.op2 .pair w₁ wg) fun ws => .bind (.op2 .pair cb ws) fun rest => .op2 .pair z rest

/-- `bipLeaf`. -/
def csBipLeafProg (W₁ : var (.list .nat)) (W₂ : var (.list (.list .nat))) (g : var .nat) :
    Prog S rec var cohLeafTy :=
  .bind (.op0 (.natLit 1)) fun one => .bind (.op0 .nil) fun l₁ => .bind (.op1 .arrayOfList l₁)
    fun a₁ =>
  .bind (.op0 .nil) fun l₂ => .bind (.op1 .arrayOfList l₂) fun a₂ => .bind (.op2 .pair a₁ a₂)
    fun cb =>
  .bind (.op2 .pair W₂ g) fun wg => .bind (.op2 .pair W₁ wg) fun ws => .bind (.op2 .pair cb ws)
    fun rest => .op2 .pair one rest

/-- The singletons of the points of `xs`. -/
def csSingletonsProg (xs : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  mapList xs fun z => .bind (.op0 .nil) fun nil => .op2 .cons z nil

/-- `compPart`. -/
def csCompPartProg (offs c : var (.array .nat)) (m : var .nat) (ps : var (.list .nat))
    (r : var .nat) : Prog S rec var cohLeafTy :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk m z) fun col =>
  .bind (.op1 .range m) fun is => .bind (mapList is fun x => csCompProg offs c ps r x) fun bl =>
  .bind (.op1 .arrayOfList bl) fun blk => csPartLeafProg col blk

/-- `colPartD`. -/
def csColPartProg (offs c : var (.array .nat)) (m : var .nat) (ps : var (.list .nat))
    (w : var .nat) : Prog S rec var cohLeafTy :=
  .bind (.op1 .range m) fun is =>
  .bind (mapList is fun x => csColProg offs c x w) fun cl => .bind (.op1 .arrayOfList cl)
    fun col =>
  .bind (mapList is fun x => .bind (csColProg offs c x w) fun fx =>
      Toolkit.filterList ps fun y => .bind (csColProg offs c y w) fun fy => .op2 .natEq fy fx)
    fun bl =>
  .bind (.op1 .arrayOfList bl) fun blk => csPartLeafProg col blk

/-- `primLeaf`, from `cols = colsD` and `oc₂ = offColsD C₂`. -/
def csPrimLeafProg (offs c : var (.array .nat)) (m : var .nat) (C₁ C₂ cols oc₂ : var (.list .nat))
    (y : var .nat) : Prog S rec var (.option cohLeafTy) :=
  .bind (csBigPrimProg offs c C₁ cols y) fun bp =>
  .caseList bp (.bind (csColPartProg offs c m C₁ y) fun l => .op1 .some l) fun _ _ =>
    .bind (csBluesProg offs c C₂ oc₂ y) fun bl =>
    .caseList bl (.op0 .none) fun _ _ =>
      .bind (Toolkit.minProg bp) fun violet => .bind (Toolkit.minProg bl) fun blue =>
      .bind (Toolkit.filterList C₁ fun x =>
          .bind (csColProg offs c x y) fun a => .op2 .natEq a violet) fun W₁ =>
      .bind (Toolkit.filterList C₂ fun z =>
          .bind (csColProg offs c y z) fun a => .op2 .natEq a blue) fun Z =>
      .bind (csSingletonsProg Z) fun W₂ =>
      .bind (csBipLeafProg W₁ W₂ violet) fun l => .op1 .some l

/-- A leaf result. -/
def csLeafRes (o : var (.option cohLeafTy)) : Prog S rec var cohResTy :=
  .bind (.op0 (.boolLit false)) fun f => .bind (.op0 .nil) fun nil =>
  .bind (.op0 .nil) fun e => .bind (.op2 .cons o e) fun l => .bind (.op1 .arrayOfList l) fun arr =>
  .bind (.op2 .pair nil arr) fun p => .op2 .pair f p

/-- A node result: the options and the leaves at all points below `m`. -/
def csNodeRes (m : var .nat) (opts : var (.list .nat))
    (k : var .nat → Prog S rec var (.option cohLeafTy)) : Prog S rec var cohResTy :=
  .bind (.op0 (.boolLit true)) fun t => .bind (.op1 .range m) fun is =>
  .bind (mapList is k) fun ls => .bind (.op1 .arrayOfList ls) fun arr =>
  .bind (.op2 .pair opts arr) fun p => .op2 .pair t p

/-- `imprimTree`, from `cols = colsD`. -/
def csImprimProg (offs c : var (.array .nat)) (m : var .nat) (C₁ C₂ cols : var (.list .nat))
    (red : var .nat) : Prog S rec var cohResTy :=
  .bind (csBigImpProg offs c C₁ C₂ cols) fun bi =>
  .caseList bi (csNodeRes m C₂ fun w => .bind (csColPartProg offs c m C₁ w) fun l => .op1 .some l)
    fun _ _ =>
      .bind (Toolkit.minProg bi) fun violet =>
      .bind (csGoodOptsProg offs c C₁ C₂ red violet) fun go =>
      .caseList go
        (.bind (csOtherColsProg cols violet) fun oc =>
          .caseList oc (.bind (.op0 .none) fun o => csLeafRes o) fun _ _ =>
            .bind (Toolkit.minProg oc) fun green =>
            .bind (mapList C₂ fun y => csCompProg offs c C₂ red y) fun W₂ =>
            .bind (csBipLeafProg C₁ W₂ green) fun l => .bind (.op1 .some l) fun o => csLeafRes o)
        fun _ _ =>
          csNodeRes m go fun y =>
            .bind (csCompProg offs c C₂ red y) fun B => .bind (csSingletonsProg B) fun W₂ =>
            .bind (csBipLeafProg C₁ W₂ violet) fun l => .op1 .some l

/-- `cohSojD` with the colouring read from `c` through the row offsets `offs`. -/
def csSojProg (offs c : var (.array .nat)) (m : var .nat) (C₁ C₂ : var (.list .nat)) :
    Prog S rec var cohResTy :=
  .bind (csDisconnProg offs c C₁) fun d₁ =>
  .caseList d₁
    (.bind (csDisconnProg offs c C₂) fun d₂ =>
      .bind (csColsProg offs c C₁ C₂) fun cols =>
      .caseList d₂
        (.bind (csOffColsProg offs c C₂) fun oc₂ =>
          csNodeRes m C₂ fun y => csPrimLeafProg offs c m C₁ C₂ cols oc₂ y)
        fun _ _ => .bind (Toolkit.minProg d₂) fun red => csImprimProg offs c m C₁ C₂ cols red)
    fun _ _ => .bind (Toolkit.minProg d₁) fun r =>
      .bind (csCompPartProg offs c m C₁ r) fun l => .bind (.op1 .some l) fun o => csLeafRes o

/-- **Coherent Split-or-Johnson on data**: the points `0, …, m - 1`, the colouring of pairs as
the `m × m` array `c` (row-major), the vertex colour classes `C₁` and `C₂` as lists. -/
def cohSojProg (m : var .nat) (c : var (.array .nat)) (C₁ C₂ : var (.list .nat)) :
    Prog S rec var cohResTy :=
  .bind (csOffsProg m) fun offs => csSojProg offs c m C₁ C₂

end Programs

/-! ### Specs -/

section Specs

open Cost Programs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem csOffs_fold (m : ℕ) : ∀ n : ℕ,
    (List.range n).foldl (fun st (_ : ℕ) => (st.1 + m, st.1 :: st.2)) ((0 : ℕ), ([] : List ℕ)) =
      (n * m, ((List.range n).map (· * m)).reverse)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, csOffs_fold m n]
    simp [Nat.succ_mul]

theorem RunsWithin.csOffsProg (m : ℕ) :
    RunsWithin X body (SoJProg.csOffsProg m) (offsArr m) (10 * m + 9) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list .nat))
    (f := fun st _ => Prog.bind (.op1 .fst st) fun off => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .cons off acc) fun acc' => .bind (.op2 .add off m) fun off' =>
      .op2 .pair off' acc')
    (F := fun st _ => (st.1 + m, st.1 :: st.2)) (cf := fun _ => 5) (List.range m) (0, [])
    fun st _ _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp [Prim.cost]
  rw [csOffs_fold, sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, offsArr]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_reverse,
      List.length_map]
    omega

theorem RunsWithin.csColProg (offs c : Array ℕ) (u v : ℕ) :
    RunsWithin X body (SoJProg.csColProg offs c u v) (fA offs c u v) 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.csMemProg (xs : List ℕ) (y : ℕ) :
    RunsWithin X body (SoJProg.csMemProg xs y) (xs.contains y) (3 * xs.length + 1) := by
  refine ((RunsWithin.anyList_le (c := 1) (P := fun x => y == x) fun x _ =>
    RunsWithin.prim_le rfl le_rfl).of_eq List.any_beq).mono ?_
  omega

theorem RunsWithin.csBeqProg (p q : Bool) :
    RunsWithin X body (SoJProg.csBeqProg p q) (p == q) 5 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by cases p <;> cases q <;> rfl) le_rfl
  case hc => simp [Prim.cost]

theorem foldl_append_rev_nat : ∀ (rows : List (List ℕ)),
    rows.reverse.foldl (fun acc row => row ++ acc) [] = rows.flatten := by
  intro rows
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp

theorem RunsWithin.csFlatMap {a' : Ty} {xs : List a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote (.list .nat)} {F : a'.denote → List ℕ} {c L : ℕ}
    (hf : ∀ x ∈ xs, RunsWithin X body (f x) (F x) c) (hL : ∀ x ∈ xs, (F x).length ≤ L) :
    RunsWithin X body (SoJProg.csFlatMap xs f) (xs.flatMap F) (xs.length * (c + L + 6) + 4) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (a' := .list .nat)
    (b' := .list .nat) (I := fun _ => True) (c := L + 1)
    (f := fun acc row => Prog.op2 .append row acc) (F := fun acc row => row ++ acc)
    (xs.map F).reverse [] (fun acc _ row hrow => by
      refine ⟨RunsWithin.prim_le rfl ?_, trivial⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hrow)
      simpa [Prim.cost] using hL x hx) trivial
  rw [foldl_append_rev_nat, List.length_reverse, List.length_map] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapList_le hf)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.1.of_eq (by simp [List.flatMap])
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map, Nat.mul_add, Nat.mul_one]
    omega

/-- A fold that iterates `g` (ignoring the elements), keeping an invariant `I` indexed by the
number of steps, with a uniform cost bound `c` for the first `K` steps. -/
theorem RunsWithin.foldList_iter {b' : Ty} {g : b'.denote → Prog S (a, b) Ty.denote b'}
    {G : b'.denote → b'.denote} {I : ℕ → b'.denote → Prop} {c K : ℕ}
    (hg : ∀ j T, j < K → I j T → RunsWithin X body (g T) (G T) c ∧ I (j + 1) (G T)) :
    ∀ (xs : List ℕ) (k : ℕ) (init : b'.denote), k + xs.length ≤ K → I k init →
      RunsWithin X body (.foldList (a := .nat) xs init fun T _ => g T) (G^[xs.length] init)
        (xs.length * (c + 1)) ∧ I (k + xs.length) (G^[xs.length] init)
  | [], k, init, _, hI => ⟨by simpa using RunsWithin.foldList_nil, by simpa using hI⟩
  | x :: xs, k, init, hK, hI => by
    simp only [List.length_cons] at hK
    obtain ⟨h₁, hI₁⟩ := hg k init (by omega) hI
    obtain ⟨h₂, hI₂⟩ := RunsWithin.foldList_iter hg xs (k + 1) (G init) (by omega) hI₁
    refine ⟨((RunsWithin.foldList_cons (x := x) h₁ h₂).of_eq ?_).mono ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply]
    · simp only [List.length_cons, Nat.succ_mul]
      omega
    · rw [List.length_cons, Function.iterate_succ_apply,
        show k + (xs.length + 1) = k + 1 + xs.length by omega]
      exact hI₂

theorem length_compStepD_le (f : ℕ → ℕ → ℕ) (ps : List ℕ) (r : ℕ) (T : List ℕ) :
    (compStepD f ps r T).length ≤ T.length + ps.length := by
  simp only [compStepD, List.length_append]
  have := List.length_filter_le (fun y => !(T.contains y) &&
    T.any fun x => f x y == r || f y x == r) ps
  omega

theorem length_iter_compStepD_le (f : ℕ → ℕ → ℕ) (ps : List ℕ) (r : ℕ) :
    ∀ (j : ℕ) (T : List ℕ), ((compStepD f ps r)^[j] T).length ≤ T.length + j * ps.length
  | 0, T => by simp
  | j + 1, T => by
    rw [Function.iterate_succ_apply]
    have h₁ := length_iter_compStepD_le f ps r j (compStepD f ps r T)
    have h₂ := length_compStepD_le f ps r T
    rw [Nat.succ_mul]
    omega

theorem length_compD_le (f : ℕ → ℕ → ℕ) (ps : List ℕ) (r x : ℕ) :
    (compD f ps r x).length ≤ ps.length * ps.length + 1 := by
  have h := length_iter_compStepD_le f ps r ps.length (if ps.contains x then [x] else [])
  have h₀ : (if ps.contains x then [x] else []).length ≤ 1 := by split <;> simp
  unfold compD
  omega

/-- The cost of `csOffColsProg` for at most `N` points. -/
def offColsCost (N : ℕ) : ℕ := N * (13 * N + 11) + 4

/-- The cost of `csCompStepProg` for at most `N` points and a current list of at most `L`. -/
def stepCost (N L : ℕ) : ℕ := N * (14 * L + 8) + L + 4

/-- The cost of `csCompProg` for at most `N` points. -/
def compCost (N : ℕ) : ℕ := 5 * N + 6 + N * (stepCost N (N * N + 1) + 1)

theorem length_offColsD_le (f : ℕ → ℕ → ℕ) (ps : List ℕ) :
    (offColsD f ps).length ≤ ps.length * ps.length := by
  unfold offColsD
  rw [List.length_flatMap]
  have : ∀ u ∈ ps, ((ps.filter fun v => v != u).map fun v => f u v).length ≤ ps.length :=
    fun u _ => by simpa using List.length_filter_le _ _
  calc (ps.map fun u => ((ps.filter fun v => v != u).map fun v => f u v).length).sum
      ≤ (ps.map fun _ => ps.length).sum := List.sum_le_sum this
    _ = ps.length * ps.length := by simp

theorem RunsWithin.csOffColsProg (offs c : Array ℕ) {ps : List ℕ} {N : ℕ}
    (hn : ps.length ≤ N) :
    RunsWithin X body (SoJProg.csOffColsProg offs c ps) (offColsD (fA offs c) ps)
      (offColsCost N) := by
  have hrow : ∀ u ∈ ps, RunsWithin X body
      (Prog.bind (Toolkit.filterList (a' := .nat) ps fun v =>
          Prog.bind (.op2 .natEq v u) fun e => .op1 .not e) fun T =>
        mapList (a' := .nat) T fun v => SoJProg.csColProg offs c u v)
      ((ps.filter fun v => v != u).map fun v => fA offs c u v) (12 * N + 5) := by
    intro u _
    apply RunsWithin.mono
    case h =>
      run_step (Toolkit.RunsWithin.filterList (c := 2) (P := fun v => v != u) fun v _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
          (by simp [Prim.cost]))
      exact RunsWithin.mapList_le fun v _ => RunsWithin.csColProg offs c u v
    case hc =>
      calc _ ≤ N * (2 + 4) + 3 + (N * (3 + 3) + 2) := by
            gcongr
            exact (List.length_filter_le _ _).trans hn
        _ ≤ 12 * N + 5 := by omega
  refine ((RunsWithin.csFlatMap (L := N) hrow fun u _ => ?_).of_eq rfl).mono ?_
  · simpa using (List.length_filter_le _ _).trans hn
  · have := Nat.mul_le_mul hn (show 12 * N + 5 + N + 6 ≤ 13 * N + 11 by omega)
    simp only [offColsCost]
    omega

theorem RunsWithin.csCompStepProg (offs c : Array ℕ) {ps T : List ℕ} (r : ℕ) {N L : ℕ}
    (hn : ps.length ≤ N) (hT : T.length ≤ L) :
    RunsWithin X body (SoJProg.csCompStepProg offs c ps r T) (compStepD (fA offs c) ps r T)
      (stepCost N L) := by
  have hy : ∀ y ∈ ps, RunsWithin X body
      (Prog.bind (SoJProg.csMemProg T y) fun inT => Prog.bind (.op1 .not inT) fun out =>
        Prog.bind (anyList (a' := .nat) T fun x =>
            Prog.bind (SoJProg.csColProg offs c x y) fun a => Prog.bind (.op2 .natEq a r)
              fun ea => Prog.bind (SoJProg.csColProg offs c y x) fun b =>
              Prog.bind (.op2 .natEq b r) fun eb => .op2 .or ea eb) fun adj =>
        .op2 .and out adj)
      (!(T.contains y) && T.any fun x => fA offs c x y == r || fA offs c y x == r)
      (14 * L + 4) := by
    intro y _
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.csMemProg T y)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.anyList_le (c := 9)
        (P := fun x => fA offs c x y == r || fA offs c y x == r) fun x _ => by
          apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.csColProg offs c x y)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.csColProg offs c y x)
            run_step (RunsWithin.prim _ _)
            exact RunsWithin.prim_le rfl le_rfl
          case hc => simp [Prim.cost])
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost]
      omega
  apply RunsWithin.mono
  case h =>
    run_step (Toolkit.RunsWithin.filterList hy)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have := Nat.mul_le_mul hn (show 14 * L + 4 + 4 ≤ 14 * L + 8 by omega)
    simp only [Prim.cost, Args.head, stepCost]
    omega

theorem RunsWithin.csCompProg (offs c : Array ℕ) {ps : List ℕ} (r x : ℕ) {N : ℕ}
    (hn : ps.length ≤ N) :
    RunsWithin X body (SoJProg.csCompProg offs c ps r x) (compD (fA offs c) ps r x)
      (compCost N) := by
  have hite : RunsWithin X body (t := .list .nat)
      (.ite (ps.contains x) (.bind (.op0 .nil) fun l₀ => .op2 .cons (x : Ty.denote .nat) l₀)
        (.op0 .nil))
      (if ps.contains x then [x] else []) 3 := by
    cases ps.contains x
    · exact (RunsWithin.ite_false (RunsWithin.prim_le rfl le_rfl)).mono (by simp [Prim.cost])
    · exact (RunsWithin.ite_true ((RunsWithin.prim _ _).bind (RunsWithin.prim_le rfl le_rfl))).mono
        (by simp [Prim.cost])
  have hfold := RunsWithin.foldList_iter (X := X) (body := body)
    (g := fun T => SoJProg.csCompStepProg offs c ps r T) (G := compStepD (fA offs c) ps r)
    (I := fun j T => T.length ≤ 1 + j * ps.length) (c := stepCost N (N * N + 1))
    (K := ps.length) (fun j T hj hT => by
      have hjn : j * ps.length ≤ N * N := Nat.mul_le_mul (by omega) hn
      refine ⟨RunsWithin.csCompStepProg offs c r hn (by omega), ?_⟩
      have := length_compStepD_le (fA offs c) ps r T
      rw [Nat.succ_mul]
      omega)
    (List.range ps.length) 0 (if ps.contains x then [x] else []) (by simp)
    (by split <;> simp)
  rw [List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.csMemProg ps x)
    run_step hite
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.1
  case hc =>
    have := Nat.mul_le_mul_right (stepCost N (N * N + 1) + 1) hn
    simp only [Prim.cost, Prim.eval, Args.head, compCost]
    omega

/-- The cost of `csDisconnProg` for at most `N` points. -/
def disconnCost (N : ℕ) : ℕ :=
  offColsCost N + (N * N * (N * (compCost N + (N * (3 * (N * N + 1) + 4) + 1) + 2) + 1 + 4) + 3)

theorem RunsWithin.csDisconnProg (offs c : Array ℕ) {ps : List ℕ} {N : ℕ} (hn : ps.length ≤ N) :
    RunsWithin X body (SoJProg.csDisconnProg offs c ps) (disconnD (fA offs c) ps)
      (disconnCost N) := by
  have hx : ∀ r x, RunsWithin X body
      (Prog.bind (SoJProg.csCompProg offs c ps r x) fun T =>
        anyList (a' := .nat) ps fun y => Prog.bind (SoJProg.csMemProg T y) fun b => .op1 .not b)
      (ps.any fun y => !((compD (fA offs c) ps r x).contains y))
      (compCost N + (N * (3 * (N * N + 1) + 4) + 1)) := by
    intro r x
    have hT : (compD (fA offs c) ps r x).length ≤ N * N + 1 :=
      (length_compD_le _ ps r x).trans (by have := Nat.mul_le_mul hn hn; omega)
    refine RunsWithin.bind (RunsWithin.csCompProg offs c r x hn) ?_
    refine (RunsWithin.anyList_le (c := 3 * (N * N + 1) + 2) fun y _ => ?_).mono ?_
    · refine RunsWithin.bind_le (RunsWithin.csMemProg _ y) (RunsWithin.prim_le rfl le_rfl) ?_
      simp only [Prim.cost]
      omega
    · calc _ ≤ N * (3 * (N * N + 1) + 2 + 2) + 1 := by gcongr
        _ = _ := by ring
  have hr := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := offColsD (fA offs c) ps)
    (P := fun r => ps.any fun x => ps.any fun y => !((compD (fA offs c) ps r x).contains y))
    (c := N * (compCost N + (N * (3 * (N * N + 1) + 4) + 1) + 2) + 1) fun r _ =>
      (RunsWithin.anyList_le fun x _ => hx r x).mono (by gcongr)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.csOffColsProg offs c hn)
    exact hr
  case hc =>
    have hl := (length_offColsD_le (fA offs c) ps).trans (Nat.mul_le_mul hn hn)
    unfold disconnCost
    gcongr

/-- The cost of `csColsProg` for at most `N` points. -/
def colsCost (N : ℕ) : ℕ := N * (7 * N + 8) + 4

theorem length_colsD (f : ℕ → ℕ → ℕ) (C₁ C₂ : List ℕ) :
    (colsD f C₁ C₂).length = C₁.length * C₂.length := by
  simp [colsD, List.length_flatMap]

theorem RunsWithin.csColsProg (offs c : Array ℕ) {C₁ C₂ : List ℕ} {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csColsProg offs c C₁ C₂) (colsD (fA offs c) C₁ C₂)
      (colsCost N) := by
  refine ((RunsWithin.csFlatMap (a' := .nat) (c := 6 * N + 2) (L := N)
    (F := fun x => C₂.map fun w => fA offs c x w) (fun x _ => ?_) fun x _ => ?_).of_eq
      rfl).mono ?_
  · refine (RunsWithin.mapList_le fun w _ => RunsWithin.csColProg offs c x w).mono ?_
    calc _ ≤ N * (3 + 3) + 2 := by gcongr
      _ = _ := by ring
  · simpa using h₂
  · calc _ ≤ N * (6 * N + 2 + N + 6) + 4 := by gcongr
      _ = _ := by unfold colsCost; ring

theorem minCount_eq_minD : ∀ l : List ℕ, Toolkit.minCount l = minD l
  | [] => rfl
  | a :: l => by
    have hg : (fun acc d : ℕ => if d < acc then d else acc) = min := by
      funext acc d
      split <;> omega
    simp only [Toolkit.minCount, minD, List.foldl_cons, hg, min_self]

theorem RunsWithin.csMinProg (l : List ℕ) :
    RunsWithin X body (Toolkit.minProg l) (minD l) (3 * l.length + 2) :=
  (Toolkit.RunsWithin.minProg l).of_eq (minCount_eq_minD l)

/-- The cost of `csMajProg` for at most `N` points. -/
def majCost (N : ℕ) : ℕ := 8 * N + 3

theorem RunsWithin.csMajProg (offs c : Array ℕ) (n₁ : ℕ) {C₁ : List ℕ} (w k : ℕ) {N : ℕ}
    (h₁ : C₁.length ≤ N) :
    RunsWithin X body (SoJProg.csMajProg offs c n₁ C₁ w k)
      (decide (n₁ < 2 * (C₁.filter fun x => fA offs c x w == k).length)) (majCost N) := by
  apply RunsWithin.mono
  case h =>
    run_step (Toolkit.RunsWithin.countList (c := 4) (P := fun x => fA offs c x w == k)
      fun x _ => RunsWithin.bind_le (RunsWithin.csColProg offs c x w)
        (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost]))
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, two_mul]) le_rfl
  case hc =>
    simp only [Prim.cost, majCost]
    omega

/-- The cost of `csBigImpProg` for at most `N` points. -/
def bigImpCost (N : ℕ) : ℕ := N + 1 + (N * N * (N * (majCost N + 2) + 1 + 4) + 3)

theorem RunsWithin.csBigImpProg (offs c : Array ℕ) {C₁ C₂ : List ℕ} {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csBigImpProg offs c C₁ C₂ (colsD (fA offs c) C₁ C₂))
      (bigImpD (fA offs c) C₁ C₂) (bigImpCost N) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact Toolkit.RunsWithin.filterList (c := N * (majCost N + 2) + 1) fun k _ =>
      (RunsWithin.anyList_le fun w _ => RunsWithin.csMajProg offs c _ w k h₁).mono (by gcongr)
  case hc =>
    have hl : (colsD (fA offs c) C₁ C₂).length ≤ N * N := by
      rw [length_colsD]
      exact Nat.mul_le_mul h₁ h₂
    simp only [Prim.cost, Args.head, bigImpCost]
    gcongr

/-- The cost of `csBigPrimProg` for at most `N` points. -/
def bigPrimCost (N : ℕ) : ℕ := N + 1 + (N * N * (majCost N + 4) + 3)

theorem RunsWithin.csBigPrimProg (offs c : Array ℕ) {C₁ C₂ : List ℕ} (y : ℕ) {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csBigPrimProg offs c C₁ (colsD (fA offs c) C₁ C₂) y)
      (bigPrimD (fA offs c) C₁ C₂ y) (bigPrimCost N) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact Toolkit.RunsWithin.filterList fun k _ => RunsWithin.csMajProg offs c _ y k h₁
  case hc =>
    have hl : (colsD (fA offs c) C₁ C₂).length ≤ N * N := by
      rw [length_colsD]
      exact Nat.mul_le_mul h₁ h₂
    simp only [Prim.cost, Args.head, bigPrimCost]
    gcongr

/-- The cost of `csOtherColsProg` for at most `N` points. -/
def otherColsCost (N : ℕ) : ℕ := N * N * (2 + 4) + 3

theorem RunsWithin.csOtherColsProg (f : ℕ → ℕ → ℕ) {C₁ C₂ : List ℕ} (g : ℕ) {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csOtherColsProg (colsD f C₁ C₂) g) (otherColsD f C₁ C₂ g)
      (otherColsCost N) := by
  refine (Toolkit.RunsWithin.filterList (a' := .nat) (c := 2) (P := fun k => k != g) fun k _ =>
    RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
      (by simp [Prim.cost])).mono ?_
  have hl : (colsD f C₁ C₂).length ≤ N * N := by
    rw [length_colsD]
    exact Nat.mul_le_mul h₁ h₂
  unfold otherColsCost
  gcongr

/-- The cost of `csBluesProg` for at most `N` points. -/
def bluesCost (N : ℕ) : ℕ := N + 1 + (N * N * (8 * N + 6 + 4) + 3)

theorem RunsWithin.csBluesProg (offs c : Array ℕ) {C₂ : List ℕ} (y : ℕ) {N : ℕ}
    (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csBluesProg offs c C₂ (offColsD (fA offs c) C₂) y)
      (bluesD (fA offs c) C₂ y) (bluesCost N) := by
  have hb : ∀ b, RunsWithin X body
      (Prog.bind (Toolkit.countList (a' := .nat) C₂ fun z =>
          Prog.bind (SoJProg.csColProg offs c y z) fun a => .op2 .natEq a b) fun cnt =>
        Prog.bind (.op0 (.natLit 0)) fun z => Prog.bind (.op2 .natLt z cnt) fun pos =>
        Prog.bind (.op2 .add cnt cnt) fun d => Prog.bind (.op2 .natLt d C₂.length) fun small =>
        .op2 .and pos small)
      (decide (0 < (C₂.filter fun z => fA offs c y z == b).length ∧
        2 * (C₂.filter fun z => fA offs c y z == b).length < C₂.length)) (8 * N + 6) := by
    intro b
    apply RunsWithin.mono
    case h =>
      run_step (Toolkit.RunsWithin.countList (c := 4) (P := fun z => fA offs c y z == b)
        fun z _ => RunsWithin.bind_le (RunsWithin.csColProg offs c y z)
          (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost]))
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval, two_mul]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact Toolkit.RunsWithin.filterList fun b _ => hb b
  case hc =>
    have hl := (length_offColsD_le (fA offs c) C₂).trans (Nat.mul_le_mul h₂ h₂)
    simp only [Prim.cost, Args.head, bluesCost]
    gcongr

/-- The cost of `csTwinOKProg` for at most `N` points and a block of at most `L` points. -/
def csTwinCost (N L : ℕ) : ℕ := N + 1 + (N * (N * (15 * L + 1 + 4) + 1 + 3 + 2) + 1)

theorem RunsWithin.csTwinOKProg (offs c : Array ℕ) {C₁ B : List ℕ} (g : ℕ) {N L : ℕ}
    (h₁ : C₁.length ≤ N) (hB : B.length ≤ L) :
    RunsWithin X body (SoJProg.csTwinOKProg offs c C₁ B g) (twinOK (fA offs c) C₁ B g)
      (csTwinCost N L) := by
  have hx : ∀ x, RunsWithin X body
      (Prog.bind (Toolkit.countList (a' := .nat) C₁ fun x' => allList (a' := .nat) B fun y =>
          Prog.bind (SoJProg.csColProg offs c x y) fun a => Prog.bind (.op2 .natEq a g) fun ea =>
          Prog.bind (SoJProg.csColProg offs c x' y) fun b => Prog.bind (.op2 .natEq b g)
            fun eb => SoJProg.csBeqProg ea eb) fun cnt =>
        Prog.bind (.op2 .add cnt cnt) fun d => Prog.bind (.op2 .natLt C₁.length d) fun lt =>
        .op1 .not lt)
      (decide (2 * (C₁.filter fun x' =>
        B.all fun y => (fA offs c x y == g) == (fA offs c x' y == g)).length ≤ C₁.length))
      (N * (15 * L + 1 + 4) + 1 + 3) := by
    intro x
    have hy : ∀ x', RunsWithin X body
        (allList (a' := .nat) B fun y =>
          Prog.bind (SoJProg.csColProg offs c x y) fun a => Prog.bind (.op2 .natEq a g) fun ea =>
          Prog.bind (SoJProg.csColProg offs c x' y) fun b => Prog.bind (.op2 .natEq b g)
            fun eb => SoJProg.csBeqProg ea eb)
        (B.all fun y => (fA offs c x y == g) == (fA offs c x' y == g)) (15 * L + 1) := by
      intro x'
      refine (RunsWithin.allList_le (c := 13) fun y _ => ?_).mono ?_
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.csColProg offs c x y)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.csColProg offs c x' y)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.csBeqProg _ _
        case hc => simp [Prim.cost]
      · calc _ ≤ L * (13 + 2) + 1 := by gcongr
          _ = _ := by ring
    apply RunsWithin.mono
    case h =>
      run_step (Toolkit.RunsWithin.countList fun x' _ => hy x')
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le
        (by simp only [Prim.eval, two_mul, ← Nat.not_le, decide_not, Bool.not_not]) le_rfl
    case hc =>
      simp only [Prim.cost]
      gcongr
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.allList_le fun x _ => hx x
  case hc =>
    simp only [Prim.cost, Args.head, csTwinCost]
    gcongr

/-- The cost of `csGoodOptsProg` for at most `N` points. -/
def goodCost (N : ℕ) : ℕ := N * (compCost N + csTwinCost N (N * N + 1) + 4) + 3

theorem RunsWithin.csGoodOptsProg (offs c : Array ℕ) {C₁ C₂ : List ℕ} (red violet : ℕ) {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csGoodOptsProg offs c C₁ C₂ red violet)
      (goodOptsD (fA offs c) C₁ C₂ red violet) (goodCost N) := by
  refine (Toolkit.RunsWithin.filterList fun y _ => RunsWithin.bind
    (RunsWithin.csCompProg offs c red y h₂) (RunsWithin.csTwinOKProg (L := N * N + 1) offs c
      violet h₁ ((length_compD_le _ C₂ red y).trans ?_))).mono ?_
  · have := Nat.mul_le_mul h₂ h₂
    omega
  · unfold goodCost
    gcongr

theorem RunsWithin.csPartLeafProg (col : Array ℕ) (blk : Array (List ℕ)) :
    RunsWithin X body (SoJProg.csPartLeafProg col blk) (partLeaf col blk) 8 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.csBipLeafProg (W₁ : List ℕ) (W₂ : List (List ℕ)) (g : ℕ) :
    RunsWithin X body (SoJProg.csBipLeafProg W₁ W₂ g) (bipLeaf W₁ W₂ g) 10 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost, Prim.eval]

theorem RunsWithin.csSingletonsProg {xs : List ℕ} {L : ℕ} (h : xs.length ≤ L) :
    RunsWithin X body (SoJProg.csSingletonsProg xs) (xs.map fun z => [z]) (L * 5 + 2) := by
  refine (RunsWithin.mapList_le (c := 2) fun z _ =>
    RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
      (by simp [Prim.cost])).mono ?_
  calc _ ≤ L * (2 + 3) + 2 := by gcongr
    _ = _ := by ring

theorem RunsWithin.csMinProg_le {l : List ℕ} {L : ℕ} (h : l.length ≤ L) :
    RunsWithin X body (Toolkit.minProg l) (minD l) (3 * L + 2) :=
  (RunsWithin.csMinProg l).mono (by omega)

/-- The cost of `csCompPartProg` for at most `N` points. -/
def compPartCost (N : ℕ) : ℕ := 1 + (N + 1) + (N + 1) + (N * (compCost N + 3) + 2) + (N + 1) + 8

theorem RunsWithin.csCompPartProg (offs c : Array ℕ) (m : ℕ) {ps : List ℕ} (r : ℕ) {N : ℕ}
    (hm : m ≤ N) (hn : ps.length ≤ N) :
    RunsWithin X body (SoJProg.csCompPartProg offs c m ps r) (compPart (fA offs c) m ps r)
      (compPartCost N) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun x _ => RunsWithin.csCompProg offs c r x hn)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.csPartLeafProg _ _
  case hc =>
    have := Nat.mul_le_mul_right (compCost N + 3) hm
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
      compPartCost]
    omega

/-- The cost of `csColPartProg` for at most `N` points. -/
def colPartCost (N : ℕ) : ℕ :=
  (N + 1) + (N * (3 + 3) + 2) + (N + 1) + (N * (3 + (N * (3 + 1 + 4) + 3) + 3) + 2) + (N + 1) + 8

theorem RunsWithin.csColPartProg (offs c : Array ℕ) (m : ℕ) {ps : List ℕ} (w : ℕ) {N : ℕ}
    (hm : m ≤ N) (hn : ps.length ≤ N) :
    RunsWithin X body (SoJProg.csColPartProg offs c m ps w) (colPartD (fA offs c) m ps w)
      (colPartCost N) := by
  have hx : ∀ x, RunsWithin X body
      (Prog.bind (SoJProg.csColProg offs c x w) fun fx =>
        Toolkit.filterList (a' := .nat) ps fun y =>
          Prog.bind (SoJProg.csColProg offs c y w) fun fy => .op2 .natEq fy fx)
      (ps.filter fun y => fA offs c y w == fA offs c x w) (3 + (N * (3 + 1 + 4) + 3)) := by
    intro x
    refine RunsWithin.bind (RunsWithin.csColProg offs c x w) ?_
    refine (Toolkit.RunsWithin.filterList (c := 3 + 1) fun y _ =>
      RunsWithin.bind (RunsWithin.csColProg offs c y w) (RunsWithin.prim_le rfl le_rfl)).mono ?_
    gcongr
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun x _ => RunsWithin.csColProg offs c x w)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun x _ => hx x)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.csPartLeafProg _ _
  case hc =>
    have := Nat.mul_le_mul_right (3 + (N * (3 + 1 + 4) + 3) + 3) hm
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
      colPartCost]
    omega

/-- The cost of the bipartite leaf of `csPrimLeafProg`, for at most `N` points. -/
def primBipCost (N : ℕ) : ℕ :=
  (3 * (N * N) + 2) + (3 * (N * N) + 2) + (N * (4 + 4) + 3) + (N * (4 + 4) + 3) +
    (N * 5 + 2) + 10 + 1

/-- The cost of `csPrimLeafProg` after `csBigPrimProg`, for at most `N` points. -/
def primRestCost (N : ℕ) : ℕ :=
  (1 + (colPartCost N + 1)) + (1 + (bluesCost N + (1 + 1 + primBipCost N)))

/-- The cost of `csPrimLeafProg` for at most `N` points. -/
def primCost (N : ℕ) : ℕ := bigPrimCost N + primRestCost N

theorem length_bigPrimD_le (f : ℕ → ℕ → ℕ) {C₁ C₂ : List ℕ} (y : ℕ) {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) : (bigPrimD f C₁ C₂ y).length ≤ N * N :=
  (List.length_filter_le _ _).trans ((length_colsD f C₁ C₂).le.trans (Nat.mul_le_mul h₁ h₂))

theorem length_bluesD_le (f : ℕ → ℕ → ℕ) {C₂ : List ℕ} (y : ℕ) {N : ℕ}
    (h₂ : C₂.length ≤ N) : (bluesD f C₂ y).length ≤ N * N :=
  (List.length_filter_le _ _).trans ((length_offColsD_le f C₂).trans (Nat.mul_le_mul h₂ h₂))

theorem RunsWithin.csPrimLeafProg (offs c : Array ℕ) (m : ℕ) {C₁ C₂ : List ℕ} (y : ℕ) {N : ℕ}
    (hm : m ≤ N) (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csPrimLeafProg offs c m C₁ C₂ (colsD (fA offs c) C₁ C₂)
      (offColsD (fA offs c) C₂) y) (primLeaf (fA offs c) m C₁ C₂ y) (primCost N) := by
  have hbp := length_bigPrimD_le (fA offs c) y h₁ h₂
  have hbl := length_bluesD_le (fA offs c) y h₂
  refine RunsWithin.bind_le (c₂ := primRestCost N) (RunsWithin.csBigPrimProg offs c y h₁ h₂) ?_
    le_rfl
  unfold primLeaf primRestCost
  rcases eb : bigPrimD (fA offs c) C₁ C₂ y with _ | ⟨v₀, vs⟩
  · refine (RunsWithin.caseList_nil ((RunsWithin.csColPartProg offs c m y hm h₁).bind
      (RunsWithin.prim _ _))).mono ?_
    simp only [Prim.cost]
    omega
  · rw [eb] at hbp
    dsimp only
    refine (RunsWithin.caseList_cons (RunsWithin.bind_le (c₂ := 1 + 1 + primBipCost N)
      (RunsWithin.csBluesProg offs c y h₂) ?_ le_rfl)).mono (by omega)
    rcases ebl : bluesD (fA offs c) C₂ y with _ | ⟨b₀, bs⟩
    · exact (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono (by simp [Prim.cost])
    · rw [ebl] at hbl
      refine (RunsWithin.caseList_cons ?_).mono (show 1 + primBipCost N ≤ _ by omega)
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.csMinProg_le hbp)
        run_step (RunsWithin.csMinProg_le hbl)
        run_step (Toolkit.RunsWithin.filterList (c := 3 + 1)
          (P := fun x => fA offs c x y == minD (v₀ :: vs)) fun x _ =>
            RunsWithin.bind (RunsWithin.csColProg offs c x y) (RunsWithin.prim_le rfl le_rfl))
        run_step (Toolkit.RunsWithin.filterList (c := 3 + 1)
          (P := fun z => fA offs c y z == minD (b₀ :: bs)) fun z _ =>
            RunsWithin.bind (RunsWithin.csColProg offs c y z) (RunsWithin.prim_le rfl le_rfl))
        run_step (RunsWithin.csSingletonsProg ((List.length_filter_le _ _).trans h₂))
        run_step (RunsWithin.csBipLeafProg _ _ _)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, primBipCost]
        omega

theorem RunsWithin.csLeafRes (m : ℕ) (o : Option LeafD) :
    RunsWithin X body (SoJProg.csLeafRes o) (toRes m (.leaf o)) 8 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost, Prim.eval]

/-- The cost of `csNodeRes` for at most `N` points and leaves of cost at most `c`. -/
def nodeCost (N c : ℕ) : ℕ := 1 + (N + 1) + (N * (c + 3) + 2) + (N + 1) + 1 + 1

theorem RunsWithin.csNodeRes {m : ℕ} (opts : List ℕ)
    {k : ℕ → Prog S (a, b) Ty.denote (.option cohLeafTy)} {K : ℕ → Option LeafD} {c N : ℕ}
    (hm : m ≤ N) (hk : ∀ y < m, RunsWithin X body (k y) (K y) c) :
    RunsWithin X body (SoJProg.csNodeRes m opts k) (toRes m (.node opts K)) (nodeCost N c) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (xs := (List.range m : List ℕ)) fun y hy =>
      hk y (List.mem_range.1 hy))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have := Nat.mul_le_mul_right (c + 3) hm
    simp only [Prim.cost, Args.head, List.length_range, List.length_map, nodeCost]
    omega

theorem length_disconnD_le (f : ℕ → ℕ → ℕ) {ps : List ℕ} {N : ℕ} (hn : ps.length ≤ N) :
    (disconnD f ps).length ≤ N * N :=
  (List.length_filter_le _ _).trans ((length_offColsD_le f ps).trans (Nat.mul_le_mul hn hn))

theorem length_bigImpD_le (f : ℕ → ℕ → ℕ) {C₁ C₂ : List ℕ} {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) : (bigImpD f C₁ C₂).length ≤ N * N :=
  (List.length_filter_le _ _).trans ((length_colsD f C₁ C₂).le.trans (Nat.mul_le_mul h₁ h₂))

theorem length_otherColsD_le (f : ℕ → ℕ → ℕ) {C₁ C₂ : List ℕ} (g : ℕ) {N : ℕ}
    (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) : (otherColsD f C₁ C₂ g).length ≤ N * N :=
  (List.length_filter_le _ _).trans ((length_colsD f C₁ C₂).le.trans (Nat.mul_le_mul h₁ h₂))

/-- The cost of `csImprimProg` when no block is good, after the good options. -/
def noGoodCost (N : ℕ) : ℕ :=
  otherColsCost N + ((1 + (1 + 8)) +
    (1 + ((3 * (N * N) + 2) + (N * (compCost N + 3) + 2) + 10 + 1 + 8)))

/-- The cost of the node of `csImprimProg` over the good options. -/
def goodNodeCost (N : ℕ) : ℕ := nodeCost N (compCost N + ((N * N + 1) * 5 + 2) + 10 + 1)

/-- The cost of `csImprimProg` when there is a `violet` colour, after it is found. -/
def violetCost (N : ℕ) : ℕ :=
  (3 * (N * N) + 2) + (goodCost N + ((1 + noGoodCost N) + (1 + goodNodeCost N)))

/-- The cost of `csImprimProg` after `csBigImpProg`. -/
def imprimRestCost (N : ℕ) : ℕ := (1 + nodeCost N (colPartCost N + 1)) + (1 + violetCost N)

/-- The cost of `csImprimProg` for at most `N` points. -/
def imprimCost (N : ℕ) : ℕ := bigImpCost N + imprimRestCost N

theorem RunsWithin.csImprimProg (offs c : Array ℕ) (m : ℕ) {C₁ C₂ : List ℕ} (red : ℕ) {N : ℕ}
    (hm : m ≤ N) (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csImprimProg offs c m C₁ C₂ (colsD (fA offs c) C₁ C₂) red)
      (toRes m (imprimTree (fA offs c) m C₁ C₂ red)) (imprimCost N) := by
  have hbi := length_bigImpD_le (fA offs c) h₁ h₂
  refine RunsWithin.bind_le (c₂ := imprimRestCost N) (RunsWithin.csBigImpProg offs c h₁ h₂) ?_
    le_rfl
  unfold imprimTree imprimRestCost
  rcases eb : bigImpD (fA offs c) C₁ C₂ with _ | ⟨v₀, vs⟩
  · refine (RunsWithin.caseList_nil (RunsWithin.csNodeRes (c := colPartCost N + 1) C₂ hm
      fun w _ => RunsWithin.bind_le (RunsWithin.csColPartProg offs c m w hm h₁)
        (RunsWithin.prim _ _) (by simp [Prim.cost]))).mono (by omega)
  · rw [eb] at hbi
    dsimp only
    refine (RunsWithin.caseList_cons ?_).mono (show 1 + violetCost N ≤ _ by omega)
    unfold violetCost
    refine RunsWithin.bind_le (RunsWithin.csMinProg_le hbi) ?_ (Nat.le_refl _)
    refine RunsWithin.bind_le (RunsWithin.csGoodOptsProg offs c red _ h₁ h₂) ?_ (Nat.le_refl _)
    rcases eg : goodOptsD (fA offs c) C₁ C₂ red (minD (v₀ :: vs)) with _ | ⟨y₀, ys⟩
    · refine (RunsWithin.caseList_nil ?_).mono (show 1 + noGoodCost N ≤ _ by omega)
      unfold noGoodCost
      refine RunsWithin.bind_le (RunsWithin.csOtherColsProg _ _ h₁ h₂) ?_ (Nat.le_refl _)
      have ho := length_otherColsD_le (fA offs c) (minD (v₀ :: vs)) h₁ h₂
      rcases eo : otherColsD (fA offs c) C₁ C₂ (minD (v₀ :: vs)) with _ | ⟨g₀, gs⟩
      · refine (RunsWithin.caseList_nil (RunsWithin.bind_le (RunsWithin.prim _ _)
          (RunsWithin.csLeafRes m none) le_rfl)).mono (by simp only [Prim.cost]; omega)
      · rw [eo] at ho
        refine (RunsWithin.caseList_cons
          (k := (3 * (N * N) + 2) + (N * (compCost N + 3) + 2) + 10 + 1 + 8) ?_).mono
          (by omega)
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.csMinProg_le ho)
          run_step (RunsWithin.mapList_le fun y _ => RunsWithin.csCompProg offs c red y h₂)
          run_step (RunsWithin.csBipLeafProg _ _ _)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.csLeafRes m _
        case hc =>
          have := Nat.mul_le_mul_right (compCost N + 3) h₂
          simp only [Prim.cost]
          omega
    · refine (RunsWithin.caseList_cons (RunsWithin.csNodeRes _ hm fun y _ => ?_)).mono
        (show 1 + goodNodeCost N ≤ _ by omega)
      have hB : (compD (fA offs c) C₂ red y).length ≤ N * N + 1 :=
        (length_compD_le _ C₂ red y).trans (by have := Nat.mul_le_mul h₂ h₂; omega)
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.csCompProg offs c red y h₂)
        run_step (RunsWithin.csSingletonsProg hB)
        run_step (RunsWithin.csBipLeafProg _ _ _)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost]
        omega

/-- The cost of the primitive branch of `csSojProg`. -/
def sojPrimCost (N : ℕ) : ℕ := offColsCost N + nodeCost N (primCost N)

/-- The cost of `csSojProg` when `C₁` has no disconnected colour, after it is found. -/
def sojD₂Cost (N : ℕ) : ℕ :=
  disconnCost N + (colsCost N + ((1 + sojPrimCost N) + (1 + ((3 * (N * N) + 2) + imprimCost N))))

/-- The cost of `csSojProg` after the disconnected colours of `C₁`. -/
def sojRestCost (N : ℕ) : ℕ :=
  (1 + sojD₂Cost N) + (1 + ((3 * (N * N) + 2) + (compPartCost N + (1 + 8))))

/-- The cost of `csSojProg` for at most `N` points. -/
def sojCost (N : ℕ) : ℕ := disconnCost N + sojRestCost N

theorem RunsWithin.csSojProg (offs c : Array ℕ) (m : ℕ) {C₁ C₂ : List ℕ} {N : ℕ}
    (hm : m ≤ N) (h₁ : C₁.length ≤ N) (h₂ : C₂.length ≤ N) :
    RunsWithin X body (SoJProg.csSojProg offs c m C₁ C₂) (toRes m (cohSojD (fA offs c) m C₁ C₂))
      (sojCost N) := by
  have hd₁ := length_disconnD_le (fA offs c) h₁
  have hd₂ := length_disconnD_le (fA offs c) h₂
  refine RunsWithin.bind_le (c₂ := sojRestCost N) (RunsWithin.csDisconnProg offs c h₁) ?_ le_rfl
  unfold cohSojD sojRestCost
  rcases e₁ : disconnD (fA offs c) C₁ with _ | ⟨r, rs⟩
  · refine (RunsWithin.caseList_nil ?_).mono (show 1 + sojD₂Cost N ≤ _ by omega)
    unfold sojD₂Cost
    refine RunsWithin.bind_le (RunsWithin.csDisconnProg offs c h₂) ?_ (Nat.le_refl _)
    refine RunsWithin.bind_le (RunsWithin.csColsProg offs c h₁ h₂) ?_ (Nat.le_refl _)
    rcases e₂ : disconnD (fA offs c) C₂ with _ | ⟨r₂, rs₂⟩
    · refine (RunsWithin.caseList_nil ?_).mono (show 1 + sojPrimCost N ≤ _ by omega)
      exact RunsWithin.bind_le (RunsWithin.csOffColsProg offs c h₂)
        (RunsWithin.csNodeRes C₂ hm fun y _ => RunsWithin.csPrimLeafProg offs c m y hm h₁ h₂)
        le_rfl
    · rw [e₂] at hd₂
      refine (RunsWithin.caseList_cons (RunsWithin.bind_le (RunsWithin.csMinProg_le hd₂)
        (RunsWithin.csImprimProg offs c m _ hm h₁ h₂) le_rfl)).mono (by omega)
  · rw [e₁] at hd₁
    dsimp only
    refine (RunsWithin.caseList_cons (k := (3 * (N * N) + 2) + (compPartCost N + (1 + 8))) ?_).mono
      (by omega)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.csMinProg_le hd₁)
      run_step (RunsWithin.csCompPartProg offs c m _ hm h₁)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.csLeafRes m _
    case hc =>
      simp only [Prim.cost]
      omega

/-- The cost of `cohSojProg` for `N ≥ m + |C₁| + |C₂|`; a polynomial of degree 7 in `N`. -/
def cohSojCost (N : ℕ) : ℕ := 10 * N + 9 + sojCost N

/-- **Coherent Split-or-Johnson on data, the program**: it computes the data tree of
`cohSojD` (decoded by `decodeRes_cohSojD`) within `cohSojCost (m + |C₁| + |C₂|)`. -/
theorem RunsWithin.cohSojProg (m : ℕ) (c : Array ℕ) (C₁ C₂ : List ℕ) :
    RunsWithin X body (SoJProg.cohSojProg m c C₁ C₂)
      (toRes m (cohSojD (fA (offsArr m) c) m C₁ C₂))
      (cohSojCost (m + C₁.length + C₂.length)) :=
  RunsWithin.bind_le (RunsWithin.csOffsProg m)
    (RunsWithin.csSojProg (N := m + C₁.length + C₂.length) (offsArr m) c m (by omega) (by omega)
      (by omega))
    (by unfold cohSojCost; omega)

/-- **The cost is polynomial**: at most `903 (N + 1)^7` (`903 = cohSojCost 1` is the sum of the
coefficients of the degree-7 polynomial `cohSojCost`). -/
theorem cohSojCost_le (N : ℕ) : cohSojCost N ≤ 903 * (N + 1) ^ 7 := by
  have hpow : ∀ i ≤ 7, N ^ i ≤ (N + 1) ^ 7 := fun i hi =>
    (Nat.pow_le_pow_left (Nat.le_succ N) i).trans (Nat.pow_le_pow_right (Nat.succ_pos N) hi)
  have h₀ := hpow 0 (by norm_num)
  have h₁ := hpow 1 (by norm_num)
  have h₂ := hpow 2 (by norm_num)
  have h₃ := hpow 3 (by norm_num)
  have h₄ := hpow 4 (by norm_num)
  have h₅ := hpow 5 (by norm_num)
  have h₆ := hpow 6 (by norm_num)
  have h₇ := hpow 7 le_rfl
  generalize (N + 1) ^ 7 = M at h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ ⊢
  simp only [cohSojCost, sojCost, sojRestCost, sojD₂Cost, sojPrimCost, imprimCost,
    imprimRestCost, violetCost, goodNodeCost, noGoodCost, nodeCost, compPartCost, primCost,
    primRestCost, primBipCost, colPartCost, bluesCost, bigPrimCost, bigImpCost, majCost,
    otherColsCost, goodCost, csTwinCost, colsCost, disconnCost, compCost, stepCost, offColsCost]
  ring_nf
  ring_nf at h₀ h₁
  omega

end Specs

/-! ### Well-formedness -/

section Wf

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ : var₁ .nat} {m₂ : var₂ .nat} {c₁ : var₁ (.array .nat)}
  {c₂ : var₂ (.array .nat)} {D₁ E₁ : var₁ (.list .nat)} {D₂ E₂ : var₂ (.list .nat)}

theorem wf_cohSojProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cohSojProg m₁ c₁ D₁ E₁) (cohSojProg m₂ c₂ D₂ E₂) := by
  unfold cohSojProg csOffsProg csSojProg csDisconnProg csOffColsProg csFlatMap csCompProg
    csCompStepProg csMemProg csColProg csColsProg csNodeRes csPrimLeafProg csBigPrimProg
    csMajProg csColPartProg csPartLeafProg csBluesProg csSingletonsProg csBipLeafProg
    csImprimProg csBigImpProg csGoodOptsProg csTwinOKProg csBeqProg csOtherColsProg csLeafRes
    csCompPartProg Toolkit.filterList Toolkit.countList Toolkit.minProg mapList anyList allList
  prog_wf

end Wf


/-! ### Edges of a `bip` leaf -/

section BipEdge

/-- The edge predicate of a `bip` leaf on data: some point of `B` has colour `g` from `x`. -/
def bipEdgeD (f : ℕ → ℕ → ℕ) (g x : ℕ) (B : List ℕ) : Bool := B.any fun y => f x y == g

/-- The relation of a `bip` leaf, materialized as a Boolean array: the entry `x * |W₂| + j` is
the edge from `x` to the `j`-th cell of `W₂`, for `x < m` (the representation of `relOf`). -/
def bipRelD (f : ℕ → ℕ → ℕ) (m : ℕ) (W₂ : List (List ℕ)) (g : ℕ) : Array Bool :=
  ((List.range m).flatMap fun x => W₂.map fun B => bipEdgeD f g x B).toArray

variable {m : ℕ}

/-- **The edge predicate decodes to `bipEdge`.** -/
theorem bipEdgeD_eq (c : Array ℕ) (g : ℕ) {x : ℕ} (hx : x < m) {B : List ℕ}
    (hB : ∀ y ∈ B, y < m) :
    bipEdgeD (fA (offsArr m) c) g x B = bipEdge (colOf m c) g ⟨x, hx⟩ (setOf m B) := by
  unfold bipEdgeD bipEdge
  rw [Bool.eq_iff_iff, List.any_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, he⟩
    have h := fA_offsArr m c ⟨x, hx⟩ ⟨y, hB y hy⟩
    dsimp only at h
    exact ⟨⟨y, hB y hy⟩, mem_setOf.2 hy, by rw [← h]; exact beq_iff_eq.1 he⟩
  · rintro ⟨⟨y, hym⟩, hy, he⟩
    have h := fA_offsArr m c ⟨x, hx⟩ ⟨y, hym⟩
    dsimp only at h
    exact ⟨y, mem_setOf.1 hy, beq_iff_eq.2 (by rw [h]; exact he)⟩

/-- Reading a flattened list of rows of equal length `k`. -/
theorem getD_flatMap_const {α β : Type*} (F : α → List β) (k : ℕ) (d : β) :
    ∀ (l : List α), (∀ a ∈ l, (F a).length = k) → ∀ (x : ℕ) (hx : x < l.length) (j : ℕ),
      j < k → (l.flatMap F).getD (x * k + j) d = (F l[x]).getD j d
  | [], _, x, hx, _, _ => absurd hx (by simp)
  | a :: l, hl, x, hx, j, hj => by
    rw [List.flatMap_cons]
    have ha : (F a).length = k := hl a List.mem_cons_self
    rcases x with _ | x
    · rw [Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by omega)]
      rfl
    · rw [List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith),
        show (x + 1) * k + j - (F a).length = x * k + j by rw [ha, Nat.succ_mul]; omega]
      exact getD_flatMap_const F k d l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) x
        (by simpa using hx) j hj

/-- The entry of the materialized relation for the point `x` and the `j`-th cell. -/
theorem bipRelD_getD (f : ℕ → ℕ → ℕ) (g : ℕ) (W₂ : List (List ℕ)) {x : ℕ} (hx : x < m)
    {j : ℕ} (hj : j < W₂.length) :
    (bipRelD f m W₂ g).getD (x * W₂.length + j) false = bipEdgeD f g x (W₂.getD j []) := by
  unfold bipRelD
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    getD_flatMap_const (fun x => W₂.map fun B => bipEdgeD f g x B) W₂.length false
      (List.range m) (fun _ _ => List.length_map _) x (by simpa using hx) j hj]
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
  simp

/-- **The materialized relation decodes to `bipEdge`** on every listed cell, when the cells are
distinct as sets and their points lie below `m`: this is the relation `relOf m W₂` that the
bipartite recursion consumes. -/
theorem relOf_bipRelD (c : Array ℕ) (g : ℕ) {W₂ : List (List ℕ)}
    (hW : ∀ i < W₂.length, ∀ j < W₂.length,
      setOf m (W₂.getD i []) = setOf m (W₂.getD j []) → i = j)
    (hlt : ∀ B ∈ W₂, ∀ y ∈ B, y < m) (x : Fin m) {s : Finset (Fin m)} (hs : s ∈ famOf m W₂) :
    relOf m W₂ (bipRelD (fA (offsArr m) c) m W₂ g) x s = bipEdge (colOf m c) g x s := by
  obtain ⟨l, hl, rfl⟩ := mem_famOf.1 hs
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
  have hget : W₂.getD j [] = W₂[j] := List.getD_eq_getElem _ _ hj
  rw [← hget, relOf_cell hW hj x, bipRelD_getD _ g W₂ x.isLt hj,
    bipEdgeD_eq c g x.isLt (fun y hy => hlt _ (by rw [hget]; exact List.getElem_mem hj) y hy)]

end BipEdge

section BipEdgeProgs

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **The edge predicate of a `bip` leaf** (`bipEdgeD`), reading the colouring through the row
offsets. -/
def bipEdgeProg (offs c : var (.array .nat)) (g x : var .nat) (B : var (.list .nat)) :
    Prog S rec var .bool :=
  anyList B fun y => .bind (csColProg offs c x y) fun a => .op2 .natEq a g

/-- `xs.flatMap F` for lists of Booleans: map, then concatenate. -/
def csFlatMapB {a' : Ty} (xs : var (.list a')) (f : var a' → Prog S rec var (.list .bool)) :
    Prog S rec var (.list .bool) :=
  .bind (mapList xs f) fun rows => .bind (.op1 .reverse rows) fun rr =>
  .bind (.op0 .nil) fun nil => .foldList rr nil fun acc row => .op2 .append row acc

/-- **The relation of a `bip` leaf, materialized** (`bipRelD`): the edges from every point
`x < m` to every cell of `W₂`, row by row. -/
def bipRelProg (offs c : var (.array .nat)) (m g : var .nat) (W₂ : var (.list (.list .nat))) :
    Prog S rec var (.array .bool) :=
  .bind (.op1 .range m) fun xs =>
  .bind (csFlatMapB xs fun x => mapList W₂ fun B => bipEdgeProg offs c g x B) fun l =>
  .op1 .arrayOfList l

end BipEdgeProgs

section BipEdgeSpecs

open Cost Programs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.bipEdgeProg (offs c : Array ℕ) (g x : ℕ) (B : List ℕ) :
    RunsWithin X body (SoJProg.bipEdgeProg offs c g x B) (bipEdgeD (fA offs c) g x B)
      (6 * B.length + 1) := by
  unfold SoJProg.bipEdgeProg bipEdgeD
  refine (RunsWithin.anyList_le (a' := .nat) (c := 4) (P := fun y => fA offs c x y == g)
    ?_).mono ?_
  · intro y _
    exact RunsWithin.bind_le (RunsWithin.csColProg offs c x y) (RunsWithin.prim_le rfl le_rfl)
      (by simp [Prim.cost])
  · omega

theorem foldl_append_rev {α : Type*} : ∀ (rows : List (List α)),
    rows.reverse.foldl (fun acc row => row ++ acc) [] = rows.flatten := by
  intro rows
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp

theorem RunsWithin.csFlatMapB {a' : Ty} {xs : List a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote (.list .bool)} {F : a'.denote → List Bool} {c L : ℕ}
    (hf : ∀ x ∈ xs, RunsWithin X body (f x) (F x) c) (hL : ∀ x ∈ xs, (F x).length ≤ L) :
    RunsWithin X body (SoJProg.csFlatMapB xs f) (xs.flatMap F)
      (xs.length * (c + L + 6) + 4) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (a' := .list .bool)
    (b' := .list .bool) (I := fun _ => True) (c := L + 1)
    (f := fun acc row => Prog.op2 .append row acc) (F := fun acc row => row ++ acc)
    (xs.map F).reverse [] (fun acc _ row hrow => by
      refine ⟨RunsWithin.prim_le rfl ?_, trivial⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hrow)
      simpa [Prim.cost] using hL x hx) trivial
  rw [foldl_append_rev, List.length_reverse, List.length_map] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapList_le hf)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.1.of_eq (by simp [List.flatMap])
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map, Nat.mul_add, Nat.mul_one]
    omega

/-- The cost of `bipRelProg` for `m` points, `k` cells, cells of at most `L` points. -/
def bipRelCost (m k L : ℕ) : ℕ := m * (k * (6 * L + 4) + k + 8) + m * k + m + 6

theorem RunsWithin.bipRelProg (offs c : Array ℕ) (m g : ℕ) {W₂ : List (List ℕ)} {L : ℕ}
    (hL : ∀ B ∈ W₂, B.length ≤ L) :
    RunsWithin X body (SoJProg.bipRelProg offs c m g W₂) (bipRelD (fA offs c) m W₂ g)
      (bipRelCost m W₂.length L) := by
  have hrow : ∀ x ∈ List.range m, RunsWithin X body
      (Programs.mapList (a' := .list .nat) W₂ fun B => SoJProg.bipEdgeProg offs c g x B)
      (W₂.map fun B => bipEdgeD (fA offs c) g x B) (W₂.length * (6 * L + 4) + 2) := by
    intro x _
    refine (RunsWithin.mapList_le (c := 6 * L + 1) fun B hB =>
      (RunsWithin.bipEdgeProg offs c g x B).mono ?_).mono (le_of_eq (by ring))
    have := hL B hB
    omega
  have hfm := RunsWithin.csFlatMapB (a' := .nat) (L := W₂.length)
    (f := fun x => Programs.mapList (a' := .list .nat) W₂ fun B => SoJProg.bipEdgeProg offs c g x B)
    hrow (fun _ _ => by simp)
  have hlen : ((List.range m).flatMap fun x => W₂.map fun B => bipEdgeD (fA offs c) g x B).length
      = m * W₂.length := by
    simp [List.length_flatMap, List.length_range]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, hlen, bipRelCost]
    ring_nf
    omega

end BipEdgeSpecs

section BipEdgeWf

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ g₁ x₁ : var₁ .nat} {m₂ g₂ x₂ : var₂ .nat}
  {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)} {B₁ : var₁ (.list .nat)}
  {B₂ : var₂ (.list .nat)} {W₁ : var₁ (.list (.list .nat))} {W₂ : var₂ (.list (.list .nat))}

theorem wf_bipEdgeProg (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hg : ⟨.nat, g₁, g₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) (hB : ⟨.list .nat, B₁, B₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (bipEdgeProg o₁ c₁ g₁ x₁ B₁)
      (bipEdgeProg o₂ c₂ g₂ x₂ B₂) := by
  unfold bipEdgeProg csColProg anyList
  prog_wf

theorem wf_bipRelProg (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hg : ⟨.nat, g₁, g₂⟩ ∈ Γ)
    (hW : ⟨.list (.list .nat), W₁, W₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (bipRelProg o₁ c₁ m₁ g₁ W₁)
      (bipRelProg o₂ c₂ m₂ g₂ W₂) := by
  unfold bipRelProg csFlatMapB bipEdgeProg csColProg anyList mapList
  prog_wf

end BipEdgeWf

end GraphIso.SoJProg
