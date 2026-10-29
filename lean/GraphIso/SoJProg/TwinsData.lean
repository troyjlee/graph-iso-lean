module

public import GraphIso.SoJProg.Data
public import GraphIso.Representation.Group

/-!
# Twins and degrees on data: the models

The data models of step 1 of milestone 11's `bstep` (`PLAN-14.md` §7 item 2) and their
decoding. The points are `Fin m`; `V₁` is a duplicate-free list of indices below `m`, the cells
are the list `cs` (distinct as sets, `k = |cs|`), and the relation is `relOf m cs a`, read on
the `j`-th cell as `relAt k a x j` (`relOf_eq_relAt`).

* `degD`, `twinD`, `twD`, `tfDegD`, `degsD`, `bigDegsD`, `optMin`: data versions of `deg`,
  `twinCls`, `tw`, `tfDeg`, `bigDegs` and the least big degree.
* `twinColD`, `twinBlkD` and `cpartOf`: the colouring and the blocks of `twinPart`.
* The decoding theorems (`deg_decode`, `twinCls_decode`, `tw_decode`, `tfDeg_decode`,
  `bigDegs_decode`, `optMin_bigDegs`, `twinPart_decode`) equate each with milestone 11's model.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.SplitJohnson GraphIso.Coherent

/-- The relation between point `x` and the `j`-th cell, from the Boolean array. -/
def relAt (k : ℕ) (a : Array Bool) (x j : ℕ) : Bool := getB a (x * k + j)

/-- The distinctness of the listed cells, as sets. -/
def CellsDistinct (m : ℕ) (cs : List (List ℕ)) : Prop :=
  ∀ i < cs.length, ∀ j < cs.length, setOf m (cs.getD i []) = setOf m (cs.getD j []) → i = j

/-- The set of the `j`-th cell. -/
def cellAt (m : ℕ) (cs : List (List ℕ)) (j : ℕ) : Finset (Fin m) := setOf m (cs.getD j [])

theorem relOf_eq_relAt {m : ℕ} {cs : List (List ℕ)} {a : Array Bool} (hcs : CellsDistinct m cs)
    {j : ℕ} (hj : j < cs.length) (x : Fin m) :
    relOf m cs a x (cellAt m cs j) = relAt cs.length a x.val j :=
  relOf_cell hcs hj x

/-- The family is the image of the cell indices. -/
theorem famOf_eq_image (m : ℕ) (cs : List (List ℕ)) :
    famOf m cs = (Finset.range cs.length).image (cellAt m cs) := by
  ext s
  rw [mem_famOf, Finset.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    exact ⟨j, Finset.mem_range.2 hj, by simp [cellAt, List.getD_eq_getElem?_getD, hj]⟩
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    exact ⟨cs[j], List.getElem_mem hj, by simp [cellAt, List.getD_eq_getElem?_getD, hj]⟩

/-- A statement about every cell of the family is one about every cell index. -/
theorem forall_famOf {m : ℕ} {cs : List (List ℕ)} {Q : Finset (Fin m) → Prop} :
    (∀ s ∈ famOf m cs, Q s) ↔ ∀ j < cs.length, Q (cellAt m cs j) := by
  rw [famOf_eq_image]
  simp

/-- Filtering the family by a Boolean predicate counts the cell indices. -/
theorem card_filter_famOf {m : ℕ} {cs : List (List ℕ)} (hcs : CellsDistinct m cs)
    (P : Finset (Fin m) → Bool) :
    ((famOf m cs).filter fun s => P s).card =
      ((List.range cs.length).filter fun j => P (cellAt m cs j)).length := by
  rw [famOf_eq_image, Finset.filter_image, Finset.card_image_of_injOn]
  · have e : ((Finset.range cs.length).filter fun j => P (cellAt m cs j) = true) =
        ((List.range cs.length).filter fun j => P (cellAt m cs j)).toFinset := by
      ext j
      simp
    rw [e, List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  · intro i hi j hj h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi hj
    exact hcs i hi.1 j hj.1 h

/-! ### Models -/

/-- The degree of `x`: the number of cells related to it. -/
def degD (k : ℕ) (a : Array Bool) (x : ℕ) : ℕ := ((List.range k).filter (relAt k a x)).length

/-- The twin class of `x` in `V₁`. -/
def twinD (V₁ : List ℕ) (k : ℕ) (a : Array Bool) (x : ℕ) : List ℕ :=
  V₁.filter fun x' => (List.range k).all fun j => relAt k a x j == relAt k a x' j

/-- The size of the twin class of `x`. -/
def twD (V₁ : List ℕ) (k : ℕ) (a : Array Bool) (x : ℕ) : ℕ := (twinD V₁ k a x).length

/-- The points of `V₁` without twins and of degree `d`. -/
def tfDegD (V₁ : List ℕ) (k : ℕ) (a : Array Bool) (d : ℕ) : List ℕ :=
  V₁.filter fun x => twD V₁ k a x == 1 && degD k a x == d

/-- Remove repetitions, keeping first occurrences. -/
def dedupD (l : List ℕ) : List ℕ :=
  (l.foldl (fun acc x => if acc.contains x then acc else x :: acc) []).reverse

/-- The degrees of the points of `V₁`, without repetitions. -/
def degsD (V₁ : List ℕ) (k : ℕ) (a : Array Bool) : List ℕ := dedupD (V₁.map (degD k a))

/-- The degrees whose points without twins are more than `t`. -/
def bigDegsD (t : ℕ) (V₁ : List ℕ) (k : ℕ) (a : Array Bool) : List ℕ :=
  (degsD V₁ k a).filter fun d => decide (t < (tfDegD V₁ k a d).length)

/-- The least entry of a list, if any. -/
def optMin : List ℕ → Option ℕ
  | [] => none
  | c :: cs => some (cs.foldl min c)

/-- The colours of `twinPart` at the points `0, …, m - 1`. -/
def twinColD (m : ℕ) (V₁ : List ℕ) (k : ℕ) (a : Array Bool) : Array ℕ :=
  ((List.range m).map fun x => Nat.pair (twD V₁ k a x) (degD k a x)).toArray

/-- The blocks of `twinPart` at the points `0, …, m - 1`. -/
def twinBlkD (m : ℕ) (V₁ : List ℕ) (k : ℕ) (a : Array Bool) : Array (List ℕ) :=
  ((List.range m).map fun x =>
    if twD V₁ k a x == 1 then tfDegD V₁ k a (degD k a x) else twinD V₁ k a x).toArray

/-- A colored partition from a colour array and a block array. -/
def cpartOf (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) : CPart (Fin m) :=
  ⟨fun x => get col x.val, fun x => setOf m (blk.getD x.val [])⟩

/-! ### Decoding -/

section Decode

variable {m : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem mem_dedupD {l : List ℕ} {x : ℕ} : x ∈ dedupD l ↔ x ∈ l := by
  have key : ∀ (l acc : List ℕ), x ∈ l.foldl (fun acc x => if acc.contains x then acc else
      x :: acc) acc ↔ x ∈ l ∨ x ∈ acc := by
    intro l
    induction l with
    | nil => simp
    | cons y l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases h : acc.contains y = true
      · simp only [h, ↓reduceIte, List.mem_cons]
        have : y ∈ acc := by simpa using h
        constructor
        · rintro (h | h) <;> tauto
        · rintro ((rfl | h) | h) <;> tauto
      · simp only [h, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
        tauto
  unfold dedupD
  rw [List.mem_reverse, key]
  simp

theorem deg_decode (hcs : CellsDistinct m cs) (x : Fin m) :
    deg (famOf m cs) (relOf m cs a) x = degD cs.length a x.val := by
  unfold deg degD
  rw [card_filter_famOf hcs]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [relOf_eq_relAt hcs (List.mem_range.1 hj)]

theorem twinCls_decode (hcs : CellsDistinct m cs) (x : Fin m) :
    twinCls (setOf m V₁) (famOf m cs) (relOf m cs a) x = setOf m (twinD V₁ cs.length a x.val) := by
  ext x'
  rw [mem_twinCls, mem_setOf, mem_setOf, forall_famOf, twinD, List.mem_filter]
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    have := h2 j hj
    rwa [relOf_eq_relAt hcs hj, relOf_eq_relAt hcs hj] at this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    rw [relOf_eq_relAt hcs hj, relOf_eq_relAt hcs hj]
    exact h2 j hj

theorem tw_decode (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs)
    (x : Fin m) : tw (setOf m V₁) (famOf m cs) (relOf m cs a) x = twD V₁ cs.length a x.val := by
  unfold tw twD
  rw [twinCls_decode hcs, twinD, card_setOf (hV₁.filter _)]
  intro i hi
  exact hV₁m i (List.mem_of_mem_filter hi)

theorem tfDeg_decode (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs)
    (d : ℕ) :
    tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d = setOf m (tfDegD V₁ cs.length a d) := by
  ext x
  rw [tfDeg, Finset.mem_filter, mem_setOf, mem_setOf, tfDegD, List.mem_filter,
    tw_decode hV₁ hV₁m hcs, deg_decode hcs]
  simp

theorem card_tfDeg (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs)
    (d : ℕ) :
    (tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d).card = (tfDegD V₁ cs.length a d).length := by
  rw [tfDeg_decode hV₁ hV₁m hcs, tfDegD, card_setOf (hV₁.filter _)]
  intro i hi
  exact hV₁m i (List.mem_of_mem_filter hi)

theorem bigDegs_decode (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs)
    (t : ℕ) :
    bigDegs t (setOf m V₁) (famOf m cs) (relOf m cs a) =
      (bigDegsD t V₁ cs.length a).toFinset := by
  ext d
  rw [bigDegs, Finset.mem_filter, Finset.mem_image, List.mem_toFinset, bigDegsD, List.mem_filter,
    degsD, mem_dedupD, List.mem_map, card_tfDeg hV₁ hV₁m hcs]
  simp only [decide_eq_true_eq, mem_setOf]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ht⟩
    exact ⟨⟨x.val, hx, (deg_decode hcs x).symm⟩, ht⟩
  · rintro ⟨⟨x, hx, rfl⟩, ht⟩
    exact ⟨⟨⟨x, hV₁m x hx⟩, hx, deg_decode hcs _⟩, ht⟩

theorem optMin_eq (l : List ℕ) :
    optMin l = if h : l.toFinset.Nonempty then some (l.toFinset.min' h) else none := by
  cases l with
  | nil => simp [optMin]
  | cons c cs =>
    have hne : (c :: cs).toFinset.Nonempty := ⟨c, by simp⟩
    simp only [hne, ↓reduceDIte, optMin, Option.some.injEq]
    have key : ∀ (l : List ℕ) (c : ℕ), l.foldl min c ∈ c :: l ∧
        ∀ y ∈ c :: l, l.foldl min c ≤ y := by
      intro l
      induction l with
      | nil => intro c; simp
      | cons d l ih =>
        intro c
        obtain ⟨h1, h2⟩ := ih (min c d)
        rw [List.foldl_cons]
        refine ⟨?_, fun y hy => ?_⟩
        · rcases List.mem_cons.1 h1 with h | h
          · rw [h]
            rcases Nat.le_total c d with hcd | hcd
            · rw [Nat.min_eq_left hcd]
              exact List.mem_cons_self
            · rw [Nat.min_eq_right hcd]
              exact List.mem_cons_of_mem _ List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact (h2 _ List.mem_cons_self).trans (Nat.min_le_left _ _)
          · rcases List.mem_cons.1 hy with rfl | hy
            · exact (h2 _ List.mem_cons_self).trans (Nat.min_le_right _ _)
            · exact h2 y (List.mem_cons_of_mem _ hy)
    obtain ⟨h1, h2⟩ := key cs c
    apply le_antisymm
    · exact h2 _ (by simpa using Finset.min'_mem _ hne)
    · exact Finset.min'_le _ _ (by simpa using h1)

theorem optMin_bigDegs (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs)
    (t : ℕ) :
    optMin (bigDegsD t V₁ cs.length a) =
      if h : (bigDegs t (setOf m V₁) (famOf m cs) (relOf m cs a)).Nonempty then
        some ((bigDegs t (setOf m V₁) (famOf m cs) (relOf m cs a)).min' h) else none := by
  rw [optMin_eq]
  simp only [bigDegs_decode hV₁ hV₁m hcs]

theorem twinPart_decode (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs) :
    cpartOf m (twinColD m V₁ cs.length a) (twinBlkD m V₁ cs.length a) =
      twinPart (setOf m V₁) (famOf m cs) (relOf m cs a) := by
  unfold cpartOf twinPart
  congr 1
  · funext x
    rw [twinColD, get, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range x.2, tw_decode hV₁ hV₁m hcs, deg_decode hcs]
    rfl
  · funext x
    rw [twinBlkD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range x.2, tw_decode hV₁ hV₁m hcs, deg_decode hcs]
    simp only [Option.map_some, Option.getD_some, beq_iff_eq]
    split_ifs
    · exact (tfDeg_decode hV₁ hV₁m hcs _).symm
    · exact (twinCls_decode hcs x).symm

end Decode

end GraphIso.SoJProg
