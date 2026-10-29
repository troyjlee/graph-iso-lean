module

public import GraphIso.SoJTree.Measure
public import GraphIso.SoJProg.JohnsonData
public import GraphIso.SoJProg.BaseCaseData
public import GraphIso.SoJProg.Coherent

/-!
# Leaves of Split-or-Johnson on data

Stage 14d, item 2 (`PLAN-14.md` §8). A leaf of milestone 11's `bsoj`, `sojAt` and `soj` on the
points `Fin m` is an `Option (Out (Fin m))`: none, a colored partition or a Johnson
embedding. On data it is an `OutD`, a tag with the arrays of stage 14c's `cpartOf` (colours and
blocks at the points `0, …, m - 1`) and `jembOf` (points, cells, the parameter `s`, and for
every point the indices of its cells).

* `decodeOut`: the decoding.
* `addPieceD`, `extendD`: `addPieceOut` and `extendOut` on data (`decodeOut_addPieceD`,
  `decodeOut_extendD`).
* `outEqD`: equality of decoded leaves (`outEqD_iff`), comparing lists as sets.
* `actOutD`: a permutation, given by its forward and inverse arrays, acting on leaf data
  (`decodeOut_actOutD`). Entries at or above `m` are dropped, so the decoding needs no
  well-formedness of the data.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg

/-- Leaf data: `(tag, (col, blk), (V0, (cs, (s, fA))))`. Tag `1` is the colored partition
`cpartOf m col blk`, tag `2` the Johnson embedding `jembOf m V0 cs s fA`, any other tag none. -/
abbrev OutD := ℕ × ((Array ℕ × Array (List ℕ)) × (List ℕ × (List (List ℕ) × (ℕ × Array (List ℕ)))))

/-- The type of leaf data in programs. -/
abbrev outTy : Cost.Ty :=
  .prod .nat (.prod (.prod (.array .nat) (.array (.list .nat)))
    (.prod (.list .nat) (.prod (.list (.list .nat)) (.prod .nat (.array (.list .nat))))))

/-- The leaf `none`. -/
def noneD : OutD := (0, (#[], #[]), ([], ([], (0, #[]))))

/-- A colored partition. -/
def partD (col : Array ℕ) (blk : Array (List ℕ)) : OutD := (1, (col, blk), ([], ([], (0, #[]))))

/-- A Johnson embedding. -/
def johnD (V0 : List ℕ) (cs : List (List ℕ)) (s : ℕ) (fA : Array (List ℕ)) : OutD :=
  (2, (#[], #[]), (V0, (cs, (s, fA))))

/-- **The decoding of leaf data.** -/
def decodeOut (m : ℕ) (o : OutD) : Option (Out (Fin m)) :=
  if o.1 = 1 then some (.inl (cpartOf m o.2.1.1 o.2.1.2))
  else if o.1 = 2 then some (.inr (jembOf m o.2.2.1 o.2.2.2.1 o.2.2.2.2.1 o.2.2.2.2.2))
  else none

theorem decodeOut_noneD (m : ℕ) : decodeOut m noneD = none := by
  simp [decodeOut, noneD]

theorem decodeOut_partD (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) :
    decodeOut m (partD col blk) = some (.inl (cpartOf m col blk)) := by
  simp [decodeOut, partD]

theorem decodeOut_johnD (m : ℕ) (V0 : List ℕ) (cs : List (List ℕ)) (s : ℕ)
    (fA : Array (List ℕ)) : decodeOut m (johnD V0 cs s fA) = some (.inr (jembOf m V0 cs s fA)) := by
  simp [decodeOut, johnD]

theorem ld_decodeOut_one {m : ℕ} {o : OutD} (h : o.1 = 1) :
    decodeOut m o = some (.inl (cpartOf m o.2.1.1 o.2.1.2)) := by
  simp [decodeOut, h]

theorem ld_decodeOut_two {m : ℕ} {o : OutD} (h : o.1 = 2) :
    decodeOut m o = some (.inr (jembOf m o.2.2.1 o.2.2.2.1 o.2.2.2.2.1 o.2.2.2.2.2)) := by
  simp [decodeOut, h]

theorem ld_decodeOut_other {m : ℕ} {o : OutD} (h₁ : o.1 ≠ 1) (h₂ : o.1 ≠ 2) :
    decodeOut m o = none := by
  simp [decodeOut, h₁, h₂]

theorem ld_get_map_range (m : ℕ) (f : ℕ → ℕ) {x : ℕ} (hx : x < m) :
    get ((List.range m).map f).toArray x = f x := by
  rw [get_toArray]
  simp [hx]

theorem ld_getD_map_range {β : Type} (m : ℕ) (f : ℕ → β) (d : β) {x : ℕ} (hx : x < m) :
    ((List.range m).map f).toArray.getD x d = f x := by
  simp [hx]

/-! ### Pieces and extensions -/

/-- `addPieceOut` on data, at the points `0, …, m - 1`. -/
def addPieceD (m : ℕ) (D : List ℕ) (o : OutD) : OutD :=
  if o.1 = 1 then
    partD ((List.range m).map fun x => if x ∈ D then 0 else get o.2.1.1 x + 1).toArray
      ((List.range m).map fun x => if x ∈ D then D else o.2.1.2.getD x []).toArray
  else o

theorem decodeOut_addPieceD (m : ℕ) (D : List ℕ) (o : OutD) :
    decodeOut m (addPieceD m D o) = addPieceOut (setOf m D) (decodeOut m o) := by
  unfold addPieceD
  split_ifs with h₁
  · rw [decodeOut_partD, ld_decodeOut_one h₁]
    simp only [addPieceOut, addPiece, cpartOf, Option.some.injEq, Sum.inl.injEq, CPart.mk.injEq]
    constructor
    · funext x
      rw [ld_get_map_range m _ x.2]
      simp [mem_setOf]
    · funext x
      rw [ld_getD_map_range m _ _ x.2]
      by_cases hx : x.val ∈ D
      · simp [hx, mem_setOf]
      · simp [hx, mem_setOf]
  · by_cases h₂ : o.1 = 2
    · rw [ld_decodeOut_two h₂]
      rfl
    · rw [ld_decodeOut_other h₁ h₂]
      rfl

/-- `extendOut` on data: outside `V₁` the colours `2 col y + 1` and their classes. -/
def extendD (m : ℕ) (V₁ : List ℕ) (col : ℕ → ℕ) (o : OutD) : OutD :=
  if o.1 = 1 then
    partD ((List.range m).map fun y => if y ∈ V₁ then 2 * get o.2.1.1 y else 2 * col y + 1).toArray
      ((List.range m).map fun y => if y ∈ V₁ then o.2.1.2.getD y [] else
        (List.range m).filter fun z => decide (z ∉ V₁ ∧ col z = col y)).toArray
  else o

theorem decodeOut_extendD (m : ℕ) (V₁ : List ℕ) {col : ℕ → ℕ} {colF : Fin m → ℕ}
    (hcol : ∀ y : Fin m, col y.val = colF y) (o : OutD) :
    decodeOut m (extendD m V₁ col o) = extendOut (setOf m V₁) colF (decodeOut m o) := by
  unfold extendD
  split_ifs with h₁
  · rw [decodeOut_partD, ld_decodeOut_one h₁]
    simp only [extendOut, extendPart, cpartOf, Option.some.injEq, Sum.inl.injEq,
      CPart.mk.injEq]
    constructor
    · funext y
      rw [ld_get_map_range m _ y.2]
      by_cases hy : y.val ∈ V₁
      · simp [hy, mem_setOf]
      · simp [hy, mem_setOf, hcol]
    · funext y
      rw [ld_getD_map_range m _ _ y.2]
      by_cases hy : y.val ∈ V₁
      · simp [hy, mem_setOf]
      · simp only [hy, ite_false, mem_setOf]
        ext z
        simp [mem_setOf, hcol]
  · by_cases h₂ : o.1 = 2
    · rw [ld_decodeOut_two h₂]
      rfl
    · rw [ld_decodeOut_other h₁ h₂]
      rfl

/-! ### Equality -/

/-- Equality of two lists as sets of points below `m`. -/
def setEqD (m : ℕ) (l l' : List ℕ) : Bool := (List.range m).all fun i => decide (i ∈ l ↔ i ∈ l')

theorem setEqD_iff (m : ℕ) (l l' : List ℕ) : setEqD m l l' = true ↔ setOf m l = setOf m l' := by
  simp only [setEqD, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h
    ext x
    rw [mem_setOf, mem_setOf]
    exact h x.val x.2
  · intro h i hi
    have := congrArg (fun s : Finset (Fin m) => (⟨i, hi⟩ : Fin m) ∈ s) h
    simpa [mem_setOf] using this

/-- Every cell of `cs` with an index in `js` equals a cell of `cs'` with an index in `js'`. -/
def famSubD (m : ℕ) (cs : List (List ℕ)) (js : List ℕ) (cs' : List (List ℕ)) (js' : List ℕ) :
    Bool :=
  js.all fun j => js'.any fun j' => setEqD m (cs.getD j []) (cs'.getD j' [])

/-- Equality of two families of indexed cells. -/
def famEqD (m : ℕ) (cs : List (List ℕ)) (js : List ℕ) (cs' : List (List ℕ)) (js' : List ℕ) :
    Bool :=
  famSubD m cs js cs' js' && famSubD m cs' js' cs js

theorem famEqD_iff (m : ℕ) (cs : List (List ℕ)) (js : List ℕ) (cs' : List (List ℕ))
    (js' : List ℕ) : famEqD m cs js cs' js' = true ↔ famIdx m cs js = famIdx m cs' js' := by
  have hsub : ∀ (cs : List (List ℕ)) (js : List ℕ) (cs' : List (List ℕ)) (js' : List ℕ),
      famSubD m cs js cs' js' = true ↔ famIdx m cs js ⊆ famIdx m cs' js' := by
    intro cs js cs' js'
    simp only [famSubD, List.all_eq_true, List.any_eq_true, setEqD_iff, famIdx]
    constructor
    · intro h s hs
      rw [List.mem_toFinset, List.mem_map] at hs
      obtain ⟨j, hj, rfl⟩ := hs
      obtain ⟨j', hj', he⟩ := h j hj
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨j', hj', by simp only [cellAt]; exact he.symm⟩
    · intro h j hj
      have := h (List.mem_toFinset.2 (List.mem_map.2 ⟨j, hj, rfl⟩))
      rw [List.mem_toFinset, List.mem_map] at this
      obtain ⟨j', hj', he⟩ := this
      exact ⟨j', hj', by simp only [cellAt] at he; exact he.symm⟩
  rw [famEqD, Bool.and_eq_true, hsub, hsub]
  exact ⟨fun h => Finset.Subset.antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- **Equality of decoded leaves**, on data. -/
def outEqD (m : ℕ) (o o' : OutD) : Bool :=
  if o.1 = 1 then
    o'.1 == 1 && (List.range m).all fun x =>
      get o.2.1.1 x == get o'.2.1.1 x && setEqD m (o.2.1.2.getD x []) (o'.2.1.2.getD x [])
  else if o.1 = 2 then
    o'.1 == 2 && setEqD m o.2.2.1 o'.2.2.1 &&
      famEqD m o.2.2.2.1 (List.range o.2.2.2.1.length) o'.2.2.2.1
        (List.range o'.2.2.2.1.length) &&
      o.2.2.2.2.1 == o'.2.2.2.2.1 && (List.range m).all fun x =>
        famEqD m o.2.2.2.1 (o.2.2.2.2.2.getD x []) o'.2.2.2.1 (o'.2.2.2.2.2.getD x [])
  else o'.1 != 1 && o'.1 != 2

theorem outEqD_iff (m : ℕ) (o o' : OutD) :
    outEqD m o o' = true ↔ decodeOut m o = decodeOut m o' := by
  have hcp : ∀ (col col' : Array ℕ) (blk blk' : Array (List ℕ)),
      cpartOf m col blk = cpartOf m col' blk' ↔ ∀ x < m, get col x = get col' x ∧
        setOf m (blk.getD x []) = setOf m (blk'.getD x []) := by
    intro col col' blk blk'
    simp only [cpartOf, CPart.mk.injEq, funext_iff]
    constructor
    · rintro ⟨h₁, h₂⟩ x hx
      exact ⟨h₁ ⟨x, hx⟩, h₂ ⟨x, hx⟩⟩
    · intro h
      exact ⟨fun x => (h x x.2).1, fun x => (h x x.2).2⟩
  have hfam : ∀ cs : List (List ℕ), famIdx m cs (List.range cs.length) = famOf m cs := by
    intro cs
    rw [famOf_eq_image]
    ext s
    simp [famIdx]
  have hje : ∀ (V0 V0' : List ℕ) (cs cs' : List (List ℕ)) (s s' : ℕ)
      (fA fA' : Array (List ℕ)), jembOf m V0 cs s fA = jembOf m V0' cs' s' fA' ↔
        setOf m V0 = setOf m V0' ∧
          famIdx m cs (List.range cs.length) = famIdx m cs' (List.range cs'.length) ∧
          s = s' ∧ ∀ x < m, famIdx m cs (fA.getD x []) = famIdx m cs' (fA'.getD x []) := by
    intro V0 V0' cs cs' s s' fA fA'
    simp only [jembOf, JEmb.mk.injEq, funext_iff, hfam]
    constructor
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨h₁, h₂, h₃, fun x hx => h₄ ⟨x, hx⟩⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨h₁, h₂, h₃, fun x => h₄ x x.2⟩
  unfold outEqD
  by_cases h₁ : o.1 = 1
  · rw [ite_eq_left h₁, ld_decodeOut_one h₁]
    by_cases h₁' : o'.1 = 1
    · rw [ld_decodeOut_one h₁']
      simp only [h₁', beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range,
        Bool.and_eq_true, beq_iff_eq, setEqD_iff, Option.some.injEq, Sum.inl.injEq, hcp]
    · by_cases h₂' : o'.1 = 2
      · rw [ld_decodeOut_two h₂']
        simp [h₁']
      · rw [ld_decodeOut_other h₁' h₂']
        simp [h₁']
  · rw [ite_eq_right h₁]
    by_cases h₂ : o.1 = 2
    · rw [ite_eq_left h₂, ld_decodeOut_two h₂]
      by_cases h₂' : o'.1 = 2
      · rw [ld_decodeOut_two h₂']
        simp only [h₂', beq_self_eq_true, Bool.true_and, List.all_eq_true, List.mem_range,
          Bool.and_eq_true, beq_iff_eq, setEqD_iff, famEqD_iff, Option.some.injEq,
          Sum.inr.injEq, hje, and_assoc]
      · by_cases h₁' : o'.1 = 1
        · rw [ld_decodeOut_one h₁']
          simp [h₂']
        · rw [ld_decodeOut_other h₁' h₂']
          simp [h₂']
    · rw [ite_eq_right h₂, ld_decodeOut_other h₁ h₂]
      by_cases h₁' : o'.1 = 1
      · rw [ld_decodeOut_one h₁']
        simp [h₁']
      · by_cases h₂' : o'.1 = 2
        · rw [ld_decodeOut_two h₂']
          simp [h₂']
        · rw [ld_decodeOut_other h₁' h₂']
          simp [h₁', h₂']

/-! ### The action of a permutation -/

/-- A list of points moved by `σ`, dropping the entries at or above `m`. -/
def mapPtsD (m : ℕ) (σ : PermData) (l : List ℕ) : List ℕ :=
  (l.filter fun i => decide (i < m)).map (get σ.1)

/-- **A permutation acting on leaf data**: `σ = (fwd, inv)` on the points `0, …, m - 1`. -/
def actOutD (m : ℕ) (σ : PermData) (o : OutD) : OutD :=
  if o.1 = 1 then
    partD ((List.range m).map fun v => get o.2.1.1 (get σ.2 v)).toArray
      ((List.range m).map fun v => mapPtsD m σ (o.2.1.2.getD (get σ.2 v) [])).toArray
  else if o.1 = 2 then
    johnD (mapPtsD m σ o.2.2.1) (o.2.2.2.1.map (mapPtsD m σ)) o.2.2.2.2.1
      ((List.range m).map fun v => o.2.2.2.2.2.getD (get σ.2 v) []).toArray
  else o

open Pointwise

theorem ld_setOf_mapPtsD {m : ℕ} {σ : PermData} (hσ : σ.Valid m) (l : List ℕ) :
    setOf m (mapPtsD m σ l) = PermData.denote m σ • setOf m l := by
  ext y
  rw [mem_setOf, Finset.mem_smul_finset]
  simp only [mapPtsD, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_setOf,
    Equiv.Perm.smul_def]
  constructor
  · rintro ⟨i, ⟨hil, him⟩, hiy⟩
    refine ⟨⟨i, him⟩, hil, Fin.ext ?_⟩
    rw [PermData.val_denote_apply hσ]
    exact hiy
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, ⟨hx, x.2⟩, (PermData.val_denote_apply hσ x).symm⟩

theorem ld_cellAt_map {m : ℕ} {σ : PermData} (hσ : σ.Valid m) (cs : List (List ℕ)) (j : ℕ) :
    cellAt m (cs.map (mapPtsD m σ)) j = PermData.denote m σ • cellAt m cs j := by
  unfold cellAt
  rw [← ld_setOf_mapPtsD hσ]
  exact congrArg (setOf m) (List.getD_map cs [] (mapPtsD m σ))

theorem ld_famIdx_map {m : ℕ} {σ : PermData} (hσ : σ.Valid m) (cs : List (List ℕ))
    (js : List ℕ) :
    famIdx m (cs.map (mapPtsD m σ)) js = PermData.denote m σ • famIdx m cs js := by
  ext s
  rw [Finset.mem_smul_finset]
  simp only [famIdx, List.mem_toFinset, List.mem_map, ld_cellAt_map hσ]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨cellAt m cs j, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem ld_famOf_map {m : ℕ} {σ : PermData} (hσ : σ.Valid m) (cs : List (List ℕ)) :
    famOf m (cs.map (mapPtsD m σ)) = PermData.denote m σ • famOf m cs := by
  ext s
  rw [Finset.mem_smul_finset]
  simp only [mem_famOf, List.mem_map]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨setOf m l, ⟨l, hl, rfl⟩, (ld_setOf_mapPtsD hσ l).symm⟩
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    exact ⟨mapPtsD m σ l, ⟨l, hl, rfl⟩, ld_setOf_mapPtsD hσ l⟩

theorem ld_cpart_ext {α : Type*} {p q : CPart α} (h₁ : ∀ v, p.col v = q.col v)
    (h₂ : ∀ v, p.blk v = q.blk v) : p = q := by
  cases p
  cases q
  simp only [CPart.mk.injEq]
  exact ⟨funext h₁, funext h₂⟩

theorem ld_jemb_ext {α : Type*} {J K : JEmb α} (h₁ : J.V0 = K.V0) (h₂ : J.Λ = K.Λ)
    (h₃ : J.s = K.s) (h₄ : ∀ v, J.f v = K.f v) : J = K := by
  cases J
  cases K
  simp only [JEmb.mk.injEq]
  exact ⟨h₁, h₂, h₃, funext h₄⟩

theorem decodeOut_actOutD {m : ℕ} {σ : PermData} (hσ : σ.Valid m) (o : OutD) :
    decodeOut m (actOutD m σ o) = PermData.denote m σ • decodeOut m o := by
  have hinv : ∀ v : Fin m, get σ.2 v.val = ((PermData.denote m σ)⁻¹ • v).val := fun v => by
    rw [Equiv.Perm.smul_def, PermData.val_denote_inv_apply hσ]
  unfold actOutD
  by_cases h₁ : o.1 = 1
  · rw [ite_eq_left h₁, decodeOut_partD, ld_decodeOut_one h₁, Option.smul_some, Sum.smul_inl]
    refine congrArg (fun p => some (Sum.inl p)) (ld_cpart_ext (fun v => ?_) (fun v => ?_))
    · rw [CPart.smul_col]
      simp only [cpartOf]
      rw [ld_get_map_range m _ v.2, hinv v]
    · rw [CPart.smul_blk]
      simp only [cpartOf]
      rw [ld_getD_map_range m _ _ v.2, ld_setOf_mapPtsD hσ, hinv v]
  · rw [ite_eq_right h₁]
    by_cases h₂ : o.1 = 2
    · rw [ite_eq_left h₂, decodeOut_johnD, ld_decodeOut_two h₂, Option.smul_some,
        Sum.smul_inr]
      refine congrArg (fun J => some (Sum.inr J)) (ld_jemb_ext ?_ ?_ rfl (fun v => ?_))
      · rw [JEmb.smul_V0]
        exact ld_setOf_mapPtsD hσ _
      · rw [JEmb.smul_Λ]
        exact ld_famOf_map hσ _
      · rw [JEmb.smul_f]
        simp only [jembOf]
        rw [ld_getD_map_range m _ _ v.2, ld_famIdx_map hσ, hinv v]
    · rw [ite_eq_right h₂, ld_decodeOut_other h₁ h₂]
      rfl

end GraphIso.SoJTree
