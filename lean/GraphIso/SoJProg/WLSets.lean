module

public import GraphIso.SoJProg.Data
public import GraphIso.Coherent.WLProg
public import GraphIso.SplitJohnson.BipartiteDef

/-!
# Weisfeiler–Leman on sets

Milestone 11 refines colourings of tuples of an arbitrary finite type with `wlOn`
(`GraphIso/Coherent/WLOn.lean`), defined through any enumeration of the type. Here the
refinement of milestone 10's program `wlProg k v` (on tuples of `Fin v`, indexed by codes) is
identified with `wlOn` along a bijection `f : Fin v → V` (`get_wlA_eq_wlOn`), for the two types
on which Split-or-Johnson refines (`PLAN-14.md` §7 item 6):

* **the cells** `↥(famOf m cs)` of a duplicate-free list of cells `cs`, numbered by their
  positions (`cellSub`, `get_wlA_cells`): the `d`-ary refinement `wlOn d cd` of step 3 of
  `bstep`;
* **points and cells** `V₁' ⊔ V₂`, numbered consecutively, points first (`sqAt`,
  `cohOn_eq_wlA`): the classical refinement `cohOn SQ c₀` of `dlCont`. Its initial colouring
  `code A Y` is computed on codes by `sqCodeArrProg` (`RunsWithin.sqCodeArrProg`,
  `toFun_sqCodeArr`), and its refinement by `cohProg` (`RunsWithin.cohProg`, `cohOn_code_eq`).

Distinct cells are stated as `(cs.map (setOf m)).Nodup`; `nodup_of_getD_inj` and
`getD_inj_of_nodup` convert from and to the form of `relOf_cell`.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.Coherent GraphIso.SplitJohnson GraphIso.Cost GraphIso.Programs

/-! ### Refinement along a bijection -/

/-- **`wlProg` computes `wlOn` along a bijection**: if the array `col` is the colouring `c` of the
tuples of `V`, read along `f : Fin v → V`, the refined array at the code of `y` is `wlOn k c`
at `f ∘ y`. -/
theorem get_wlA_eq_wlOn {V : Type*} [Fintype V] [DecidableEq V] {k v : ℕ} {f : Fin v → V}
    (hf : Function.Bijective f) (c : (Fin k → V) → ℕ) {col : Array ℕ}
    (hcol : ∀ y : Tup k v, toFun col y = c (f ∘ y)) (y : Tup k v) :
    get (wlA k v col).1 (enc y) = wlOn k c (f ∘ y) := by
  let e : V ≃ Fin v := (Equiv.ofBijective f hf).symm
  have hes : ∀ z, e.symm z = f z := fun _ => rfl
  rw [wlA_eq, get_arrOf, wlOn_eq' c e]
  have h1 : toFun col = fun y => c (⇑e.symm ∘ y) := by
    funext y
    rw [hcol]
    rfl
  rw [h1]
  have h2 : ⇑e ∘ (f ∘ y) = y := by
    funext i
    show e (f (y i)) = y i
    rw [← hes, Equiv.apply_symm_apply]
  show _ = (wl k v fun y => c (⇑e.symm ∘ y)).1 (⇑e ∘ (f ∘ y))
  rw [h2]

/-! ### The cells -/

/-- The `j`-th listed cell, as a point of the family of cells. -/
def cellSub (m : ℕ) (cs : List (List ℕ)) (j : Fin cs.length) : ↥(famOf m cs) :=
  ⟨setOf m (cs.get j), mem_famOf.2 ⟨cs.get j, List.get_mem _ _, rfl⟩⟩

theorem coe_cellSub (m : ℕ) (cs : List (List ℕ)) (j : Fin cs.length) :
    (cellSub m cs j : Finset (Fin m)) = setOf m (cs.get j) := rfl

/-- **Distinct cells are numbered bijectively** by their positions. -/
theorem cellSub_bijective {m : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup) :
    Function.Bijective (cellSub m cs) := by
  constructor
  · intro i j h
    have h' : setOf m (cs.get i) = setOf m (cs.get j) := congrArg Subtype.val h
    have hi : (cs.map (setOf m)).get ⟨i, by simp⟩ = (cs.map (setOf m)).get ⟨j, by simp⟩ := by
      simpa using h'
    have := (List.Nodup.get_inj_iff hcs).1 hi
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · rintro ⟨s, hs⟩
    obtain ⟨l, hl, rfl⟩ := mem_famOf.1 hs
    obtain ⟨j, rfl⟩ := List.get_of_mem hl
    exact ⟨j, rfl⟩

/-- **The `d`-ary refinement of the cells** (`wlOn d cd` in step 3 of `bstep`). -/
theorem get_wlA_cells {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    (c : (Fin d → ↥(famOf m cs)) → ℕ) {col : Array ℕ}
    (hcol : ∀ y : Tup d cs.length, toFun col y = c (cellSub m cs ∘ y)) (y : Tup d cs.length) :
    get (wlA d cs.length col).1 (enc y) = wlOn d c (cellSub m cs ∘ y) :=
  get_wlA_eq_wlOn (cellSub_bijective hcs) c hcol y

/-! ### Points and cells -/

/-- The set `V₁' ⊔ V₂` of points `ps` and cells `cs`. -/
def sqSet (m : ℕ) (ps : List ℕ) (cs : List (List ℕ)) : Finset (Fin m ⊕ Finset (Fin m)) :=
  (setOf m ps).disjSum (famOf m cs)

/-- The numbering of `V₁' ⊔ V₂`: the points of `ps` first, then the cells of `cs`. -/
def sqAt (m : ℕ) (ps : List ℕ) (cs : List (List ℕ)) (hps : ∀ i ∈ ps, i < m)
    (j : Fin (ps.length + cs.length)) : ↥(sqSet m ps cs) :=
  if h : j.val < ps.length then
    ⟨.inl ⟨ps.get ⟨j, h⟩, hps _ (List.get_mem _ _)⟩, by
      simp only [sqSet, Finset.inl_mem_disjSum, mem_setOf]
      exact List.get_mem _ _⟩
  else
    ⟨.inr (setOf m (cs.get ⟨j - ps.length, by omega⟩)), by
      simp only [sqSet, Finset.inr_mem_disjSum]
      exact mem_famOf.2 ⟨_, List.get_mem _ _, rfl⟩⟩

theorem sqAt_lt {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} {hps : ∀ i ∈ ps, i < m}
    {j : Fin (ps.length + cs.length)} (h : j.val < ps.length) :
    (sqAt m ps cs hps j : Fin m ⊕ Finset (Fin m)) =
      .inl ⟨ps.get ⟨j, h⟩, hps _ (List.get_mem _ _)⟩ := by
  simp [sqAt, h]

theorem sqAt_ge {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} {hps : ∀ i ∈ ps, i < m}
    {j : Fin (ps.length + cs.length)} (h : ps.length ≤ j.val) :
    (sqAt m ps cs hps j : Fin m ⊕ Finset (Fin m)) =
      .inr (setOf m (cs.get ⟨j - ps.length, by omega⟩)) := by
  simp [sqAt, show ¬ j.val < ps.length by omega]

/-- **The numbering of points and cells is bijective** for duplicate-free points and distinct
cells. -/
theorem sqAt_bijective {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} (hps : ∀ i ∈ ps, i < m)
    (hpn : ps.Nodup) (hcs : (cs.map (setOf m)).Nodup) : Function.Bijective (sqAt m ps cs hps) := by
  constructor
  · intro i j h
    have h' := congrArg Subtype.val h
    by_cases hi : i.val < ps.length <;> by_cases hj : j.val < ps.length
    · rw [sqAt_lt hi, sqAt_lt hj] at h'
      have hv : ps.get ⟨i, hi⟩ = ps.get ⟨j, hj⟩ := by
        have := Sum.inl_injective h'
        exact congrArg Fin.val this
      have := (List.Nodup.get_inj_iff hpn).1 hv
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · rw [sqAt_lt hi, sqAt_ge (by omega)] at h'
      exact absurd h' Sum.inl_ne_inr
    · rw [sqAt_ge (by omega), sqAt_lt hj] at h'
      exact absurd h' Sum.inr_ne_inl
    · rw [sqAt_ge (by omega), sqAt_ge (by omega)] at h'
      have hv := Sum.inr_injective h'
      have := (cellSub_bijective hcs).1 (Subtype.ext (by simpa [coe_cellSub] using hv) :
        cellSub m cs ⟨i - ps.length, by omega⟩ = cellSub m cs ⟨j - ps.length, by omega⟩)
      have := congrArg Fin.val this
      simp only at this
      exact Fin.ext (by omega)
  · rintro ⟨z, hz⟩
    rcases z with x | s
    · have hx : x.val ∈ ps := by
        simpa [sqSet, Finset.inl_mem_disjSum, mem_setOf] using hz
      obtain ⟨i, hi⟩ := List.get_of_mem hx
      refine ⟨⟨i, by omega⟩, Subtype.ext ?_⟩
      rw [sqAt_lt (by simp)]
      congr 1
      exact Fin.ext hi
    · have hs : s ∈ famOf m cs := by simpa [sqSet, Finset.inr_mem_disjSum] using hz
      obtain ⟨⟨j, hj⟩, hj'⟩ := (cellSub_bijective hcs).2 ⟨s, hs⟩
      refine ⟨⟨ps.length + j, by omega⟩, Subtype.ext ?_⟩
      rw [sqAt_ge (by simp)]
      have := congrArg Subtype.val hj'
      rw [coe_cellSub] at this
      simp only [add_tsub_cancel_left]
      exact congrArg Sum.inr this

/-- **The classical refinement on points and cells** (`cohOn SQ c₀` of `dlCont`): if `col` is the
colouring `c₀` of the pairs, read along the numbering, the refined array at the code of
`![i, j]` is `cohOn` at the numbered points. -/
theorem cohOn_eq_wlA {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} (hps : ∀ i ∈ ps, i < m)
    (hpn : ps.Nodup) (hcs : (cs.map (setOf m)).Nodup)
    (c₀ : Fin m ⊕ Finset (Fin m) → Fin m ⊕ Finset (Fin m) → ℕ) {col : Array ℕ}
    (hcol : ∀ y : Tup 2 (ps.length + cs.length),
      toFun col y = c₀ (sqAt m ps cs hps (y 0)).val (sqAt m ps cs hps (y 1)).val)
    (i j : Fin (ps.length + cs.length)) :
    cohOn (sqSet m ps cs) c₀ (sqAt m ps cs hps i).val (sqAt m ps cs hps j).val =
      get (wlA 2 (ps.length + cs.length) col).1 (enc ![i, j]) := by
  have hb := sqAt_bijective hps hpn hcs
  have h := get_wlA_eq_wlOn hb (fun p : Fin 2 → ↥(sqSet m ps cs) => c₀ (p 0).val (p 1).val)
    (col := col) (fun y => hcol y) ![i, j]
  rw [h, cohOn]
  split_ifs with hh
  · congr 1
    funext t
    rcases t with ⟨_ | _ | _, ht⟩
    · rfl
    · rfl
    · omega
  · exact absurd ⟨(sqAt m ps cs hps i).2, (sqAt m ps cs hps j).2⟩ hh

/-! ### The initial colouring `code A Y` on codes -/

/-- An array built by mapping the tuples of `Fin v` in code order, read at the code of `y`. -/
theorem get_tupMap {k v : ℕ} (F : List ℕ → ℕ) (y : Tup k v) :
    get ((tupList k v).map F).toArray (enc y) = F (digits y) := by
  have h := enc_lt y
  have hd := digits_symm (k := k) (m := v) ⟨enc y, h⟩
  rw [symm_enc] at hd
  rw [tupList_eq, hd]
  simp [get, Array.getD_eq_getD_getElem?, h]

/-- The entry of `code A Y` at the numbered pair `(i, j)`: points `ps` first (`p = |ps|`), then
`q` cells; the relation `a` is read at `x · q + j'` and the 2-skeleton `Y` of the cells at
`i' + j' · q`. -/
def sqCodeEntry (ps : List ℕ) (q : ℕ) (a : Array Bool) (Y : Array ℕ) (i j : ℕ) : ℕ :=
  if i < ps.length then
    if j < ps.length then 0
    else if getB a (ps.getD i 0 * q + (j - ps.length)) then 1 else 2
  else if j < ps.length then
    if getB a (ps.getD j 0 * q + (i - ps.length)) then 3 else 4
  else 5 + get Y ((i - ps.length) + (j - ps.length) * q)

/-- The array of `code A Y` on the codes of the pairs of `V₁' ⊔ V₂`. -/
def sqCodeArr (ps : List ℕ) (q : ℕ) (a : Array Bool) (Y : Array ℕ) : Array ℕ :=
  ((tupList 2 (ps.length + q)).map fun ds =>
    sqCodeEntry ps q a Y (ds.getD 0 0) (ds.getD 1 0)).toArray

/-- Distinct cells in the form `relOf_cell` uses. -/
theorem getD_inj_of_nodup {m : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup) :
    ∀ i < cs.length, ∀ j < cs.length,
      setOf m (cs.getD i []) = setOf m (cs.getD j []) → i = j := by
  intro i hi j hj h
  have hgi : cs.getD i [] = cs.get ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]
  have hgj : cs.getD j [] = cs.get ⟨j, hj⟩ := by simp [List.getD_eq_getElem?_getD, hj]
  rw [hgi, hgj] at h
  have := (cellSub_bijective hcs).1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h)
  exact congrArg Fin.val this

/-- Conversely, cells distinct in the form `relOf_cell` uses are duplicate-free as sets. -/
theorem nodup_of_getD_inj {m : ℕ} {cs : List (List ℕ)}
    (hcs : ∀ i < cs.length, ∀ j < cs.length,
      setOf m (cs.getD i []) = setOf m (cs.getD j []) → i = j) :
    (cs.map (setOf m)).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [List.get_eq_getElem, List.getElem_map, List.length_map] at h hi hj
  exact Fin.ext (hcs i hi j hj (by simpa [List.getD_eq_getElem?_getD, hi, hj] using h))

/-- **`sqCodeArr` is `code A Y`** on the numbered pairs, for the relation `relOf m cs a` and a
2-skeleton `Y` of the cells read from the array `Ydat` at `i + j · q`. -/
theorem toFun_sqCodeArr {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} (hps : ∀ i ∈ ps, i < m)
    (hcs : (cs.map (setOf m)).Nodup) (a : Array Bool) {Y : ↥(famOf m cs) → ↥(famOf m cs) → ℕ}
    {Ydat : Array ℕ}
    (hY : ∀ i j : Fin cs.length, Y (cellSub m cs i) (cellSub m cs j) = get Ydat (i + j * cs.length))
    (y : Tup 2 (ps.length + cs.length)) :
    toFun (sqCodeArr ps cs.length a Ydat) y =
      code (relOf m cs a) (extCells (famOf m cs) Y) (sqAt m ps cs hps (y 0)).val
        (sqAt m ps cs hps (y 1)).val := by
  have hinj := getD_inj_of_nodup hcs
  rw [toFun, sqCodeArr, get_tupMap]
  have h0 : (digits y).getD 0 0 = (y 0 : ℕ) := by simp [digits]
  have h1 : (digits y).getD 1 0 = (y 1 : ℕ) := by simp [digits]
  rw [h0, h1, sqCodeEntry]
  -- the relation on a listed cell
  have hrel : ∀ (x : Fin m) (j : ℕ) (hj : j < cs.length),
      relOf m cs a x (setOf m (cs.get ⟨j, hj⟩)) = getB a (x.val * cs.length + j) := by
    intro x j hj
    rw [show cs.get ⟨j, hj⟩ = cs.getD j [] by simp [List.getD_eq_getElem?_getD, hj]]
    rw [relOf_cell hinj hj x]
    rfl
  by_cases hi : (y 0 : ℕ) < ps.length <;> by_cases hj : (y 1 : ℕ) < ps.length
  · simp only [hi, hj, ↓reduceIte]
    rw [sqAt_lt hi, sqAt_lt hj]
    rfl
  · simp only [hi, hj, ↓reduceIte]
    rw [sqAt_lt hi, sqAt_ge (by omega)]
    simp only [code]
    rw [hrel _ _ (by omega)]
    simp [List.getD_eq_getElem?_getD, hi]
  · simp only [hi, hj, ↓reduceIte]
    rw [sqAt_ge (by omega), sqAt_lt hj]
    simp only [code]
    rw [hrel _ _ (by omega)]
    simp [List.getD_eq_getElem?_getD, hj]
  · simp only [hi, hj, ↓reduceIte]
    rw [sqAt_ge (by omega), sqAt_ge (by omega)]
    simp only [code, extCells]
    have hm : setOf m (cs.get ⟨(y 0 : ℕ) - ps.length, by omega⟩) ∈ famOf m cs ∧
        setOf m (cs.get ⟨(y 1 : ℕ) - ps.length, by omega⟩) ∈ famOf m cs :=
      ⟨mem_famOf.2 ⟨_, List.get_mem _ _, rfl⟩, mem_famOf.2 ⟨_, List.get_mem _ _, rfl⟩⟩
    rw [dite_eq_left_of_eq_true (eq_true hm)]
    have := hY ⟨(y 0 : ℕ) - ps.length, by omega⟩ ⟨(y 1 : ℕ) - ps.length, by omega⟩
    rw [← this]
    rfl

/-! ### The program for `code A Y` and the classical refinement -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The entry of `code A Y` at the pair of digits `ds = [i, j]`, with `rowA[i] = ps[i] · q` and
`colA[j'] = j' · q`. -/
def sqCodeEntryProg (p : var .nat) (rowA colA : var (.array .nat)) (a : var (.array .bool))
    (Y : var (.array .nat)) (ds : var (.list .nat)) : Prog S rec var .nat :=
  .caseList ds (.op0 (.natLit 0)) fun i rest =>
  .caseList rest (.op0 (.natLit 0)) fun j _ =>
  .bind (.op2 .natLt i p) fun ip => .bind (.op2 .natLt j p) fun jp =>
  .ite ip
    (.ite jp (.op0 (.natLit 0))
      (.bind (.op2 .arrayGet rowA i) fun r => .bind (.op2 .sub j p) fun j' =>
       .bind (.op2 .add r j') fun idx => .bind (.op2 .arrayGet a idx) fun b =>
       .ite b (.op0 (.natLit 1)) (.op0 (.natLit 2))))
    (.ite jp
      (.bind (.op2 .arrayGet rowA j) fun r => .bind (.op2 .sub i p) fun i' =>
       .bind (.op2 .add r i') fun idx => .bind (.op2 .arrayGet a idx) fun b =>
       .ite b (.op0 (.natLit 3)) (.op0 (.natLit 4)))
      (.bind (.op2 .sub i p) fun i' => .bind (.op2 .sub j p) fun j' =>
       .bind (.op2 .arrayGet colA j') fun c => .bind (.op2 .add i' c) fun idx =>
       .bind (.op2 .arrayGet Y idx) fun yv => .bind (.op0 (.natLit 5)) fun five =>
       .op2 .add five yv))

/-- **The array of `code A Y`** on the codes of the pairs of `V₁' ⊔ V₂` (points `ps`, `q` cells,
relation array `a`, 2-skeleton array `Y` of the cells). -/
def sqCodeArrProg (ps : var (.list .nat)) (q : var .nat) (a : var (.array .bool))
    (Y : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .length ps) fun p => .bind (.op2 .add p q) fun N =>
  .bind (mapList ps fun x => Coherent.mulNProg x q) fun rows =>
  .bind (.op1 .arrayOfList rows) fun rowA =>
  .bind (.op1 .range q) fun rq => .bind (mapList rq fun j => Coherent.mulNProg j q) fun cols =>
  .bind (.op1 .arrayOfList cols) fun colA =>
  .bind (.op0 (.natLit 2)) fun two => .bind (Coherent.tupsProg two N) fun tups =>
  .bind (mapList tups fun ds => sqCodeEntryProg p rowA colA a Y ds) fun es => .op1 .arrayOfList es

/-- **The classical refinement on points and cells**: `sqCodeArrProg`, then `wlProg 2`. -/
def cohProg (ps : var (.list .nat)) (q : var .nat) (a : var (.array .bool))
    (Y : var (.array .nat)) : Prog S rec var (.prod (.array .nat) (.list .nat)) :=
  .bind (sqCodeArrProg ps q a Y) fun col => .bind (.op1 .length ps) fun p =>
  .bind (.op2 .add p q) fun N => .bind (.op0 (.natLit 2)) fun two => Coherent.wlProg two N col

end Prog

/-- The cost of `sqCodeArrProg` for `p` points of degree at most `m` and `q` cells. -/
def sqCodeArrCost (m p q : ℕ) : ℕ :=
  p * (3 * m + 5) + q * (3 * q + 5) + (p + q) ^ 2 * 25 + Coherent.tupsCost 2 (p + q) + 3 * q +
    2 * p + 30

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- A Boolean choice between two literals. -/
theorem cond_lit (c : Bool) (x y : ℕ) :
    RunsWithin X body (cond c (Prog.op0 (Prim.natLit x)) (Prog.op0 (Prim.natLit y)))
      (if c = true then x else y) 1 := by
  cases c <;> exact RunsWithin.prim_le rfl (by simp [Prim.cost])

theorem sqCodeEntryProg_spec {ps : List ℕ} {q : ℕ} {rowA colA : Array ℕ} {a' : Array Bool}
    {Y : Array ℕ} (hrow : ∀ i < ps.length, get rowA i = ps.getD i 0 * q)
    (hcol : ∀ j < q, get colA j = j * q) {i j : ℕ} (hj : j < ps.length + q) :
    RunsWithin X body (sqCodeEntryProg ps.length rowA colA a' Y [i, j])
      (sqCodeEntry ps q a' Y i j) 20 := by
  unfold sqCodeEntryProg
  by_cases hi' : i < ps.length <;> by_cases hj' : j < ps.length
  · apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseList_cons _
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, hi', hj', decide_true, Bool.cond_true]
      run_with RunsWithin.ite _
      simp only [Bool.cond_true]
      refine RunsWithin.prim_le ?_ le_rfl
      simp [Prim.eval, sqCodeEntry, hi', hj']
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseList_cons _
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, hi', hj', decide_true, decide_false, Bool.cond_true]
      run_with RunsWithin.ite _
      simp only [Bool.cond_false]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, Ty.default]
      have hr := hrow i hi'
      simp only [get] at hr
      rw [hr]
      simp only [sqCodeEntry, hi', hj', ↓reduceIte, getB]
      exact cond_lit _ _ _
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseList_cons _
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, hi', hj', decide_true, decide_false, Bool.cond_false]
      run_with RunsWithin.ite _
      simp only [Bool.cond_true]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, Ty.default]
      have hr := hrow j hj'
      simp only [get] at hr
      rw [hr]
      simp only [sqCodeEntry, hi', hj', ↓reduceIte, getB]
      exact cond_lit _ _ _
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseList_cons _
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, hi', hj', decide_false, Bool.cond_false]
      run_with RunsWithin.ite _
      simp only [Bool.cond_false]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      have hc := hcol (j - ps.length) (by omega)
      simp only [get] at hc
      refine RunsWithin.prim_le ?_ le_rfl
      simp [Prim.eval, sqCodeEntry, hi', hj', get, Ty.default, ← hc]
    case hc => simp [Prim.cost]

/-- The digit lists of the pairs: two digits below `N`. -/
theorem mem_tupList_two {N : ℕ} {ds : List ℕ} (hds : ds ∈ tupList 2 N) :
    ds = [ds.getD 0 0, ds.getD 1 0] ∧ ds.getD 0 0 < N ∧ ds.getD 1 0 < N := by
  rw [tupList_eq] at hds
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hds
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h] at ht
    · exact h
  simp [digitsOf, List.ofFn_succ, Nat.mod_lt _ hN]

theorem get_map_mul_toArray (l : List ℕ) (q : ℕ) {i : ℕ} (hi : i < l.length) :
    get (l.map (· * q)).toArray i = l.getD i 0 * q := by
  simp [get, Array.getD_eq_getD_getElem?, hi, List.getD_eq_getElem?_getD]

/-- **The array of `code A Y`**. -/
theorem RunsWithin.sqCodeArrProg {m : ℕ} (ps : List ℕ) (hps : ∀ i ∈ ps, i < m) (q : ℕ)
    (a' : Array Bool) (Y : Array ℕ) :
    RunsWithin X body (SoJProg.sqCodeArrProg ps q a' Y) (sqCodeArr ps q a' Y)
      (sqCodeArrCost m ps.length q) := by
  have hrows := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := ps) (f := fun x => Coherent.mulNProg x q) (F := (· * q)) (c := 3 * m + 2)
    fun x hx => (RunsWithin.mulNProg x q).mono (by have := hps x hx; omega)
  have hcols := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := List.range q) (f := fun j => Coherent.mulNProg j q) (F := (· * q)) (c := 3 * q + 2)
    fun j hj => (RunsWithin.mulNProg j q).mono (by have := List.mem_range.1 hj; omega)
  have hrow : ∀ i < ps.length, get (ps.map (· * q)).toArray i = ps.getD i 0 * q :=
    fun i hi => get_map_mul_toArray ps q hi
  have hcol : ∀ j < q, get ((List.range q).map (· * q)).toArray j = j * q := by
    intro j hj
    rw [get_map_mul_toArray _ q (by simpa using hj)]
    simp [List.getD_eq_getElem?_getD, hj]
  have hent := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := .nat)
    (xs := tupList 2 (ps.length + q))
    (f := fun ds => sqCodeEntryProg ps.length (ps.map (· * q)).toArray
      ((List.range q).map (· * q)).toArray a' Y ds)
    (F := fun ds => sqCodeEntry ps q a' Y (ds.getD 0 0) (ds.getD 1 0)) (c := 20) fun ds hds => by
      obtain ⟨hds', -, h1⟩ := mem_tupList_two hds
      rw [hds']
      exact sqCodeEntryProg_spec hrow hcol h1
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.sqCodeArrProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hrows
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hcols
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.tupsProg 2 (ps.length + q))
    run_step hent
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map, List.length_range, length_tupList,
      sqCodeArrCost]
    nlinarith

/-- **The classical refinement on points and cells**, as an array on the codes of the pairs. -/
theorem RunsWithin.cohProg {m : ℕ} (ps : List ℕ) (hps : ∀ i ∈ ps, i < m) (q : ℕ)
    (a' : Array Bool) (Y : Array ℕ) :
    RunsWithin X body (SoJProg.cohProg ps q a' Y) (wlA 2 (ps.length + q) (sqCodeArr ps q a' Y))
      (sqCodeArrCost m ps.length q + wlCost 2 (ps.length + q) + ps.length + 3) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.cohProg
    run_step (RunsWithin.sqCodeArrProg ps hps q a' Y)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact Coherent.RunsWithin.wlProg 2 (ps.length + q) _
  case hc => simp only [Prim.cost, Args.head]; omega

end Specs

/-- **What `cohProg` computes**: on the points `ps` and the duplicate-free cells `cs`, with the
relation array `a` and the 2-skeleton `Y` of the cells given by `Ydat`, the refined array at the
code of a pair `(i, j)` of indices is `cohOn SQ (code A Y)` at the numbered vertices. -/
theorem cohOn_code_eq {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} (hps : ∀ i ∈ ps, i < m)
    (hpn : ps.Nodup) (hcs : (cs.map (setOf m)).Nodup) (a : Array Bool)
    {Y : ↥(famOf m cs) → ↥(famOf m cs) → ℕ} {Ydat : Array ℕ}
    (hY : ∀ i j : Fin cs.length, Y (cellSub m cs i) (cellSub m cs j) = get Ydat (i + j * cs.length))
    (i j : Fin (ps.length + cs.length)) :
    cohOn (sqSet m ps cs) (code (relOf m cs a) (extCells (famOf m cs) Y))
        (sqAt m ps cs hps i).val (sqAt m ps cs hps j).val =
      get (wlA 2 (ps.length + cs.length) (sqCodeArr ps cs.length a Ydat)).1 (enc ![i, j]) :=
  cohOn_eq_wlA hps hpn hcs _ (toFun_sqCodeArr hps hcs a hY) i j

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_sqCodeEntryProg {p₁ : var₁ .nat} {p₂ : var₂ .nat} {rowA₁ colA₁ : var₁ (.array .nat)}
    {rowA₂ colA₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    {Y₁ : var₁ (.array .nat)} {Y₂ : var₂ (.array .nat)} {ds₁ : var₁ (.list .nat)}
    {ds₂ : var₂ (.list .nat)} (hp : ⟨.nat, p₁, p₂⟩ ∈ Γ)
    (hrow : ⟨.array .nat, rowA₁, rowA₂⟩ ∈ Γ) (hcol : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hY : ⟨.array .nat, Y₁, Y₂⟩ ∈ Γ)
    (hds : ⟨.list .nat, ds₁, ds₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sqCodeEntryProg p₁ rowA₁ colA₁ a₁ Y₁ ds₁)
      (sqCodeEntryProg p₂ rowA₂ colA₂ a₂ Y₂ ds₂) := by
  unfold sqCodeEntryProg
  prog_wf

theorem wf_sqCodeArrProg {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} {q₁ : var₁ .nat}
    {q₂ : var₂ .nat} {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    {Y₁ : var₁ (.array .nat)} {Y₂ : var₂ (.array .nat)} (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ)
    (hq : ⟨.nat, q₁, q₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hY : ⟨.array .nat, Y₁, Y₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sqCodeArrProg ps₁ q₁ a₁ Y₁)
      (sqCodeArrProg ps₂ q₂ a₂ Y₂) := by
  have hm : ∀ Γ₀ : WfCtx var₁ var₂, ⟨.nat, q₁, q₂⟩ ∈ Γ₀ →
      WfFun r Γ₀ (fun x => Coherent.mulNProg (S := S) (rec := rec) x q₁)
        (fun x => Coherent.mulNProg x q₂) := by
    intro Γ₀ hq₀ Γ' hΓ x₁ x₂ hx
    have hq' := hΓ hq₀
    unfold Coherent.mulNProg
    prog_wf
  unfold sqCodeArrProg
  exact .bind (.prim _ (.cons hps .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp [hq]) .nil))) fun _ _ =>
    .bind (wf_mapList (by simp [hps]) (hm _ (by simp [hq]))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hq]) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) (hm _ (by simp [hq]))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (Coherent.wf_tupsProg (by simp) (by simp)) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ hΓ _ _ hds => wf_sqCodeEntryProg (hΓ (by simp))
      (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp [ha])) (hΓ (by simp [hY])) hds) fun _ _ =>
    .prim _ (.cons (by simp) .nil)

theorem wf_cohProg {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} {q₁ : var₁ .nat}
    {q₂ : var₂ .nat} {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    {Y₁ : var₁ (.array .nat)} {Y₂ : var₂ (.array .nat)} (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ)
    (hq : ⟨.nat, q₁, q₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hY : ⟨.array .nat, Y₁, Y₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cohProg ps₁ q₁ a₁ Y₁) (cohProg ps₂ q₂ a₂ Y₂) := by
  unfold cohProg
  exact .bind (wf_sqCodeArrProg hps hq ha hY) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hps]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp [hq]) .nil))) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => Coherent.wf_wlProg (by simp) (by simp) (by simp)

end Wf

end GraphIso.SoJProg
