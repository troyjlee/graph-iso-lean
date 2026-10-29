module

public import GraphIso.SoJProg.JohnsonData
public import Mathlib.Data.List.Permutation
public import Mathlib.Data.Fintype.List

/-!
# The base case on data: the models

The data models of step 0 of milestone 11's `bstep` (`PLAN-14.md` §7 item 4) and their
decoding. A choice of the base case is an enumeration of the cells; on data it is a list of
cell indices (`choiceOf`).

* `enums_decode`: the permutations of the cell indices (mathlib's `List.permutations'`, which
  the program computes by insertion) decode to `enums`.
* `nbrCodeD`, `nbrCode_decode`: the code of a point along an enumeration.
* `colBlkD`, `colPart_decode`: the blocks of `colPart` for a colour array; `baseLeaf_decode`:
  the leaf of the base case.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.SplitJohnson GraphIso.Coherent

/-- The choice listing the cells with the given indices. -/
def choiceOf (m : ℕ) (cs : List (List ℕ)) (js : List ℕ) : Choice (Fin m) :=
  js.map fun j => (Sum.inr (cellAt m cs j) : Fin m ⊕ Finset (Fin m))

/-- The code of `x` along the enumeration `js` of cell indices. -/
def nbrCodeD (k : ℕ) (a : Array Bool) (js : List ℕ) (x : ℕ) : ℕ :=
  Nat.ofDigits 2 (js.map fun j => if relAt k a x j then 1 else 0)

/-- The blocks of `colPart S col` at the points `0, …, m - 1`. -/
def colBlkD (m : ℕ) (S : List ℕ) (col : Array ℕ) : Array (List ℕ) :=
  ((List.range m).map fun x => S.filter fun y => get col y == get col x).toArray

/-- The codes of the points `0, …, m - 1` along `js`. -/
def nbrCodeArrD (m k : ℕ) (a : Array Bool) (js : List ℕ) : Array ℕ :=
  ((List.range m).map (nbrCodeD k a js)).toArray

section Decode

variable {m : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a : Array Bool}

/-- The index of a cell of the family. -/
def cellIdx (m : ℕ) (cs : List (List ℕ)) (s : Finset (Fin m)) : ℕ :=
  ((List.range cs.length).find? fun j => decide (cellAt m cs j = s)).getD 0

theorem cellIdx_cellAt (hcs : CellsDistinct m cs) {j : ℕ} (hj : j < cs.length) :
    cellIdx m cs (cellAt m cs j) = j := by
  have hfind : (List.range cs.length).find? (fun i =>
      decide (cellAt m cs i = cellAt m cs j)) = some j := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, j, by simpa using hj, by simp, ?_⟩
    intro i hi
    simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    intro h
    have := hcs i (by omega) j hj h
    omega
  rw [cellIdx, hfind]
  rfl

theorem choiceCells_choiceOf (js : List ℕ) :
    choiceCells (choiceOf m cs js) = js.map (cellAt m cs) := by
  unfold choiceCells choiceOf
  rw [List.filterMap_map]
  induction js with
  | nil => rfl
  | cons j js ih => simp [ih]

/-- Membership in `enums`. -/
theorem mem_enums {α : Type*} [DecidableEq α] {V₂ : Finset (Finset α)} {c : Choice α} :
    c ∈ enums V₂ ↔
      ∃ l : List (Finset α), V₂.val = (l : Multiset _) ∧ (l.map Sum.inr : Choice α) = c := by
  unfold enums
  constructor
  · intro h
    obtain ⟨l, hl, hc⟩ := Finset.mem_image.1 h
    rw [Multiset.mem_toFinset, Multiset.mem_lists_iff] at hl
    exact ⟨l, hl, hc⟩
  · rintro ⟨l, hl, hc⟩
    refine Finset.mem_image.2 ⟨l, ?_, hc⟩
    rw [Multiset.mem_toFinset, Multiset.mem_lists_iff]
    exact hl

/-- **The enumerations decoded**: the permutations of the cell indices give exactly the
choices of the base case. -/
theorem enums_decode (hcs : CellsDistinct m cs) :
    ((List.range cs.length).permutations'.map (choiceOf m cs)).toFinset =
      enums (famOf m cs) := by
  have hval : (famOf m cs).val = (((List.range cs.length).map (cellAt m cs) :
      List (Finset (Fin m))) : Multiset (Finset (Fin m))) := by
    have hnd : ((List.range cs.length).map (cellAt m cs)).Nodup := by
      refine (List.nodup_range).map_on fun i hi j hj h => ?_
      exact hcs i (List.mem_range.1 hi) j (List.mem_range.1 hj) h
    have e : famOf m cs = ((List.range cs.length).map (cellAt m cs)).toFinset := by
      ext s
      rw [famOf_eq_image, List.mem_toFinset]
      simp
    rw [e, List.toFinset_val, hnd.dedup]
  ext c
  rw [List.mem_toFinset, mem_enums, List.mem_map]
  simp only [List.mem_permutations', hval, Multiset.coe_eq_coe]
  constructor
  · rintro ⟨js, hjs, rfl⟩
    refine ⟨js.map (cellAt m cs), (hjs.map _).symm, ?_⟩
    simp [choiceOf]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.map (cellIdx m cs), ?_, ?_⟩
    · have h := (hl.symm).map (cellIdx m cs)
      rw [List.map_map] at h
      refine h.trans (List.Perm.of_eq ?_)
      conv_rhs => rw [← List.map_id (List.range cs.length)]
      refine List.map_congr_left fun j hj => ?_
      exact cellIdx_cellAt hcs (List.mem_range.1 hj)
    · have hmem : ∀ s ∈ l, cellAt m cs (cellIdx m cs s) = s := by
        intro s hs
        have := hl.symm.subset hs
        obtain ⟨j, hj, rfl⟩ := List.mem_map.1 this
        rw [cellIdx_cellAt hcs (List.mem_range.1 hj)]
      unfold choiceOf
      rw [List.map_map]
      exact List.map_congr_left fun s hs => by simp [hmem s hs]

/-- **The code decoded.** -/
theorem nbrCode_decode (hcs : CellsDistinct m cs) {js : List ℕ}
    (hjs : ∀ j ∈ js, j < cs.length) (x : Fin m) :
    nbrCode (relOf m cs a) (choiceCells (choiceOf m cs js)) x = nbrCodeD cs.length a js x.val := by
  rw [choiceCells_choiceOf, nbrCode, nbrCodeD, List.map_map]
  congr 1
  refine List.map_congr_left fun j hj => ?_
  simp only [Function.comp_apply]
  rw [relOf_eq_relAt hcs (hjs j hj)]

/-- **`colPart` decoded.** -/
theorem colPart_decode (col : Array ℕ) :
    cpartOf m col (colBlkD m V₁ col) = colPart (setOf m V₁) (fun x => get col x.val) := by
  unfold cpartOf colPart
  congr 1
  funext x
  rw [colBlkD, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range x.2]
  ext y
  simp only [Option.map_some, Option.getD_some, mem_setOf, List.mem_filter, beq_iff_eq,
    Finset.mem_filter]

/-- **The leaf of the base case decoded.** -/
theorem baseLeaf_decode (hcs : CellsDistinct m cs) {js : List ℕ}
    (hjs : ∀ j ∈ js, j < cs.length) :
    cpartOf m (nbrCodeArrD m cs.length a js) (colBlkD m V₁ (nbrCodeArrD m cs.length a js)) =
      colPart (setOf m V₁) (nbrCode (relOf m cs a) (choiceCells (choiceOf m cs js))) := by
  rw [colPart_decode]
  congr 1
  funext x
  rw [nbrCode_decode hcs hjs, nbrCodeArrD, get, Array.getD_eq_getD_getElem?,
    List.getElem?_toArray, List.getElem?_map, List.getElem?_range x.2]
  rfl

end Decode

end GraphIso.SoJProg
