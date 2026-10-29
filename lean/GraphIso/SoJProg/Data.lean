module

public import GraphIso.SplitJohnson.MainDef
public import GraphIso.Representation.Permutation

/-!
# Split-or-Johnson on data

The data representation of milestone 11's model for the programs of stages 14c–14d
(`PLAN-14.md` §7). The points are `Fin m`.

* A set of points is a list of indices (`setOf`); a family of cells is a list of such lists
  (`famOf`).
* A colouring of pairs is an `m × m` array, row-major (`colOf`).
* A bipartite relation between points and the cells of a list `cs` is a Boolean array indexed
  by `x * |cs| + j` for the `j`-th cell (`relOf`); a cell outside the list is unrelated.

The decoding lemmas: membership (`mem_setOf`, `mem_famOf`), cardinalities (`card_setOf`,
`card_famOf`), and the relation on listed cells (`relOf_cell`).
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso

/-- The set of points listed by `l`. -/
def setOf (m : ℕ) (l : List ℕ) : Finset (Fin m) := univ.filter fun i => i.val ∈ l

/-- The family of cells listed by `ls`. -/
def famOf (m : ℕ) (ls : List (List ℕ)) : Finset (Finset (Fin m)) := (ls.map (setOf m)).toFinset

/-- The colouring of pairs given by an `m × m` array, row-major. -/
def colOf (m : ℕ) (c : Array ℕ) (u v : Fin m) : ℕ := get c (u.val * m + v.val)

/-- The relation between points and the cells of `cs` given by a Boolean array indexed by
`x * |cs| + j`; a set that is not one of the listed cells is unrelated. -/
def relOf (m : ℕ) (cs : List (List ℕ)) (a : Array Bool) (x : Fin m) (s : Finset (Fin m)) :
    Bool :=
  match (List.range cs.length).find? fun j => setOf m (cs.getD j []) = s with
  | some j => a.getD (x.val * cs.length + j) false
  | none => false

theorem mem_setOf {m : ℕ} {l : List ℕ} {i : Fin m} : i ∈ setOf m l ↔ i.val ∈ l := by
  simp [setOf]

theorem mem_famOf {m : ℕ} {ls : List (List ℕ)} {s : Finset (Fin m)} :
    s ∈ famOf m ls ↔ ∃ l ∈ ls, setOf m l = s := by
  simp [famOf]

/-- On the `j`-th listed cell, when the cells are distinct as sets, the relation reads the
array. -/
theorem relOf_cell {m : ℕ} {cs : List (List ℕ)} {a : Array Bool}
    (hcs : ∀ i < cs.length, ∀ j < cs.length,
      setOf m (cs.getD i []) = setOf m (cs.getD j []) → i = j)
    {j : ℕ} (hj : j < cs.length) (x : Fin m) :
    relOf m cs a x (setOf m (cs.getD j [])) = a.getD (x.val * cs.length + j) false := by
  have hfind : (List.range cs.length).find? (fun i =>
      decide (setOf m (cs.getD i []) = setOf m (cs.getD j []))) = some j := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp, j, by simpa using hj, by simp, ?_⟩
    intro i hi
    simp only [List.getElem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    intro h
    have := hcs i (by omega) j hj h
    omega
  unfold relOf
  rw [hfind]

/-- `setOf` of a list of indices below `m` is the image of the list. -/
theorem setOf_eq_pmap {m : ℕ} {l : List ℕ} (hlt : ∀ i ∈ l, i < m) :
    setOf m l = (l.pmap (fun i h => (⟨i, h⟩ : Fin m)) hlt).toFinset := by
  ext x
  rw [mem_setOf, List.mem_toFinset, List.mem_pmap]
  constructor
  · intro h
    exact ⟨x.val, h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ha

/-- A duplicate-free list of indices below `m` lists a set of its length. -/
theorem card_setOf {m : ℕ} {l : List ℕ} (hl : l.Nodup) (hlt : ∀ i ∈ l, i < m) :
    (setOf m l).card = l.length := by
  rw [setOf_eq_pmap hlt, List.toFinset_card_of_nodup, List.length_pmap]
  exact hl.pmap fun a _ b _ h => by simpa using congrArg Fin.val h

/-- Cells that are distinct as sets list a family of their number. -/
theorem card_famOf {m : ℕ} {cs : List (List ℕ)}
    (hcs : ∀ i < cs.length, ∀ j < cs.length,
      setOf m (cs.getD i []) = setOf m (cs.getD j []) → i = j) :
    (famOf m cs).card = cs.length := by
  unfold famOf
  rw [List.toFinset_card_of_nodup, List.length_map]
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  simp only [List.get_eq_getElem, List.getElem_map, List.length_map] at h hi hj
  have := hcs i hi j hj (by simpa [List.getD_eq_getElem?_getD, hi, hj] using h)
  exact Fin.ext this

end GraphIso.SoJProg
