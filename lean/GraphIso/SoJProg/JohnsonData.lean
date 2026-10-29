module

public import GraphIso.SoJProg.TwinsData

/-!
# The Johnson test on data: the models

The data models of step 2 of milestone 11's `bstep` (`PLAN-14.md` §7 item 3) and their
decoding: the neighbourhoods `nbr` (`nbrD`), their complements `fOf` (`fOfD`), the binomial
coefficient by Pascal's rule (`pascalRow`, `pascalRow_getD`), the Johnson test, and the leaf
`⟨V₁', V₂, s, fOf V₂ A d₁⟩` (`jembOf`, `johnson_decode`). Families of cells are lists of cell
indices, decoded by `famIdx`.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.SplitJohnson GraphIso.Coherent

/-- The family of the cells with the listed indices. -/
def famIdx (m : ℕ) (cs : List (List ℕ)) (js : List ℕ) : Finset (Finset (Fin m)) :=
  (js.map (cellAt m cs)).toFinset

/-- The cells related to `x`, as indices. -/
def nbrD (k : ℕ) (a : Array Bool) (x : ℕ) : List ℕ := (List.range k).filter (relAt k a x)

/-- The neighbourhood of `x` after complementing (if `2 d₁ > k`). -/
def fOfD (k : ℕ) (a : Array Bool) (d₁ x : ℕ) : List ℕ :=
  if k < 2 * d₁ then (List.range k).filter (fun j => !relAt k a x j) else nbrD k a x

/-- Row `n` of Pascal's triangle. -/
def pascalRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => List.zipWith (· + ·) (0 :: pascalRow n) (pascalRow n ++ [0])

/-- The neighbourhoods after complementing, at the points `0, …, m - 1`. -/
def fArrD (m k : ℕ) (a : Array Bool) (d₁ : ℕ) : Array (List ℕ) :=
  ((List.range m).map (fOfD k a d₁)).toArray

/-- A Johnson embedding from data: the points `V0`, the cells `cs`, the parameter `s`, and for
every point the indices of its `s` cells. -/
def jembOf (m : ℕ) (V0 : List ℕ) (cs : List (List ℕ)) (s : ℕ) (fA : Array (List ℕ)) :
    JEmb (Fin m) :=
  ⟨setOf m V0, famOf m cs, s, fun x => famIdx m cs (fA.getD x.val [])⟩

theorem length_pascalRow (n : ℕ) : (pascalRow n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pascalRow, ih]

theorem getD_append_zero (l : List ℕ) (s : ℕ) : (l ++ [0]).getD s 0 = l.getD s 0 := by
  rcases Nat.lt_or_ge s l.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_default _ _ h]
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · subst h'
      simp
    · exact List.getD_eq_default _ _ (by simp; omega)

theorem getD_zipWith_add : ∀ (l₁ l₂ : List ℕ), l₁.length = l₂.length → ∀ s,
    (List.zipWith (· + ·) l₁ l₂).getD s 0 = l₁.getD s 0 + l₂.getD s 0
  | [], [], _, s => by simp
  | x :: l₁, y :: l₂, h, s => by
    cases s with
    | zero => simp
    | succ s =>
      simp only [List.zipWith_cons_cons, List.getD_cons_succ]
      exact getD_zipWith_add l₁ l₂ (by simpa using h) s

/-- **Pascal's rule**: row `n` lists the binomial coefficients `C(n, s)`. -/
theorem pascalRow_getD (n s : ℕ) : (pascalRow n).getD s 0 = n.choose s := by
  induction n generalizing s with
  | zero => cases s <;> simp [pascalRow]
  | succ n ih =>
    rw [pascalRow, getD_zipWith_add _ _ (by simp [length_pascalRow]), getD_append_zero, ih]
    cases s with
    | zero => simp
    | succ s => rw [List.getD_cons_succ, ih, Nat.choose_succ_succ]

section Decode

variable {m : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a : Array Bool}

theorem mem_famIdx {js : List ℕ} {s : Finset (Fin m)} :
    s ∈ famIdx m cs js ↔ ∃ j ∈ js, cellAt m cs j = s := by
  simp [famIdx]

theorem nbr_decode (hcs : CellsDistinct m cs) (x : Fin m) :
    nbr (famOf m cs) (relOf m cs a) x = famIdx m cs (nbrD cs.length a x.val) := by
  ext s
  rw [nbr, Finset.mem_filter, famOf_eq_image, Finset.mem_image, mem_famIdx]
  simp only [Finset.mem_range, nbrD, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hr⟩
    exact ⟨j, ⟨hj, by rwa [relOf_eq_relAt hcs hj] at hr⟩, rfl⟩
  · rintro ⟨j, ⟨hj, hr⟩, rfl⟩
    exact ⟨⟨j, hj, rfl⟩, by rwa [relOf_eq_relAt hcs hj]⟩

theorem fOf_decode (hcs : CellsDistinct m cs) (d₁ : ℕ) (x : Fin m) :
    fOf (famOf m cs) (relOf m cs a) d₁ x = famIdx m cs (fOfD cs.length a d₁ x.val) := by
  rw [fOf, fOfD, card_famOf hcs]
  split_ifs
  · ext s
    rw [Finset.mem_sdiff, nbr_decode hcs, famOf_eq_image, Finset.mem_image, mem_famIdx,
      mem_famIdx]
    simp only [Finset.mem_range, nbrD, List.mem_filter, List.mem_range, Bool.not_eq_true']
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hn⟩
      refine ⟨j, ⟨hj, ?_⟩, rfl⟩
      cases h : relAt cs.length a x.val j
      · rfl
      · exact absurd ⟨j, ⟨hj, h⟩, rfl⟩ hn
    · rintro ⟨j, ⟨hj, hr⟩, rfl⟩
      refine ⟨⟨j, hj, rfl⟩, ?_⟩
      rintro ⟨j', ⟨hj', hr'⟩, he⟩
      have := hcs j' hj' j hj he
      subst this
      rw [hr] at hr'
      exact Bool.false_ne_true hr'
  · exact nbr_decode hcs x

/-- **The Johnson leaf decoded.** -/
theorem johnson_decode (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m) (hcs : CellsDistinct m cs)
    (d₁ : ℕ) :
    jembOf m (tfDegD V₁ cs.length a d₁) cs (sOf cs.length d₁) (fArrD m cs.length a d₁) =
      ⟨tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d₁, famOf m cs,
        sOf (famOf m cs).card d₁, fOf (famOf m cs) (relOf m cs a) d₁⟩ := by
  rw [jembOf, card_famOf hcs, tfDeg_decode hV₁ hV₁m hcs]
  congr 1
  funext x
  rw [fOf_decode hcs, fArrD, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_range x.2]
  rfl

/-- **The Johnson test decoded.** -/
theorem johnsonTest_decode (hV₁ : V₁.Nodup) (hV₁m : ∀ x ∈ V₁, x < m)
    (hcs : CellsDistinct m cs) (d₁ : ℕ) :
    ((tfDegD V₁ cs.length a d₁).length == cs.length.choose (sOf cs.length d₁)) =
      decide ((tfDeg (setOf m V₁) (famOf m cs) (relOf m cs a) d₁).card =
        (famOf m cs).card.choose (sOf (famOf m cs).card d₁)) := by
  rw [card_tfDeg hV₁ hV₁m hcs, card_famOf hcs]
  cases h : (tfDegD V₁ cs.length a d₁).length == cs.length.choose (sOf cs.length d₁) <;>
    simp_all

end Decode

end GraphIso.SoJProg
