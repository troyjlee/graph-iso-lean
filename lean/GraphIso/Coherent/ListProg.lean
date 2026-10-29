module

public import GraphIso.Programs.List
public import GraphIso.Sims.SiftProg
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic.Linarith

/-!
# Comparing, sorting and ranking lists

Programs of the cost language for the lexicographic order, generic in the comparison of the
elements, with functional models matched to mathlib:

* `ord3 a b` encodes the comparison of `a` and `b` in a linear order (`0`: `a < b`, `1`: equal,
  `2`: `b < a`); `lexCmpProg cmp` compares lists lexicographically (`lexCmp_eq`: the encoding of
  mathlib's order on lists), at a cost linear in the length of the first list plus the costs of
  the element comparisons.
* `insertProg` inserts into a sorted list (`List.orderedInsert`), `sortProg` sorts
  (`List.insertionSort`), `dedupSortProg` sorts without repetitions (`Finset.sort` of the set of
  elements), `idxOfProg` finds the position of an element (`List.idxOf`).
* `cmpNatProg`, `cmpNProg` (lists of numbers) and `cmpLProg` (lists of lists of numbers) are the
  instances used by the Weisfeiler–Leman programs.
-/

@[expose] public section

namespace GraphIso.Coherent

open Cost Programs Sims

/-! ### Models -/

/-- The three-way comparison: `0` if `a < b`, `1` if `a = b`, `2` if `b < a`. -/
def ord3 {α : Type} [LinearOrder α] (a b : α) : ℕ := if a < b then 0 else if a = b then 1 else 2

/-- One step of the lexicographic comparison: while equal so far (status `1`), compare the next
element of the first list with the head of the rest of the second. -/
def lexStep {α : Type} (e : α → α → ℕ) (st : List α × ℕ) (x : α) : List α × ℕ :=
  if st.2 = 1 then
    match st.1 with
    | [] => ([], 2)
    | y :: ys => (ys, e x y)
  else st

/-- The lexicographic three-way comparison computed by `lexCmpProg`. -/
def lexCmp {α : Type} (e : α → α → ℕ) (a b : List α) : ℕ :=
  if (a.foldl (lexStep e) (b, 1)).2 = 1 then
    match (a.foldl (lexStep e) (b, 1)).1 with
    | [] => 1
    | _ :: _ => 0
  else (a.foldl (lexStep e) (b, 1)).2

theorem foldl_lexStep_ne {α : Type} (e : α → α → ℕ) {s : ℕ} (hs : s ≠ 1) :
    ∀ (l : List α) (bs : List α), l.foldl (lexStep e) (bs, s) = (bs, s)
  | [], _ => rfl
  | _ :: l, bs => by
    simp only [List.foldl_cons, lexStep, hs, ↓reduceIte]
    exact foldl_lexStep_ne e hs l bs

theorem ord3_lt {α : Type} [LinearOrder α] {a b : α} (h : a < b) : ord3 a b = 0 := by
  simp [ord3, h]

theorem ord3_self {α : Type} [LinearOrder α] (a : α) : ord3 a a = 1 := by
  simp [ord3]

theorem ord3_gt {α : Type} [LinearOrder α] {a b : α} (h : b < a) : ord3 a b = 2 := by
  simp [ord3, not_lt.2 h.le, h.ne']

theorem ord3_eq_one {α : Type} [LinearOrder α] {a b : α} : ord3 a b = 1 ↔ a = b := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [ord3_lt h, h.ne]
  · simp [ord3_self]
  · simp [ord3_gt h, h.ne']

theorem ord3_eq_two {α : Type} [LinearOrder α] {a b : α} : ord3 a b = 2 ↔ b < a := by
  rcases lt_trichotomy a b with h | rfl | h
  · simp [ord3_lt h, h.le.not_gt]
  · simp [ord3_self]
  · simp [ord3_gt h, h]

theorem ord3_cons_self {α : Type} [LinearOrder α] (x : α) (as ys : List α) :
    ord3 (x :: as) (x :: ys) = ord3 as ys := by
  rcases lt_trichotomy as ys with h | rfl | h
  · rw [ord3_lt h, ord3_lt (α := List α) (List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩))]
  · rw [ord3_self, ord3_self]
  · rw [ord3_gt h, ord3_gt (α := List α) (List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, h⟩))]

/-- **The lexicographic comparison encodes mathlib's order on lists.** -/
theorem lexCmp_eq {α : Type} [LinearOrder α] {e : α → α → ℕ} (he : ∀ x y, e x y = ord3 x y) :
    ∀ a b : List α, lexCmp e a b = ord3 a b
  | [], [] => by simp [lexCmp, ord3_self]
  | [], _ :: _ => by
    simp only [lexCmp, List.foldl_nil, ↓reduceIte]
    exact (ord3_lt (α := List α) (List.nil_lt_cons _ _)).symm
  | x :: as, [] => by
    have h2 : (2 : ℕ) ≠ 1 := by decide
    simp only [lexCmp, List.foldl_cons, lexStep, ↓reduceIte, foldl_lexStep_ne e h2]
    exact (ord3_gt (α := List α) (List.nil_lt_cons _ _)).symm
  | x :: as, y :: ys => by
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have h0 : e x y ≠ 1 := by rw [he, ord3_lt hxy]; decide
      simp only [lexCmp, List.foldl_cons, lexStep, ↓reduceIte, foldl_lexStep_ne e h0, h0]
      rw [he, ord3_lt hxy, ord3_lt (α := List α) (List.cons_lt_cons_iff.2 (Or.inl hxy))]
    · have ih := lexCmp_eq he as ys
      have h1 : e x x = 1 := by rw [he, ord3_self]
      simp only [lexCmp, List.foldl_cons, lexStep, ↓reduceIte, h1] at ih ⊢
      rw [ih, ord3_cons_self]
    · have h2 : e x y ≠ 1 := by rw [he, ord3_gt hxy]; decide
      simp only [lexCmp, List.foldl_cons, lexStep, ↓reduceIte, foldl_lexStep_ne e h2, h2]
      rw [he, ord3_gt hxy, ord3_gt (α := List α) (List.cons_lt_cons_iff.2 (Or.inl hxy))]

/-- One step of the ordered insertion of `a`: before the first `x` with `a ≤ x`. -/
def insStep {α : Type} (e : α → α → ℕ) (a : α) (st : List α × Bool) (x : α) : List α × Bool :=
  if st.2 then (x :: st.1, true)
  else if e a x = 2 then (x :: st.1, false) else (x :: a :: st.1, true)

/-- The ordered insertion computed by `insertProg`. -/
def insertM {α : Type} (e : α → α → ℕ) (a : α) (l : List α) : List α :=
  (if (l.foldl (insStep e a) ([], false)).2 then (l.foldl (insStep e a) ([], false)).1
    else a :: (l.foldl (insStep e a) ([], false)).1).reverse

theorem foldl_insStep_true {α : Type} (e : α → α → ℕ) (a : α) :
    ∀ (l acc : List α), l.foldl (insStep e a) (acc, true) = (l.reverse ++ acc, true)
  | [], _ => rfl
  | x :: l, acc => by
    simp only [List.foldl_cons, insStep, ↓reduceIte]
    rw [foldl_insStep_true e a l]
    simp

theorem foldl_insStep_false {α : Type} [LinearOrder α] {e : α → α → ℕ}
    (he : ∀ x y, e x y = ord3 x y) (a : α) :
    ∀ (l acc : List α),
      (if (l.foldl (insStep e a) (acc, false)).2 then (l.foldl (insStep e a) (acc, false)).1
        else a :: (l.foldl (insStep e a) (acc, false)).1).reverse =
        acc.reverse ++ l.orderedInsert (· ≤ ·) a
  | [], acc => by simp
  | x :: l, acc => by
    by_cases hax : a ≤ x
    · have hne : e a x ≠ 2 := by rw [he, ne_eq, ord3_eq_two, not_lt]; exact hax
      simp only [List.foldl_cons, insStep, Bool.false_eq_true, ↓reduceIte, hne,
        foldl_insStep_true, List.orderedInsert_cons, hax]
      simp
    · have h2 : e a x = 2 := by rw [he, ord3_eq_two]; exact not_le.1 hax
      simp only [List.foldl_cons, insStep, Bool.false_eq_true, ↓reduceIte, h2,
        List.orderedInsert_cons, hax]
      rw [foldl_insStep_false he a l (x :: acc)]
      simp

/-- **Ordered insertion.** -/
theorem insertM_eq {α : Type} [LinearOrder α] {e : α → α → ℕ} (he : ∀ x y, e x y = ord3 x y)
    (a : α) (l : List α) : insertM e a l = l.orderedInsert (· ≤ ·) a := by
  have := foldl_insStep_false he a l []
  simpa [insertM] using this

/-- The insertion sort computed by `sortProg`. -/
def sortM {α : Type} (e : α → α → ℕ) (l : List α) : List α :=
  l.reverse.foldl (fun acc x => insertM e x acc) []

theorem insertionSort_eq_foldr {α : Type} [LinearOrder α] :
    ∀ l : List α, l.insertionSort (· ≤ ·) = l.foldr (fun x acc => acc.orderedInsert (· ≤ ·) x) []
  | [] => by rw [List.insertionSort_nil, List.foldr_nil]
  | x :: l => by
    rw [List.insertionSort_cons, insertionSort_eq_foldr l, List.foldr_cons]

/-- **Insertion sort.** -/
theorem sortM_eq {α : Type} [LinearOrder α] {e : α → α → ℕ} (he : ∀ x y, e x y = ord3 x y)
    (l : List α) : sortM e l = l.insertionSort (· ≤ ·) := by
  rw [insertionSort_eq_foldr, sortM, List.foldl_reverse]
  congr 1
  funext x acc
  exact insertM_eq he x acc

/-- Insertion into a strictly increasing list, skipping an element already present. -/
def insertNewR {α : Type} [LinearOrder α] (a : α) : List α → List α
  | [] => [a]
  | x :: l => if a < x then a :: x :: l else if a = x then x :: l else x :: insertNewR a l

/-- One step of `insertNewProg`. -/
def insNewStep {α : Type} (e : α → α → ℕ) (a : α) (st : List α × Bool) (x : α) :
    List α × Bool :=
  if st.2 then (x :: st.1, true)
  else if e a x = 2 then (x :: st.1, false)
  else if e a x = 1 then (x :: st.1, true) else (x :: a :: st.1, true)

/-- The insertion without repetition computed by `insertNewProg`. -/
def insertNewM {α : Type} (e : α → α → ℕ) (a : α) (l : List α) : List α :=
  (if (l.foldl (insNewStep e a) ([], false)).2 then (l.foldl (insNewStep e a) ([], false)).1
    else a :: (l.foldl (insNewStep e a) ([], false)).1).reverse

theorem foldl_insNewStep_true {α : Type} (e : α → α → ℕ) (a : α) :
    ∀ (l acc : List α), l.foldl (insNewStep e a) (acc, true) = (l.reverse ++ acc, true)
  | [], _ => rfl
  | x :: l, acc => by
    simp only [List.foldl_cons, insNewStep, ↓reduceIte]
    rw [foldl_insNewStep_true e a l]
    simp

theorem foldl_insNewStep_false {α : Type} [LinearOrder α] {e : α → α → ℕ}
    (he : ∀ x y, e x y = ord3 x y) (a : α) :
    ∀ (l acc : List α),
      (if (l.foldl (insNewStep e a) (acc, false)).2 then (l.foldl (insNewStep e a) (acc, false)).1
        else a :: (l.foldl (insNewStep e a) (acc, false)).1).reverse =
        acc.reverse ++ insertNewR a l
  | [], acc => by simp [insertNewR]
  | x :: l, acc => by
    rcases lt_trichotomy a x with hax | rfl | hax
    · have h2 : e a x ≠ 2 := by rw [he, ord3_lt hax]; decide
      have h1 : e a x ≠ 1 := by rw [he, ord3_lt hax]; decide
      simp only [List.foldl_cons, insNewStep, Bool.false_eq_true, ↓reduceIte, h2, h1,
        foldl_insNewStep_true, insertNewR, hax]
      simp
    · have h2 : e a a ≠ 2 := by rw [he, ord3_self]; decide
      have h1 : e a a = 1 := by rw [he, ord3_self]
      have hs : insNewStep e a (acc, false) a = (a :: acc, true) := by
        simp [insNewStep, h1]
      simp only [List.foldl_cons, hs, foldl_insNewStep_true, insertNewR, lt_self_iff_false]
      simp
    · have h2 : e a x = 2 := by rw [he, ord3_gt hax]
      simp only [List.foldl_cons, insNewStep, Bool.false_eq_true, ↓reduceIte, h2, insertNewR,
        not_lt.2 hax.le, hax.ne']
      rw [foldl_insNewStep_false he a l (x :: acc)]
      simp

theorem insertNewM_eq {α : Type} [LinearOrder α] {e : α → α → ℕ} (he : ∀ x y, e x y = ord3 x y)
    (a : α) (l : List α) : insertNewM e a l = insertNewR a l := by
  have := foldl_insNewStep_false he a l []
  simpa [insertNewM] using this

theorem mem_insertNewR {α : Type} [LinearOrder α] (a : α) :
    ∀ (l : List α) (b : α), b ∈ insertNewR a l ↔ b = a ∨ b ∈ l
  | [], b => by simp [insertNewR]
  | x :: l, b => by
    unfold insertNewR
    split_ifs with h₁ h₂
    · simp
    · subst h₂
      simp only [List.mem_cons]
      tauto
    · simp only [List.mem_cons, mem_insertNewR a l b]
      tauto

theorem pairwise_insertNewR {α : Type} [LinearOrder α] (a : α) :
    ∀ l : List α, l.Pairwise (· < ·) → (insertNewR a l).Pairwise (· < ·)
  | [], _ => by simp [insertNewR]
  | x :: l, h => by
    unfold insertNewR
    split_ifs with h₁ h₂
    · refine List.Pairwise.cons (fun b hb => ?_) h
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h₁
      · exact h₁.trans (List.rel_of_pairwise_cons h hb)
    · exact h
    · have hx : ∀ b ∈ l, x < b := fun b hb => List.rel_of_pairwise_cons h hb
      refine List.Pairwise.cons (fun b hb => ?_) (pairwise_insertNewR a l h.of_cons)
      rcases (mem_insertNewR a l b).1 hb with rfl | hb
      · exact lt_of_le_of_ne (not_lt.1 h₁) (Ne.symm h₂)
      · exact hx _ hb

/-- The sorted list without repetitions computed by `dedupSortProg`. -/
def dedupSortM {α : Type} (e : α → α → ℕ) (l : List α) : List α :=
  l.foldl (fun acc x => insertNewM e x acc) []

theorem foldl_insertNewR {α : Type} [LinearOrder α] :
    ∀ (l acc : List α), acc.Pairwise (· < ·) →
      (l.foldl (fun acc x => insertNewR x acc) acc).Pairwise (· < ·) ∧
        ∀ b, b ∈ l.foldl (fun acc x => insertNewR x acc) acc ↔ b ∈ l ∨ b ∈ acc
  | [], acc, h => ⟨h, fun b => by simp⟩
  | x :: l, acc, h => by
    obtain ⟨h₁, h₂⟩ := foldl_insertNewR l (insertNewR x acc) (pairwise_insertNewR x acc h)
    refine ⟨h₁, fun b => ?_⟩
    simp only [List.foldl_cons, h₂, mem_insertNewR, List.mem_cons]
    tauto

/-- **Sorting without repetitions** gives `Finset.sort` of the set of elements. -/
theorem dedupSortM_eq {α : Type} [LinearOrder α] [DecidableEq α] {e : α → α → ℕ}
    (he : ∀ x y, e x y = ord3 x y) (l : List α) :
    dedupSortM e l = l.toFinset.sort (· ≤ ·) := by
  have hfun : (fun acc x => insertNewM e x acc) = fun acc x => insertNewR x acc := by
    funext acc x
    exact insertNewM_eq he x acc
  obtain ⟨hp, hm⟩ := foldl_insertNewR l [] List.Pairwise.nil
  rw [dedupSortM, hfun]
  refine List.Perm.eq_of_pairwise' (hp.imp le_of_lt) (Finset.pairwise_sort _ _) ?_
  refine (List.perm_ext_iff_of_nodup (hp.imp ne_of_lt) (Finset.sort_nodup _ _)).2 fun b => ?_
  rw [hm, Finset.mem_sort, List.mem_toFinset]
  simp

/-- One step of the search for the position of `a`. -/
def idxStep {α : Type} (e : α → α → ℕ) (a : α) (st : ℕ × Option ℕ) (x : α) : ℕ × Option ℕ :=
  (st.1 + 1, match st.2 with
    | none => if e a x = 1 then some st.1 else none
    | some j => some j)

/-- The position computed by `idxOfProg`: the first index of `a`, or the length. -/
def idxM {α : Type} (e : α → α → ℕ) (a : α) (l : List α) : ℕ :=
  (l.foldl (idxStep e a) (0, none)).2.getD (l.foldl (idxStep e a) (0, none)).1

theorem foldl_idxStep_some {α : Type} (e : α → α → ℕ) (a : α) (j : ℕ) :
    ∀ (l : List α) (i : ℕ), l.foldl (idxStep e a) (i, some j) = (i + l.length, some j)
  | [], i => by simp
  | x :: l, i => by
    simp only [List.foldl_cons, idxStep]
    rw [foldl_idxStep_some e a j l]
    simp only [List.length_cons, Prod.mk.injEq, and_true]
    omega

theorem foldl_idxStep_none {α : Type} [LinearOrder α] [BEq α] [LawfulBEq α] {e : α → α → ℕ}
    (he : ∀ x y, e x y = ord3 x y) (a : α) :
    ∀ (l : List α) (i : ℕ),
      ((l.foldl (idxStep e a) (i, none)).2.getD (l.foldl (idxStep e a) (i, none)).1) =
        i + l.idxOf a
  | [], i => by simp
  | x :: l, i => by
    by_cases hax : a = x
    · subst hax
      have h1 : e a a = 1 := by rw [he, ord3_self]
      simp only [List.foldl_cons, idxStep, h1, ↓reduceIte, foldl_idxStep_some]
      simp
    · have h1 : e a x ≠ 1 := by rw [he, ne_eq, ord3_eq_one]; exact hax
      simp only [List.foldl_cons, idxStep, h1, ↓reduceIte]
      rw [foldl_idxStep_none he a l (i + 1), List.idxOf_cons_ne _ (Ne.symm hax)]
      omega

/-- **The position of an element.** -/
theorem idxM_eq {α : Type} [LinearOrder α] [BEq α] [LawfulBEq α] {e : α → α → ℕ}
    (he : ∀ x y, e x y = ord3 x y)
    (a : α) (l : List α) : idxM e a l = l.idxOf a := by
  have := foldl_idxStep_none he a l 0
  simpa [idxM] using this

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Three-way comparison of numbers. -/
def cmpNatProg (x y : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natLt x y) fun lt => .ite lt (.op0 (.natLit 0))
    (.bind (.op2 .natLt y x) fun gt => .ite gt (.op0 (.natLit 2)) (.op0 (.natLit 1)))

/-- One step of the lexicographic comparison. -/
def lexStepProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat)
    (st : var (.prod (.list t) .nat)) (x : var t) : Prog S rec var (.prod (.list t) .nat) :=
  .bind (.op1 .snd st) fun s => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natEq s one) fun eq =>
  .ite eq
    (.bind (.op1 .fst st) fun bs => .caseList bs
      (.bind (.op0 (.natLit 2)) fun two => .op2 .pair bs two)
      fun y ys => .bind (cmp x y) fun r => .op2 .pair ys r)
    (.ret st)

/-- **Lexicographic three-way comparison** of lists. -/
def lexCmpProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a b : var (.list t)) :
    Prog S rec var .nat :=
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .pair b one) fun st₀ =>
  .bind (.foldList a st₀ fun st x => lexStepProg cmp st x) fun st =>
  .bind (.op1 .snd st) fun s => .bind (.op2 .natEq s one) fun eq =>
  .ite eq
    (.bind (.op1 .fst st) fun bs => .caseList bs (.ret one) fun _ _ => .op0 (.natLit 0))
    (.ret s)

/-- One step of the ordered insertion of `a`. -/
def insStepProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a : var t)
    (st : var (.prod (.list t) .bool)) (x : var t) : Prog S rec var (.prod (.list t) .bool) :=
  .bind (.op1 .fst st) fun acc => .bind (.op1 .snd st) fun done =>
  .ite done
    (.bind (.op2 .cons x acc) fun acc' => .op2 .pair acc' done)
    (.bind (cmp a x) fun r => .bind (.op0 (.natLit 2)) fun two =>
      .bind (.op2 .natEq r two) fun gt =>
      .ite gt
        (.bind (.op2 .cons x acc) fun acc' => .op2 .pair acc' done)
        (.bind (.op2 .cons a acc) fun acc₁ => .bind (.op2 .cons x acc₁) fun acc₂ =>
          .bind (.op0 (.boolLit true)) fun tt => .op2 .pair acc₂ tt))

/-- **Ordered insertion** of `a` into `l`. -/
def insertProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a : var t)
    (l : var (.list t)) : Prog S rec var (.list t) :=
  .bind (.op0 .nil) fun nil => .bind (.op0 (.boolLit false)) fun ff =>
  .bind (.op2 .pair nil ff) fun st₀ =>
  .bind (.foldList l st₀ fun st x => insStepProg cmp a st x) fun st =>
  .bind (.op1 .fst st) fun acc => .bind (.op1 .snd st) fun done =>
  .bind (.ite done (.ret acc) (.op2 .cons a acc)) fun acc' => .op1 .reverse acc'

/-- **Insertion sort.** -/
def sortProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (l : var (.list t)) :
    Prog S rec var (.list t) :=
  .bind (.op1 .reverse l) fun rl => .bind (.op0 .nil) fun nil =>
  .foldList rl nil fun acc x => insertProg cmp x acc

/-- One step of the insertion without repetition. -/
def insNewStepProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a : var t)
    (st : var (.prod (.list t) .bool)) (x : var t) : Prog S rec var (.prod (.list t) .bool) :=
  .bind (.op1 .fst st) fun acc => .bind (.op1 .snd st) fun done =>
  .ite done
    (.bind (.op2 .cons x acc) fun acc' => .op2 .pair acc' done)
    (.bind (cmp a x) fun r => .bind (.op0 (.natLit 2)) fun two =>
      .bind (.op2 .natEq r two) fun gt =>
      .ite gt
        (.bind (.op2 .cons x acc) fun acc' => .op2 .pair acc' done)
        (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natEq r one) fun eq =>
          .bind (.op0 (.boolLit true)) fun tt =>
          .ite eq
            (.bind (.op2 .cons x acc) fun acc' => .op2 .pair acc' tt)
            (.bind (.op2 .cons a acc) fun acc₁ => .bind (.op2 .cons x acc₁) fun acc₂ =>
              .op2 .pair acc₂ tt)))

/-- Insertion of `a` into a strictly increasing list, unless present. -/
def insertNewProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a : var t)
    (l : var (.list t)) : Prog S rec var (.list t) :=
  .bind (.op0 .nil) fun nil => .bind (.op0 (.boolLit false)) fun ff =>
  .bind (.op2 .pair nil ff) fun st₀ =>
  .bind (.foldList l st₀ fun st x => insNewStepProg cmp a st x) fun st =>
  .bind (.op1 .fst st) fun acc => .bind (.op1 .snd st) fun done =>
  .bind (.ite done (.ret acc) (.op2 .cons a acc)) fun acc' => .op1 .reverse acc'

/-- **The sorted list of the distinct elements.** -/
def dedupSortProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (l : var (.list t)) :
    Prog S rec var (.list t) :=
  .bind (.op0 .nil) fun nil => .foldList l nil fun acc x => insertNewProg cmp x acc

/-- One step of the search for `a`. -/
def idxStepProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a : var t)
    (st : var (.prod .nat (.option .nat))) (x : var t) :
    Prog S rec var (.prod .nat (.option .nat)) :=
  .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun r =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' =>
  .caseOption r
    (.bind (cmp a x) fun c => .bind (.op2 .natEq c one) fun eq =>
      .ite eq (.bind (.op1 .some i) fun si => .op2 .pair i' si) (.op2 .pair i' r))
    (fun _ => .op2 .pair i' r)

/-- **The position of `a` in `l`** (the length if absent). -/
def idxOfProg {t : Ty} (cmp : var t → var t → Prog S rec var .nat) (a : var t)
    (l : var (.list t)) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .none) fun nn => .bind (.op2 .pair z nn) fun st₀ =>
  .bind (.foldList l st₀ fun st x => idxStepProg cmp a st x) fun st =>
  .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun r =>
  .caseOption r (.ret i) fun j => .ret j

/-- The elements of a list satisfying a Boolean program, in order. -/
def filterProg {t : Ty} (xs : var (.list t)) (p : var t → Prog S rec var .bool) :
    Prog S rec var (.list t) :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList xs nil fun acc x => .bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc))
    fun racc => .op1 .reverse racc

/-- Comparison of lists of numbers. -/
def cmpNProg (a b : var (.list .nat)) : Prog S rec var .nat := lexCmpProg cmpNatProg a b

/-- Comparison of lists of lists of numbers. -/
def cmpLProg (a b : var (.list (.list .nat))) : Prog S rec var .nat :=
  lexCmpProg (fun x y => cmpNProg x y) a b

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.caseList_eq_nil {a' t : Ty} {l : (Ty.list a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t}
    {r : t.denote} {k : ℕ} (hl : l = []) (h : RunsWithin X body p r k) :
    RunsWithin X body (.caseList l p q) r (1 + k) := by
  subst hl
  exact RunsWithin.caseList_nil h

theorem RunsWithin.caseList_eq_cons {a' t : Ty} {l : (Ty.list a').denote} {x : a'.denote}
    {xs : List a'.denote} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (hl : l = x :: xs) (h : RunsWithin X body (q x xs) r k) :
    RunsWithin X body (.caseList l p q) r (1 + k) := by
  subst hl
  exact RunsWithin.caseList_cons h

theorem RunsWithin.caseOpt_eq_none {a' t : Ty} {o : (Ty.option a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (ho : o = none) (h : RunsWithin X body p r k) :
    RunsWithin X body (.caseOption o p q) r (1 + k) := by
  subst ho
  exact RunsWithin.caseOption_none h

theorem RunsWithin.caseOpt_eq_some {a' t : Ty} {o : (Ty.option a').denote} {v : a'.denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (ho : o = some v) (h : RunsWithin X body (q v) r k) :
    RunsWithin X body (.caseOption o p q) r (1 + k) := by
  subst ho
  exact RunsWithin.caseOption_some h

theorem RunsWithin.cmpNatProg (x y : ℕ) :
    RunsWithin X body (Coherent.cmpNatProg x y) (ord3 x y) 5 := by
  by_cases h : x < y
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show decide (x < y) = true by simpa using h) _
      exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, ord3_lt h])
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show decide (x < y) = false by simpa using h) _
      run_step (RunsWithin.prim _ _)
      by_cases h' : y < x
      · run_with RunsWithin.ite_pos (show decide (y < x) = true by simpa using h') _
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, ord3_gt h'])
      · run_with RunsWithin.ite_neg (show decide (y < x) = false by simpa using h') _
        have hxy : x = y := le_antisymm (not_lt.1 h') (not_lt.1 h)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, hxy, ord3_self])
    case hc => simp [Prim.cost]

theorem RunsWithin.lexStepProg {t : Ty} {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat}
    {e : t.denote → t.denote → ℕ} {x : t.denote} {ce : ℕ}
    (hcmp : ∀ y, RunsWithin X body (cmp x y) (e x y) ce) (st : List t.denote × ℕ) :
    RunsWithin X body (Coherent.lexStepProg cmp st x) (lexStep e st x) (ce + 8) := by
  obtain ⟨bs, s⟩ := st
  by_cases hs : s = 1
  · subst hs
    cases bs with
    | nil =>
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show ((1 : ℕ) == 1) = true from rfl) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_eq_nil rfl _
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, lexStep])
      case hc => simp [Prim.cost]
    | cons y ys =>
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show ((1 : ℕ) == 1) = true from rfl) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_eq_cons rfl _
        run_step (hcmp y)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, lexStep])
      case hc => simp [Prim.cost]; omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (s == 1) = false by simpa using hs) _
      exact (RunsWithin.ret _).of_eq (by simp [lexStep, hs])
    case hc => simp [Prim.cost]

/-- **Lexicographic comparison**, at a cost of the element comparisons plus `9` per element of
the first list. -/
theorem RunsWithin.lexCmpProg {t : Ty} {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat}
    {e : t.denote → t.denote → ℕ} {ce : t.denote → ℕ} {as : List t.denote}
    (hcmp : ∀ x ∈ as, ∀ y, RunsWithin X body (cmp x y) (e x y) (ce x)) (bs : List t.denote) :
    RunsWithin X body (Coherent.lexCmpProg cmp as bs) (lexCmp e as bs)
      ((as.map fun x => ce x + 9).sum + 8) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (F := lexStep e)
    (cf := fun x => ce x + 8) (f := fun st x => Coherent.lexStepProg cmp st x) as (bs, 1)
    fun st x hx => RunsWithin.lexStepProg (hcmp x hx) st
  have hsum : (as.map fun x => ce x + 8 + 1) = as.map fun x => ce x + 9 := by simp
  rw [hsum] at hfold
  set st := as.foldl (lexStep e) (bs, 1) with hst
  by_cases h1 : st.2 = 1
  · rcases hb : st.1 with _ | ⟨y, ys⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hfold
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (st.2 == 1) = true by simpa using h1) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_eq_nil (show st.1 = [] from hb) _
        refine (RunsWithin.ret _).of_eq ?_
        simp [Prim.eval, lexCmp, ← hst, h1, hb]
      case hc => simp [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hfold
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (st.2 == 1) = true by simpa using h1) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_eq_cons (show st.1 = y :: ys from hb) _
        refine (RunsWithin.prim (Prim.natLit 0) .nil).of_eq ?_
        simp [Prim.eval, lexCmp, ← hst, h1, hb]
      case hc => simp [Prim.cost]; omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (st.2 == 1) = false by simpa using h1) _
      refine (RunsWithin.ret _).of_eq ?_
      simp [Prim.eval, lexCmp, ← hst, h1]
    case hc => simp [Prim.cost]; omega

theorem RunsWithin.insStepProg {t : Ty} {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat}
    {e : t.denote → t.denote → ℕ} {x : t.denote} {ce : ℕ} {a' : t.denote}
    (hcmp : RunsWithin X body (cmp a' x) (e a' x) ce) (st : List t.denote × Bool) :
    RunsWithin X body (Coherent.insStepProg cmp a' st x) (insStep e a' st x) (ce + 10) := by
  obtain ⟨acc, done⟩ := st
  cases done with
  | true =>
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos rfl _
      run_step (RunsWithin.prim _ _)
      exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insStep])
    case hc => simp [Prim.cost]
  | false =>
    by_cases h2 : e a' x = 2
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg rfl _
        run_step hcmp
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (e a' x == 2) = true by simpa using h2) _
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insStep, h2])
      case hc => simp [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg rfl _
        run_step hcmp
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (e a' x == 2) = false by simpa using h2) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insStep, h2])
      case hc => simp [Prim.cost]; omega

theorem length_insertM {α : Type} [LinearOrder α] {e : α → α → ℕ} (he : ∀ x y, e x y = ord3 x y)
    (a : α) (l : List α) : (insertM e a l).length = l.length + 1 := by
  rw [insertM_eq he, List.orderedInsert_length]

theorem length_insertNewR {α : Type} [LinearOrder α] (a : α) :
    ∀ l : List α, (insertNewR a l).length ≤ l.length + 1
  | [] => by simp [insertNewR]
  | x :: l => by
    unfold insertNewR
    split_ifs
    · simp
    · simp
    · simpa using length_insertNewR a l

/-- A fold over a list accumulator that grows by at most one element per step, starting short
enough to stay below `n`. -/
theorem RunsWithin.foldList_len {a' b'' : Ty}
    {f : List b''.denote → a'.denote → Prog S (a, b) Ty.denote (.list b'')}
    {F : List b''.denote → a'.denote → List b''.denote} {n c : ℕ} :
    ∀ (xs : List a'.denote) (init : List b''.denote), init.length + xs.length ≤ n →
      (∀ acc : List b''.denote, acc.length < n → ∀ x ∈ xs,
        RunsWithin X body (f acc x) (F acc x) c ∧ (F acc x).length ≤ acc.length + 1) →
      RunsWithin X body (Prog.foldList (a := a') (b := .list b'') xs init f) (xs.foldl F init)
        (xs.length * (c + 1))
  | [], init, _, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, init, hn, hf => by
    simp only [List.length_cons] at hn
    obtain ⟨h₁, hl⟩ := hf init (by omega) x List.mem_cons_self
    have h₂ := RunsWithin.foldList_len xs (F init x) (by omega)
      fun acc hacc y hy => hf acc hacc y (List.mem_cons_of_mem _ hy)
    refine (RunsWithin.foldList_cons h₁ h₂).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- **Ordered insertion**, at a cost of one comparison and `12` per element. -/
theorem RunsWithin.insertProg {t : Ty} [LinearOrder t.denote]
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    (he : ∀ x y, e x y = ord3 x y) {a' : t.denote} {ce : ℕ}
    (hcmp : ∀ x, RunsWithin X body (cmp a' x) (e a' x) ce) (l : List t.denote) :
    RunsWithin X body (Coherent.insertProg cmp a' l) (l.orderedInsert (· ≤ ·) a')
      (l.length * (ce + 12) + 9) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (F := insStep e a')
    (cf := fun _ => ce + 10) (f := fun st x => Coherent.insStepProg cmp a' st x) l ([], false)
    fun st x _ => RunsWithin.insStepProg (hcmp x) st
  rw [sum_map_const] at hfold
  set st := l.foldl (insStep e a') ([], false) with hst
  have hlen : (if st.2 then st.1 else a' :: st.1).length = l.length + 1 := by
    rw [← List.length_reverse, ← length_insertM he a' l]
    rfl
  have hres : (if st.2 then st.1 else a' :: st.1).reverse = l.orderedInsert (· ≤ ·) a' := by
    rw [← insertM_eq he]
    rfl
  cases hd : st.2 with
  | true =>
    rw [hd] at hlen hres
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.ite_pos (show st.2 = true from hd) (RunsWithin.ret _))
      refine (RunsWithin.prim _ _).of_eq ?_
      simpa [Prim.eval] using hres
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons]
      simp only [↓reduceIte] at hlen
      rw [hlen]
      nlinarith
  | false =>
    rw [hd] at hlen hres
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.ite_neg (show st.2 = false from hd) (RunsWithin.prim _ _))
      refine (RunsWithin.prim _ _).of_eq ?_
      simpa [Prim.eval] using hres
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlen
      simp only [List.length_cons, hlen]
      nlinarith

/-- **Insertion sort**, at a cost quadratic in the length. -/
theorem RunsWithin.sortProg {t : Ty} [LinearOrder t.denote]
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    (he : ∀ x y, e x y = ord3 x y) {ce : ℕ} {l : List t.denote}
    (hcmp : ∀ x ∈ l, ∀ y, RunsWithin X body (cmp x y) (e x y) ce) :
    RunsWithin X body (Coherent.sortProg cmp l) (l.insertionSort (· ≤ ·))
      (l.length * (l.length * (ce + 12) + 10) + l.length + 2) := by
  have hfold := RunsWithin.foldList_len (X := X) (body := body) (n := l.length)
    (c := l.length * (ce + 12) + 9) (F := fun acc x => acc.orderedInsert (· ≤ ·) x)
    (f := fun acc x => Coherent.insertProg cmp x acc) l.reverse [] (by simp)
    fun acc hacc x hx => ⟨(RunsWithin.insertProg he (hcmp x (List.mem_reverse.1 hx)) acc).mono
      (by have := Nat.mul_le_mul_right (ce + 12) hacc.le; omega),
      by rw [List.orderedInsert_length]⟩
  have hres : l.reverse.foldl (fun acc x => acc.orderedInsert (· ≤ ·) x) [] =
      l.insertionSort (· ≤ ·) := by
    rw [← sortM_eq he, sortM]
    congr 1
    funext acc x
    exact (insertM_eq he x acc).symm
  rw [hres, List.length_reverse] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    nlinarith

theorem RunsWithin.insNewStepProg {t : Ty}
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    {x : t.denote} {ce : ℕ} {a' : t.denote} (hcmp : RunsWithin X body (cmp a' x) (e a' x) ce)
    (st : List t.denote × Bool) :
    RunsWithin X body (Coherent.insNewStepProg cmp a' st x) (insNewStep e a' st x) (ce + 13) := by
  obtain ⟨acc, done⟩ := st
  cases done with
  | true =>
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos rfl _
      run_step (RunsWithin.prim _ _)
      exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insNewStep])
    case hc => simp [Prim.cost]
  | false =>
    by_cases h2 : e a' x = 2
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg rfl _
        run_step hcmp
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (e a' x == 2) = true by simpa using h2) _
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insNewStep, h2])
      case hc => simp [Prim.cost]; omega
    · by_cases h1 : e a' x = 1
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg rfl _
          run_step hcmp
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (e a' x == 2) = false by simpa using h2) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (show (e a' x == 1) = true by simpa using h1) _
          run_step (RunsWithin.prim _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insNewStep, h1])
        case hc => simp [Prim.cost]; omega
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg rfl _
          run_step hcmp
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (e a' x == 2) = false by simpa using h2) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (e a' x == 1) = false by simpa using h1) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, insNewStep, h2, h1])
        case hc => simp [Prim.cost]; omega

/-- **Insertion without repetition** into a strictly increasing list. -/
theorem RunsWithin.insertNewProg {t : Ty} [LinearOrder t.denote]
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    (he : ∀ x y, e x y = ord3 x y) {a' : t.denote} {ce : ℕ}
    (hcmp : ∀ x, RunsWithin X body (cmp a' x) (e a' x) ce) (l : List t.denote) :
    RunsWithin X body (Coherent.insertNewProg cmp a' l) (insertNewR a' l)
      (l.length * (ce + 15) + 9) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (F := insNewStep e a')
    (cf := fun _ => ce + 13) (f := fun st x => Coherent.insNewStepProg cmp a' st x) l ([], false)
    fun st x _ => RunsWithin.insNewStepProg (hcmp x) st
  rw [sum_map_const] at hfold
  set st := l.foldl (insNewStep e a') ([], false) with hst
  have hres : (if st.2 then st.1 else a' :: st.1).reverse = insertNewR a' l := by
    rw [← insertNewM_eq he]
    rfl
  have hlen : (if st.2 then st.1 else a' :: st.1).length ≤ l.length + 1 := by
    rw [← List.length_reverse, hres]
    exact length_insertNewR a' l
  cases hd : st.2 with
  | true =>
    rw [hd] at hlen hres
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.ite_pos (show st.2 = true from hd) (RunsWithin.ret _))
      refine (RunsWithin.prim _ _).of_eq ?_
      simpa [Prim.eval] using hres
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons]
      simp only [↓reduceIte] at hlen
      nlinarith
  | false =>
    rw [hd] at hlen hres
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.ite_neg (show st.2 = false from hd) (RunsWithin.prim _ _))
      refine (RunsWithin.prim _ _).of_eq ?_
      simpa [Prim.eval] using hres
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons]
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlen
      simp only [List.length_cons]
      nlinarith

/-- **Sorting without repetition**: `Finset.sort` of the set of elements, at a cost quadratic in
the length. -/
theorem RunsWithin.dedupSortProg {t : Ty} [LinearOrder t.denote] [DecidableEq t.denote]
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    (he : ∀ x y, e x y = ord3 x y) {ce : ℕ} {l : List t.denote}
    (hcmp : ∀ x ∈ l, ∀ y, RunsWithin X body (cmp x y) (e x y) ce) :
    RunsWithin X body (Coherent.dedupSortProg cmp l) (l.toFinset.sort (· ≤ ·))
      (l.length * (l.length * (ce + 15) + 10) + 1) := by
  have hfold := RunsWithin.foldList_len (X := X) (body := body) (n := l.length)
    (c := l.length * (ce + 15) + 9) (F := fun acc x => insertNewR x acc)
    (f := fun acc x => Coherent.insertNewProg cmp x acc) l [] (by simp)
    fun acc hacc x hx => ⟨(RunsWithin.insertNewProg he (hcmp x hx) acc).mono
      (by have := Nat.mul_le_mul_right (ce + 15) hacc.le; omega), length_insertNewR x acc⟩
  have hres : l.foldl (fun acc x => insertNewR x acc) [] = l.toFinset.sort (· ≤ ·) := by
    rw [← dedupSortM_eq he, dedupSortM]
    congr 1
    funext acc x
    exact (insertNewM_eq he x acc).symm
  rw [hres] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp only [Prim.cost]; nlinarith

theorem RunsWithin.idxStepProg {t : Ty}
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    {x : t.denote} {ce : ℕ} {a' : t.denote} (hcmp : RunsWithin X body (cmp a' x) (e a' x) ce)
    (st : ℕ × Option ℕ) :
    RunsWithin X body (Coherent.idxStepProg cmp a' st x) (idxStep e a' st x) (ce + 9) := by
  obtain ⟨i, r⟩ := st
  cases r with
  | some j =>
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOpt_eq_some (show (some j : Option ℕ) = some j from rfl) _
      refine (RunsWithin.prim _ _).of_eq ?_
      simp [Prim.eval, idxStep]
    case hc => simp [Prim.cost]
  | none =>
    by_cases h1 : e a' x = 1
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
        run_step hcmp
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (e a' x == 1) = true by simpa using h1) _
        run_step (RunsWithin.prim _ _)
        refine (RunsWithin.prim _ _).of_eq ?_
        simp [Prim.eval, idxStep, h1]
      case hc => simp [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
        run_step hcmp
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (e a' x == 1) = false by simpa using h1) _
        refine (RunsWithin.prim _ _).of_eq ?_
        simp [Prim.eval, idxStep, h1]
      case hc => simp [Prim.cost]; omega

/-- **The position of `a`**, at a cost of one comparison and `10` per element. -/
theorem RunsWithin.idxOfProg {t : Ty} [LinearOrder t.denote] [BEq t.denote] [LawfulBEq t.denote]
    {cmp : t.denote → t.denote → Prog S (a, b) Ty.denote .nat} {e : t.denote → t.denote → ℕ}
    (he : ∀ x y, e x y = ord3 x y) {a' : t.denote} {ce : ℕ}
    (hcmp : ∀ x, RunsWithin X body (cmp a' x) (e a' x) ce) (l : List t.denote) :
    RunsWithin X body (Coherent.idxOfProg cmp a' l) (l.idxOf a') (l.length * (ce + 10) + 6) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (F := idxStep e a')
    (cf := fun _ => ce + 9) (f := fun st x => Coherent.idxStepProg cmp a' st x) l (0, none)
    fun st x _ => RunsWithin.idxStepProg (hcmp x) st
  rw [sum_map_const, show ce + 9 + 1 = ce + 10 from rfl] at hfold
  set st := l.foldl (idxStep e a') (0, none) with hst
  have hres : st.2.getD st.1 = l.idxOf a' := by
    rw [← idxM_eq he]
    rfl
  cases hr : st.2 with
  | none =>
    rw [hr] at hres
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOpt_eq_none (show st.2 = none from hr) _
      refine (RunsWithin.ret _).of_eq ?_
      simpa [Prim.eval] using hres
    case hc => simp only [Prim.cost]; omega
  | some j =>
    rw [hr] at hres
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOpt_eq_some (show st.2 = some j from hr) _
      refine (RunsWithin.ret _).of_eq ?_
      simpa using hres
    case hc => simp only [Prim.cost]; omega

private theorem fold_filter_spec {t : Ty} {p : t.denote → Prog S (a, b) Ty.denote .bool}
    {P : t.denote → Bool} {c : ℕ} :
    ∀ (xs : List t.denote) (acc : List t.denote),
      (∀ x ∈ xs, RunsWithin X body (p x) (P x) c) →
      RunsWithin X body
        (.foldList xs acc fun acc x => .bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc))
        ((xs.filter P).reverse ++ acc) (xs.length * (c + 3))
  | [], acc, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, acc, hp => by
    have h₁ : RunsWithin X body (.bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc))
        (if P x then x :: acc else acc) (c + 2) := by
      refine (hp x List.mem_cons_self).bind ?_
      cases P x
      · exact (RunsWithin.ite_false (RunsWithin.ret _)).mono (by omega)
      · exact RunsWithin.ite_true (RunsWithin.prim _ _)
    have h₂ := fold_filter_spec xs (if P x then x :: acc else acc)
      fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have h := RunsWithin.foldList_cons h₁ h₂
    have e₁ : ((x :: xs).filter P).reverse ++ acc =
        (xs.filter P).reverse ++ (if P x then x :: acc else acc) := by
      cases hPx : P x <;> simp [hPx]
    have e₂ : (x :: xs).length * (c + 3) = 1 + (c + 2) + xs.length * (c + 3) := by
      simp only [List.length_cons, Nat.succ_mul]
      omega
    rw [e₁, e₂]
    exact h

/-- **Filtering**, at a cost of the tests plus `4` per element. -/
theorem RunsWithin.filterProg {t : Ty} {xs : List t.denote}
    {p : t.denote → Prog S (a, b) Ty.denote .bool} {P : t.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (Coherent.filterProg xs p) (xs.filter P) (xs.length * (c + 4) + 2) := by
  refine RunsWithin.bind_le (c₂ := xs.length * (c + 3) + (xs.length + 1)) (RunsWithin.prim _ _)
    ?_ (by simp only [Prim.cost, Nat.mul_add]; omega)
  refine RunsWithin.bind_le (c₂ := xs.length + 1) (fold_filter_spec xs [] hp) ?_ le_rfl
  refine RunsWithin.prim_le (by simp [Prim.eval]) ?_
  simp only [Prim.cost, Args.head_cons, List.append_nil, List.length_reverse]
  have := List.length_filter_le P xs
  omega

/-- Comparison of lists of numbers: `14` per element of the first list. -/
theorem RunsWithin.cmpNProg (x y : List ℕ) :
    RunsWithin X body (Coherent.cmpNProg x y) (ord3 x y) (14 * x.length + 8) := by
  have h := RunsWithin.lexCmpProg (X := X) (body := body) (t := .nat)
    (cmp := fun z w => Coherent.cmpNatProg z w) (e := ord3) (ce := fun _ => 5)
    (as := x) (fun z _ w => RunsWithin.cmpNatProg z w) y
  rw [lexCmp_eq (fun _ _ => rfl), sum_map_const] at h
  exact h.mono (by omega)

/-- Comparison of lists of lists of numbers, each of the first list of length at most `w`. -/
theorem RunsWithin.cmpLProg {w : ℕ} {x : List (List ℕ)} (hw : ∀ z ∈ x, z.length ≤ w)
    (y : List (List ℕ)) :
    RunsWithin X body (Coherent.cmpLProg x y) (ord3 x y) (x.length * (14 * w + 17) + 8) := by
  have h := RunsWithin.lexCmpProg (X := X) (body := body) (t := .list .nat)
    (cmp := fun z v => Coherent.cmpNProg z v) (e := ord3) (ce := fun _ => 14 * w + 8) (as := x)
    (fun z hz v => (RunsWithin.cmpNProg z v).mono (by have := hw z hz; omega)) y
  rw [lexCmp_eq (fun _ _ => rfl), sum_map_const] at h
  exact h.mono (by nlinarith)

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

/-- Well-formedness of a comparison program, in every extension of the context. -/
def WfCmp {t : Ty} (r : Bool) (Γ : WfCtx var₁ var₂)
    (f₁ : var₁ t → var₁ t → Prog S rec var₁ .nat) (f₂ : var₂ t → var₂ t → Prog S rec var₂ .nat) :
    Prop :=
  ∀ Γ' : WfCtx var₁ var₂, Γ ⊆ Γ' → ∀ x₁ x₂ y₁ y₂, ⟨t, x₁, x₂⟩ ∈ Γ' → ⟨t, y₁, y₂⟩ ∈ Γ' →
    Prog.Wf r Γ' (f₁ x₁ y₁) (f₂ x₂ y₂)

theorem WfCmp.mono {t : Ty} {Γ Γ' : WfCtx var₁ var₂}
    {f₁ : var₁ t → var₁ t → Prog S rec var₁ .nat} {f₂ : var₂ t → var₂ t → Prog S rec var₂ .nat}
    (h : WfCmp r Γ f₁ f₂) (hΓ : Γ ⊆ Γ') : WfCmp r Γ' f₁ f₂ :=
  fun Γ'' h' => h Γ'' (List.Subset.trans hΓ h')

theorem wf_filterProg {t : Ty} {xs₁ : var₁ (.list t)} {xs₂ : var₂ (.list t)}
    {p₁ : var₁ t → Prog S rec var₁ .bool} {p₂ : var₂ t → Prog S rec var₂ .bool}
    (hxs : ⟨.list t, xs₁, xs₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (filterProg xs₁ p₁) (filterProg xs₂ p₂) := by
  unfold filterProg
  prog_wf
  all_goals exact hp _ (fun y hy => by simp [hy]) _ _ (by simp)

theorem wfCmp_cmpNat :
    WfCmp (S := S) (rec := rec) r Γ (fun x y => cmpNatProg (var := var₁) x y)
      (fun x y => cmpNatProg (var := var₂) x y) := by
  intro Γ' _ x₁ x₂ y₁ y₂ hx hy
  unfold cmpNatProg
  prog_wf

theorem wf_lexCmpProg {t : Ty} {cmp₁ : var₁ t → var₁ t → Prog S rec var₁ .nat}
    {cmp₂ : var₂ t → var₂ t → Prog S rec var₂ .nat} (hc : WfCmp r Γ cmp₁ cmp₂)
    {a₁ b₁ : var₁ (.list t)} {a₂ b₂ : var₂ (.list t)} (ha : ⟨.list t, a₁, a₂⟩ ∈ Γ)
    (hb : ⟨.list t, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf r Γ (lexCmpProg cmp₁ a₁ b₁) (lexCmpProg cmp₂ a₂ b₂) := by
  unfold lexCmpProg lexStepProg
  prog_wf
  all_goals exact hc _ (fun z hz => by simp [hz]) _ _ _ _ (by simp) (by simp)

theorem wfCmp_cmpN :
    WfCmp (S := S) (rec := rec) r Γ (fun x y => cmpNProg (var := var₁) x y)
      (fun x y => cmpNProg (var := var₂) x y) :=
  fun _ _ _ _ _ _ hx hy => wf_lexCmpProg wfCmp_cmpNat hx hy

theorem wfCmp_cmpL :
    WfCmp (S := S) (rec := rec) r Γ (fun x y => cmpLProg (var := var₁) x y)
      (fun x y => cmpLProg (var := var₂) x y) :=
  fun _ _ _ _ _ _ hx hy => wf_lexCmpProg wfCmp_cmpN hx hy

theorem wf_insertProg {t : Ty} {cmp₁ : var₁ t → var₁ t → Prog S rec var₁ .nat}
    {cmp₂ : var₂ t → var₂ t → Prog S rec var₂ .nat} (hc : WfCmp r Γ cmp₁ cmp₂)
    {a₁ : var₁ t} {a₂ : var₂ t} {l₁ : var₁ (.list t)} {l₂ : var₂ (.list t)}
    (ha : ⟨t, a₁, a₂⟩ ∈ Γ) (hl : ⟨.list t, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf r Γ (insertProg cmp₁ a₁ l₁) (insertProg cmp₂ a₂ l₂) := by
  unfold insertProg insStepProg
  prog_wf
  all_goals exact hc _ (fun z hz => by simp [hz]) _ _ _ _ (by simp [ha]) (by simp)

theorem wf_sortProg {t : Ty} {cmp₁ : var₁ t → var₁ t → Prog S rec var₁ .nat}
    {cmp₂ : var₂ t → var₂ t → Prog S rec var₂ .nat} (hc : WfCmp r Γ cmp₁ cmp₂)
    {l₁ : var₁ (.list t)} {l₂ : var₂ (.list t)} (hl : ⟨.list t, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf r Γ (sortProg cmp₁ l₁) (sortProg cmp₂ l₂) := by
  unfold sortProg
  refine .bind (.prim _ (.cons hl .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .foldList (by simp) (by simp) fun acc₁ acc₂ x₁ x₂ => ?_
  exact wf_insertProg (hc.mono fun z hz => by simp [hz]) (by simp) (by simp)

theorem wf_insertNewProg {t : Ty} {cmp₁ : var₁ t → var₁ t → Prog S rec var₁ .nat}
    {cmp₂ : var₂ t → var₂ t → Prog S rec var₂ .nat} (hc : WfCmp r Γ cmp₁ cmp₂)
    {a₁ : var₁ t} {a₂ : var₂ t} {l₁ : var₁ (.list t)} {l₂ : var₂ (.list t)}
    (ha : ⟨t, a₁, a₂⟩ ∈ Γ) (hl : ⟨.list t, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf r Γ (insertNewProg cmp₁ a₁ l₁) (insertNewProg cmp₂ a₂ l₂) := by
  unfold insertNewProg insNewStepProg
  prog_wf
  all_goals exact hc _ (fun z hz => by simp [hz]) _ _ _ _ (by simp [ha]) (by simp)

theorem wf_dedupSortProg {t : Ty} {cmp₁ : var₁ t → var₁ t → Prog S rec var₁ .nat}
    {cmp₂ : var₂ t → var₂ t → Prog S rec var₂ .nat} (hc : WfCmp r Γ cmp₁ cmp₂)
    {l₁ : var₁ (.list t)} {l₂ : var₂ (.list t)} (hl : ⟨.list t, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf r Γ (dedupSortProg cmp₁ l₁) (dedupSortProg cmp₂ l₂) := by
  unfold dedupSortProg
  refine .bind (.prim _ .nil) fun _ _ => .foldList (by simp [hl]) (by simp) fun _ _ _ _ => ?_
  exact wf_insertNewProg (hc.mono fun z hz => by simp [hz]) (by simp) (by simp)

theorem wf_idxOfProg {t : Ty} {cmp₁ : var₁ t → var₁ t → Prog S rec var₁ .nat}
    {cmp₂ : var₂ t → var₂ t → Prog S rec var₂ .nat} (hc : WfCmp r Γ cmp₁ cmp₂)
    {a₁ : var₁ t} {a₂ : var₂ t} {l₁ : var₁ (.list t)} {l₂ : var₂ (.list t)}
    (ha : ⟨t, a₁, a₂⟩ ∈ Γ) (hl : ⟨.list t, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf r Γ (idxOfProg cmp₁ a₁ l₁) (idxOfProg cmp₂ a₂ l₂) := by
  unfold idxOfProg idxStepProg
  prog_wf
  all_goals exact hc _ (fun z hz => by simp [hz]) _ _ _ _ (by simp [ha]) (by simp)

end Wf

end GraphIso.Coherent
