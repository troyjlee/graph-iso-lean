module

public import GraphIso.SoJProg.Data
public import GraphIso.Coherent.DesignProg
public import GraphIso.SplitJohnson.BipartiteCount
public import GraphIso.SplitJohnson.BipartiteDary

/-!
# The Design Lemma test of Split-or-Johnson, on data

Stage 14c, item 7 (`PLAN-14.md` §7): the pieces of `bstep` and `dlCont` (milestone 11,
`GraphIso/SplitJohnson/BipartiteDef.lean`) that read a refined colouring, as costed programs.

* **Transport.** `DLGood` is milestone 10's `DesignGood`; both move along a bijection of the
  points (`dlGood_comp_equiv`), as do the individualized colourings (`skel1_comp_equiv`,
  `card_cls1_comp_equiv`, `isClique_comp_equiv`). So the test on the cells of `V₂` reduces to
  the test on `Fin v` through an enumeration of `V₂`.
* **The test on arrays** is milestone 10's `goodA` (`goodA_iff_dlGood`, for `v ≤ 2 t`, which
  holds for `t = ⌊2v/3⌋` unless `v = 1`: `le_two_mul_two_mul_div_three`). The vertex colouring
  and the "no dominant class" test are milestone 10's `col1A` and `domA`
  (`skel1_eq_getD_col1A`, `domA_eq_none_iff`).
* **The options of the Design Lemma node**: `goodList c d v t` lists the candidates (lists of
  fewer than `d` cell indices) where the test holds, computed by `goodListProg`
  (`RunsWithin.goodListProg`); decoded, they are `(tuplesLt univ d).filter (DLGood W t)`
  (`goodList_decode`).
* **`dlCont`'s pieces** on index lists with colours read from arrays: `selThirdL` (`selThird`,
  `selThirdL_decode`), `allSmallL` (every class at most `t`), `bigL` (the points of classes
  of more than `t`), `constRectL` (a function constant on a rectangle), each linked to the
  `Finset` form of the model through an injective decoding (`allSmallL_iff`, `bigL_decode`,
  `constRectL_iff`), and computed by programs with explicit polynomial costs.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.Coherent GraphIso.SplitJohnson GraphIso.Cost GraphIso.Programs
  GraphIso.Sims

/-! ### Transport along a bijection of the points -/

section Transport

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] {d : ℕ}

omit [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] in
theorem pad1_comp_equiv (e : V ≃ U) (x : List V) (u : V) :
    (⇑e ∘ pad1 d x u) = pad1 d (x.map e) (e u) := by
  funext i
  simp only [Function.comp, pad1, List.length_map, List.getElem_map]
  split_ifs <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] in
theorem pad2_comp_equiv (e : V ≃ U) (x : List V) (u v : V) :
    (⇑e ∘ pad2 d x u v) = pad2 d (x.map e) (e u) (e v) := by
  funext i
  simp only [Function.comp, pad2, List.length_map, List.getElem_map]
  split_ifs <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] in
theorem skel1_comp_equiv (e : V ≃ U) (F : (Fin d → U) → ℕ) (x : List V) (u : V) :
    skel1 (fun y => F (⇑e ∘ y)) x u = skel1 F (x.map e) (e u) := by
  simp only [skel1, pad1_comp_equiv]

omit [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] in
theorem skel2_comp_equiv (e : V ≃ U) (F : (Fin d → U) → ℕ) (x : List V) (u v : V) :
    skel2 (fun y => F (⇑e ∘ y)) x u v = skel2 F (x.map e) (e u) (e v) := by
  simp only [skel2, pad2_comp_equiv]

omit [DecidableEq V] [DecidableEq U] in
theorem mem_cls1_comp_equiv (e : V ≃ U) (F : (Fin d → U) → ℕ) (x : List V) (u w : V) :
    w ∈ cls1 (fun y => F (⇑e ∘ y)) x u ↔ e w ∈ cls1 F (x.map e) (e u) := by
  simp only [cls1, mem_filter, mem_univ, true_and, skel1_comp_equiv]

omit [DecidableEq V] [DecidableEq U] in
theorem card_cls1_comp_equiv (e : V ≃ U) (F : (Fin d → U) → ℕ) (x : List V) (u : V) :
    (cls1 (fun y => F (⇑e ∘ y)) x u).card = (cls1 F (x.map e) (e u)).card := by
  refine Finset.card_bij (fun w _ => e w) (fun w hw => (mem_cls1_comp_equiv e F x u w).1 hw)
    (fun _ _ _ _ h => e.injective h) fun w' hw' => ⟨e.symm w', ?_, by simp⟩
  rw [mem_cls1_comp_equiv, Equiv.apply_symm_apply]
  exact hw'

omit [DecidableEq V] [DecidableEq U] in
theorem isClique_comp_equiv (e : V ≃ U) (F : (Fin d → U) → ℕ) (x : List V) (u : V) :
    IsClique (skel2 (fun y => F (⇑e ∘ y)) x) (cls1 (fun y => F (⇑e ∘ y)) x u) ↔
      IsClique (skel2 F (x.map e)) (cls1 F (x.map e) (e u)) := by
  constructor
  · intro h a ha b hb a' ha' b' hb' hab hab'
    have := h (e.symm a) (by rw [mem_cls1_comp_equiv]; simpa using ha) (e.symm b)
      (by rw [mem_cls1_comp_equiv]; simpa using hb) (e.symm a')
      (by rw [mem_cls1_comp_equiv]; simpa using ha') (e.symm b')
      (by rw [mem_cls1_comp_equiv]; simpa using hb') (by simpa using hab) (by simpa using hab')
    simpa [skel2_comp_equiv] using this
  · intro h a ha b hb a' ha' b' hb' hab hab'
    rw [mem_cls1_comp_equiv] at ha hb ha' hb'
    rw [skel2_comp_equiv, skel2_comp_equiv]
    exact h _ ha _ hb _ ha' _ hb' (fun h' => hab (e.injective h'))
      (fun h' => hab' (e.injective h'))

/-- **`DLGood` moves along a bijection of the points.** -/
theorem dlGood_comp_equiv (e : V ≃ U) (F : (Fin d → U) → ℕ) (t : ℕ) (x : List V) :
    DLGood (fun y => F (⇑e ∘ y)) t x ↔ DLGood F t (x.map e) := by
  unfold DLGood
  rw [List.length_map]
  constructor
  · rintro (h | ⟨hl, u, hu, hc⟩)
    · refine Or.inl fun u' => ?_
      have := h (e.symm u')
      rwa [card_cls1_comp_equiv, Equiv.apply_symm_apply] at this
    · refine Or.inr ⟨hl, e u, ?_, ?_⟩
      · rwa [← card_cls1_comp_equiv]
      · rwa [← isClique_comp_equiv]
  · rintro (h | ⟨hl, u', hu, hc⟩)
    · refine Or.inl fun u => ?_
      rw [card_cls1_comp_equiv]
      exact h _
    · refine Or.inr ⟨hl, e.symm u', ?_, ?_⟩
      · rwa [card_cls1_comp_equiv, Equiv.apply_symm_apply]
      · rwa [isClique_comp_equiv, Equiv.apply_symm_apply]

end Transport

/-! ### The test on arrays -/

section Arrays

variable {V : Type*} [Fintype V] [DecidableEq V] {d v : ℕ}

/-- `⌊2v/3⌋` is at least half of `v`, unless `v = 1`. -/
theorem le_two_mul_two_mul_div_three {v : ℕ} (hv : v ≠ 1) : v ≤ 2 * (2 * v / 3) := by
  omega

/-- **The test on arrays is `DLGood`** (milestone 10's `goodA`, for `v ≤ 2t`). -/
theorem goodA_iff_dlGood (c : Array ℕ) {t : ℕ} (ht : v ≤ 2 * t) (x : List (Fin v)) :
    goodA c (pwTab d v) d v t (x.map Fin.val) = true ↔ DLGood (toFun (k := d) c) t x :=
  goodA_iff c ht x

/-- **`DLGood` on an enumerated set**: through `e : V ≃ Fin v`, the test of a colouring read
from an array is `goodA`. -/
theorem dlGood_iff_goodA (e : V ≃ Fin v) (c : Array ℕ) {t : ℕ} (ht : v ≤ 2 * t)
    (x : List V) :
    DLGood (fun y => toFun (k := d) c (⇑e ∘ y)) t x ↔
      goodA c (pwTab d v) d v t ((x.map e).map Fin.val) = true := by
  rw [dlGood_comp_equiv, goodA_iff_dlGood c ht]

omit [Fintype V] [DecidableEq V] in
/-- The individualized vertex colouring through an enumeration, read from `col1A`. -/
theorem skel1_eq_getD_col1A (e : V ≃ Fin v) (c : Array ℕ) (x : List V) (u : V) :
    skel1 (fun y => toFun (k := d) c (⇑e ∘ y)) x u =
      (col1A c (pwTab d v) d v (x.map e).length ((x.map e).map Fin.val).toArray).getD
        (e u) 0 := by
  rw [skel1_comp_equiv, getD_col1A]

omit [DecidableEq V] in
/-- **No dominant class** through an enumeration: `domA` finds none. -/
theorem domA_eq_none_iff (e : V ≃ Fin v) (c : Array ℕ) (x : List V) (t : ℕ) :
    (∀ u, (cls1 (fun y => toFun (k := d) c (⇑e ∘ y)) x u).card ≤ t) ↔
      domA (col1A c (pwTab d v) d v (x.map e).length ((x.map e).map Fin.val).toArray) t =
        none := by
  rw [domA_eq_none, length_col1A]
  constructor
  · intro h u hu
    have := h (e.symm ⟨u, hu⟩)
    rw [card_cls1_comp_equiv, Equiv.apply_symm_apply, ← cntA_eq] at this
    exact this
  · intro h u
    rw [card_cls1_comp_equiv, ← cntA_eq]
    exact h (e u) (e u).2

end Arrays

/-! ### The options of the Design Lemma node -/

/-- The candidates where the test holds, in order. -/
def goodList (c : Array ℕ) (k m t : ℕ) : List (List ℕ) :=
  (cands k m).filter (goodA c (pwTab k m) k m t)

/-- A list of cell indices, decoded through an enumeration (indices `≥ v` are dropped). -/
def decList {V : Type*} {v : ℕ} (e : V ≃ Fin v) (xd : List ℕ) : List V :=
  xd.filterMap fun i => if h : i < v then some (e.symm ⟨i, h⟩) else none

theorem decList_map_val {V : Type*} {v : ℕ} (e : V ≃ Fin v) (y : List (Fin v)) :
    decList e (y.map Fin.val) = y.map e.symm := by
  induction y with
  | nil => rfl
  | cons a y ih =>
    simp only [List.map_cons, decList, List.filterMap_cons, a.2, dite_true] at ih ⊢
    rw [ih]

theorem mem_tuplesLt {β : Type*} [DecidableEq β] {S : Finset β} {d : ℕ} {x : List β} :
    x ∈ tuplesLt S d ↔ x.length < d ∧ ∀ a ∈ x, a ∈ S := by
  constructor
  · intro hx
    obtain ⟨l, hl, hx⟩ := mem_biUnion.1 hx
    obtain ⟨hlen, hS⟩ := BCount.mem_tuples.1 hx
    exact ⟨hlen ▸ mem_range.1 hl, hS⟩
  · rintro ⟨hl, hS⟩
    exact mem_tuplesLt_of hl hS

/-- **The options of the Design Lemma node, decoded**: the candidates where the test holds
are the lists of fewer than `d` cells where `DLGood` holds. -/
theorem goodList_decode {V : Type*} [Fintype V] [DecidableEq V] {d v t : ℕ} (e : V ≃ Fin v)
    (c : Array ℕ) (ht : v ≤ 2 * t) :
    ((goodList c d v t).map (decList e)).toFinset =
      (tuplesLt univ d).filter (DLGood (fun y => toFun (k := d) c (⇑e ∘ y)) t) := by
  ext x
  simp only [List.mem_toFinset, List.mem_map, goodList, List.mem_filter, mem_filter,
    mem_tuplesLt, mem_univ, implies_true, and_true]
  constructor
  · rintro ⟨xd, ⟨hxd, hg⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := mem_cands.1 hxd
    rw [decList_map_val]
    refine ⟨by simpa using hy, ?_⟩
    rw [dlGood_iff_goodA e c ht, List.map_map, List.map_map]
    convert hg using 2
    ext a
    simp
  · rintro ⟨hl, hg⟩
    refine ⟨(x.map e).map Fin.val, ⟨mem_cands.2 ⟨x.map e, by simpa using hl, rfl⟩, ?_⟩, ?_⟩
    · exact (dlGood_iff_goodA e c ht x).1 hg
    · rw [decList_map_val, List.map_map]
      simp

/-! ### The candidate list as a program -/

section GoodProg

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One candidate: keep it if the test holds. -/
def goodStepProg (c : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk rm : var (.list .nat)) (k t : var .nat) (acc : var (.list (.list .nat)))
    (xd : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  .bind (goodProg c pw rk rm k t xd) fun g => .bind (.op1 .fst g) fun good =>
  .ite good (.op2 .cons xd acc) (.ret acc)

/-- The candidates of length `l`. -/
def goodLenProg (c : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk rm : var (.list .nat)) (k m t : var .nat) (acc : var (.list (.list .nat)))
    (l : var .nat) : Prog S rec var (.list (.list .nat)) :=
  .bind (tupsProg l m) fun tups =>
  .foldList tups acc fun acc' xd => goodStepProg c pw rk rm k t acc' xd

/-- **The options of the Design Lemma node**: the lists of fewer than `k` points (digits) where
the test holds for the colouring `c`, in order. -/
def goodListProg (c : var (.array .nat)) (k m t : var .nat) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (pwTabProg m rk rm) fun pw => .bind (.op0 .nil) fun nl =>
  .bind (.foldList rk nl fun acc l => goodLenProg c pw rk rm k m t acc l) fun racc =>
  .op1 .reverse racc

end GoodProg

/-- One step of the candidate fold. -/
def gstep (c : Array ℕ) (k m t : ℕ) (acc : List (List ℕ)) (xd : List ℕ) : List (List ℕ) :=
  if goodA c (pwTab k m) k m t xd then xd :: acc else acc

theorem foldl_gstep (c : Array ℕ) (k m t : ℕ) :
    ∀ (l : List (List ℕ)) (acc : List (List ℕ)),
      l.foldl (gstep c k m t) acc = (l.filter (goodA c (pwTab k m) k m t)).reverse ++ acc
  | [], acc => rfl
  | xd :: l, acc => by
    rw [List.foldl_cons, foldl_gstep c k m t l]
    unfold gstep
    by_cases h : goodA c (pwTab k m) k m t xd = true
    · simp [h]
    · simp [h]

theorem length_cands_le (k m : ℕ) : (cands k m).length ≤ k * (m ^ k + 1) := by
  rw [cands, List.length_flatMap]
  have : ∀ l ∈ List.range k, (tupList l m).length ≤ m ^ k + 1 := fun l hl => by
    rw [length_tupList]
    exact pow_le_pow_add_one (List.mem_range.1 hl).le
  calc ((List.range k).map fun l => (tupList l m).length).sum
      ≤ ((List.range k).map fun _ => m ^ k + 1).sum := List.sum_le_sum fun l hl => this l hl
    _ = k * (m ^ k + 1) := by rw [sum_map_const, List.length_range]

/-- **The cost of the candidate list.** -/
def goodListCost (k m : ℕ) : ℕ :=
  k + m + 4 + pwTabCost k m + k * (1 + tupsBound k m + (m ^ k + 1) * (goodCost k m + 6)) +
    (k * (m ^ k + 1) + 1)

section GoodSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.goodStepProg (c : Array ℕ) (k m t : ℕ) (acc : List (List ℕ))
    {xd : List ℕ} (hxd : xd.length ≤ k) :
    RunsWithin X body
      (SoJProg.goodStepProg c (pwTab k m) (List.range k) (List.range m) k t acc xd)
      (gstep c k m t acc xd) (goodCost k m + 5) := by
  have hg := RunsWithin.goodProg (X := X) (body := body) c k m t hxd
  by_cases h : goodA c (pwTab k m) k m t xd = true
  · apply RunsWithin.mono
    case h =>
      run_step hg
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show goodA c (pwTab k m) k m t xd = true from h) _
      exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, gstep, h])
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step hg
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show goodA c (pwTab k m) k m t xd = false by simpa using h) _
      exact (RunsWithin.ret _).of_eq (by simp [gstep, h])
    case hc => simp [Prim.cost]

theorem RunsWithin.goodLenProg (c : Array ℕ) (k m t : ℕ) (acc : List (List ℕ)) {l : ℕ}
    (hl : l ≤ k) :
    RunsWithin X body
      (SoJProg.goodLenProg c (pwTab k m) (List.range k) (List.range m) k m t acc l)
      ((tupList l m).foldl (gstep c k m t) acc) (tupsCost l m + m ^ l * (goodCost k m + 6)) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat)
    (b' := .list (.list .nat)) (cf := fun _ => goodCost k m + 5) (F := gstep c k m t)
    (f := fun acc' xd => SoJProg.goodStepProg c (pwTab k m) (List.range k) (List.range m) k t
      acc' xd) (tupList l m) acc fun acc' xd hxd => RunsWithin.goodStepProg c k m t acc'
        (by rw [length_of_mem_tupList hxd]; exact hl)
  rw [sum_map_const, length_tupList,
    show goodCost k m + 5 + 1 = goodCost k m + 6 from rfl] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.tupsProg l m)
    exact hfold
  case hc => omega

/-- **The options of the Design Lemma node, as a program.** -/
theorem RunsWithin.goodListProg (c : Array ℕ) (k m t : ℕ) :
    RunsWithin X body (SoJProg.goodListProg c k m t) (goodList c k m t) (goodListCost k m) := by
  have hstep : ∀ (acc : List (List ℕ)) (l : ℕ), l ∈ List.range k →
      RunsWithin X body
        (SoJProg.goodLenProg c (pwTab k m) (List.range k) (List.range m) k m t acc l)
        ((tupList l m).foldl (gstep c k m t) acc)
        (tupsBound k m + (m ^ k + 1) * (goodCost k m + 6)) := by
    intro acc l hl
    have hl' : l ≤ k := (List.mem_range.1 hl).le
    refine (RunsWithin.goodLenProg c k m t acc hl').mono ?_
    have := tupsCost_le (m := m) hl'
    have := Nat.mul_le_mul_right (goodCost k m + 6) (pow_le_pow_add_one (m := m) hl')
    omega
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.list .nat))
    (cf := fun _ => tupsBound k m + (m ^ k + 1) * (goodCost k m + 6))
    (F := fun acc l => (tupList l m).foldl (gstep c k m t) acc)
    (f := fun acc l => SoJProg.goodLenProg c (pwTab k m) (List.range k) (List.range m) k m t
      acc l) (List.range k) [] hstep
  rw [sum_map_const, List.length_range, ← List.foldl_flatMap] at hfold
  have hres : (List.range k).flatMap (fun l => tupList l m) = cands k m := rfl
  rw [hres, foldl_gstep, List.append_nil] at hfold
  have hlen : ((cands k m).filter (goodA c (pwTab k m) k m t)).reverse.length ≤
      k * (m ^ k + 1) := by
    rw [List.length_reverse]
    exact (List.length_filter_le _ _).trans (length_cands_le k m)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.pwTabProg k m)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, goodList])
  case hc =>
    simp only [Prim.cost, Args.head_cons, goodListCost]
    nlinarith

end GoodSpecs

/-! ### `dlCont`'s pieces on index lists -/

section Pieces

/-- The size of the class of `i` among `S` for the colouring `col`. -/
def clsCount (S : List ℕ) (col : ℕ → ℕ) (i : ℕ) : ℕ := (S.filter fun j => col j = col i).length

/-- Every class has at most `t` points. -/
def allSmallL (S : List ℕ) (col : ℕ → ℕ) (t : ℕ) : Bool :=
  S.all fun i => decide (clsCount S col i ≤ t)

/-- The points of classes of more than `t` points. -/
def bigL (S : List ℕ) (col : ℕ → ℕ) (t : ℕ) : List ℕ :=
  S.filter fun i => decide (t < clsCount S col i)

/-- `f` is constant on `C₁ × C₂`. -/
def constRectL (C₁ C₂ : List ℕ) (f : ℕ → ℕ → ℕ) : Bool :=
  match C₁, C₂ with
  | y₀ :: _, s₀ :: _ => C₁.all fun y => C₂.all fun s => f y s = f y₀ s₀
  | _, _ => true

/-- A third of `S` by colour (milestone 11's `selThird`, on an index list). -/
def selThirdL (S : List ℕ) (col : ℕ → ℕ) : List ℕ :=
  let cols := (S.map col).toFinset.sort (· ≤ ·)
  match cols.find? (fun k => decide (S.length < 3 * (S.filter fun i => col i = k).length)) with
  | some k => S.filter fun i => col i = k
  | none =>
    let m := ((List.range (cols.length + 1)).find? fun m =>
      decide (S.length < 3 * (S.filter fun i => col i ∈ cols.take m).length)).getD cols.length
    S.filter fun i => col i ∈ cols.take m

variable {β : Type*} [DecidableEq β]

/-- A decoding of an index list: no duplicates, injective on the list, carrying `col` to
`g`. -/
structure DecOK (S : List ℕ) (dec : ℕ → β) (col : ℕ → ℕ) (g : β → ℕ) : Prop where
  nodup : S.Nodup
  inj : ∀ i ∈ S, ∀ j ∈ S, dec i = dec j → i = j
  col : ∀ i ∈ S, g (dec i) = col i

variable {S : List ℕ} {dec : ℕ → β} {col : ℕ → ℕ} {g : β → ℕ}

omit [DecidableEq β] in
theorem DecOK.nodup_map (h : DecOK S dec col g) (P : ℕ → Prop) [DecidablePred P] :
    ((S.filter P).map dec).Nodup :=
  (h.nodup.filter P).map_on fun i hi j hj hij =>
    h.inj i (List.mem_of_mem_filter hi) j (List.mem_of_mem_filter hj) hij

theorem DecOK.filter_decode (h : DecOK S dec col g) (P : ℕ → Prop) [DecidablePred P] :
    ((S.map dec).toFinset.filter fun b => P (g b)) =
      ((S.filter fun i => P (col i)).map dec).toFinset := by
  ext b
  simp only [mem_filter, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hP⟩
    exact ⟨i, ⟨hi, by rwa [← h.col i hi]⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hP⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, by rwa [h.col i hi]⟩

theorem DecOK.card_filter (h : DecOK S dec col g) (P : ℕ → Prop) [DecidablePred P] :
    ((S.map dec).toFinset.filter fun b => P (g b)).card = (S.filter fun i => P (col i)).length := by
  rw [h.filter_decode, List.toFinset_card_of_nodup (h.nodup_map _), List.length_map]

theorem DecOK.card (h : DecOK S dec col g) : (S.map dec).toFinset.card = S.length := by
  have := h.card_filter (fun _ => True)
  simpa using this

theorem DecOK.image (h : DecOK S dec col g) :
    (S.map dec).toFinset.image g = (S.map col).toFinset := by
  ext k
  simp only [mem_image, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨b, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (h.col i hi).symm⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨dec i, ⟨i, hi, rfl⟩, h.col i hi⟩

/-- **Every class small**, decoded. -/
theorem allSmallL_iff (h : DecOK S dec col g) (t : ℕ) :
    allSmallL S col t = true ↔
      ∀ b ∈ (S.map dec).toFinset, ((S.map dec).toFinset.filter fun b' => g b' = g b).card ≤ t := by
  simp only [allSmallL, List.all_eq_true, decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  constructor
  · rintro hall b ⟨i, hi, rfl⟩
    rw [h.col i hi, h.card_filter (fun j => j = col i)]
    exact hall i hi
  · intro hall i hi
    have := hall (dec i) ⟨i, hi, rfl⟩
    rwa [h.col i hi, h.card_filter (fun j => j = col i)] at this

/-- **The points of large classes**, decoded. -/
theorem bigL_decode (h : DecOK S dec col g) (t : ℕ) :
    ((bigL S col t).map dec).toFinset =
      (S.map dec).toFinset.filter fun b =>
        t < ((S.map dec).toFinset.filter fun b' => g b' = g b).card := by
  ext b
  simp only [bigL, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq,
    mem_filter]
  constructor
  · rintro ⟨i, ⟨hi, ht⟩, rfl⟩
    refine ⟨⟨i, hi, rfl⟩, ?_⟩
    rw [h.col i hi, h.card_filter (fun j => j = col i)]
    exact ht
  · rintro ⟨⟨i, hi, rfl⟩, ht⟩
    refine ⟨i, ⟨hi, ?_⟩, rfl⟩
    rwa [h.col i hi, h.card_filter (fun j => j = col i)] at ht

/-- **A function constant on a rectangle**, decoded. -/
theorem constRectL_iff {β₁ β₂ : Type*} {C₁ C₂ : List ℕ} {dec₁ : ℕ → β₁} {dec₂ : ℕ → β₂}
    {f : ℕ → ℕ → ℕ} {F : β₁ → β₂ → ℕ} (hF : ∀ y ∈ C₁, ∀ s ∈ C₂, F (dec₁ y) (dec₂ s) = f y s) :
    constRectL C₁ C₂ f = true ↔
      ∀ y ∈ C₁.map dec₁, ∀ s ∈ C₂.map dec₂, ∀ y' ∈ C₁.map dec₁, ∀ s' ∈ C₂.map dec₂,
        F y s = F y' s' := by
  simp only [List.mem_map]
  rcases C₁ with _ | ⟨y₀, C₁'⟩
  · simp [constRectL]
  rcases C₂ with _ | ⟨s₀, C₂'⟩
  · simp [constRectL]
  simp only [constRectL, List.all_eq_true, decide_eq_true_eq]
  constructor
  · rintro hall _ ⟨y, hy, rfl⟩ _ ⟨s, hs, rfl⟩ _ ⟨y', hy', rfl⟩ _ ⟨s', hs', rfl⟩
    rw [hF y hy s hs, hF y' hy' s' hs', hall y hy s hs, hall y' hy' s' hs']
  · intro hall y hy s hs
    have := hall _ ⟨y, hy, rfl⟩ _ ⟨s, hs, rfl⟩ _ ⟨y₀, List.mem_cons_self, rfl⟩ _
      ⟨s₀, List.mem_cons_self, rfl⟩
    rwa [hF y hy s hs, hF y₀ List.mem_cons_self s₀ List.mem_cons_self] at this

/-- **`selThird`, decoded.** -/
theorem selThirdL_decode (h : DecOK S dec col g) :
    ((selThirdL S col).map dec).toFinset = selThird (S.map dec).toFinset g := by
  have hcols : ((S.map dec).toFinset.image g).sort (· ≤ ·) = (S.map col).toFinset.sort (· ≤ ·) := by
    rw [h.image]
  have hP : ∀ k,
      (S.map dec).toFinset.card < 3 * ((S.map dec).toFinset.filter fun x => g x = k).card ↔
      S.length < 3 * (S.filter fun i => col i = k).length := fun k => by
    rw [h.card, h.card_filter (fun j => j = k)]
  have hQ : ∀ (l : List ℕ), (S.map dec).toFinset.card <
      3 * ((S.map dec).toFinset.filter fun x => g x ∈ l).card ↔
      S.length < 3 * (S.filter fun i => col i ∈ l).length := fun l => by
    rw [h.card, h.card_filter (fun j => j ∈ l)]
  unfold selThird selThirdL
  simp only [hcols, hP, hQ]
  generalize (S.map col).toFinset.sort (· ≤ ·) = cols
  rcases hf : cols.find? (fun k => decide (S.length < 3 * (S.filter fun i => col i = k).length))
    with _ | k
  · exact (h.filter_decode _).symm
  · exact (h.filter_decode (fun j => j = k)).symm

end Pieces

/-! ### `dlCont`'s pieces as programs -/

section PieceProg

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The size of the class of `i` among `Sl`, colours read from `colA`. -/
def clsCountProg (Sl : var (.list .nat)) (colA : var (.array .nat)) (i : var .nat) :
    Prog S rec var .nat :=
  .bind (.op2 .arrayGet colA i) fun ci =>
  .bind (filterProg Sl fun j => .bind (.op2 .arrayGet colA j) fun cj => .op2 .natEq cj ci)
    fun f => .op1 .length f

/-- Every class has at most `t` points. -/
def allSmallProg (Sl : var (.list .nat)) (colA : var (.array .nat)) (t : var .nat) :
    Prog S rec var .bool :=
  allList Sl fun i => .bind (clsCountProg Sl colA i) fun n =>
    .bind (.op2 .natLt t n) fun big => .op1 .not big

/-- The points of classes of more than `t` points. -/
def bigProg (Sl : var (.list .nat)) (colA : var (.array .nat)) (t : var .nat) :
    Prog S rec var (.list .nat) :=
  filterProg Sl fun i => .bind (clsCountProg Sl colA i) fun n => .op2 .natLt t n

/-- A table of rows constant on `C₁ × C₂`. -/
def constRectProg (C₁ C₂ : var (.list .nat)) (fA : var (.array (.array .nat))) :
    Prog S rec var .bool :=
  .bind (.op0 (.boolLit true)) fun tt =>
  .caseList C₁ (.ret tt) fun y₀ _ => .caseList C₂ (.ret tt) fun s₀ _ =>
  .bind (get2Prog fA y₀ s₀) fun r =>
  allList C₁ fun y => allList C₂ fun s => .bind (get2Prog fA y s) fun v => .op2 .natEq v r

end PieceProg

section PieceSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.clsCountProg (Sl : List ℕ) (colA : Array ℕ) (i : ℕ) :
    RunsWithin X body (SoJProg.clsCountProg Sl colA i) (clsCount Sl (get colA) i)
      (7 * Sl.length + 4) := by
  set ci := Prim.eval (Prim.arrayGet (a := .nat)) (.cons colA (.cons i .nil)) with hci
  have hci' : ci = get colA i := by simp [hci, Prim.eval, Ty.default, get]
  set P : ℕ → Bool := fun j => Prim.eval Prim.natEq
    (.cons (Prim.eval (Prim.arrayGet (a := .nat)) (.cons colA (.cons j .nil))) (.cons ci .nil))
    with hP
  have hf := RunsWithin.filterProg (X := X) (body := body) (t := .nat) (xs := Sl) (c := 2)
    (p := fun j => .bind (.op2 .arrayGet colA j) fun cj => .op2 .natEq cj ci)
    (P := P) fun j _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
  have hlen := List.length_filter_le P Sl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hf
    refine (RunsWithin.prim _ _).of_eq ?_
    simp only [Prim.eval, clsCount, hP, hci']
    exact congrArg List.length (List.filter_congr fun x _ => by
      rw [Bool.eq_iff_iff]
      simp [Ty.default, get])
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    omega

theorem RunsWithin.allSmallProg (Sl : List ℕ) (colA : Array ℕ) (t : ℕ) :
    RunsWithin X body (SoJProg.allSmallProg Sl colA t) (allSmallL Sl (get colA) t)
      (Sl.length * (7 * Sl.length + 8) + 1) := by
  have h := RunsWithin.allList_le (X := X) (body := body) (a' := .nat) (xs := Sl)
    (c := 7 * Sl.length + 6)
    (p := fun i => .bind (SoJProg.clsCountProg Sl colA i) fun n =>
      .bind (.op2 .natLt t n) fun big => .op1 .not big)
    (P := fun i => !decide (t < clsCount Sl (get colA) i)) fun i _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.clsCountProg Sl colA i)
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
      case hc => simp [Prim.cost]
  refine h.of_eq ?_
  unfold allSmallL
  congr 1
  funext i
  rw [Bool.eq_iff_iff]
  simp

theorem RunsWithin.bigProg (Sl : List ℕ) (colA : Array ℕ) (t : ℕ) :
    RunsWithin X body (SoJProg.bigProg Sl colA t) (bigL Sl (get colA) t)
      (Sl.length * (7 * Sl.length + 9) + 2) := by
  have h := RunsWithin.filterProg (X := X) (body := body) (t := .nat) (xs := Sl)
    (c := 7 * Sl.length + 5)
    (p := fun i => .bind (SoJProg.clsCountProg Sl colA i) fun n => .op2 .natLt t n)
    (P := fun i => decide (t < clsCount Sl (get colA) i)) fun i _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.clsCountProg Sl colA i)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
      case hc => simp [Prim.cost]
  refine (h.of_eq rfl).mono ?_
  simp only [Nat.mul_add]
  omega

theorem RunsWithin.constRectProg (C₁ C₂ : List ℕ) (fA : Array (Array ℕ)) :
    RunsWithin X body (SoJProg.constRectProg C₁ C₂ fA) (constRectL C₁ C₂ (get2 fA))
      (C₁.length * (C₂.length * 5 + 3) + 8) := by
  rcases C₁ with _ | ⟨y₀, C₁'⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_nil _
      exact (RunsWithin.ret _).of_eq (by simp [Prim.eval, constRectL])
    case hc => simp [Prim.cost]
  rcases C₂ with _ | ⟨s₀, C₂'⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_cons _
      run_with RunsWithin.caseList_nil _
      exact (RunsWithin.ret _).of_eq (by simp [Prim.eval, constRectL])
    case hc => simp [Prim.cost]
  have hin : ∀ y, RunsWithin X body
      (Programs.allList (a' := .nat) (s₀ :: C₂') fun s =>
        .bind (get2Prog fA y s) fun v => .op2 .natEq v (get2 fA y₀ s₀))
      ((s₀ :: C₂').all fun s => decide (get2 fA y s = get2 fA y₀ s₀))
      ((C₂'.length + 1) * (3 + 2) + 1) := fun y => by
    refine RunsWithin.allList_le (a' := .nat) fun s _ => ?_
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.get2Prog fA y s)
      exact (RunsWithin.prim _ _).of_eq (by
        simp only [Prim.eval]
        rw [Bool.eq_iff_iff]
        simp)
    case hc => simp [Prim.cost]
  have hout := RunsWithin.allList_le (X := X) (body := body) (a' := .nat) (xs := y₀ :: C₁')
    (c := (C₂'.length + 1) * (3 + 2) + 1)
    (p := fun y => Programs.allList (a' := .nat) (s₀ :: C₂') fun s =>
        .bind (get2Prog fA y s) fun v => .op2 .natEq v (get2 fA y₀ s₀))
    (P := fun y => (s₀ :: C₂').all fun s => decide (get2 fA y s = get2 fA y₀ s₀))
    fun y _ => hin y
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.caseList_cons _
    run_with RunsWithin.caseList_cons _
    run_step (RunsWithin.get2Prog fA y₀ s₀)
    exact hout.of_eq (by simp [constRectL])
  case hc =>
    simp only [Prim.cost, List.length_cons]
    nlinarith

end PieceSpecs

/-! ### `selThird` as a program -/

section SelProg

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The first element satisfying a Boolean program. -/
def findProg {t : Ty} (l : var (.list t)) (p : var t → Prog S rec var .bool) :
    Prog S rec var (.option t) :=
  .bind (.op0 .none) fun nn => .foldList l nn fun st x =>
    .caseOption st (.bind (p x) fun c => .ite c (.op1 .some x) (.ret st)) fun _ => .ret st

/-- The first `m` elements. -/
def takeProg (l : var (.list .nat)) (m : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nl => .bind (.op2 .pair z nl) fun st₀ =>
  .bind (.foldList l st₀ fun st x => .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .natLt i m) fun lt =>
      .ite lt (.bind (.op2 .cons x acc) fun acc' => .bind (.op0 (.natLit 1)) fun one =>
        .bind (.op2 .add i one) fun i' => .op2 .pair i' acc') (.ret st)) fun st =>
  .bind (.op1 .snd st) fun acc => .op1 .reverse acc

/-- Membership of a number in a list. -/
def memProg (x : var .nat) (l : var (.list .nat)) : Prog S rec var .bool :=
  anyList l fun y => .op2 .natEq y x

/-- The points of `Sl` whose colour satisfies a test. -/
def colFilterProg (Sl : var (.list .nat)) (colA : var (.array .nat))
    (q : var .nat → Prog S rec var .bool) : Prog S rec var (.list .nat) :=
  filterProg Sl fun i => .bind (.op2 .arrayGet colA i) fun ci => q ci

/-- `n < 3 · |{i ∈ Sl | q (col i)}|`. -/
def thirdTestProg (n : var .nat) (Sl : var (.list .nat)) (colA : var (.array .nat))
    (q : var .nat → Prog S rec var .bool) : Prog S rec var .bool :=
  .bind (colFilterProg Sl colA q) fun f => .bind (.op1 .length f) fun c =>
  .bind (.op2 .add c c) fun c₂ => .bind (.op2 .add c₂ c) fun c₃ => .op2 .natLt n c₃

/-- **A third of `Sl` by colour** (`selThird`). -/
def selThirdProg (Sl : var (.list .nat)) (colA : var (.array .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (mapList Sl fun i => .op2 .arrayGet colA i) fun cl =>
  .bind (dedupSortProg cmpNatProg cl) fun cols =>
  .bind (.op1 .length Sl) fun n =>
  .bind (findProg cols fun k => thirdTestProg n Sl colA fun ci => .op2 .natEq ci k) fun fk =>
  .caseOption fk
    (.bind (.op1 .length cols) fun L => .bind (.op0 (.natLit 1)) fun one =>
      .bind (.op2 .add L one) fun L₁ => .bind (.op1 .range L₁) fun rL =>
      .bind (findProg rL fun m => .bind (takeProg cols m) fun tk =>
          thirdTestProg n Sl colA fun ci => memProg ci tk) fun fm =>
      .bind (.caseOption fm (.ret L) fun m => .ret m) fun m =>
      .bind (takeProg cols m) fun tk => colFilterProg Sl colA fun ci => memProg ci tk)
    fun k => colFilterProg Sl colA fun ci => .op2 .natEq ci k

end SelProg

/-- One step of `findProg`. -/
def fstep {α : Type} (P : α → Bool) (st : Option α) (x : α) : Option α :=
  match st with
  | none => if P x then some x else none
  | some y => some y

theorem foldl_fstep {α : Type} (P : α → Bool) (l : List α) :
    l.foldl (fstep P) none = l.find? P := by
  have hs : ∀ (l : List α) (y : α), l.foldl (fstep P) (some y) = some y := by
    intro l
    induction l with
    | nil => intro y; rfl
    | cons x l ih => intro y; exact ih y
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldl_cons, List.find?_cons]
    by_cases h : P x = true
    · rw [show fstep P none x = some x from ite_eq_left h, h]
      exact hs l x
    · rw [show fstep P none x = none from ite_eq_right h]
      simp only [Bool.not_eq_true] at h
      rw [h]
      exact ih

/-- One step of `takeProg`. -/
def tstep (m : ℕ) (st : ℕ × List ℕ) (x : ℕ) : ℕ × List ℕ :=
  if st.1 < m then (st.1 + 1, x :: st.2) else st

theorem foldl_tstep_stop (m i : ℕ) (hi : ¬ i < m) :
    ∀ (l acc : List ℕ), l.foldl (tstep m) (i, acc) = (i, acc)
  | [], _ => rfl
  | x :: l, acc => by
    rw [List.foldl_cons, show tstep m (i, acc) x = (i, acc) from ite_eq_right hi]
    exact foldl_tstep_stop m i hi l acc

theorem foldl_tstep (m : ℕ) :
    ∀ (l : List ℕ) (i : ℕ) (acc : List ℕ), i ≤ m →
      (l.foldl (tstep m) (i, acc)).2 = (l.take (m - i)).reverse ++ acc
  | [], i, acc, _ => by simp
  | x :: l, i, acc, hi => by
    rw [List.foldl_cons]
    by_cases h : i < m
    · rw [show tstep m (i, acc) x = (i + 1, x :: acc) from ite_eq_left h,
        foldl_tstep m l (i + 1) (x :: acc) h,
        show m - i = (m - (i + 1)) + 1 by omega, List.take_succ_cons, List.reverse_cons,
        List.append_assoc, List.singleton_append]
    · rw [show tstep m (i, acc) x = (i, acc) from ite_eq_right h, foldl_tstep_stop m i h,
        show m - i = 0 by omega]
      simp

section SelSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.findProg {t : Ty} (l : List t.denote)
    {p : t.denote → Prog S (a, b) Ty.denote .bool} {P : t.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ l, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (SoJProg.findProg l p) (l.find? P) (l.length * (c + 4) + 1) := by
  have hf := RunsWithin.foldList_of (X := X) (body := body) (F := fstep P)
    (cf := fun _ => c + 3)
    (f := fun st x => .caseOption st (.bind (p x) fun c => .ite c (.op1 .some x) (.ret st))
      fun _ => .ret st) l none fun st x hx => by
    rcases st with _ | y
    · rcases hP : P x
      · apply RunsWithin.mono
        case h =>
          run_with RunsWithin.caseOption_none _
          run_step (hp x hx)
          run_with RunsWithin.ite_neg hP _
          exact (RunsWithin.ret _).of_eq (by simp [fstep, hP])
        case hc => omega
      · apply RunsWithin.mono
        case h =>
          run_with RunsWithin.caseOption_none _
          run_step (hp x hx)
          run_with RunsWithin.ite_pos hP _
          exact (RunsWithin.prim _ _).of_eq (by simp [fstep, hP, Prim.eval])
        case hc => simp only [Prim.cost]; omega
    · apply RunsWithin.mono
      case h => exact RunsWithin.caseOption_some (RunsWithin.ret _)
      case hc => simp
  rw [foldl_fstep, sum_map_const] at hf
  have e : l.length * (c + 3 + 1) = l.length * (c + 4) := rfl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hf
  case hc => simp only [Prim.cost]; omega

theorem RunsWithin.takeProg (l : List ℕ) (m : ℕ) :
    RunsWithin X body (SoJProg.takeProg l m) (l.take m) (10 * l.length + 5) := by
  have hf := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list .nat)) (F := tstep m) (cf := fun _ => 8)
    (f := fun st x => .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .natLt i m) fun lt =>
      .ite lt (.bind (.op2 .cons x acc) fun acc' => .bind (.op0 (.natLit 1)) fun one =>
        .bind (.op2 .add i one) fun i' => .op2 .pair i' acc') (.ret st)) l (0, [])
    fun st x _ => by
      by_cases h : st.1 < m
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (by simp [Prim.eval, h]) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, tstep, h])
        case hc => simp [Prim.cost]
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (by simp [Prim.eval, h]) _
          exact (RunsWithin.ret _).of_eq (by simp [tstep, h])
        case hc => simp [Prim.cost]
  rw [sum_map_const] at hf
  have hres := foldl_tstep m l 0 [] (Nat.zero_le _)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hf
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    show (List.foldl (tstep m) (0, []) l).2.reverse = List.take m l
    rw [hres]
    simp
  case hc =>
    show 1 + (1 + (1 + (l.length * (8 + 1) + (1 + ((List.foldl (tstep m) (0, []) l).2.length
      + 1))))) ≤ 10 * l.length + 5
    rw [hres]
    simp only [List.append_nil, List.length_reverse, List.length_take]
    omega

theorem RunsWithin.memProg (x : ℕ) (l : List ℕ) :
    RunsWithin X body (SoJProg.memProg x l) (decide (x ∈ l)) (3 * l.length + 1) := by
  refine ((RunsWithin.anyList_le (a' := .nat) (P := fun y => decide (y = x)) (c := 1)
    fun y _ => (RunsWithin.prim _ _).of_eq ?_).of_eq ?_).mono (by omega)
  · rw [Bool.eq_iff_iff]
    simp [Prim.eval]
  · rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem RunsWithin.colFilterProg (Sl : List ℕ) (colA : Array ℕ)
    {q : ℕ → Prog S (a, b) Ty.denote .bool} {Q : ℕ → Bool} {c : ℕ}
    (hq : ∀ i ∈ Sl, RunsWithin X body (q (get colA i)) (Q (get colA i)) c) :
    RunsWithin X body (SoJProg.colFilterProg Sl colA q) (Sl.filter fun i => Q (get colA i))
      (Sl.length * (c + 5) + 2) :=
  RunsWithin.filterProg fun i hi => by
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim_le (v := get colA i) (by simp [Prim.eval, Ty.default, get])
        le_rfl)
      exact hq i hi
    case hc => simp only [Prim.cost]; omega

theorem RunsWithin.thirdTestProg (n : ℕ) (Sl : List ℕ) (colA : Array ℕ)
    {q : ℕ → Prog S (a, b) Ty.denote .bool} {Q : ℕ → Bool} {c : ℕ}
    (hq : ∀ i ∈ Sl, RunsWithin X body (q (get colA i)) (Q (get colA i)) c) :
    RunsWithin X body (SoJProg.thirdTestProg n Sl colA q)
      (decide (n < 3 * (Sl.filter fun i => Q (get colA i)).length)) (Sl.length * (c + 6) + 6) := by
  have hlen := List.length_filter_le (α := Ty.nat.denote) (fun i => Q (get colA i)) Sl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.colFilterProg Sl colA hq)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    have e3 : ∀ k : ℕ, k + k + k = 3 * k := fun k => by omega
    exact congrArg (fun k => decide (n < k)) (e3 _)
  case hc =>
    simp only [Prim.cost, Args.head_cons, Nat.mul_add]
    omega

end SelSpecs

/-- The cost bound of `selThirdProg` on `n` points. -/
def selThirdCost (n : ℕ) : ℕ := 100 * (n + 1) ^ 3

theorem length_sort_map_le (Sl : List ℕ) (col : ℕ → ℕ) :
    ((Sl.map col).toFinset.sort (· ≤ ·)).length ≤ Sl.length := by
  rw [Finset.length_sort]
  exact (List.toFinset_card_le _).trans (by simp)

section SelThirdSpec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.caseOption_getD (o : Option ℕ) (L : ℕ) :
    RunsWithin X body (Prog.caseOption (a := .nat) (t := .nat) o (.ret L) fun m => .ret m)
      (o.getD L) 1 := by
  rcases o with _ | m
  · exact (RunsWithin.caseOption_none (RunsWithin.ret _)).mono (by simp)
  · exact (RunsWithin.caseOption_some (RunsWithin.ret _)).mono (by simp)

/-- **`selThird`, as a program.** -/
theorem RunsWithin.selThirdProg (Sl : List ℕ) (colA : Array ℕ) :
    RunsWithin X body (SoJProg.selThirdProg Sl colA) (selThirdL Sl (get colA))
      (selThirdCost Sl.length) := by
  obtain ⟨cols, hcols⟩ : ∃ cols, cols = (Sl.map (get colA)).toFinset.sort (· ≤ ·) := ⟨_, rfl⟩
  have hL : cols.length ≤ Sl.length := hcols ▸ length_sort_map_le Sl (get colA)
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := Sl) (f := fun i => .op2 .arrayGet colA i) (F := get colA) (c := 1)
    fun i _ => RunsWithin.prim_le (by simp [Prim.eval, Ty.default, get]) le_rfl
  have hsort := RunsWithin.dedupSortProg (X := X) (body := body) (t := .nat)
    (cmp := fun x y => Coherent.cmpNatProg x y) (e := ord3) (fun _ _ => rfl) (ce := 5)
    (l := Sl.map (get colA)) fun x _ y => RunsWithin.cmpNatProg x y
  rw [List.length_map, ← hcols] at hsort
  have hfind1 := RunsWithin.findProg (X := X) (body := body) (t := .nat) cols
    (p := fun k => SoJProg.thirdTestProg Sl.length Sl colA fun ci => .op2 .natEq ci k)
    (P := fun k => decide (Sl.length < 3 * (Sl.filter fun i => decide (get colA i = k)).length))
    (c := Sl.length * (1 + 6) + 6) fun k _ => RunsWithin.thirdTestProg Sl.length Sl colA
      (Q := fun ci => decide (ci = k)) (c := 1) fun i _ =>
        (RunsWithin.prim _ _).of_eq (by rw [Bool.eq_iff_iff]; simp [Prim.eval])
  have hmem : ∀ m, ∀ i ∈ Sl, RunsWithin X body (SoJProg.memProg (get colA i) (cols.take m))
      (decide (get colA i ∈ cols.take m)) (3 * cols.length + 1) := fun m i _ =>
    (RunsWithin.memProg _ _).mono (by simp only [List.length_take]; omega)
  rcases hf : cols.find? (fun k =>
      decide (Sl.length < 3 * (Sl.filter fun i => decide (get colA i = k)).length)) with _ | k
  · have hfind2 := RunsWithin.findProg (X := X) (body := body) (t := .nat)
      (List.range (cols.length + 1))
      (p := fun m => .bind (SoJProg.takeProg cols m) fun tk =>
        SoJProg.thirdTestProg Sl.length Sl colA fun ci => SoJProg.memProg ci tk)
      (P := fun m => decide (Sl.length <
        3 * (Sl.filter fun i => decide (get colA i ∈ cols.take m)).length))
      (c := 10 * cols.length + 5 + (Sl.length * (3 * cols.length + 1 + 6) + 6))
      fun m _ => RunsWithin.step (RunsWithin.takeProg cols m)
        (RunsWithin.thirdTestProg Sl.length Sl colA
          (q := fun ci => SoJProg.memProg ci (cols.take m))
          (Q := fun ci => decide (ci ∈ cols.take m)) (hmem m))
    apply RunsWithin.mono
    case h =>
      run_step hmap
      run_step hsort
      run_step (RunsWithin.prim _ _)
      run_step hfind1
      rw [hf]
      run_with RunsWithin.caseOption_none _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfind2
      run_step (RunsWithin.caseOption_getD _ _)
      run_step (RunsWithin.takeProg cols _)
      refine (RunsWithin.colFilterProg Sl colA (q := fun ci => SoJProg.memProg ci (cols.take _))
        (Q := fun ci => decide (ci ∈ cols.take _)) (hmem _)).of_eq ?_
      simp only [selThirdL]
      rw [← hcols, hf]
      rfl
    case hc =>
      simp only [Prim.cost, Args.head_cons, Prim.eval, List.length_range, selThirdCost]
      generalize cols.length = L at hL ⊢
      generalize Sl.length = n at hL ⊢
      nlinarith [Nat.mul_le_mul hL hL, Nat.mul_le_mul (Nat.mul_le_mul hL hL) (le_refl n)]
  · apply RunsWithin.mono
    case h =>
      run_step hmap
      run_step hsort
      run_step (RunsWithin.prim _ _)
      run_step hfind1
      rw [hf]
      run_with RunsWithin.caseOption_some _
      refine (RunsWithin.colFilterProg Sl colA (Q := fun ci => decide (ci = k)) (c := 1)
        fun i _ => (RunsWithin.prim _ _).of_eq (by rw [Bool.eq_iff_iff]; simp [Prim.eval])).of_eq ?_
      simp only [selThirdL]
      rw [← hcols, hf]
    case hc =>
      simp only [Prim.cost, Args.head_cons, selThirdCost]
      generalize cols.length = L at hL ⊢
      generalize Sl.length = n at hL ⊢
      nlinarith [Nat.mul_le_mul hL hL, Nat.mul_le_mul (Nat.mul_le_mul hL hL) (le_refl n)]

end SelThirdSpec

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_goodStepProg {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)} {k₁ t₁ : var₁ .nat}
    {k₂ t₂ : var₂ .nat} {acc₁ : var₁ (.list (.list .nat))} {acc₂ : var₂ (.list (.list .nat))}
    {xd₁ : var₁ (.list .nat)} {xd₂ : var₂ (.list .nat)}
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hacc : ⟨.list (.list .nat), acc₁, acc₂⟩ ∈ Γ) (hxd : ⟨.list .nat, xd₁, xd₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (goodStepProg c₁ pw₁ rk₁ rm₁ k₁ t₁ acc₁ xd₁)
      (goodStepProg c₂ pw₂ rk₂ rm₂ k₂ t₂ acc₂ xd₂) := by
  unfold goodStepProg
  exact .bind (wf_goodProg hc hpw hrk hrm hk ht hxd) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .ite (by simp) (.prim _ (.cons (by simp [hxd]) (.cons (by simp [hacc]) .nil)))
      (.ret (by simp [hacc]))

theorem wf_goodLenProg {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)} {k₁ m₁ t₁ l₁ : var₁ .nat}
    {k₂ m₂ t₂ l₂ : var₂ .nat} {acc₁ : var₁ (.list (.list .nat))}
    {acc₂ : var₂ (.list (.list .nat))}
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hacc : ⟨.list (.list .nat), acc₁, acc₂⟩ ∈ Γ) (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (goodLenProg c₁ pw₁ rk₁ rm₁ k₁ m₁ t₁ acc₁ l₁)
      (goodLenProg c₂ pw₂ rk₂ rm₂ k₂ m₂ t₂ acc₂ l₂) := by
  unfold goodLenProg
  exact .bind (wf_tupsProg hl hm) fun _ _ => .foldList (by simp) (by simp [hacc])
    fun _ _ _ _ => wf_goodStepProg (by simp [hc]) (by simp [hpw]) (by simp [hrk])
      (by simp [hrm]) (by simp [hk]) (by simp [ht]) (by simp) (by simp)

theorem wf_goodListProg {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {k₁ m₁ t₁ : var₁ .nat} {k₂ m₂ t₂ : var₂ .nat} (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (goodListProg c₁ k₁ m₁ t₁) (goodListProg c₂ k₂ m₂ t₂) := by
  unfold goodListProg
  exact .bind (.prim _ (.cons hk .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_pwTabProg (by simp [hm]) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (.foldList (by simp) (by simp) fun _ _ _ _ => wf_goodLenProg (by simp [hc]) (by simp)
      (by simp) (by simp) (by simp [hk]) (by simp [hm]) (by simp [ht]) (by simp) (by simp))
      fun _ _ => .prim _ (.cons (by simp) .nil)

theorem wf_clsCountProg {S₁ : var₁ (.list .nat)} {S₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)} {i₁ : var₁ .nat} {i₂ : var₂ .nat}
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (clsCountProg S₁ colA₁ i₁) (clsCountProg S₂ colA₂ i₂) := by
  unfold clsCountProg
  refine .bind (.prim _ (.cons hcolA (.cons hi .nil))) fun _ _ =>
    .bind (wf_filterProg (by simp [hS]) fun Γ' hΓ j₁ j₂ hj => ?_) fun _ _ =>
      .prim _ (.cons (by simp) .nil)
  have := hΓ List.mem_cons_self
  have := hΓ (List.mem_cons_of_mem _ hcolA)
  prog_wf

theorem wf_allSmallProg {S₁ : var₁ (.list .nat)} {S₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)} {t₁ : var₁ .nat} {t₂ : var₂ .nat}
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (allSmallProg S₁ colA₁ t₁) (allSmallProg S₂ colA₂ t₂) := by
  unfold allSmallProg
  refine wf_allList hS fun Γ' hΓ i₁ i₂ hi => ?_
  exact .bind (wf_clsCountProg (hΓ hS) (hΓ hcolA) hi) fun _ _ =>
    .bind (.prim _ (.cons (List.mem_cons_of_mem _ (hΓ ht)) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) .nil)

theorem wf_bigProg {S₁ : var₁ (.list .nat)} {S₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)} {t₁ : var₁ .nat} {t₂ : var₂ .nat}
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (bigProg S₁ colA₁ t₁) (bigProg S₂ colA₂ t₂) := by
  unfold bigProg
  refine wf_filterProg hS fun Γ' hΓ i₁ i₂ hi => ?_
  exact .bind (wf_clsCountProg (hΓ hS) (hΓ hcolA) hi) fun _ _ =>
    .prim _ (.cons (List.mem_cons_of_mem _ (hΓ ht)) (.cons (by simp) .nil))

theorem wf_constRectProg {C₁ D₁ : var₁ (.list .nat)} {C₂ D₂ : var₂ (.list .nat)}
    {fA₁ : var₁ (.array (.array .nat))} {fA₂ : var₂ (.array (.array .nat))}
    (hC : ⟨.list .nat, C₁, C₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hfA : ⟨.array (.array .nat), fA₁, fA₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (constRectProg C₁ D₁ fA₁) (constRectProg C₂ D₂ fA₂) := by
  unfold constRectProg get2Prog allList
  prog_wf

theorem wf_findProg {t : Ty} {l₁ : var₁ (.list t)} {l₂ : var₂ (.list t)}
    {p₁ : var₁ t → Prog S rec var₁ .bool} {p₂ : var₂ t → Prog S rec var₂ .bool}
    (hl : ⟨.list t, l₁, l₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (findProg l₁ p₁) (findProg l₂ p₂) := by
  unfold findProg
  prog_wf
  all_goals exact hp _ (fun y hy => by simp [hy]) _ _ (by simp)

theorem wf_takeProg {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)} {m₁ : var₁ .nat}
    {m₂ : var₂ .nat} (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (takeProg l₁ m₁) (takeProg l₂ m₂) := by
  unfold takeProg
  prog_wf

theorem wf_memProg {x₁ : var₁ .nat} {x₂ : var₂ .nat} {l₁ : var₁ (.list .nat)}
    {l₂ : var₂ (.list .nat)} (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (memProg x₁ l₁) (memProg x₂ l₂) := by
  unfold memProg
  exact wf_anyList hl fun Γ' hΓ y₁ y₂ hy => .prim _ (.cons hy (.cons (hΓ hx) .nil))

theorem wf_colFilterProg {S₁ : var₁ (.list .nat)} {S₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)}
    {q₁ : var₁ .nat → Prog S rec var₁ .bool} {q₂ : var₂ .nat → Prog S rec var₂ .bool}
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (hq : WfFun r Γ q₁ q₂) :
    Prog.Wf r Γ (colFilterProg S₁ colA₁ q₁) (colFilterProg S₂ colA₂ q₂) := by
  unfold colFilterProg
  exact wf_filterProg hS fun Γ' hΓ i₁ i₂ hi => .bind (.prim _ (.cons (hΓ hcolA) (.cons hi .nil)))
    fun _ _ => hq _ (fun y hy => List.mem_cons_of_mem _ (hΓ hy)) _ _ List.mem_cons_self

theorem wf_thirdTestProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {S₁ : var₁ (.list .nat)}
    {S₂ : var₂ (.list .nat)} {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)}
    {q₁ : var₁ .nat → Prog S rec var₁ .bool} {q₂ : var₂ .nat → Prog S rec var₂ .bool}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ)
    (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ) (hq : WfFun r Γ q₁ q₂) :
    Prog.Wf r Γ (thirdTestProg n₁ S₁ colA₁ q₁) (thirdTestProg n₂ S₂ colA₂ q₂) := by
  unfold thirdTestProg
  refine .bind (wf_colFilterProg hS hcolA hq) fun _ _ => ?_
  prog_wf

theorem wf_selThirdProg {S₁ : var₁ (.list .nat)} {S₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)}
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (selThirdProg S₁ colA₁) (selThirdProg S₂ colA₂) := by
  unfold selThirdProg
  refine .bind (wf_mapList hS fun Γ' hΓ i₁ i₂ hi =>
      .prim _ (.cons (hΓ hcolA) (.cons hi .nil))) fun _ _ =>
    .bind (wf_dedupSortProg wfCmp_cmpNat (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hS]) .nil)) fun _ _ =>
    .bind (wf_findProg (by simp) fun Γ' hΓ k₁ k₂ hk =>
      wf_thirdTestProg (hΓ (by simp)) (hΓ (by simp [hS])) (hΓ (by simp [hcolA]))
        fun Γ'' hΓ' c₁ c₂ hc => .prim _ (.cons hc (.cons (hΓ' hk) .nil))) fun _ _ =>
    .caseOption (by simp) ?_ fun _ _ => wf_colFilterProg (by simp [hS]) (by simp [hcolA])
      fun Γ' hΓ c₁ c₂ hc => .prim _ (.cons hc (.cons (hΓ (by simp)) .nil))
  exact .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_findProg (by simp) fun Γ' hΓ m₁ m₂ hm =>
      .bind (wf_takeProg (hΓ (by simp)) hm) fun _ _ =>
      wf_thirdTestProg (List.mem_cons_of_mem _ (hΓ (by simp)))
        (List.mem_cons_of_mem _ (hΓ (by simp [hS])))
        (List.mem_cons_of_mem _ (hΓ (by simp [hcolA])))
        fun Γ'' hΓ' c₁ c₂ hc => wf_memProg hc (hΓ' List.mem_cons_self)) fun _ _ =>
    .bind (.caseOption (by simp) (.ret (by simp)) fun _ _ => .ret (by simp)) fun _ _ =>
    .bind (wf_takeProg (by simp) (by simp)) fun _ _ =>
    wf_colFilterProg (by simp [hS]) (by simp [hcolA])
      fun Γ' hΓ c₁ c₂ hc => wf_memProg hc (hΓ (by simp))

end Wf

end GraphIso.SoJProg
