module

public import GraphIso.Toolkit.Base
public import GraphIso.Recursion.Coarsen
public import GraphIso.Programs.List
public import GraphIso.Reductions.RestrictionData

/-!
# Label programs

The label coarsenings of stage 14a (`GraphIso/Recursion/Coarsen.lean`) as costed programs on
data (`PLAN-14.md` §6 item 3). A label is a list of base indices (`LabelData`, one list per
position). Each program has a model function, an explicit cost (polynomial in the label sizes
and the base) and a `RunsWithin` spec; each model is linked to the stage 14a definition it
computes.

* `filterList`, `countList`: generic filtering and counting over lists.
* `markArr k L`: the Boolean mask of the entries of `L` below `k` (`getB_markArr`).
* **M1** `interLab pos mask L`: the label intersected with a set of base points `pts` (given by
  its mask) and renumbered by positions in `pts` (`mem_interLab`); `mem_subLab_iff_interLab`
  links it to `subLab`.
* **M2a** `blockCounts`, `blockLab k bidx L`: the block label for the block system given by a
  block-index array (`mem_blockLab_iff`, linked to `blockLabel`); `equidistB` decides
  `Equidist` (`equidistB_iff`).
* **M2b**: the intersection with one block is `interLab` for the block's points.
* **Johnson union** `jUnionData nc v0 fcell L`: the cells met by the label inside `V₀`
  (`mem_jUnionData_iff`, linked to `jUnion`).
* `complLab m L`: the complement within the base (`mem_complLab`).
* `mapLabels L w F`: apply a label map at every window point (`getD_mapLabels`).
* **Lengths** `labLen L`: the largest length of a label (stage 14j-6a). A label map at a window
  keeps the other labels (`labLen_mapLabels_le`); `interLab`, filters and `blockLab` do not
  lengthen a label (`labLen_mapLabels_short`, `length_blockLab_le`).
-/

@[expose] public section

namespace GraphIso.Toolkit

open Equiv Cost GraphIso.Programs GraphIso.Recursion

/-! ### Generic combinators -/

section Combinators

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Keep the elements of a list for which a Boolean program returns `true`. -/
def filterList {a' : Ty} (xs : var (.list a')) (p : var a' → Prog S rec var .bool) :
    Prog S rec var (.list a') :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList xs nil fun acc x =>
      .bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc)) fun racc =>
  .op1 .reverse racc

/-- Count the elements of a list for which a Boolean program returns `true`. -/
def countList {a' : Ty} (xs : var (.list a')) (p : var a' → Prog S rec var .bool) :
    Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z =>
  .foldList xs z fun acc x =>
    .bind (p x) fun c => .ite c (.bind (.op0 (.natLit 1)) fun one => .op2 .add acc one)
      (.ret acc)

end Combinators

theorem foldl_filter_cons {α : Type*} (P : α → Bool) :
    ∀ (xs acc : List α),
      xs.foldl (fun acc x => if P x then x :: acc else acc) acc = (xs.filter P).reverse ++ acc
  | [], acc => rfl
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_filter_cons P xs, List.filter_cons]
    by_cases h : P x <;> simp [h]

theorem foldl_count_add {α : Type*} (P : α → Bool) :
    ∀ (xs : List α) (acc : ℕ),
      xs.foldl (fun acc x => if P x then acc + 1 else acc) acc = acc + (xs.filter P).length
  | [], acc => rfl
  | x :: xs, acc => by
    rw [List.foldl_cons, foldl_count_add P xs, List.filter_cons]
    by_cases h : P x
    · simp [h]
      omega
    · simp [h]

section CombinatorSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.filterList {a' : Ty} {xs : List a'.denote}
    {p : a'.denote → Prog S (a, b) Ty.denote .bool} {P : a'.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (Toolkit.filterList xs p) (xs.filter P) (xs.length * (c + 4) + 3) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (I := fun _ => True)
    (c := c + 2)
    (f := fun (acc : (Ty.list a').denote) (x : a'.denote) =>
      Prog.bind (p x) fun c => Prog.ite c (.op2 .cons x acc) (.ret acc))
    (F := fun acc x => if P x then x :: acc else acc) xs [] (fun acc _ x hx => by
      refine ⟨?_, trivial⟩
      refine RunsWithin.bind_le (hp x hx) ?_ (le_refl _)
      by_cases h : P x
      · simp only [h, ↓reduceIte]
        exact (RunsWithin.ite_true (RunsWithin.prim _ _)).mono (by simp [Prim.cost])
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        exact (RunsWithin.ite_false (RunsWithin.ret _)).mono (by omega)) trivial
  rw [foldl_filter_cons, List.append_nil] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
  case hc =>
    have hle : (xs.filter P).length ≤ xs.length := List.length_filter_le _ _
    simp only [Prim.cost, Args.head_cons, List.length_reverse]
    have e : xs.length * (c + 4) = xs.length * (c + 2 + 1) + xs.length := by
      rw [show c + 4 = c + 2 + 1 + 1 by omega, Nat.mul_succ]
    omega

theorem RunsWithin.countList {a' : Ty} {xs : List a'.denote}
    {p : a'.denote → Prog S (a, b) Ty.denote .bool} {P : a'.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (Toolkit.countList xs p) (xs.filter P).length (xs.length * (c + 4) + 1) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (I := fun _ => True)
    (c := c + 3)
    (f := fun (acc : Ty.nat.denote) (x : a'.denote) =>
      Prog.bind (p x) fun c =>
        Prog.ite c (.bind (.op0 (.natLit 1)) fun one => .op2 .add acc one) (.ret acc))
    (F := fun acc x => if P x then acc + 1 else acc) xs 0 (fun acc _ x hx => by
      refine ⟨?_, trivial⟩
      refine RunsWithin.bind_le (hp x hx) ?_ (le_refl _)
      by_cases h : P x
      · simp only [h, ↓reduceIte]
        exact (RunsWithin.ite_true ((RunsWithin.prim _ _).bind (RunsWithin.prim _ _))).mono
          (by simp [Prim.cost])
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        exact (RunsWithin.ite_false (RunsWithin.ret _)).mono (by omega)) trivial
  rw [foldl_count_add, Nat.zero_add] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold.1
  case hc =>
    simp only [Prim.cost]
    rw [show c + 4 = c + 3 + 1 by omega]
    omega

end CombinatorSpecs

/-! ### Models -/

section Models

/-- The writes marking the entries of `L`. -/
def markWrites (L : List ℕ) : List (ℕ × Bool) := L.map fun j => (j, true)

/-- The Boolean mask of the entries of `L` below `k`. -/
def markArr (k : ℕ) (L : List ℕ) : Array Bool :=
  Prim.applyWrites (a := .bool) (Array.replicate k false) (markWrites L)

theorem getB_applyWrites_true (arr : Array Bool) (L : List ℕ) (j : ℕ) :
    getB (Prim.applyWrites (a := .bool) arr (markWrites L)) j = true ↔
      (j < arr.size ∧ j ∈ L) ∨ getB arr j = true := by
  induction L generalizing arr with
  | nil => simp [markWrites, Prim.applyWrites]
  | cons i L ih =>
    have e : Prim.applyWrites (a := .bool) arr (markWrites (i :: L)) =
        Prim.applyWrites (a := .bool) (arr.setIfInBounds i true) (markWrites L) := rfl
    rw [e, ih, Array.size_setIfInBounds]
    have hset : getB (arr.setIfInBounds i true) j = true ↔
        (j = i ∧ j < arr.size) ∨ getB arr j = true := by
      simp only [getB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
      split_ifs with h₁ h₂
      · subst h₁
        simp [h₂]
      · subst h₁
        rw [Array.getElem?_eq_none (Nat.le_of_not_lt h₂)]
        simp [h₂]
      · simp [Ne.symm h₁]
    rw [hset]
    simp only [List.mem_cons]
    tauto

/-- **The mask**: `j` is marked exactly when `j < k` and `j ∈ L`. -/
theorem getB_markArr (k : ℕ) (L : List ℕ) (j : ℕ) :
    getB (markArr k L) j = true ↔ j < k ∧ j ∈ L := by
  rw [markArr, getB_applyWrites_true]
  simp only [Array.size_replicate, getB, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split_ifs <;> simp

/-- **M1**: the label `L` intersected with the points marked in `mask`, renumbered by `pos`. -/
def interLab (pos : Array ℕ) (mask : Array Bool) (L : List ℕ) : List ℕ :=
  (L.filter (getB mask)).map fun j => get pos j

/-- **The renumbered intersection.** If `mask` marks exactly the points of `pts` and `pos`
gives their positions in `pts`, position `i` is in the result exactly when `pts[i] ∈ L`. -/
theorem mem_interLab {pts : List ℕ} {pos : Array ℕ} {mask : Array Bool}
    (hpos : ∀ i (h : i < pts.length), get pos pts[i] = i)
    (hmask : ∀ j, getB mask j = true ↔ j ∈ pts) (L : List ℕ) (i : ℕ) :
    i ∈ interLab pos mask L ↔ ∃ h : i < pts.length, pts[i] ∈ L := by
  simp only [interLab, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨j, ⟨hjL, hjm⟩, rfl⟩
    obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ((hmask j).1 hjm)
    rw [hpos i' hi']
    exact ⟨hi', hjL⟩
  · rintro ⟨hi, hL⟩
    exact ⟨pts[i], ⟨hL, (hmask _).2 (List.getElem_mem hi)⟩, hpos i hi⟩

/-- **Link to stage 14a's `subLab`**: for the base points `Γ'` listed in `pts`, a point of `Γ'`
lies in `subLab Γ' T` exactly when its position lies in `interLab`. -/
theorem mem_subLab_iff_interLab {m : ℕ} {pts : List ℕ} {pos : Array ℕ} {mask : Array Bool}
    (hpos : ∀ i (h : i < pts.length), get pos pts[i] = i)
    (hmask : ∀ j, getB mask j = true ↔ j ∈ pts) {L : List ℕ} {T : Finset (Fin m)}
    (hT : ∀ x : Fin m, x ∈ T ↔ x.val ∈ L)
    (x : ↥(Finset.univ.filter fun y : Fin m => y.val ∈ pts)) :
    x ∈ subLab _ T ↔ get pos x.1.val ∈ interLab pos mask L := by
  rw [mem_subLab, hT, mem_interLab hpos hmask]
  have hx : x.1.val ∈ pts := (Finset.mem_filter.1 x.2).2
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hx
  rw [← he, hpos i hi]
  exact ⟨fun h => ⟨hi, h⟩, fun ⟨_, h⟩ => h⟩

/-- The number of points of `L` in block `i`. -/
def blockCount (bidx : Array ℕ) (L : List ℕ) (i : ℕ) : ℕ :=
  (L.filter fun j => get bidx j == i).length

/-- The block counts of `L` for blocks `0, …, k - 1`. -/
def blockCounts (k : ℕ) (bidx : Array ℕ) (L : List ℕ) : List ℕ :=
  (List.range k).map (blockCount bidx L)

/-- The least entry of a list (`0` for the empty list). -/
def minCount : List ℕ → ℕ
  | [] => 0
  | c :: cs => (c :: cs).foldl (fun acc d => if d < acc then d else acc) c

theorem foldl_min_le (cs : List ℕ) :
    ∀ a, (cs.foldl (fun acc d => if d < acc then d else acc) a ≤ a ∧
      ∀ d ∈ cs, cs.foldl (fun acc d => if d < acc then d else acc) a ≤ d) ∧
      (cs.foldl (fun acc d => if d < acc then d else acc) a = a ∨
        cs.foldl (fun acc d => if d < acc then d else acc) a ∈ cs) := by
  induction cs with
  | nil => intro a; simp
  | cons d cs ih =>
    intro a
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp]
    by_cases hd : d < a
    · simp only [hd, ↓reduceIte]
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := ih d
      refine ⟨⟨by omega, h₁, h₂⟩, ?_⟩
      rcases h₃ with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · simp only [hd, ↓reduceIte]
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := ih a
      refine ⟨⟨h₁, by omega, h₂⟩, ?_⟩
      rcases h₃ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem minCount_le {cs : List ℕ} {d : ℕ} (hd : d ∈ cs) : minCount cs ≤ d := by
  cases cs with
  | nil => simp at hd
  | cons c cs => exact ((foldl_min_le (c :: cs) c).1.2 d hd)

theorem minCount_mem {cs : List ℕ} (h : cs ≠ []) : minCount cs ∈ cs := by
  cases cs with
  | nil => exact absurd rfl h
  | cons c cs =>
    rcases (foldl_min_le (c :: cs) c).2 with h' | h'
    · simp only [minCount]
      rw [h']
      exact List.mem_cons_self
    · exact h'

/-- **M2a**: the block label of `L` (block indices): the blocks it meets, or, if it meets
every block, those of least intersection. -/
def blockLab (k : ℕ) (bidx : Array ℕ) (L : List ℕ) : List ℕ :=
  if (blockCounts k bidx L).all fun c => decide (0 < c) then
    (List.range k).filter fun i => blockCount bidx L i == minCount (blockCounts k bidx L)
  else (List.range k).filter fun i => decide (0 < blockCount bidx L i)

/-- `L` meets every block in the same number of points. -/
def equidistB (k : ℕ) (bidx : Array ℕ) (L : List ℕ) : Bool :=
  (blockCounts k bidx L).all fun c => c == (blockCounts k bidx L).headD 0

/-- **The Johnson union** as data: the cells (indices below `nc`) of the points of `L` marked
in `v0`. -/
def jUnionData (nc : ℕ) (v0 : Array Bool) (fcell : Array (List ℕ)) (L : List ℕ) : List ℕ :=
  (List.range nc).filter (getB (markArr nc ((L.filter (getB v0)).foldl
      (fun acc j => fcell.getD j [] ++ acc) [])))

theorem mem_foldl_append (fcell : Array (List ℕ)) :
    ∀ (L acc : List ℕ) (c : ℕ),
      c ∈ L.foldl (fun acc j => fcell.getD j [] ++ acc) acc ↔
        c ∈ acc ∨ ∃ j ∈ L, c ∈ fcell.getD j []
  | [], acc, c => by simp
  | j :: L, acc, c => by
    rw [List.foldl_cons, mem_foldl_append fcell L, List.mem_append]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem mem_jUnionData (nc : ℕ) (v0 : Array Bool) (fcell : Array (List ℕ)) (L : List ℕ)
    (c : ℕ) :
    c ∈ jUnionData nc v0 fcell L ↔
      c < nc ∧ ∃ j ∈ L, getB v0 j = true ∧ c ∈ fcell.getD j [] := by
  simp only [jUnionData, List.mem_filter, List.mem_range, getB_markArr, mem_foldl_append,
    List.not_mem_nil, false_or, List.mem_filter]
  constructor
  · rintro ⟨hc, -, j, ⟨hj, hv⟩, hcj⟩
    exact ⟨hc, j, hj, hv, hcj⟩
  · rintro ⟨hc, j, hj, hv, hcj⟩
    exact ⟨hc, hc, j, ⟨hj, hv⟩, hcj⟩

/-- The complement of `L` within the base `0, …, m - 1`. -/
def complLab (m : ℕ) (L : List ℕ) : List ℕ :=
  (List.range m).filter fun j => !getB (markArr m L) j

theorem mem_complLab (m : ℕ) (L : List ℕ) (j : ℕ) : j ∈ complLab m L ↔ j < m ∧ j ∉ L := by
  simp only [complLab, List.mem_filter, List.mem_range, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, getB_markArr, not_and]
  constructor
  · rintro ⟨hj, h⟩
    exact ⟨hj, h hj⟩
  · rintro ⟨hj, h⟩
    exact ⟨hj, fun _ => h⟩

/-- Apply a label map at every point of `w`. -/
def mapLabels (L : LabelData) (w : List ℕ) (F : List ℕ → List ℕ) : LabelData :=
  Prim.applyWrites (a := .list .nat) L (w.map fun i => (i, F (L.getD i [])))

theorem size_mapLabels (L : LabelData) (w : List ℕ) (F : List ℕ → List ℕ) :
    (mapLabels L w F).size = L.size :=
  size_applyWrites _ _

theorem getD_mapLabels {L : LabelData} {w : List ℕ} (hw : w.Nodup) (F : List ℕ → List ℕ)
    (i : ℕ) :
    (mapLabels L w F).getD i [] = if i ∈ w ∧ i < L.size then F (L.getD i []) else L.getD i [] := by
  simp only [Array.getD_eq_getD_getElem?]
  by_cases h : i ∈ w ∧ i < L.size
  · rw [if_pos' h, mapLabels, getElem?_applyWrites_of_mem (a := .list .nat) L
      (by simpa [List.map_map, Function.comp_def] using hw) (List.mem_map.2 ⟨i, h.1, rfl⟩) h.2]
    simp [Array.getD_eq_getD_getElem?]
  · rw [if_neg' h]
    by_cases hi : i ∈ w
    · have hs : ¬ i < L.size := fun hl => h ⟨hi, hl⟩
      have hs' : ¬ i < (mapLabels L w F).size := by rwa [size_mapLabels]
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt hs'),
        Array.getElem?_eq_none (Nat.le_of_not_lt hs)]
    · rw [mapLabels, getElem?_applyWrites_of_not_mem (a := .list .nat) L (by simpa using hi)]

end Models

/-! ### Label lengths

Stage 14j-6a (`PLAN-14.md` §14.10): `labLen L`, the largest length of the lists of `L`, which
the label invariant of the recursion bounds, and its behaviour under the label maps. -/

section Lengths

/-- **The label length** of `L`: the largest length of its lists, `0` for the empty array. -/
def labLen (L : LabelData) : ℕ := L.toList.foldr (fun l a => max l.length a) 0

theorem foldr_maxLen_le_iff {ls : List (List ℕ)} {t : ℕ} :
    ls.foldr (fun l a => max l.length a) 0 ≤ t ↔ ∀ l ∈ ls, l.length ≤ t := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.foldr_cons, max_le_iff, ih, List.mem_cons, forall_eq_or_imp]

theorem labLen_le_iff {L : LabelData} {t : ℕ} : labLen L ≤ t ↔ ∀ l ∈ L.toList, l.length ≤ t :=
  foldr_maxLen_le_iff

theorem length_le_labLen {L : LabelData} {l : List ℕ} (h : l ∈ L.toList) : l.length ≤ labLen L :=
  labLen_le_iff.1 le_rfl l h

/-- Every label has length at most `labLen L`. -/
theorem length_getD_le_labLen (L : LabelData) (i : ℕ) : (L.getD i []).length ≤ labLen L := by
  by_cases h : i < L.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]
    exact length_le_labLen (Array.getElem_mem_toList h)
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.le_of_not_lt h)]
    exact Nat.zero_le _

/-- **`labLen` from the entries.** -/
theorem labLen_le_of_getD {L : LabelData} {t : ℕ} (h : ∀ i < L.size, (L.getD i []).length ≤ t) :
    labLen L ≤ t := by
  refine labLen_le_iff.2 fun l hl => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
  have hi' : i < L.size := by simpa using hi
  have := h i hi'
  rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi', Option.getD_some,
    ← Array.getElem_toList] at this

/-- **A label map at the points of a window**: entries off the window keep their length. -/
theorem labLen_mapLabels_le {L : LabelData} {w : List ℕ} (hw : w.Nodup) {F : List ℕ → List ℕ}
    {t : ℕ} (hL : labLen L ≤ t) (hF : ∀ i ∈ w, (F (L.getD i [])).length ≤ t) :
    labLen (mapLabels L w F) ≤ t := by
  refine labLen_le_of_getD fun i _ => ?_
  rw [getD_mapLabels hw]
  split_ifs with h
  · exact hF i h.1
  · exact (length_getD_le_labLen L i).trans hL

/-- **A shortening label map** does not lengthen the labels. -/
theorem labLen_mapLabels_short {L : LabelData} {w : List ℕ} (hw : w.Nodup)
    {F : List ℕ → List ℕ} (hF : ∀ l, (F l).length ≤ l.length) :
    labLen (mapLabels L w F) ≤ labLen L :=
  labLen_mapLabels_le hw le_rfl fun i _ => (hF _).trans (length_getD_le_labLen L i)

theorem length_interLab_le (pos : Array ℕ) (mask : Array Bool) (l : List ℕ) :
    (interLab pos mask l).length ≤ l.length := by
  rw [interLab, List.length_map]
  exact List.length_filter_le _ _

/-- The blocks met by a label are at most its points. -/
theorem length_filter_pos_blockCount_le (k : ℕ) (bidx : Array ℕ) (l : List ℕ) :
    ((List.range k).filter fun i => decide (0 < blockCount bidx l i)).length ≤ l.length := by
  have hnd : ((List.range k).filter fun i => decide (0 < blockCount bidx l i)).Nodup :=
    List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnd]
  calc _ ≤ (l.map fun j => get bidx j).toFinset.card := by
        apply Finset.card_le_card
        intro i hi
        simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi
        obtain ⟨j, hj⟩ := List.exists_mem_of_length_pos hi.2
        simp only [List.mem_filter, beq_iff_eq] at hj
        exact List.mem_toFinset.2 (List.mem_map.2 ⟨j, hj.1, hj.2⟩)
    _ ≤ (l.map fun j => get bidx j).length := List.toFinset_card_le _
    _ = l.length := List.length_map _

/-- **A block label** has at most as many blocks as the label has points: every block it keeps
meets the label. -/
theorem length_blockLab_le (k : ℕ) (bidx : Array ℕ) (l : List ℕ) :
    (blockLab k bidx l).length ≤ l.length := by
  refine le_trans ?_ (length_filter_pos_blockCount_le k bidx l)
  unfold blockLab
  split_ifs with h
  · rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    refine List.countP_mono_left fun i hi _ => ?_
    have hall := List.all_eq_true.1 h (blockCount bidx l i)
      (List.mem_map.2 ⟨i, hi, rfl⟩)
    exact hall
  · exact le_rfl

end Lengths

/-! ### Links to stage 14a -/

section Links

variable {m : ℕ}

/-- Block `i` of the block-index array, as a set of base points. -/
def blockSet (m : ℕ) (bidx : Array ℕ) (i : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun x => get bidx x.val = i

/-- The blocks `0, …, k - 1` of the block-index array. -/
def blockFamily (m k : ℕ) (bidx : Array ℕ) : Finset (Finset (Fin m)) :=
  (Finset.range k).image (blockSet m bidx)

/-- The intersection of the label with block `i` has `blockCount` points. -/
theorem card_inter_blockSet {bidx : Array ℕ} {L : List ℕ} {T : Finset (Fin m)} (hL : L.Nodup)
    (hT : ∀ x : Fin m, x ∈ T ↔ x.val ∈ L) (hLm : ∀ j ∈ L, j < m) (i : ℕ) :
    (T ∩ blockSet m bidx i).card = blockCount bidx L i := by
  have e : (T ∩ blockSet m bidx i).map Fin.valEmbedding =
      (L.filter fun j => get bidx j == i).toFinset := by
    ext y
    simp only [Finset.mem_map, Finset.mem_inter, blockSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.valEmbedding_apply, List.mem_toFinset, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨x, ⟨hxT, hxb⟩, rfl⟩
      exact ⟨(hT x).1 hxT, hxb⟩
    · rintro ⟨hyL, hyb⟩
      exact ⟨⟨y, hLm y hyL⟩, ⟨(hT _).2 hyL, hyb⟩, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, List.toFinset_card_of_nodup (hL.filter _)]
  rfl

theorem blockSet_inj {k : ℕ} {bidx : Array ℕ} (hne : ∀ i < k, ∃ x : Fin m, get bidx x.val = i)
    {i i' : ℕ} (hi : i < k) (h : blockSet m bidx i = blockSet m bidx i') : i = i' := by
  obtain ⟨x, hx⟩ := hne i hi
  have hxi : x ∈ blockSet m bidx i := by simp [blockSet, hx]
  rw [h] at hxi
  simp only [blockSet, Finset.mem_filter, Finset.mem_univ, true_and] at hxi
  rw [← hx, hxi]

theorem mem_blockFamily {k : ℕ} {bidx : Array ℕ} {B : Finset (Fin m)} :
    B ∈ blockFamily m k bidx ↔ ∃ i < k, blockSet m bidx i = B := by
  simp [blockFamily]

theorem mem_blockCounts {k : ℕ} {bidx : Array ℕ} {L : List ℕ} {c : ℕ} :
    c ∈ blockCounts k bidx L ↔ ∃ i < k, blockCount bidx L i = c := by
  simp [blockCounts]

theorem blockLab_lt {k : ℕ} {bidx : Array ℕ} {L : List ℕ} {i : ℕ} (h : i ∈ blockLab k bidx L) :
    i < k := by
  unfold blockLab at h
  split_ifs at h <;> exact List.mem_range.1 (List.mem_filter.1 h).1

/-- **Link to stage 14a's `blockLabel`.** For the blocks `0, …, k - 1` of a block-index array,
block `i` is in the block label of `L` exactly when its set of points is in `blockLabel` of
the label `T` of `L` (for the family `blockFamily` of these blocks). -/
theorem mem_blockLab_iff {k : ℕ} {bidx : Array ℕ} {L : List ℕ} {T : Finset (Fin m)}
    (hL : L.Nodup)
    (hT : ∀ x : Fin m, x ∈ T ↔ x.val ∈ L) (hLm : ∀ j ∈ L, j < m) {i : ℕ} (hi : i < k) :
    i ∈ blockLab k bidx L ↔ blockSet m bidx i ∈ blockLabel (blockFamily m k bidx) T := by
  have hcard := card_inter_blockSet (bidx := bidx) hL hT hLm
  have hmemΨ : blockSet m bidx i ∈ blockFamily m k bidx := mem_blockFamily.2 ⟨i, hi, rfl⟩
  have hnonempty : ∀ i', ((T ∩ blockSet m bidx i').Nonempty ↔ 0 < blockCount bidx L i') := by
    intro i'
    rw [← hcard, Finset.card_pos]
  have hall : ((blockCounts k bidx L).all fun c => decide (0 < c)) = true ↔
      metBlocks (blockFamily m k bidx) T = blockFamily m k bidx := by
    simp only [List.all_eq_true, decide_eq_true_eq, mem_blockCounts]
    constructor
    · intro h
      refine Finset.filter_true_of_mem fun B hB => ?_
      obtain ⟨i', hi', rfl⟩ := mem_blockFamily.1 hB
      exact (hnonempty i').2 (h _ ⟨i', hi', rfl⟩)
    · rintro h c ⟨i', hi', rfl⟩
      have hB : blockSet m bidx i' ∈ metBlocks (blockFamily m k bidx) T := by
        rw [h]
        exact mem_blockFamily.2 ⟨i', hi', rfl⟩
      exact (hnonempty i').1 (mem_metBlocks.1 hB).2
  unfold blockLab blockLabel
  by_cases ha : ((blockCounts k bidx L).all fun c => decide (0 < c)) = true
  · rw [if_pos' ha, if_pos' (hall.1 ha), mem_leastBlocks]
    simp only [List.mem_filter, List.mem_range, hi, true_and, beq_iff_eq]
    have hcs : blockCounts k bidx L ≠ [] := by
      simp [blockCounts]
      omega
    obtain ⟨i₀, hi₀, he₀⟩ := mem_blockCounts.1 (minCount_mem hcs)
    constructor
    · intro hmin
      refine ⟨hmemΨ, fun C hC => ?_⟩
      obtain ⟨i', hi', rfl⟩ := mem_blockFamily.1 hC
      rw [hcard, hcard, hmin]
      exact minCount_le (mem_blockCounts.2 ⟨i', hi', rfl⟩)
    · rintro ⟨-, h⟩
      have h₁ := h _ (mem_blockFamily.2 ⟨i₀, hi₀, rfl⟩)
      rw [hcard, hcard, he₀] at h₁
      exact le_antisymm h₁ (minCount_le (mem_blockCounts.2 ⟨i, hi, rfl⟩))
  · rw [if_neg' ha, if_neg' (fun h => ha (hall.2 h)), mem_metBlocks]
    simp only [List.mem_filter, List.mem_range, hi, true_and, decide_eq_true_eq]
    rw [hnonempty]
    exact ⟨fun h => ⟨hmemΨ, h⟩, fun h => h.2⟩

/-- **Link to stage 14a's `Equidist`.** -/
theorem equidistB_iff {k : ℕ} {bidx : Array ℕ} {L : List ℕ} {T : Finset (Fin m)} (hL : L.Nodup)
    (hT : ∀ x : Fin m, x ∈ T ↔ x.val ∈ L) (hLm : ∀ j ∈ L, j < m) :
    equidistB k bidx L = true ↔ Equidist (blockFamily m k bidx) T := by
  have hcard := card_inter_blockSet (bidx := bidx) hL hT hLm
  simp only [equidistB, List.all_eq_true, beq_iff_eq, mem_blockCounts, Equidist]
  constructor
  · intro h B hB C hC
    obtain ⟨i, hi, rfl⟩ := mem_blockFamily.1 hB
    obtain ⟨i', hi', rfl⟩ := mem_blockFamily.1 hC
    rw [hcard, hcard, h _ ⟨i, hi, rfl⟩, h _ ⟨i', hi', rfl⟩]
  · rintro h c ⟨i, hi, rfl⟩
    have hk : 0 < k := by omega
    have hhead : (blockCounts k bidx L).headD 0 = blockCount bidx L 0 := by
      cases k with
      | zero => omega
      | succ k => simp [blockCounts, List.range_succ_eq_map]
    rw [hhead, ← hcard, ← hcard]
    exact h _ (mem_blockFamily.2 ⟨i, hi, rfl⟩) _ (mem_blockFamily.2 ⟨0, hk, rfl⟩)

/-- **Link to stage 14a's `jUnion`.** The cells are indexed by `cell : ℕ → Finset (Fin m)`,
injectively below `nc`; `v0` marks `J.V0`, and `fcell` lists, for each point of `J.V0`, the
indices of the cells of `J.f`. Then cell `c` is in the union exactly when `c` is in
`jUnionData`. -/
theorem mem_jUnionData_iff {nc : ℕ} {v0 : Array Bool} {fcell : Array (List ℕ)}
    {cell : ℕ → Finset (Fin m)} {J : GraphIso.SplitJohnson.JEmb (Fin m)} {L : List ℕ}
    {T : Finset (Fin m)} (hT : ∀ x : Fin m, x ∈ T ↔ x.val ∈ L) (hLm : ∀ j ∈ L, j < m)
    (hV0 : ∀ x : Fin m, x ∈ J.V0 ↔ getB v0 x.val = true)
    (hfc : ∀ x ∈ J.V0, ∀ c ∈ fcell.getD x.val [], c < nc)
    (hf : ∀ x ∈ J.V0, J.f x = (fcell.getD x.val []).toFinset.image cell)
    (hinj : ∀ c < nc, ∀ c' < nc, cell c = cell c' → c = c') {c : ℕ} (hc : c < nc) :
    c ∈ jUnionData nc v0 fcell L ↔ cell c ∈ jUnion J T := by
  rw [mem_jUnionData, jUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨-, j, hj, hv, hcj⟩
    let x : Fin m := ⟨j, hLm j hj⟩
    have hxV : x ∈ J.V0 := (hV0 x).2 hv
    refine ⟨x, Finset.mem_inter.2 ⟨(hT x).2 hj, hxV⟩, ?_⟩
    rw [hf x hxV]
    exact Finset.mem_image.2 ⟨c, List.mem_toFinset.2 hcj, rfl⟩
  · rintro ⟨x, hx, hcx⟩
    obtain ⟨hxT, hxV⟩ := Finset.mem_inter.1 hx
    rw [hf x hxV] at hcx
    obtain ⟨c', hc', he⟩ := Finset.mem_image.1 hcx
    have hc'' := List.mem_toFinset.1 hc'
    have : c' = c := hinj c' (hfc x hxV c' hc'') c hc he
    subst this
    exact ⟨hc, x.val, (hT x).1 hxT, (hV0 x).1 hxV, hc''⟩

/-- **The complement**: the complement of the label `T` of `L`. -/
theorem mem_complLab_iff {L : List ℕ} {T : Finset (Fin m)} (hT : ∀ x : Fin m, x ∈ T ↔ x.val ∈ L)
    (x : Fin m) : x.val ∈ complLab m L ↔ x ∉ T := by
  rw [mem_complLab, hT]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem lt_of_mem_complLab {L : List ℕ} {j : ℕ} (h : j ∈ complLab m L) : j < m :=
  ((mem_complLab m L j).1 h).1

/-- The label of a position in `labOf` is its list read as base points. -/
theorem mem_labOf_iff {n N : ℕ} {L : LabelData} {u : Fin N} (x : Fin (N - n)) :
    x ∈ labOf n N L u ↔ x.val ∈ L.getD u.val [] := by
  simp only [labOf, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨j, hj, he⟩
    split_ifs at he with h
    · cases he
      exact hj
  · intro h
    exact ⟨x.val, h, by simp [x.2]⟩

/-! ### The outputs are labels again -/

theorem nodup_interLab {pts : List ℕ} {pos : Array ℕ} {mask : Array Bool}
    (hpos : ∀ i (h : i < pts.length), get pos pts[i] = i)
    (hmask : ∀ j, getB mask j = true ↔ j ∈ pts) {L : List ℕ} (hL : L.Nodup) :
    (interLab pos mask L).Nodup := by
  refine (hL.filter _).map_on fun x hx y hy hxy => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((hmask x).1 (List.mem_filter.1 hx).2)
  obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem ((hmask y).1 (List.mem_filter.1 hy).2)
  rw [hpos i hi, hpos i' hi'] at hxy
  subst hxy
  rfl

theorem lt_of_mem_interLab {pts : List ℕ} {pos : Array ℕ} {mask : Array Bool}
    (hpos : ∀ i (h : i < pts.length), get pos pts[i] = i)
    (hmask : ∀ j, getB mask j = true ↔ j ∈ pts) {L : List ℕ} {i : ℕ}
    (h : i ∈ interLab pos mask L) : i < pts.length :=
  ((mem_interLab hpos hmask L i).1 h).1

theorem nodup_blockLab (k : ℕ) (bidx : Array ℕ) (L : List ℕ) : (blockLab k bidx L).Nodup := by
  unfold blockLab
  split_ifs <;> exact List.nodup_range.filter _

theorem nodup_jUnionData (nc : ℕ) (v0 : Array Bool) (fcell : Array (List ℕ)) (L : List ℕ) :
    (jUnionData nc v0 fcell L).Nodup :=
  List.nodup_range.filter _

theorem nodup_complLab (m : ℕ) (L : List ℕ) : (complLab m L).Nodup :=
  List.nodup_range.filter _

end Links

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The mask of the entries of `L` below `k`. -/
def markProg (k : var .nat) (L : var (.list .nat)) : Prog S rec var (.array .bool) :=
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .arrayMk k f) fun blank =>
  .bind (mapList L fun j => .bind (.op0 (.boolLit true)) fun t => .op2 .pair j t) fun ws =>
  .prim .arrayUpdate (.cons blank (.cons ws .nil))

/-- **M1**: the label intersected with the marked points, renumbered by `pos`. -/
def interLabProg (pos : var (.array .nat)) (mask : var (.array .bool))
    (L : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (filterList L fun j => .op2 .arrayGet mask j) fun fl =>
  mapList fl fun j => .op2 .arrayGet pos j

/-- The block counts of `L`. -/
def countsProg (k : var .nat) (bidx : var (.array .nat)) (L : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .range k) fun rk =>
  mapList rk fun i => countList L fun j => .bind (.op2 .arrayGet bidx j) fun b => .op2 .natEq b i

/-- The least entry of a list. -/
def minProg (cs : var (.list .nat)) : Prog S rec var .nat :=
  .caseList cs (.op0 (.natLit 0)) fun c _ =>
    .foldList cs c fun acc d => .bind (.op2 .natLt d acc) fun lt => .ite lt (.ret d) (.ret acc)

/-- **M2a**: the block label. -/
def blockLabProg (k : var .nat) (bidx : var (.array .nat)) (L : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (countsProg k bidx L) fun cs => .bind (.op1 .arrayOfList cs) fun ca =>
  .bind (allList cs fun c => .bind (.op0 (.natLit 0)) fun z => .op2 .natLt z c) fun allpos =>
  .bind (.op1 .range k) fun rk =>
  .ite allpos
    (.bind (minProg cs) fun mn =>
      filterList rk fun i => .bind (.op2 .arrayGet ca i) fun ci => .op2 .natEq ci mn)
    (filterList rk fun i =>
      .bind (.op2 .arrayGet ca i) fun ci => .bind (.op0 (.natLit 0)) fun z => .op2 .natLt z ci)

/-- Whether `L` meets every block in the same number of points. -/
def equidistProg (k : var .nat) (bidx : var (.array .nat)) (L : var (.list .nat)) :
    Prog S rec var .bool :=
  .bind (countsProg k bidx L) fun cs =>
  .bind (.caseList cs (.op0 (.natLit 0)) fun c _ => .ret c) fun h =>
  allList cs fun c => .op2 .natEq c h

/-- **The Johnson union**: the cells of the points of `L` marked in `v0`. -/
def jUnionProg (nc : var .nat) (v0 : var (.array .bool)) (fcell : var (.array (.list .nat)))
    (L : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (filterList L fun j => .op2 .arrayGet v0 j) fun fl =>
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList fl nil fun acc j =>
      .bind (.op2 .arrayGet fcell j) fun cj => .op2 .append cj acc) fun cl =>
  .bind (markProg nc cl) fun mk =>
  .bind (.op1 .range nc) fun rn =>
  filterList rn fun c => .op2 .arrayGet mk c

/-- The complement of `L` within `0, …, m - 1`. -/
def complLabProg (m : var .nat) (L : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (markProg m L) fun mk => .bind (.op1 .range m) fun rm =>
  filterList rm fun j => .bind (.op2 .arrayGet mk j) fun b => .op1 .not b

/-- Apply a label program at every point of `w`. -/
def mapLabelsProg (L : var (.array (.list .nat))) (w : var (.list .nat))
    (f : var (.list .nat) → Prog S rec var (.list .nat)) : Prog S rec var (.array (.list .nat)) :=
  .bind (mapList w fun i =>
      .bind (.op2 .arrayGet L i) fun li => .bind (f li) fun li' => .op2 .pair i li') fun ws =>
  .prim .arrayUpdate (.cons L (.cons ws .nil))

end Programs

/-! ### Costs -/

/-- The cost of `markProg` for a base of `k` points and `t` entries. -/
def markCost (k t : ℕ) : ℕ := 2 * k + 6 * t + 5

/-- The cost of `interLabProg` for a label of `t` entries. -/
def interCost (t : ℕ) : ℕ := 9 * t + 5

/-- The cost of `countsProg` for `k` blocks and a label of `t` entries. -/
def countsCost (k t : ℕ) : ℕ := k * (6 * t + 5) + 3

/-- The cost of `blockLabProg`. -/
def blockLabCost (k t : ℕ) : ℕ := k * (6 * t + 21) + 12

/-- The cost of `equidistProg`. -/
def equidistCost (k t : ℕ) : ℕ := k * (6 * t + 8) + 6

/-- The cost of `jUnionProg` for `nc` cells, a label of `t` entries and at most `s` cells per
point. -/
def jUnionCost (nc t s : ℕ) : ℕ := 8 * nc + 7 * t * s + 8 * t + 13

/-- The cost of `complLabProg`. -/
def complCost (m t : ℕ) : ℕ := 9 * m + 6 * t + 9

/-! ### Specs -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.markProg (k : ℕ) (L : List ℕ) :
    RunsWithin X body (Toolkit.markProg k L) (markArr k L) (markCost k L.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 2) fun j _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, Args.tail, List.length_map,
      Array.size_replicate, markCost]
    omega

theorem RunsWithin.interLabProg (pos : Array ℕ) (mask : Array Bool) (L : List ℕ) :
    RunsWithin X body (Toolkit.interLabProg pos mask L) (interLab pos mask L)
      (interCost L.length) := by
  have hf := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := L)
    (p := fun j => .op2 .arrayGet mask j) (P := getB mask) (c := 1)
    fun j _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  have hle : (L.filter (getB mask)).length ≤ L.length := List.length_filter_le _ _
  apply RunsWithin.mono
  case h =>
    run_step hf
    exact RunsWithin.mapList_le (c := 1) fun j _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  case hc =>
    simp only [interCost]
    omega

theorem RunsWithin.countsProg (k : ℕ) (bidx : Array ℕ) (L : List ℕ) :
    RunsWithin X body (Toolkit.countsProg k bidx L) (blockCounts k bidx L)
      (countsCost k L.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.mapList_le (c := L.length * 6 + 1) fun i _ =>
      RunsWithin.countList (c := 2) fun j _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
          (by simp [Prim.cost])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, countsCost]
    ring_nf
    omega

theorem RunsWithin.minProg (cs : List ℕ) :
    RunsWithin X body (Toolkit.minProg cs) (minCount cs) (3 * cs.length + 2) := by
  cases cs with
  | nil =>
    exact (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono (by simp [Prim.cost])
  | cons c cs' =>
    have hfold := RunsWithin.foldList_inv (X := X) (body := body) (I := fun _ => True)
      (c := 2) (a' := .nat) (b' := .nat)
      (f := fun (acc : Ty.nat.denote) (d : Ty.nat.denote) =>
        Prog.bind (.op2 .natLt d acc) fun lt => Prog.ite lt (.ret d) (.ret acc))
      (F := fun acc d => if d < acc then d else acc) (c :: cs') c (fun acc _ d _ => by
        refine ⟨?_, trivial⟩
        by_cases h : d < acc
        · refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
          simp only [Prim.eval, h, decide_true, ↓reduceIte]
          exact (RunsWithin.ite_true (RunsWithin.ret _)).mono (by omega)
        · refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
          simp only [Prim.eval, h, decide_false, ↓reduceIte]
          exact (RunsWithin.ite_false (RunsWithin.ret _)).mono (by omega)) trivial
    refine (RunsWithin.caseList_cons hfold.1).mono ?_
    simp only [List.length_cons]
    omega

theorem getD_toArray_blockCounts (k : ℕ) (bidx : Array ℕ) (L : List ℕ) {i : ℕ} (hi : i < k) :
    (blockCounts k bidx L).toArray.getD i 0 = blockCount bidx L i := by
  simp [blockCounts, Array.getD_eq_getD_getElem?, hi]

theorem RunsWithin.blockLabProg (k : ℕ) (bidx : Array ℕ) (L : List ℕ) :
    RunsWithin X body (Toolkit.blockLabProg k bidx L) (blockLab k bidx L)
      (blockLabCost k L.length) := by
  have hlen : (blockCounts k bidx L).length = k := by simp [blockCounts]
  have hall := RunsWithin.allList_le (X := X) (body := body) (a' := .nat)
    (xs := blockCounts k bidx L)
    (p := fun c => .bind (.op0 (.natLit 0)) fun z => .op2 .natLt z c)
    (P := fun c => decide (0 < c)) (c := 2) fun c _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
        (by simp [Prim.cost])
  have htrue : RunsWithin X body
      (Prog.bind (Toolkit.minProg (blockCounts k bidx L)) fun mn =>
        Toolkit.filterList (a' := .nat) (List.range k) fun i =>
          Prog.bind (.op2 .arrayGet (blockCounts k bidx L).toArray i) fun ci =>
            Prog.op2 .natEq ci mn)
      ((List.range k).filter fun i => blockCount bidx L i == minCount (blockCounts k bidx L))
      (9 * k + 5) := by
    refine RunsWithin.bind_le (RunsWithin.minProg _) (RunsWithin.filterList (c := 2) ?_) ?_
    · intro i hi
      refine RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le ?_ le_rfl)
        (by simp [Prim.cost])
      simp only [Prim.eval]
      rw [show (blockCounts k bidx L).toArray.getD i Ty.nat.default = blockCount bidx L i from
        getD_toArray_blockCounts k bidx L (List.mem_range.1 hi)]
    · simp only [hlen, List.length_range]
      omega
  have hfalse : RunsWithin X body
      (Toolkit.filterList (a' := .nat) (List.range k) fun i =>
        Prog.bind (.op2 .arrayGet (blockCounts k bidx L).toArray i) fun ci =>
          Prog.bind (.op0 (.natLit 0)) fun z => Prog.op2 .natLt z ci)
      ((List.range k).filter fun i => decide (0 < blockCount bidx L i)) (7 * k + 3) := by
    refine (RunsWithin.filterList (c := 3) fun i hi => ?_).mono (by simp [Nat.mul_comm])
    refine RunsWithin.bind_le (RunsWithin.prim _ _)
      (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le ?_ le_rfl) le_rfl)
      (by simp [Prim.cost])
    simp only [Prim.eval]
    rw [show (blockCounts k bidx L).toArray.getD i Ty.nat.default = blockCount bidx L i from
      getD_toArray_blockCounts k bidx L (List.mem_range.1 hi)]
  have hbranch : RunsWithin X body
      (cond ((blockCounts k bidx L).all fun c => decide (0 < c))
        (Prog.bind (Toolkit.minProg (blockCounts k bidx L)) fun mn =>
          Toolkit.filterList (a' := .nat) (List.range k) fun i =>
            Prog.bind (.op2 .arrayGet (blockCounts k bidx L).toArray i) fun ci =>
              Prog.op2 .natEq ci mn)
        (Toolkit.filterList (a' := .nat) (List.range k) fun i =>
          Prog.bind (.op2 .arrayGet (blockCounts k bidx L).toArray i) fun ci =>
            Prog.bind (.op0 (.natLit 0)) fun z => Prog.op2 .natLt z ci))
      (blockLab k bidx L) (9 * k + 5) := by
    unfold blockLab
    cases ha : (blockCounts k bidx L).all fun c => decide (0 < c)
    · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
      exact hfalse.mono (by omega)
    · simp only [Bool.cond_true, ↓reduceIte]
      exact htrue
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.countsProg k bidx L)
    run_step (RunsWithin.prim _ _)
    run_step hall
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.ite hbranch
  case hc =>
    simp only [Prim.cost, Args.head, hlen, countsCost, blockLabCost]
    ring_nf
    omega

theorem RunsWithin.equidistProg (k : ℕ) (bidx : Array ℕ) (L : List ℕ) :
    RunsWithin X body (Toolkit.equidistProg k bidx L) (equidistB k bidx L)
      (equidistCost k L.length) := by
  have hlen : (blockCounts k bidx L).length = k := by simp [blockCounts]
  have hhead : RunsWithin X body
      (Prog.caseList (a := .nat) (blockCounts k bidx L) (.op0 (.natLit 0)) fun c _ => .ret c)
      ((blockCounts k bidx L).headD 0) 2 := by
    generalize blockCounts k bidx L = cs
    cases cs with
    | nil =>
      exact (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono (by simp [Prim.cost])
    | cons c cs =>
      have h := RunsWithin.caseList_cons (X := X) (body := body) (a' := .nat) (t := .nat)
        (x := c) (xs := cs) (p := Prog.op0 (Prim.natLit 0)) (q := fun c _ => Prog.ret c)
        (RunsWithin.ret (X := X) (body := body) (t := .nat) c)
      exact h.mono (by omega)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.countsProg k bidx L)
    run_step hhead
    exact RunsWithin.allList_le (c := 1) fun c _ => RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [hlen, countsCost, equidistCost]
    ring_nf
    omega

theorem RunsWithin.complLabProg (m : ℕ) (L : List ℕ) :
    RunsWithin X body (Toolkit.complLabProg m L) (complLab m L) (complCost m L.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.markProg m L)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.filterList (c := 2) fun j _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
        (by simp [Prim.cost])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, markCost, complCost]
    omega

theorem length_foldl_append_le (fcell : Array (List ℕ)) {s : ℕ} :
    ∀ (L acc : List ℕ), (∀ j ∈ L, (fcell.getD j []).length ≤ s) →
      (L.foldl (fun acc j => fcell.getD j [] ++ acc) acc).length ≤ acc.length + L.length * s
  | [], acc, _ => by simp
  | j :: L, acc, h => by
    rw [List.foldl_cons]
    have := length_foldl_append_le fcell L (fcell.getD j [] ++ acc)
      fun j' hj' => h j' (List.mem_cons_of_mem _ hj')
    have hj := h j List.mem_cons_self
    simp only [List.length_append, List.length_cons] at this ⊢
    rw [Nat.succ_mul]
    omega

theorem RunsWithin.jUnionProg (nc : ℕ) (v0 : Array Bool) (fcell : Array (List ℕ))
    (L : List ℕ) {s : ℕ} (hs : ∀ j ∈ L, (fcell.getD j []).length ≤ s) :
    RunsWithin X body (Toolkit.jUnionProg nc v0 fcell L) (jUnionData nc v0 fcell L)
      (jUnionCost nc L.length s) := by
  have hfl := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := L)
    (p := fun j => .op2 .arrayGet v0 j) (P := getB v0) (c := 1)
    fun j _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  have hsfl : ∀ j ∈ L.filter (getB v0), (fcell.getD j []).length ≤ s :=
    fun j hj => hs j (List.mem_of_mem_filter hj)
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (I := fun _ => True)
    (c := s + 2) (a' := .nat) (b' := .list .nat)
    (f := fun (acc : (Ty.list .nat).denote) (j : Ty.nat.denote) =>
      Prog.bind (.op2 .arrayGet fcell j) fun cj => Prog.op2 .append cj acc)
    (F := fun acc j => fcell.getD j [] ++ acc) (L.filter (getB v0)) [] (fun acc _ j hj => by
      refine ⟨?_, trivial⟩
      refine RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) ?_
      simp only [Prim.cost, Prim.eval, Args.head]
      have := hsfl j hj
      change 1 + ((fcell.getD j []).length + 1) ≤ s + 2
      omega) trivial
  have hlenfl : (L.filter (getB v0)).length ≤ L.length := List.length_filter_le _ _
  have hlencl := length_foldl_append_le fcell (L.filter (getB v0)) [] hsfl
  simp only [List.length_nil, Nat.zero_add] at hlencl
  have hmul : (L.filter (getB v0)).length * s ≤ L.length * s := Nat.mul_le_mul_right _ hlenfl
  apply RunsWithin.mono
  case h =>
    run_step hfl
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    run_step (RunsWithin.markProg nc _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.filterList (c := 1) fun c _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, markCost, jUnionCost]
    have e2 : (L.filter (getB v0)).length * (s + 2 + 1) =
        (L.filter (getB v0)).length * s + 3 * (L.filter (getB v0)).length := by ring
    rw [show 7 * L.length * s = 7 * (L.length * s) by ring]
    dsimp only [Ty.denote] at *
    rw [e2]
    omega

theorem RunsWithin.mapLabelsProg {L : LabelData} {w : List ℕ}
    {f : (Ty.list .nat).denote → Prog S (a, b) Ty.denote (.list .nat)} {F : List ℕ → List ℕ}
    {c : ℕ} (hf : ∀ i ∈ w, RunsWithin X body (f (L.getD i [])) (F (L.getD i [])) c) :
    RunsWithin X body (Toolkit.mapLabelsProg L w f) (mapLabels L w F)
      (w.length * (c + 6) + L.size + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapList_le (c := c + 2) (F := fun i => (i, F (L.getD i []))) fun i hi =>
      RunsWithin.bind_le (RunsWithin.prim _ _)
        (RunsWithin.bind_le (hf i hi) (RunsWithin.prim _ _) le_rfl) (by simp [Prim.cost]; omega))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Args.tail, List.length_map]
    have e : w.length * (c + 6) = w.length * (c + 2 + 3) + w.length := by ring
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_filterList {a' : Ty} {xs₁ : var₁ (.list a')} {xs₂ : var₂ (.list a')}
    {p₁ : var₁ a' → Prog S rec var₁ .bool} {p₂ : var₂ a' → Prog S rec var₂ .bool}
    (hxs : ⟨.list a', xs₁, xs₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (filterList xs₁ p₁) (filterList xs₂ p₂) := by
  unfold filterList
  prog_wf
  all_goals exact hp _ (fun y hy => by simp [hy]) _ _ (by simp)

theorem wf_countList {a' : Ty} {xs₁ : var₁ (.list a')} {xs₂ : var₂ (.list a')}
    {p₁ : var₁ a' → Prog S rec var₁ .bool} {p₂ : var₂ a' → Prog S rec var₂ .bool}
    (hxs : ⟨.list a', xs₁, xs₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (countList xs₁ p₁) (countList xs₂ p₂) := by
  unfold countList
  prog_wf
  all_goals exact hp _ (fun y hy => by simp [hy]) _ _ (by simp)

theorem wf_markProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {L₁ : var₁ (.list .nat)}
    {L₂ : var₂ (.list .nat)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (markProg k₁ L₁) (markProg k₂ L₂) := by
  unfold markProg mapList
  prog_wf

theorem wf_interLabProg {p₁ : var₁ (.array .nat)} {p₂ : var₂ (.array .nat)}
    {m₁ : var₁ (.array .bool)} {m₂ : var₂ (.array .bool)} {L₁ : var₁ (.list .nat)}
    {L₂ : var₂ (.list .nat)} (hp : ⟨.array .nat, p₁, p₂⟩ ∈ Γ)
    (hm : ⟨.array .bool, m₁, m₂⟩ ∈ Γ) (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (interLabProg p₁ m₁ L₁) (interLabProg p₂ m₂ L₂) := by
  unfold interLabProg filterList mapList
  prog_wf

theorem wf_countsProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {L₁ : var₁ (.list .nat)} {L₂ : var₂ (.list .nat)}
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ)
    (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (countsProg k₁ b₁ L₁) (countsProg k₂ b₂ L₂) := by
  unfold countsProg countList mapList
  prog_wf

theorem wf_blockLabProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {L₁ : var₁ (.list .nat)} {L₂ : var₂ (.list .nat)}
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ)
    (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (blockLabProg k₁ b₁ L₁) (blockLabProg k₂ b₂ L₂) := by
  unfold blockLabProg countsProg countList minProg filterList allList mapList
  prog_wf

theorem wf_equidistProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {L₁ : var₁ (.list .nat)} {L₂ : var₂ (.list .nat)}
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ)
    (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (equidistProg k₁ b₁ L₁) (equidistProg k₂ b₂ L₂) := by
  unfold equidistProg countsProg countList allList mapList
  prog_wf

theorem wf_jUnionProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {v₁ : var₁ (.array .bool)}
    {v₂ : var₂ (.array .bool)} {f₁ : var₁ (.array (.list .nat))}
    {f₂ : var₂ (.array (.list .nat))} {L₁ : var₁ (.list .nat)} {L₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hv : ⟨.array .bool, v₁, v₂⟩ ∈ Γ)
    (hf : ⟨.array (.list .nat), f₁, f₂⟩ ∈ Γ) (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (jUnionProg n₁ v₁ f₁ L₁) (jUnionProg n₂ v₂ f₂ L₂) := by
  unfold jUnionProg markProg filterList mapList
  prog_wf

theorem wf_complLabProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {L₁ : var₁ (.list .nat)}
    {L₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (complLabProg m₁ L₁) (complLabProg m₂ L₂) := by
  unfold complLabProg markProg filterList mapList
  prog_wf

theorem wf_mapLabelsProg {L₁ : var₁ (.array (.list .nat))} {L₂ : var₂ (.array (.list .nat))}
    {w₁ : var₁ (.list .nat)} {w₂ : var₂ (.list .nat)}
    {f₁ : var₁ (.list .nat) → Prog S rec var₁ (.list .nat)}
    {f₂ : var₂ (.list .nat) → Prog S rec var₂ (.list .nat)}
    (hL : ⟨.array (.list .nat), L₁, L₂⟩ ∈ Γ) (hw : ⟨.list .nat, w₁, w₂⟩ ∈ Γ)
    (hf : WfFun r Γ f₁ f₂) :
    Prog.Wf r Γ (mapLabelsProg L₁ w₁ f₁) (mapLabelsProg L₂ w₂ f₂) := by
  unfold mapLabelsProg mapList
  prog_wf
  all_goals exact hf _ (fun y hy => by simp [hy]) _ _ (by simp)

end Wf

end GraphIso.Toolkit
