module

public import GraphIso.Align.Interface
public import GraphIso.Toolkit.Reduce
public import GraphIso.SoJProg.DLTest

/-!
# Colored partitions as structures for Align

Stage 14f (`PLAN-14.md` §10, items 2–4). A colored partition of `Fin m` is the data
`(col, blk)` decoded by stage 14c's `cpartOf m col blk`. Under `IsColPart univ t` its blocks
partition `Fin m`, the colour is constant on blocks, and blocks of one colour have one size.

* **Blocks on data.** `blkL m blk v` lists the block of `v` in increasing order (entries of the
  data at or above `m` are ignored); its first point is the block's representative
  (`repsD m blk` lists the representatives).
* **Stabilizer generators** (`partGensD`): for each block the transpositions of its
  representative with its other points, and for each colour the exchanges (pointwise, in list
  order) of the first block of that colour with each other block of that colour.
  `partGens_closure`: under `IsColPart` they generate exactly the stabilizer of the partition in
  `Sym(Fin m)`: transpositions inside blocks generate every block-preserving permutation
  (`po_mem_of_rel`, by induction on the support), and an element of the stabilizer moving a
  point out of its block is reduced by an exchange of two blocks of one colour.
* **Isomorphisms** (`isoPartD`): the representatives of the first partition are matched
  greedily with unused representatives of the second of the same colour and block size
  (`matchD`); the matched blocks are then mapped onto each other pointwise in list order. The
  matching succeeds exactly when the multisets of (colour, block size) over the blocks agree
  (`matchD_isSome_iff`), which an isomorphism forces.
* `partOps m` and `partOps_spec`: the `StructOps` of colored partitions, valid when the decoded
  partition is a colored `t`-partition of `Fin m` for some `t` (Split-or-Johnson's leaves on
  `univ` and Case 1's orbit partition are).
-/

@[expose] public section

namespace GraphIso.Align

open Equiv Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg Pointwise

/-! ### Data -/

section Data

/-- The block of `v`, in increasing order, as points below `m`. -/
def blkL (m : ℕ) (blk : Array (List ℕ)) (v : ℕ) : List ℕ :=
  (List.range m).filter fun w => decide (w ∈ blk.getD v [])

/-- `v` is the least point of its block. -/
def isRepD (m : ℕ) (blk : Array (List ℕ)) (v : ℕ) : Bool := (blkL m blk v).head? == some v

/-- The representatives of the blocks. -/
def repsD (m : ℕ) (blk : Array (List ℕ)) : List ℕ := (List.range m).filter (isRepD m blk)

/-- A transposition of `Fin m`, as data. -/
def swapD (m v w : ℕ) : PermData := Toolkit.swapPair m v w v w

/-- The array of the exchange of the lists `L` and `L'` (pointwise, in list order). -/
def exchArr (m : ℕ) (L L' : List ℕ) : Array ℕ :=
  Cost.Prim.applyWrites (a := .nat) (List.range m).toArray (L.zip L' ++ L'.zip L)

/-- The exchange of two blocks, as data (an involution). -/
def exchD (m : ℕ) (L L' : List ℕ) : PermData := (exchArr m L L', exchArr m L L')

/-- The transpositions of each representative with the other points of its block. -/
def withinGensD (m : ℕ) (blk : Array (List ℕ)) : List PermData :=
  (repsD m blk).flatMap fun r => ((blkL m blk r).filter fun w => w != r).map (swapD m r)

/-- The first representative of the colour of `r`. -/
def firstRepD (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) (r : ℕ) : ℕ :=
  ((repsD m blk).find? fun r' => get col r' == get col r).getD r

/-- The exchanges of the first block of each colour with the other blocks of that colour. -/
def exchGensD (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) : List PermData :=
  ((repsD m blk).filter fun r => firstRepD m col blk r != r).map fun r =>
    exchD m (blkL m blk (firstRepD m col blk r)) (blkL m blk r)

/-- **The stabilizer generators of a colored partition.** -/
def partGensD (m : ℕ) (x : Array ℕ × Array (List ℕ)) : List PermData :=
  withinGensD m x.2 ++ exchGensD m x.1 x.2

/-- The key of a block: its colour and its size. -/
def keyD (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) (r : ℕ) : ℕ × ℕ :=
  (get col r, (blkL m blk r).length)

/-- One step of the greedy matching: match `r` with the first unused representative of the
second partition with the same key. -/
def matchStep (m : ℕ) (x y : Array ℕ × Array (List ℕ)) (st : Option (List ℕ × List (ℕ × ℕ)))
    (r : ℕ) : Option (List ℕ × List (ℕ × ℕ)) :=
  st.bind fun s =>
    (s.1.find? fun r' => keyD m y.1 y.2 r' == keyD m x.1 x.2 r).map fun r' =>
      (s.1.filter fun r'' => r'' != r', (r, r') :: s.2)

/-- **The greedy matching** of the blocks of `x` with those of `y`, if it uses every block. -/
def matchD (m : ℕ) (x y : Array ℕ × Array (List ℕ)) : Option (List (ℕ × ℕ)) :=
  match (repsD m x.2).foldl (matchStep m x y) (some (repsD m y.2, [])) with
  | some ([], acc) => some acc
  | _ => none

/-- The array of the writes `ws` on `m` zeros. -/
def writesArr (m : ℕ) (ws : List (ℕ × ℕ)) : Array ℕ :=
  Cost.Prim.applyWrites (a := .nat) (Array.replicate m 0) ws

/-- The permutation mapping the matched blocks onto each other pointwise. -/
def permOfMatch (m : ℕ) (x y : Array ℕ × Array (List ℕ)) (prs : List (ℕ × ℕ)) : PermData :=
  let src := prs.flatMap fun pr => blkL m x.2 pr.1
  let dst := prs.flatMap fun pr => blkL m y.2 pr.2
  (writesArr m (src.zip dst), writesArr m (dst.zip src))

/-- **An isomorphism of colored partitions**, if there is one. -/
def isoPartD (m : ℕ) (x y : Array ℕ × Array (List ℕ)) : Option PermData :=
  (matchD m x y).map (permOfMatch m x y)

/-- The decoding. -/
def decPart (m : ℕ) (x : Array ℕ × Array (List ℕ)) : CPart (Fin m) := cpartOf m x.1 x.2

/-- **Colored partitions as structures for Align.** -/
def partOps (m : ℕ) : StructOps m (Array ℕ × Array (List ℕ)) (CPart (Fin m)) where
  dec := decPart m
  gens := partGensD m
  iso := isoPartD m

/-- The representation invariant: a colored partition of `Fin m`. -/
def PartValid (m : ℕ) (x : Array ℕ × Array (List ℕ)) : Prop :=
  ∃ t, IsColPart Finset.univ t (decPart m x)

end Data

/-! ### Blocks -/

section Blocks

variable {m : ℕ}

theorem po_mem_blkL {blk : Array (List ℕ)} {v w : ℕ} :
    w ∈ blkL m blk v ↔ w < m ∧ w ∈ blk.getD v [] := by
  simp [blkL]

theorem po_blkL_sorted (blk : Array (List ℕ)) (v : ℕ) : (blkL m blk v).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem po_blkL_nodup (blk : Array (List ℕ)) (v : ℕ) : (blkL m blk v).Nodup :=
  (po_blkL_sorted blk v).imp ne_of_lt

theorem po_lt_of_mem_blkL {blk : Array (List ℕ)} {v w : ℕ} (h : w ∈ blkL m blk v) : w < m :=
  (po_mem_blkL.1 h).1

theorem po_decPart_col (x : Array ℕ × Array (List ℕ)) (v : Fin m) :
    (decPart m x).col v = get x.1 v.val := rfl

theorem po_mem_blk_iff {x : Array ℕ × Array (List ℕ)} {v w : Fin m} :
    w ∈ (decPart m x).blk v ↔ w.val ∈ blkL m x.2 v.val := by
  show w ∈ setOf m (x.2.getD v.val []) ↔ _
  rw [mem_setOf, po_mem_blkL]
  exact ⟨fun h => ⟨w.2, h⟩, fun h => h.2⟩

/-- The block list depends only on the block. -/
theorem po_blkL_congr {x : Array ℕ × Array (List ℕ)} {v w : Fin m}
    (h : (decPart m x).blk v = (decPart m x).blk w) : blkL m x.2 v.val = blkL m x.2 w.val := by
  unfold blkL
  refine List.filter_congr fun u hu => ?_
  have hu' : u < m := List.mem_range.1 hu
  have := congrArg (fun B : Finset (Fin m) => (⟨u, hu'⟩ : Fin m) ∈ B) h
  simp only [eq_iff_iff] at this
  rw [po_mem_blk_iff, po_mem_blk_iff] at this
  simp only [po_mem_blkL, hu', true_and] at this
  simp only [decide_eq_decide]
  exact this

/-- The members of a block, as points of `Fin m`. -/
theorem po_mem_blkL_fin {x : Array ℕ × Array (List ℕ)} {v : Fin m} {w : ℕ} :
    w ∈ blkL m x.2 v.val ↔ ∃ h : w < m, (⟨w, h⟩ : Fin m) ∈ (decPart m x).blk v := by
  constructor
  · intro hw
    exact ⟨po_lt_of_mem_blkL hw, po_mem_blk_iff.2 hw⟩
  · rintro ⟨h, hw⟩
    exact po_mem_blk_iff.1 hw

variable {x : Array ℕ × Array (List ℕ)} {t : ℕ}

/-- Two points in one block have the same block. -/
theorem po_blk_eq (hp : IsColPart univ t (decPart m x)) {v w : Fin m}
    (h : w ∈ (decPart m x).blk v) : (decPart m x).blk w = (decPart m x).blk v :=
  hp.blk_eq v (mem_univ v) w h

/-- Blocks that meet are equal. -/
theorem po_blk_eq_of_mem (hp : IsColPart univ t (decPart m x)) {u v w : Fin m}
    (hv : u ∈ (decPart m x).blk v) (hw : u ∈ (decPart m x).blk w) :
    (decPart m x).blk v = (decPart m x).blk w := by
  rw [← po_blk_eq hp hv, po_blk_eq hp hw]

/-- The block of a point contains it. -/
theorem po_mem_blk_self (hp : IsColPart univ t (decPart m x)) (v : Fin m) :
    v ∈ (decPart m x).blk v :=
  hp.mem_blk v (mem_univ v)

/-- The block list of a point starts with its representative. -/
theorem po_exists_head (hp : IsColPart univ t (decPart m x)) (v : Fin m) :
    ∃ r, (blkL m x.2 v.val).head? = some r := by
  have h := List.ne_nil_of_mem (po_mem_blk_iff.1 (po_mem_blk_self hp v))
  rcases hl : blkL m x.2 v.val with _ | ⟨a, l⟩
  · exact absurd hl h
  · exact ⟨a, rfl⟩

theorem po_mem_reps {blk : Array (List ℕ)} {r : ℕ} :
    r ∈ repsD m blk ↔ r < m ∧ (blkL m blk r).head? = some r := by
  simp [repsD, isRepD]

theorem po_reps_nodup (blk : Array (List ℕ)) : (repsD m blk).Nodup :=
  List.nodup_range.filter _

theorem po_mem_blkL_of_head {blk : Array (List ℕ)} {v r : ℕ}
    (h : (blkL m blk v).head? = some r) : r ∈ blkL m blk v :=
  List.mem_of_mem_head? h

theorem po_head_le {blk : Array (List ℕ)} {v r : ℕ} (h : (blkL m blk v).head? = some r)
    {w : ℕ} (hw : w ∈ blkL m blk v) : r ≤ w := by
  rcases hl : blkL m blk v with _ | ⟨a, l⟩
  · rw [hl] at hw; simp at hw
  · rw [hl] at h hw
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    rcases List.mem_cons.1 hw with rfl | hw
    · exact le_refl _
    · have := po_blkL_sorted (m := m) blk v
      rw [hl] at this
      exact le_of_lt (List.rel_of_pairwise_cons this hw)

/-- The representative of the block of `v` is a representative, with the same block. -/
theorem po_head_rep (hp : IsColPart univ t (decPart m x)) {v : Fin m} {r : ℕ}
    (h : (blkL m x.2 v.val).head? = some r) :
    ∃ hr : r < m, r ∈ repsD m x.2 ∧
      (decPart m x).blk ⟨r, hr⟩ = (decPart m x).blk v := by
  have hmem := po_mem_blkL_of_head h
  have hr := po_lt_of_mem_blkL hmem
  have hblk := po_blk_eq hp (v := v) (w := ⟨r, hr⟩) (po_mem_blk_iff.2 hmem)
  refine ⟨hr, po_mem_reps.2 ⟨hr, ?_⟩, hblk⟩
  rw [show r = (⟨r, hr⟩ : Fin m).val from rfl, po_blkL_congr hblk]
  exact h

/-- A representative is the head of its own block. -/
theorem po_rep_head {r : ℕ} (hr : r ∈ repsD m x.2) : (blkL m x.2 r).head? = some r :=
  (po_mem_reps.1 hr).2

theorem po_rep_lt {r : ℕ} (hr : r ∈ repsD m x.2) : r < m := (po_mem_reps.1 hr).1

theorem po_rep_mem_blkL {r : ℕ} (hr : r ∈ repsD m x.2) : r ∈ blkL m x.2 r :=
  po_mem_blkL_of_head (po_rep_head hr)

/-- Two representatives with the same block are equal. -/
theorem po_rep_eq {r r' : ℕ} (hr : r ∈ repsD m x.2) (hr' : r' ∈ repsD m x.2)
    (h : (decPart m x).blk ⟨r, po_rep_lt hr⟩ = (decPart m x).blk ⟨r', po_rep_lt hr'⟩) :
    r = r' := by
  have e := po_blkL_congr h
  have h₁ := po_rep_head hr
  have h₂ := po_rep_head hr'
  simp only at e
  rw [e, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- Every point lies in the block of exactly one representative. -/
theorem po_exists_rep (hp : IsColPart univ t (decPart m x)) (u : Fin m) :
    ∃ r ∈ repsD m x.2, u.val ∈ blkL m x.2 r := by
  obtain ⟨r, hr⟩ := po_exists_head hp u
  obtain ⟨hrm, hreps, hblk⟩ := po_head_rep hp hr
  refine ⟨r, hreps, ?_⟩
  have := po_blkL_congr hblk
  simp only at this
  rw [this]
  exact po_mem_blk_iff.1 (po_mem_blk_self hp u)

theorem po_rep_unique (hp : IsColPart univ t (decPart m x)) {u : Fin m} {r r' : ℕ}
    (hr : r ∈ repsD m x.2) (hr' : r' ∈ repsD m x.2) (hu : u.val ∈ blkL m x.2 r)
    (hu' : u.val ∈ blkL m x.2 r') : r = r' := by
  refine po_rep_eq hr hr' (po_blk_eq_of_mem hp (u := u) ?_ ?_)
  · exact po_mem_blk_iff.2 hu
  · exact po_mem_blk_iff.2 hu'

/-- The blocks of distinct representatives are disjoint. -/
theorem po_blkL_disjoint (hp : IsColPart univ t (decPart m x)) {r r' : ℕ}
    (hr : r ∈ repsD m x.2) (hr' : r' ∈ repsD m x.2) (hne : r ≠ r') :
    List.Disjoint (blkL m x.2 r) (blkL m x.2 r') := by
  intro u hu hu'
  exact hne (po_rep_unique hp (u := ⟨u, po_lt_of_mem_blkL hu⟩) hr hr' hu hu')

/-- **The blocks partition `[0, m)`.** -/
theorem po_flatten_perm (hp : IsColPart univ t (decPart m x)) :
    ((repsD m x.2).flatMap (blkL m x.2)).Perm (List.range m) := by
  refine (List.perm_ext_iff_of_nodup ?_ List.nodup_range).2 fun u => ?_
  · refine List.nodup_flatMap.2 ⟨fun r _ => po_blkL_nodup _ r, ?_⟩
    exact (po_reps_nodup x.2).imp_of_mem fun {a b} ha hb hab => po_blkL_disjoint hp ha hb hab
  · simp only [List.mem_flatMap, List.mem_range]
    constructor
    · rintro ⟨r, -, hu⟩
      exact po_lt_of_mem_blkL hu
    · intro hu
      exact po_exists_rep hp ⟨u, hu⟩

end Blocks

/-! ### The action on colored partitions -/

section Action

variable {m : ℕ}

theorem po_apply_inv (σ : Perm (Fin m)) (v : Fin m) : σ (σ⁻¹ v) = v := by simp

theorem po_inv_apply (σ : Perm (Fin m)) (v : Fin m) : σ⁻¹ (σ v) = v := by simp

theorem po_smul_eq_iff {σ : Perm (Fin m)} {p q : CPart (Fin m)} :
    σ • p = q ↔ ∀ u, q.col (σ u) = p.col u ∧ q.blk (σ u) = σ • p.blk u := by
  constructor
  · rintro rfl u
    refine ⟨?_, ?_⟩
    · rw [CPart.smul_col, Perm.smul_def]
      simp
    · rw [CPart.smul_blk, Perm.smul_def]
      simp
  · intro h
    obtain ⟨qc, qb⟩ := q
    show CPart.mk _ _ = CPart.mk qc qb
    congr 1
    · funext v
      have := (h (σ⁻¹ v)).1
      rw [po_apply_inv] at this
      rw [Perm.smul_def, ← this]
    · funext v
      have := (h (σ⁻¹ v)).2
      rw [po_apply_inv] at this
      rw [Perm.smul_def]
      exact this.symm

/-- A permutation fixing every point of a set maps it onto itself. -/
theorem po_smul_finset_of_fix {σ : Perm (Fin m)} {B : Finset (Fin m)} (h : ∀ u ∈ B, σ u = u) :
    σ • B = B := by
  ext z
  rw [← Finset.inv_smul_mem_iff, Perm.smul_def]
  constructor
  · intro hz
    have := h _ hz
    rw [po_apply_inv] at this
    rw [this]
    exact hz
  · intro hz
    have e : σ⁻¹ z = z := by
      have := h z hz
      rw [← this, po_inv_apply, this]
    rw [e]
    exact hz

/-- An exchange of two disjoint sets: it maps each into the other, fixes every other point, and
is an involution. -/
def PoExch (B B' : Finset (Fin m)) (β : Perm (Fin m)) : Prop :=
  (∀ u ∈ B, β u ∈ B') ∧ (∀ u ∈ B', β u ∈ B) ∧ (∀ u, u ∉ B → u ∉ B' → β u = u) ∧
    ∀ u, β (β u) = u

theorem PoExch.symm {B B' : Finset (Fin m)} {β : Perm (Fin m)} (h : PoExch B B' β) :
    PoExch B' B β :=
  ⟨h.2.1, h.1, fun u h₁ h₂ => h.2.2.1 u h₂ h₁, h.2.2.2⟩

/-- An exchange maps the first set onto the second. -/
theorem PoExch.smul_eq {B B' : Finset (Fin m)} {β : Perm (Fin m)} (h : PoExch B B' β)
    (hd : Disjoint B B') : β • B = B' := by
  ext z
  rw [← Finset.inv_smul_mem_iff, Perm.smul_def]
  have hinv : β⁻¹ z = β z := by
    have := h.2.2.2 z
    rw [← po_inv_apply β (β z), this]
  rw [hinv]
  constructor
  · intro hz
    by_cases hzB : z ∈ B
    · exact absurd (h.1 z hzB) (Finset.disjoint_left.1 hd hz)
    · by_cases hzB' : z ∈ B'
      · exact hzB'
      · rw [h.2.2.1 z hzB hzB'] at hz
        exact absurd hz hzB
  · intro hz
    exact h.2.1 z hz

/-- Conjugating exchanges with a common set gives an exchange of the other two. -/
theorem po_exch_conj {B₀ B B' : Finset (Fin m)} {e₁ e₂ : Perm (Fin m)} (h₁ : PoExch B₀ B e₁)
    (h₂ : PoExch B₀ B' e₂) (d₀ : Disjoint B₀ B) (d₀' : Disjoint B₀ B') (d : Disjoint B B') :
    PoExch B B' (e₁ * e₂ * e₁) := by
  have fix₁ : ∀ u ∈ B', e₁ u = u := fun u hu =>
    h₁.2.2.1 u (Finset.disjoint_right.1 d₀' hu) (Finset.disjoint_right.1 d hu)
  have fix₂ : ∀ u ∈ B, e₂ u = u := fun u hu =>
    h₂.2.2.1 u (Finset.disjoint_right.1 d₀ hu) (Finset.disjoint_left.1 d hu)
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u hu hu' => ?_, fun u => ?_⟩
  · simp only [Perm.mul_apply]
    have a₁ := h₁.2.1 u hu
    have a₂ := h₂.1 _ a₁
    rw [fix₁ _ a₂]
    exact a₂
  · simp only [Perm.mul_apply]
    rw [fix₁ u hu]
    exact h₁.1 _ (h₂.2.1 u hu)
  · simp only [Perm.mul_apply]
    by_cases hu₀ : u ∈ B₀
    · have a₁ := h₁.1 u hu₀
      rw [fix₂ _ a₁, h₁.2.2.2]
    · rw [h₁.2.2.1 u hu₀ hu, h₂.2.2.1 u hu₀ hu', h₁.2.2.1 u hu₀ hu]
  · simp only [Perm.mul_apply, h₁.2.2.2, h₂.2.2.2]

end Action

/-! ### Transpositions and exchanges on data -/

section PermData

variable {m : ℕ}

theorem po_sp_swap (v w z : ℕ) : Toolkit.sp v w v w z = Equiv.swap v w z := by
  unfold Toolkit.sp
  rw [Equiv.swap_apply_def]
  by_cases h₁ : z = v <;> by_cases h₂ : z = w <;> simp [h₁, h₂]

theorem po_get_swapD {v w z : ℕ} (hz : z < m) : get (swapD m v w).1 z = Equiv.swap v w z := by
  rw [swapD, Toolkit.get_swapPair_fst hz, po_sp_swap]

theorem po_swapD_valid {v w : ℕ} (hv : v < m) (hw : w < m) : (swapD m v w).Valid m := by
  have hlt : ∀ z < m, Equiv.swap v w z < m := fun z hz => by
    rw [Equiv.swap_apply_def]; split_ifs <;> omega
  have h2 : ∀ z < m, get (swapD m v w).2 z = Equiv.swap v w z := fun z hz => by
    rw [swapD, Toolkit.get_swapPair_snd hz, po_sp_swap]
  refine ⟨by simp [swapD, Toolkit.swapPair], by simp [swapD, Toolkit.swapPair], fun z hz => ?_,
    fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · rw [po_get_swapD hz]; exact hlt z hz
  · rw [h2 z hz]; exact hlt z hz
  · rw [po_get_swapD hz, h2 _ (hlt z hz), Equiv.swap_apply_self]
  · rw [h2 z hz, po_get_swapD (hlt z hz), Equiv.swap_apply_self]

theorem po_denote_swapD {v w : ℕ} (hv : v < m) (hw : w < m) :
    PermData.denote m (swapD m v w) = Equiv.swap (⟨v, hv⟩ : Fin m) ⟨w, hw⟩ := by
  ext z
  rw [PermData.val_denote_apply (po_swapD_valid hv hw), po_get_swapD z.2, Equiv.swap_apply_def,
    Equiv.swap_apply_def]
  by_cases h₁ : z.val = v <;> by_cases h₂ : z.val = w <;> simp [h₁, h₂, Fin.ext_iff]
  split_ifs <;> simp

/-- The hypotheses of an exchange of two lists. -/
structure ExchOK (m : ℕ) (L L' : List ℕ) : Prop where
  nodup : L.Nodup
  nodup' : L'.Nodup
  disj : List.Disjoint L L'
  len : L.length = L'.length
  lt : ∀ u ∈ L, u < m
  lt' : ∀ u ∈ L', u < m

theorem po_size_exchArr (L L' : List ℕ) : (exchArr m L L').size = m := by
  rw [exchArr, size_applyWrites]
  simp

theorem po_exch_fst_nodup {L L' : List ℕ} (h : ExchOK m L L') :
    ((L.zip L' ++ L'.zip L).map Prod.fst).Nodup := by
  rw [List.map_append, List.map_fst_zip (le_of_eq h.len), List.map_fst_zip (le_of_eq h.len.symm)]
  exact List.nodup_append.2 ⟨h.nodup, h.nodup', fun a ha b hb e => h.disj ha (e ▸ hb)⟩

theorem po_get_exch_of_mem {L L' : List ℕ} (h : ExchOK m L L') {u v : ℕ}
    (huv : (u, v) ∈ L.zip L' ++ L'.zip L) : get (exchArr m L L') u = v := by
  have hu : u < m := by
    rcases List.mem_append.1 huv with h' | h'
    · exact h.lt _ (List.of_mem_zip h').1
    · exact h.lt' _ (List.of_mem_zip h').1
  have := getElem?_applyWrites_of_mem (a := .nat) (List.range m).toArray (po_exch_fst_nodup h)
    huv (by simpa using hu)
  simp only [get, Array.getD_eq_getD_getElem?]
  rw [show (exchArr m L L')[u]? = some v from this]
  rfl

theorem po_get_exch_L {L L' : List ℕ} (h : ExchOK m L L') {i : ℕ} (hi : i < L.length) :
    get (exchArr m L L') L[i] = L'[i]'(h.len ▸ hi) := by
  refine po_get_exch_of_mem h (List.mem_append_left _ ?_)
  have hz : i < (L.zip L').length := by simp [hi, ← h.len]
  have := List.getElem_mem (l := L.zip L') hz
  simpa using this

theorem po_get_exch_L' {L L' : List ℕ} (h : ExchOK m L L') {i : ℕ} (hi : i < L'.length) :
    get (exchArr m L L') L'[i] = L[i]'(h.len.symm ▸ hi) := by
  refine po_get_exch_of_mem h (List.mem_append_right _ ?_)
  have hz : i < (L'.zip L).length := by simp [hi, h.len]
  have := List.getElem_mem (l := L'.zip L) hz
  simpa using this

theorem po_get_exch_out {L L' : List ℕ} (h : ExchOK m L L') {u : ℕ} (hu : u < m)
    (hL : u ∉ L) (hL' : u ∉ L') : get (exchArr m L L') u = u := by
  have hnm : u ∉ (L.zip L' ++ L'.zip L).map Prod.fst := by
    rw [List.map_append, List.map_fst_zip (le_of_eq h.len),
      List.map_fst_zip (le_of_eq h.len.symm)]
    simp [hL, hL']
  have := getElem?_applyWrites_of_not_mem (a := .nat) (List.range m).toArray hnm
  simp only [get, Array.getD_eq_getD_getElem?]
  rw [show (exchArr m L L')[u]? = (List.range m).toArray[u]? from this]
  simp [hu]

/-- The exchange on data: the image of every point below `m`. -/
theorem po_get_exch_cases {L L' : List ℕ} (h : ExchOK m L L') {u : ℕ} (hu : u < m) :
    (∃ i, ∃ hi : i < L.length, u = L[i] ∧ get (exchArr m L L') u = L'[i]'(h.len ▸ hi)) ∨
    (∃ i, ∃ hi : i < L'.length, u = L'[i] ∧
      get (exchArr m L L') u = L[i]'(h.len.symm ▸ hi)) ∨
    (u ∉ L ∧ u ∉ L' ∧ get (exchArr m L L') u = u) := by
  by_cases hL : u ∈ L
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
    exact Or.inl ⟨i, hi, rfl, po_get_exch_L h hi⟩
  · by_cases hL' : u ∈ L'
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL'
      exact Or.inr (Or.inl ⟨i, hi, rfl, po_get_exch_L' h hi⟩)
    · exact Or.inr (Or.inr ⟨hL, hL', po_get_exch_out h hu hL hL'⟩)

theorem po_get_exch_lt {L L' : List ℕ} (h : ExchOK m L L') {u : ℕ} (hu : u < m) :
    get (exchArr m L L') u < m := by
  rcases po_get_exch_cases h hu with ⟨i, hi, -, e⟩ | ⟨i, hi, -, e⟩ | ⟨-, -, e⟩
  · rw [e]; exact h.lt' _ (List.getElem_mem _)
  · rw [e]; exact h.lt _ (List.getElem_mem _)
  · rw [e]; exact hu

theorem po_get_exch_invol {L L' : List ℕ} (h : ExchOK m L L') {u : ℕ} (hu : u < m) :
    get (exchArr m L L') (get (exchArr m L L') u) = u := by
  rcases po_get_exch_cases h hu with ⟨i, hi, rfl, e⟩ | ⟨i, hi, rfl, e⟩ | ⟨-, -, e⟩
  · rw [e, po_get_exch_L' h]
  · rw [e, po_get_exch_L h]
  · rw [e, e]

theorem po_exchD_valid {L L' : List ℕ} (h : ExchOK m L L') : (exchD m L L').Valid m :=
  ⟨po_size_exchArr L L', po_size_exchArr L L', fun _ hu => po_get_exch_lt h hu,
    fun _ hu => po_get_exch_lt h hu, fun _ hu => po_get_exch_invol h hu,
    fun _ hu => po_get_exch_invol h hu⟩

/-- The set of points of `Fin m` listed in `L`. -/
def finOfL (m : ℕ) (L : List ℕ) : Finset (Fin m) := Finset.univ.filter fun u => u.val ∈ L

theorem po_mem_finOfL {L : List ℕ} {u : Fin m} : u ∈ finOfL m L ↔ u.val ∈ L := by
  simp [finOfL]

/-- **The data exchange is an exchange.** -/
theorem po_exchD_exch {L L' : List ℕ} (h : ExchOK m L L') :
    PoExch (finOfL m L) (finOfL m L') (PermData.denote m (exchD m L L')) := by
  have hv := po_exchD_valid h
  have val : ∀ u : Fin m, (PermData.denote m (exchD m L L') u).val = get (exchArr m L L') u :=
    fun u => PermData.val_denote_apply hv u
  refine ⟨fun u hu => ?_, fun u hu => ?_, fun u h₁ h₂ => ?_, fun u => ?_⟩
  · rw [po_mem_finOfL] at hu ⊢
    rw [val]
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hu
    rw [← e, po_get_exch_L h hi]
    exact List.getElem_mem _
  · rw [po_mem_finOfL] at hu ⊢
    rw [val]
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem hu
    rw [← e, po_get_exch_L' h hi]
    exact List.getElem_mem _
  · rw [po_mem_finOfL] at h₁ h₂
    exact Fin.ext (by rw [val, po_get_exch_out h u.2 h₁ h₂])
  · exact Fin.ext (by rw [val, val, po_get_exch_invol h u.2])

theorem po_card_finOfL {L : List ℕ} (hn : L.Nodup) (hlt : ∀ u ∈ L, u < m) :
    (finOfL m L).card = L.length := by
  have e : (finOfL m L).map Fin.valEmbedding = L.toFinset := by
    ext n
    simp only [Finset.mem_map, po_mem_finOfL, Fin.valEmbedding_apply, List.mem_toFinset]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hn'
      exact ⟨⟨n, hlt n hn'⟩, hn', rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, e, List.toFinset_card_of_nodup hn]

end PermData

/-! ### The generators generate the stabilizer -/

section Closure

variable {m : ℕ}

/-- The subgroup generated by data generators. -/
abbrev genGroup (m : ℕ) (gs : List PermData) : Subgroup (Perm (Fin m)) :=
  Subgroup.closure {σ | ∃ g ∈ gs, PermData.denote m g = σ}

theorem po_mem_genGroup {gs : List PermData} {g : PermData} (hg : g ∈ gs) :
    PermData.denote m g ∈ genGroup m gs :=
  Subgroup.subset_closure ⟨g, hg, rfl⟩

/-- **Transpositions inside the classes of a relation generate its class-preserving
permutations.** -/
theorem po_mem_of_rel {K : Subgroup (Perm (Fin m))} {R : Fin m → Fin m → Prop}
    (hrefl : ∀ v, R v v) (htrans : ∀ u v w, R u v → R v w → R u w)
    (hK : ∀ v w, v ≠ w → R v w → Equiv.swap v w ∈ K) :
    ∀ σ : Perm (Fin m), (∀ u, R u (σ u)) → σ ∈ K := by
  intro σ
  induction h : σ.support.card using Nat.strong_induction_on generalizing σ with
  | _ n ih =>
    intro hσ
    by_cases h1 : σ = 1
    · rw [h1]; exact K.one_mem
    · obtain ⟨v, hv⟩ : ∃ v, σ v ≠ v := by
        by_contra hc
        simp only [not_exists, ne_eq, not_not] at hc
        exact h1 (Equiv.ext hc)
      set τ := Equiv.swap v (σ v) * σ with hτ
      have hlt : τ.support.card < n := h ▸ Perm.card_support_swap_mul hv
      have hτR : ∀ u, R u (τ u) := by
        intro u
        rw [hτ, Perm.mul_apply, Equiv.swap_apply_def]
        split_ifs with e₁ e₂
        · have h1' : R u v := e₁ ▸ hσ u
          exact htrans _ _ _ h1' (hσ v)
        · have : u = v := σ.injective e₂
          subst this
          exact hrefl u
        · exact hσ u
      have hτK := ih _ hlt τ rfl hτR
      have e : σ = Equiv.swap v (σ v) * τ := by
        rw [hτ, ← mul_assoc, Equiv.swap_mul_self, one_mul]
      rw [e]
      exact K.mul_mem (hK v (σ v) hv.symm (hσ v)) hτK

variable {x : Array ℕ × Array (List ℕ)} {t : ℕ}

theorem po_finOfL_blkL (v : Fin m) : finOfL m (blkL m x.2 v.val) = (decPart m x).blk v := by
  ext u
  rw [po_mem_finOfL, po_mem_blk_iff]

theorem po_card_blk (v : Fin m) : ((decPart m x).blk v).card = (blkL m x.2 v.val).length := by
  rw [← po_finOfL_blkL, po_card_finOfL (po_blkL_nodup _ _) fun u hu => po_lt_of_mem_blkL hu]

/-- A transposition of a representative with a point of its block is a generator. -/
theorem po_swap_gen {r u : ℕ} (hr : r ∈ repsD m x.2) (hu : u ∈ blkL m x.2 r) (hne : u ≠ r) :
    Equiv.swap (⟨r, po_rep_lt hr⟩ : Fin m) ⟨u, po_lt_of_mem_blkL hu⟩ ∈
      genGroup m (partGensD m x) := by
  rw [← po_denote_swapD]
  refine po_mem_genGroup (List.mem_append_left _ ?_)
  simp only [withinGensD, List.mem_flatMap, List.mem_map, List.mem_filter]
  exact ⟨r, hr, u, ⟨hu, by simpa using hne⟩, rfl⟩

/-- **Transpositions inside a block are generated.** -/
theorem po_swap_mem (hp : IsColPart univ t (decPart m x)) {v w : Fin m} (hvw : v ≠ w)
    (hw : w ∈ (decPart m x).blk v) : Equiv.swap v w ∈ genGroup m (partGensD m x) := by
  obtain ⟨r, hr⟩ := po_exists_head hp v
  obtain ⟨hrm, hreps, hblk⟩ := po_head_rep hp hr
  have hL : blkL m x.2 r = blkL m x.2 v.val := po_blkL_congr hblk
  have hvL : v.val ∈ blkL m x.2 r := hL ▸ po_mem_blk_iff.1 (po_mem_blk_self hp v)
  have hwL : w.val ∈ blkL m x.2 r := hL ▸ po_mem_blk_iff.1 hw
  have gen : ∀ (u : Fin m), u.val ∈ blkL m x.2 r → u ≠ ⟨r, hrm⟩ →
      Equiv.swap (⟨r, hrm⟩ : Fin m) u ∈ genGroup m (partGensD m x) := fun u hu hne =>
    po_swap_gen hreps hu (fun e => hne (Fin.ext e))
  by_cases hv : v = ⟨r, hrm⟩
  · subst hv
    exact gen w hwL (Ne.symm hvw)
  · by_cases hw' : w = ⟨r, hrm⟩
    · subst hw'
      rw [Equiv.swap_comm]
      exact gen v hvL hv
    · have e := Equiv.swap_mul_swap_mul_swap (x := v) (y := ⟨r, hrm⟩) (z := w) hv hvw
      rw [Equiv.swap_comm v w, ← e, Equiv.swap_comm v ⟨r, hrm⟩]
      exact (genGroup m _).mul_mem ((genGroup m _).mul_mem (gen w hwL hw') (gen v hvL hv))
        (gen w hwL hw')

/-- **Block-preserving permutations are generated.** -/
theorem po_mem_of_blockwise (hp : IsColPart univ t (decPart m x)) {σ : Perm (Fin m)}
    (hσ : ∀ u, σ u ∈ (decPart m x).blk u) : σ ∈ genGroup m (partGensD m x) :=
  po_mem_of_rel (R := fun u w => w ∈ (decPart m x).blk u) (po_mem_blk_self hp)
    (fun u v w huv hvw => by
      rw [← po_blk_eq hp huv]
      exact hvw)
    (fun v w hvw h => po_swap_mem hp hvw h) σ hσ

/-- A transposition of two points of a set maps it onto itself. -/
theorem po_swap_smul {B : Finset (Fin m)} {v w : Fin m} (hv : v ∈ B) (hw : w ∈ B) :
    Equiv.swap v w • B = B := by
  ext z
  rw [← Finset.inv_smul_mem_iff, Equiv.swap_inv, Perm.smul_def, Equiv.swap_apply_def]
  split_ifs with h₁ h₂
  · subst h₁; exact ⟨fun _ => hv, fun _ => hw⟩
  · subst h₂; exact ⟨fun _ => hw, fun _ => hv⟩
  · exact Iff.rfl

/-- The colour is constant on blocks. -/
theorem po_col_eq (hp : IsColPart univ t (decPart m x)) {v w : Fin m}
    (h : w ∈ (decPart m x).blk v) : (decPart m x).col w = (decPart m x).col v :=
  hp.col_eq v (mem_univ v) w h

/-- A point outside a block has a block disjoint from it. -/
theorem po_not_mem_of_not_mem (hp : IsColPart univ t (decPart m x)) {v y z : Fin m}
    (hy : y ∉ (decPart m x).blk v) (hz : z ∈ (decPart m x).blk v) :
    z ∉ (decPart m x).blk y := by
  intro hzy
  apply hy
  rw [← po_blk_eq_of_mem hp hzy hz]
  exact po_mem_blk_self hp y

theorem po_swap_stab (hp : IsColPart univ t (decPart m x)) {v w : Fin m}
    (hw : w ∈ (decPart m x).blk v) :
    Equiv.swap v w ∈ MulAction.stabilizer (Perm (Fin m)) (decPart m x) := by
  rw [MulAction.mem_stabilizer_iff, po_smul_eq_iff]
  intro y
  by_cases hy : y ∈ (decPart m x).blk v
  · have hsy : Equiv.swap v w y ∈ (decPart m x).blk v := by
      rw [Equiv.swap_apply_def]
      split_ifs
      · exact hw
      · exact po_mem_blk_self hp v
      · exact hy
    refine ⟨?_, ?_⟩
    · rw [po_col_eq hp hsy, po_col_eq hp hy]
    · rw [po_blk_eq hp hsy, po_blk_eq hp hy, po_swap_smul (po_mem_blk_self hp v) hw]
  · have hvy : y ≠ v := fun e => hy (e ▸ po_mem_blk_self hp v)
    have hwy : y ≠ w := fun e => hy (e ▸ hw)
    rw [Equiv.swap_apply_of_ne_of_ne hvy hwy]
    refine ⟨rfl, (po_smul_finset_of_fix fun z hz => ?_).symm⟩
    have hzv : z ≠ v := fun e => po_not_mem_of_not_mem hp hy (po_mem_blk_self hp v) (e ▸ hz)
    have hzw : z ≠ w := fun e => po_not_mem_of_not_mem hp hy hw (e ▸ hz)
    exact Equiv.swap_apply_of_ne_of_ne hzv hzw

/-- An exchange of two blocks of one colour preserves the partition. -/
theorem po_exch_stab (hp : IsColPart univ t (decPart m x)) {a b : Fin m} {β : Perm (Fin m)}
    (hne : (decPart m x).blk a ≠ (decPart m x).blk b)
    (hc : (decPart m x).col a = (decPart m x).col b)
    (hβ : PoExch ((decPart m x).blk a) ((decPart m x).blk b) β) :
    β ∈ MulAction.stabilizer (Perm (Fin m)) (decPart m x) := by
  have hd : Disjoint ((decPart m x).blk a) ((decPart m x).blk b) :=
    Finset.disjoint_left.2 fun u ha hb => hne (po_blk_eq_of_mem hp ha hb)
  rw [MulAction.mem_stabilizer_iff, po_smul_eq_iff]
  intro y
  by_cases ha : y ∈ (decPart m x).blk a
  · have hb := hβ.1 y ha
    refine ⟨?_, ?_⟩
    · rw [po_col_eq hp hb, po_col_eq hp ha, hc]
    · rw [po_blk_eq hp hb, po_blk_eq hp ha, hβ.smul_eq hd]
  · by_cases hb : y ∈ (decPart m x).blk b
    · have ha' := hβ.2.1 y hb
      refine ⟨?_, ?_⟩
      · rw [po_col_eq hp ha', po_col_eq hp hb, hc]
      · rw [po_blk_eq hp ha', po_blk_eq hp hb, hβ.symm.smul_eq hd.symm]
    · rw [hβ.2.2.1 y ha hb]
      refine ⟨rfl, (po_smul_finset_of_fix fun z hz => ?_).symm⟩
      refine hβ.2.2.1 z (fun hza => ?_) (fun hzb => ?_)
      · exact po_not_mem_of_not_mem hp ha hza hz
      · exact po_not_mem_of_not_mem hp hb hzb hz

theorem po_finOfL_blkL' {r : ℕ} (hr : r < m) :
    finOfL m (blkL m x.2 r) = (decPart m x).blk ⟨r, hr⟩ :=
  po_finOfL_blkL ⟨r, hr⟩

theorem po_firstRep_spec {r : ℕ} (hr : r ∈ repsD m x.2) :
    ((repsD m x.2).find? fun r' => get x.1 r' == get x.1 r) = some (firstRepD m x.1 x.2 r) ∧
      firstRepD m x.1 x.2 r ∈ repsD m x.2 ∧
        get x.1 (firstRepD m x.1 x.2 r) = get x.1 r := by
  have hsome : ((repsD m x.2).find? fun r' => get x.1 r' == get x.1 r).isSome :=
    List.find?_isSome.2 ⟨r, hr, by simp⟩
  obtain ⟨r0, h0⟩ := Option.isSome_iff_exists.1 hsome
  have e : firstRepD m x.1 x.2 r = r0 := by
    unfold firstRepD
    rw [h0]
    rfl
  rw [e]
  refine ⟨h0, List.mem_of_find?_eq_some h0, ?_⟩
  have := List.find?_some h0
  simpa using this

theorem po_firstRep_congr {r r' : ℕ} (hr : r ∈ repsD m x.2) (hr' : r' ∈ repsD m x.2)
    (h : get x.1 r = get x.1 r') : firstRepD m x.1 x.2 r = firstRepD m x.1 x.2 r' := by
  have h₁ := (po_firstRep_spec hr).1
  have h₂ := (po_firstRep_spec hr').1
  rw [h] at h₁
  rw [h₁] at h₂
  exact Option.some.inj h₂

theorem po_blk_disjoint (hp : IsColPart univ t (decPart m x)) {r r' : ℕ}
    (hr : r ∈ repsD m x.2) (hr' : r' ∈ repsD m x.2) (hne : r ≠ r') :
    Disjoint ((decPart m x).blk ⟨r, po_rep_lt hr⟩) ((decPart m x).blk ⟨r', po_rep_lt hr'⟩) :=
  Finset.disjoint_left.2 fun _ h₁ h₂ => hne (po_rep_eq hr hr' (po_blk_eq_of_mem hp h₁ h₂))

/-- The data of an exchange generator satisfy the exchange hypotheses. -/
theorem po_exchOK (hp : IsColPart univ t (decPart m x)) {r r' : ℕ} (hr : r ∈ repsD m x.2)
    (hr' : r' ∈ repsD m x.2) (hne : r ≠ r') (hc : get x.1 r = get x.1 r') :
    ExchOK m (blkL m x.2 r) (blkL m x.2 r') where
  nodup := po_blkL_nodup _ _
  nodup' := po_blkL_nodup _ _
  disj := po_blkL_disjoint hp hr hr' hne
  len := by
    have := hp.card_eq ⟨r, po_rep_lt hr⟩ (mem_univ _) ⟨r', po_rep_lt hr'⟩ (mem_univ _) hc
    rwa [po_card_blk, po_card_blk] at this
  lt := fun _ hu => po_lt_of_mem_blkL hu
  lt' := fun _ hu => po_lt_of_mem_blkL hu

/-- An exchange generator is an exchange of two blocks of one colour. -/
theorem po_exch_gen (hp : IsColPart univ t (decPart m x)) {r : ℕ} (hr : r ∈ repsD m x.2)
    (hne : firstRepD m x.1 x.2 r ≠ r) :
    PermData.denote m (exchD m (blkL m x.2 (firstRepD m x.1 x.2 r)) (blkL m x.2 r)) ∈
        genGroup m (partGensD m x) ∧
      PoExch ((decPart m x).blk ⟨firstRepD m x.1 x.2 r, po_rep_lt (po_firstRep_spec hr).2.1⟩)
        ((decPart m x).blk ⟨r, po_rep_lt hr⟩)
        (PermData.denote m (exchD m (blkL m x.2 (firstRepD m x.1 x.2 r)) (blkL m x.2 r))) := by
  obtain ⟨-, h0, hc⟩ := po_firstRep_spec hr
  refine ⟨po_mem_genGroup (List.mem_append_right _ ?_), ?_⟩
  · simp only [exchGensD, List.mem_map, List.mem_filter]
    exact ⟨r, ⟨hr, by simpa using hne⟩, rfl⟩
  · have := po_exchD_exch (po_exchOK hp h0 hr hne hc)
    rwa [po_finOfL_blkL' (po_rep_lt h0), po_finOfL_blkL' (po_rep_lt hr)] at this

/-- **Two blocks of one colour are exchanged by a generated element.** -/
theorem po_exists_exch (hp : IsColPart univ t (decPart m x)) {a b : Fin m}
    (hne : (decPart m x).blk a ≠ (decPart m x).blk b)
    (hc : (decPart m x).col a = (decPart m x).col b) :
    ∃ β ∈ genGroup m (partGensD m x),
      PoExch ((decPart m x).blk a) ((decPart m x).blk b) β := by
  obtain ⟨r, hra⟩ := po_exists_head hp a
  obtain ⟨hrm, hr, hba⟩ := po_head_rep hp hra
  obtain ⟨r', hrb⟩ := po_exists_head hp b
  obtain ⟨hrm', hr', hbb⟩ := po_head_rep hp hrb
  have hcr : get x.1 r = get x.1 r' := by
    have h₁ := po_col_eq hp (v := a) (w := ⟨r, hrm⟩) (hba ▸ po_mem_blk_self hp _)
    have h₂ := po_col_eq hp (v := b) (w := ⟨r', hrm'⟩) (hbb ▸ po_mem_blk_self hp _)
    rw [po_decPart_col] at h₁ h₂
    rw [h₁, h₂]
    exact hc
  have hrr : r ≠ r' := by
    rintro rfl
    exact hne (hba.symm.trans hbb)
  have hf := po_firstRep_congr hr hr' hcr
  set r0 := firstRepD m x.1 x.2 r with hr0
  have h0 := (po_firstRep_spec hr).2.1
  by_cases e0 : r0 = r
  · have hne' : firstRepD m x.1 x.2 r' ≠ r' := by rw [← hf, e0]; exact hrr
    obtain ⟨hK, hE⟩ := po_exch_gen hp hr' hne'
    refine ⟨_, hK, ?_⟩
    have : (⟨firstRepD m x.1 x.2 r', po_rep_lt (po_firstRep_spec hr').2.1⟩ : Fin m) =
        ⟨r, hrm⟩ := Fin.ext (hf.symm.trans e0)
    rw [this, hba, hbb] at hE
    exact hE
  · by_cases e0' : r0 = r'
    · obtain ⟨hK, hE⟩ := po_exch_gen hp hr e0
      refine ⟨_, hK, ?_⟩
      have : (⟨firstRepD m x.1 x.2 r, po_rep_lt (po_firstRep_spec hr).2.1⟩ : Fin m) =
          ⟨r', hrm'⟩ := Fin.ext e0'
      rw [this, hba, hbb] at hE
      exact hE.symm
    · obtain ⟨hK₁, hE₁⟩ := po_exch_gen hp hr e0
      have hne' : firstRepD m x.1 x.2 r' ≠ r' := by rw [← hf]; exact e0'
      obtain ⟨hK₂, hE₂⟩ := po_exch_gen hp hr' hne'
      have e₂ : (⟨firstRepD m x.1 x.2 r', po_rep_lt (po_firstRep_spec hr').2.1⟩ : Fin m) =
          ⟨r0, po_rep_lt h0⟩ := Fin.ext hf.symm
      rw [e₂] at hE₂
      rw [hba] at hE₁
      rw [hbb] at hE₂
      refine ⟨_, (genGroup m _).mul_mem ((genGroup m _).mul_mem hK₁ hK₂) hK₁, ?_⟩
      refine po_exch_conj hE₁ hE₂ ?_ ?_ ?_
      · rw [← hba]; exact po_blk_disjoint hp h0 hr e0
      · rw [← hbb]; exact po_blk_disjoint hp h0 hr' e0'
      · rw [← hba, ← hbb]; exact po_blk_disjoint hp hr hr' hrr

/-- **The generators lie in the stabilizer.** -/
theorem po_gens_le (hp : IsColPart univ t (decPart m x)) :
    genGroup m (partGensD m x) ≤ MulAction.stabilizer (Perm (Fin m)) (decPart m x) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro σ ⟨g, hg, rfl⟩
  rcases List.mem_append.1 hg with hg | hg
  · simp only [withinGensD, List.mem_flatMap, List.mem_map, List.mem_filter] at hg
    obtain ⟨r, hr, u, ⟨hu, -⟩, rfl⟩ := hg
    rw [po_denote_swapD (po_rep_lt hr) (po_lt_of_mem_blkL hu)]
    refine po_swap_stab hp ?_
    exact po_mem_blk_iff.2 hu
  · simp only [exchGensD, List.mem_map, List.mem_filter] at hg
    obtain ⟨r, ⟨hr, hne⟩, rfl⟩ := hg
    have hne' : firstRepD m x.1 x.2 r ≠ r := by simpa using hne
    obtain ⟨-, hE⟩ := po_exch_gen hp hr hne'
    obtain ⟨-, h0, hc⟩ := po_firstRep_spec hr
    refine po_exch_stab hp ?_ ?_ hE
    · intro e
      exact hne' (po_rep_eq h0 hr e)
    · rw [po_decPart_col, po_decPart_col]
      exact hc

/-- **The stabilizer is generated.** -/
theorem po_stab_le (hp : IsColPart univ t (decPart m x)) :
    MulAction.stabilizer (Perm (Fin m)) (decPart m x) ≤ genGroup m (partGensD m x) := by
  intro σ hσ
  induction h : (univ.filter fun u => σ u ∉ (decPart m x).blk u).card
      using Nat.strong_induction_on generalizing σ with
  | _ n ih =>
    by_cases hb : ∀ u, σ u ∈ (decPart m x).blk u
    · exact po_mem_of_blockwise hp hb
    · simp only [not_forall] at hb
      obtain ⟨v, hv⟩ := hb
      have hst := po_smul_eq_iff.1 (MulAction.mem_stabilizer_iff.1 hσ)
      have hne : (decPart m x).blk v ≠ (decPart m x).blk (σ v) :=
        fun e => hv (e ▸ po_mem_blk_self hp (σ v))
      obtain ⟨β, hβK, hβ⟩ := po_exists_exch hp hne (hst v).1.symm
      have hd : Disjoint ((decPart m x).blk v) ((decPart m x).blk (σ v)) :=
        Finset.disjoint_left.2 fun u h₁ h₂ => hne (po_blk_eq_of_mem hp h₁ h₂)
      have hτ : β * σ ∈ MulAction.stabilizer (Perm (Fin m)) (decPart m x) :=
        Subgroup.mul_mem _ (po_gens_le hp hβK) hσ
      have hsub : (univ.filter fun u => (β * σ) u ∉ (decPart m x).blk u) ⊂
          univ.filter fun u => σ u ∉ (decPart m x).blk u := by
        refine Finset.ssubset_iff_of_subset (fun u hu => ?_) |>.2 ⟨v, ?_, ?_⟩
        · simp only [Finset.mem_filter, mem_univ, true_and] at hu ⊢
          intro hσu
          apply hu
          rw [Perm.mul_apply]
          by_cases h₁ : σ u ∈ (decPart m x).blk v
          · exfalso
            have e₁ := po_blk_eq hp h₁
            have e₂ := po_blk_eq hp hσu
            have hu' : u ∈ (decPart m x).blk v := e₁ ▸ e₂ ▸ po_mem_blk_self hp u
            have : σ u ∈ (decPart m x).blk (σ v) := by
              rw [(hst v).2]
              exact Finset.smul_mem_smul_finset hu'
            exact Finset.disjoint_left.1 hd h₁ this
          · by_cases h₂ : σ u ∈ (decPart m x).blk (σ v)
            · exfalso
              have e₁ := po_blk_eq hp h₂
              have e₂ := po_blk_eq hp hσu
              have hsm : σ • (decPart m x).blk u = σ • (decPart m x).blk v := by
                rw [← (hst u).2, ← (hst v).2, e₁]
              have huv : (decPart m x).blk u = (decPart m x).blk v := by
                have := congrArg (fun B => σ⁻¹ • B) hsm
                simpa only [inv_smul_smul] using this
              exact hne (huv.symm.trans (e₂.symm.trans e₁))
            · rw [hβ.2.2.1 _ h₁ h₂]
              exact hσu
        · simpa using hv
        · intro hmem
          rw [Finset.mem_filter] at hmem
          exact hmem.2 (hβ.2.1 _ (po_mem_blk_self hp (σ v)))
      have hτK := ih _ (h ▸ Finset.card_lt_card hsub) hτ rfl
      have e : σ = β⁻¹ * (β * σ) := by rw [inv_mul_cancel_left]
      rw [e]
      exact (genGroup m _).mul_mem ((genGroup m _).inv_mem hβK) hτK

/-- **The generators generate exactly the stabilizer.** -/
theorem partGens_closure (hp : IsColPart univ t (decPart m x)) :
    genGroup m (partGensD m x) = MulAction.stabilizer (Perm (Fin m)) (decPart m x) :=
  le_antisymm (po_gens_le hp) (po_stab_le hp)

/-- The generators are valid. -/
theorem partGens_valid (hp : IsColPart univ t (decPart m x)) {g : PermData}
    (hg : g ∈ partGensD m x) : g.Valid m := by
  rcases List.mem_append.1 hg with hg | hg
  · simp only [withinGensD, List.mem_flatMap, List.mem_map, List.mem_filter] at hg
    obtain ⟨r, hr, u, ⟨hu, -⟩, rfl⟩ := hg
    exact po_swapD_valid (po_rep_lt hr) (po_lt_of_mem_blkL hu)
  · simp only [exchGensD, List.mem_map, List.mem_filter] at hg
    obtain ⟨r, ⟨hr, hne⟩, rfl⟩ := hg
    obtain ⟨-, h0, hc⟩ := po_firstRep_spec hr
    exact po_exchD_valid (po_exchOK hp h0 hr (by simpa using hne) hc)

end Closure

/-! ### The greedy matching -/

section Match

variable {m : ℕ} {x y : Array ℕ × Array (List ℕ)}

theorem po_foldl_none (R : List ℕ) : R.foldl (matchStep m x y) none = none := by
  induction R with
  | nil => rfl
  | cons r R ih => simpa [matchStep] using ih

theorem po_nodup_filter_perm {rem : List ℕ} (hn : rem.Nodup) {r' : ℕ} (hr : r' ∈ rem) :
    rem.Perm (r' :: rem.filter fun r'' => r'' != r') := by
  have e : rem.filter (fun r'' => r'' != r') = rem.erase r' := by
    rw [List.Nodup.erase_eq_filter hn]
  rw [e]
  exact List.perm_cons_erase hr

/-- **What the greedy matching computes.** -/
theorem po_fold_spec : ∀ (R rem : List ℕ) (acc : List (ℕ × ℕ)) (res : List ℕ × List (ℕ × ℕ)),
    rem.Nodup → R.foldl (matchStep m x y) (some (rem, acc)) = some res →
    res.2.map Prod.fst = R.reverse ++ acc.map Prod.fst ∧
      (res.2.map Prod.snd ++ res.1).Perm (acc.map Prod.snd ++ rem) ∧
      (∀ pr ∈ res.2, pr ∈ acc ∨ keyD m x.1 x.2 pr.1 = keyD m y.1 y.2 pr.2)
  | [], rem, acc, res, _, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨by simp, List.Perm.refl _, fun pr hpr => Or.inl hpr⟩
  | r :: R, rem, acc, res, hn, h => by
    simp only [List.foldl_cons, matchStep, Option.bind_some] at h
    rcases hf : rem.find? (fun r' => keyD m y.1 y.2 r' == keyD m x.1 x.2 r) with _ | r'
    · rw [hf] at h
      simp only [Option.map_none] at h
      rw [po_foldl_none] at h
      exact absurd h (by simp)
    · rw [hf] at h
      simp only [Option.map_some] at h
      have hr' : r' ∈ rem := List.mem_of_find?_eq_some hf
      have hk : keyD m y.1 y.2 r' = keyD m x.1 x.2 r := by
        have := List.find?_some hf
        simpa using this
      obtain ⟨ha, hb, hc⟩ := po_fold_spec R _ _ res (hn.filter _) h
      refine ⟨?_, ?_, fun pr hpr => ?_⟩
      · rw [ha]
        simp
      · refine hb.trans ?_
        simp only [List.map_cons, List.cons_append]
        exact List.perm_middle.symm.trans (List.Perm.append_left _
          (po_nodup_filter_perm hn hr').symm)
      · rcases hc pr hpr with h' | h'
        · rcases List.mem_cons.1 h' with rfl | h''
          · exact Or.inr hk.symm
          · exact Or.inl h''
        · exact Or.inr h'

theorem po_matchD_eq {prs : List (ℕ × ℕ)} (h : matchD m x y = some prs) :
    (repsD m x.2).foldl (matchStep m x y) (some (repsD m y.2, [])) = some ([], prs) := by
  unfold matchD at h
  split at h
  · rename_i acc e
    rw [e]
    simp only [Option.some.injEq] at h
    rw [h]
  · exact absurd h (by simp)

/-- **A successful matching pairs the blocks with equal keys.** -/
theorem po_matchD_spec {prs : List (ℕ × ℕ)} (h : matchD m x y = some prs) :
    (prs.map Prod.fst).Perm (repsD m x.2) ∧ (prs.map Prod.snd).Perm (repsD m y.2) ∧
      ∀ pr ∈ prs, keyD m x.1 x.2 pr.1 = keyD m y.1 y.2 pr.2 := by
  obtain ⟨ha, hb, hc⟩ := po_fold_spec _ _ _ _ (po_reps_nodup y.2) (po_matchD_eq h)
  refine ⟨?_, ?_, fun pr hpr => ?_⟩
  · simp only [List.map_nil, List.append_nil] at ha
    rw [ha]
    exact List.reverse_perm _
  · simpa using hb
  · rcases hc pr hpr with h' | h'
    · simp at h'
    · exact h'

/-- **The greedy matching succeeds when the keys agree as multisets.** -/
theorem po_fold_some : ∀ (R rem : List ℕ) (acc : List (ℕ × ℕ)), rem.Nodup →
    (R.map (keyD m x.1 x.2)).Perm (rem.map (keyD m y.1 y.2)) →
    ∃ acc', R.foldl (matchStep m x y) (some (rem, acc)) = some ([], acc')
  | [], rem, acc, _, hp => by
    have : rem = [] := by
      have := hp.symm.length_eq
      simpa using this
    subst this
    exact ⟨acc, rfl⟩
  | r :: R, rem, acc, hn, hp => by
    have hmem : keyD m x.1 x.2 r ∈ rem.map (keyD m y.1 y.2) :=
      hp.subset List.mem_cons_self
    obtain ⟨r₁, hr₁, hk₁⟩ := List.mem_map.1 hmem
    have hsome : (rem.find? fun r' => keyD m y.1 y.2 r' == keyD m x.1 x.2 r).isSome :=
      List.find?_isSome.2 ⟨r₁, hr₁, by simp [hk₁]⟩
    obtain ⟨r', hf⟩ := Option.isSome_iff_exists.1 hsome
    have hr' : r' ∈ rem := List.mem_of_find?_eq_some hf
    have hk : keyD m y.1 y.2 r' = keyD m x.1 x.2 r := by
      have := List.find?_some hf
      simpa using this
    have hp' : (R.map (keyD m x.1 x.2)).Perm
        ((rem.filter fun r'' => r'' != r').map (keyD m y.1 y.2)) := by
      have h1 := (po_nodup_filter_perm hn hr').map (keyD m y.1 y.2)
      rw [List.map_cons, hk] at h1
      exact (hp.trans h1).cons_inv
    obtain ⟨acc', h⟩ := po_fold_some R _ ((r, r') :: acc) (hn.filter _) hp'
    refine ⟨acc', ?_⟩
    simp only [List.foldl_cons, matchStep, Option.bind_some, hf, Option.map_some]
    exact h

theorem po_matchD_isSome (h : ((repsD m x.2).map (keyD m x.1 x.2)).Perm
    ((repsD m y.2).map (keyD m y.1 y.2))) : (matchD m x y).isSome := by
  obtain ⟨acc', h'⟩ := po_fold_some _ _ [] (po_reps_nodup y.2) h
  unfold matchD
  rw [h']
  rfl

end Match

/-! ### Isomorphisms -/

section Iso

variable {m : ℕ} {x y : Array ℕ × Array (List ℕ)} {t t' : ℕ}

theorem po_keyD_eq {r : ℕ} (hr : r < m) :
    keyD m x.1 x.2 r = ((decPart m x).col ⟨r, hr⟩, ((decPart m x).blk ⟨r, hr⟩).card) := by
  rw [keyD, po_card_blk]
  rfl

/-- The representative of the block of `σ₀ r` in the second partition. -/
def po_phi (m : ℕ) (y : Array ℕ × Array (List ℕ)) (σ₀ : Perm (Fin m)) (r : ℕ) : ℕ :=
  if h : r < m then ((blkL m y.2 (σ₀ ⟨r, h⟩).val).head?.getD 0) else 0

theorem po_phi_spec (hy : IsColPart univ t' (decPart m y)) (σ₀ : Perm (Fin m)) {r : ℕ}
    (hr : r < m) : ∃ h : po_phi m y σ₀ r < m, po_phi m y σ₀ r ∈ repsD m y.2 ∧
      (decPart m y).blk ⟨po_phi m y σ₀ r, h⟩ = (decPart m y).blk (σ₀ ⟨r, hr⟩) := by
  obtain ⟨r₁, h₁⟩ := po_exists_head hy (σ₀ ⟨r, hr⟩)
  have e : po_phi m y σ₀ r = r₁ := by
    unfold po_phi
    simp only [hr, ↓reduceDIte, h₁]
    rfl
  obtain ⟨hm, hreps, hblk⟩ := po_head_rep hy h₁
  subst e
  exact ⟨hm, hreps, hblk⟩

/-- **An isomorphism matches the blocks with equal keys.** -/
theorem po_keys_perm (hx : IsColPart univ t (decPart m x)) (hy : IsColPart univ t' (decPart m y))
    {σ₀ : Perm (Fin m)} (hσ : σ₀ • decPart m x = decPart m y) :
    ((repsD m x.2).map (keyD m x.1 x.2)).Perm ((repsD m y.2).map (keyD m y.1 y.2)) := by
  have hst := po_smul_eq_iff.1 hσ
  have hkey : ∀ r ∈ repsD m x.2, keyD m x.1 x.2 r = keyD m y.1 y.2 (po_phi m y σ₀ r) := by
    intro r hr
    obtain ⟨hm, -, hblk⟩ := po_phi_spec hy σ₀ (po_rep_lt hr)
    rw [po_keyD_eq (po_rep_lt hr), po_keyD_eq hm, hblk, (hst _).2,
      Finset.card_smul_finset]
    congr 1
    rw [← (hst _).1]
    exact (po_col_eq hy (hblk ▸ po_mem_blk_self hy _)).symm
  have hinj : ∀ r ∈ repsD m x.2, ∀ r' ∈ repsD m x.2, po_phi m y σ₀ r = po_phi m y σ₀ r' →
      r = r' := by
    intro r hr r' hr' e
    obtain ⟨hm, -, hb⟩ := po_phi_spec hy σ₀ (po_rep_lt hr)
    obtain ⟨hm', -, hb'⟩ := po_phi_spec hy σ₀ (po_rep_lt hr')
    have e' : (⟨po_phi m y σ₀ r, hm⟩ : Fin m) = ⟨po_phi m y σ₀ r', hm'⟩ := Fin.ext e
    rw [e', hb', (hst _).2, (hst _).2] at hb
    have := congrArg (fun B => σ₀⁻¹ • B) hb
    simp only [inv_smul_smul] at this
    exact po_rep_eq hr hr' this.symm
  have hperm : ((repsD m x.2).map (po_phi m y σ₀)).Perm (repsD m y.2) := by
    refine List.perm_of_nodup_nodup_toFinset_eq
      ((po_reps_nodup x.2).map_on fun r hr r' hr' e => hinj r hr r' hr' e)
      (po_reps_nodup y.2) ?_
    ext r'
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (po_phi_spec hy σ₀ (po_rep_lt hr)).2.1
    · intro hr'
      set u := σ₀⁻¹ ⟨r', po_rep_lt hr'⟩
      obtain ⟨r₁, h₁⟩ := po_exists_head hx u
      obtain ⟨hm₁, hreps₁, hblk₁⟩ := po_head_rep hx h₁
      refine ⟨r₁, hreps₁, ?_⟩
      obtain ⟨hm, hreps, hblk⟩ := po_phi_spec hy σ₀ hm₁
      refine po_rep_eq hreps hr' ?_
      rw [hblk, (hst _).2, hblk₁, ← (hst _).2, po_apply_inv]
  rw [List.map_congr_left hkey]
  have e : List.map (fun a => keyD m y.1 y.2 (po_phi m y σ₀ a)) (repsD m x.2) =
      ((repsD m x.2).map (po_phi m y σ₀)).map (keyD m y.1 y.2) := by
    rw [List.map_map]
    rfl
  rw [e]
  exact hperm.map _

/-- The source and target lists of a matching. -/
def po_src (m : ℕ) (x : Array ℕ × Array (List ℕ)) (prs : List (ℕ × ℕ)) : List ℕ :=
  prs.flatMap fun pr => blkL m x.2 pr.1

def po_dst (m : ℕ) (y : Array ℕ × Array (List ℕ)) (prs : List (ℕ × ℕ)) : List ℕ :=
  prs.flatMap fun pr => blkL m y.2 pr.2

theorem po_src_perm (hx : IsColPart univ t (decPart m x)) {prs : List (ℕ × ℕ)}
    (h : (prs.map Prod.fst).Perm (repsD m x.2)) : (po_src m x prs).Perm (List.range m) := by
  have e : po_src m x prs = (prs.map Prod.fst).flatMap (blkL m x.2) := by
    simp [po_src, List.flatMap_map]
  rw [e]
  exact (h.flatMap_right _).trans (po_flatten_perm hx)

theorem po_dst_perm (hy : IsColPart univ t' (decPart m y)) {prs : List (ℕ × ℕ)}
    (h : (prs.map Prod.snd).Perm (repsD m y.2)) : (po_dst m y prs).Perm (List.range m) := by
  have e : po_dst m y prs = (prs.map Prod.snd).flatMap (blkL m y.2) := by
    simp [po_dst, List.flatMap_map]
  rw [e]
  exact (h.flatMap_right _).trans (po_flatten_perm hy)

theorem po_zip_flatMap {α : Type*} (f g : α → List ℕ) :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = (g a).length) →
      (l.flatMap f).zip (l.flatMap g) = l.flatMap fun a => (f a).zip (g a)
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.flatMap_cons]
    rw [List.zip_append (h a List.mem_cons_self),
      po_zip_flatMap f g l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem po_get_writes {ws : List (ℕ × ℕ)} (hn : (ws.map Prod.fst).Nodup) {u v : ℕ}
    (huv : (u, v) ∈ ws) (hu : u < m) : get (writesArr m ws) u = v := by
  have := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate m 0) hn huv (by simpa using hu)
  simp only [get, Array.getD_eq_getD_getElem?]
  rw [show (writesArr m ws)[u]? = some v from this]
  rfl

theorem po_size_writes (ws : List (ℕ × ℕ)) : (writesArr m ws).size = m := by
  rw [writesArr, size_applyWrites]
  simp

/-- **Permutation data from two enumerations of `[0, m)`.** -/
theorem po_zip_valid {src dst : List ℕ} (hs : src.Perm (List.range m))
    (hd : dst.Perm (List.range m)) :
    PermData.Valid m (writesArr m (src.zip dst), writesArr m (dst.zip src)) ∧
      ∀ u v, (u, v) ∈ src.zip dst → get (writesArr m (src.zip dst)) u = v := by
  have hls : src.length = m := by simpa using hs.length_eq
  have hld : dst.length = m := by simpa using hd.length_eq
  have hns : src.Nodup := hs.nodup_iff.2 List.nodup_range
  have hnd : dst.Nodup := hd.nodup_iff.2 List.nodup_range
  have hf : ((src.zip dst).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (by omega)]; exact hns
  have hf' : ((dst.zip src).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (by omega)]; exact hnd
  have lts : ∀ u ∈ src, u < m := fun u hu => List.mem_range.1 (hs.subset hu)
  have ltd : ∀ u ∈ dst, u < m := fun u hu => List.mem_range.1 (hd.subset hu)
  have g₁ : ∀ u v, (u, v) ∈ src.zip dst → get (writesArr m (src.zip dst)) u = v :=
    fun u v huv => po_get_writes hf huv (lts _ (List.of_mem_zip huv).1)
  have g₂ : ∀ u v, (u, v) ∈ src.zip dst → get (writesArr m (dst.zip src)) v = u := by
    intro u v huv
    have : (v, u) ∈ dst.zip src := by
      rw [← List.zip_swap]
      exact List.mem_map.2 ⟨(u, v), huv, rfl⟩
    exact po_get_writes hf' this (ltd _ (List.of_mem_zip huv).2)
  have ex₁ : ∀ u < m, ∃ v, (u, v) ∈ src.zip dst := by
    intro u hu
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem (hs.symm.subset (List.mem_range.2 hu))
    refine ⟨dst[i]'(by omega), ?_⟩
    rw [← e]
    have hz : i < (src.zip dst).length := by simp; omega
    have := List.getElem_mem (l := src.zip dst) hz
    simpa using this
  have ex₂ : ∀ v < m, ∃ u, (u, v) ∈ src.zip dst := by
    intro v hv
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem (hd.symm.subset (List.mem_range.2 hv))
    refine ⟨src[i]'(by omega), ?_⟩
    rw [← e]
    have hz : i < (src.zip dst).length := by simp; omega
    have := List.getElem_mem (l := src.zip dst) hz
    simpa using this
  refine ⟨⟨po_size_writes _, po_size_writes _, fun u hu => ?_, fun v hv => ?_, fun u hu => ?_,
    fun v hv => ?_⟩, g₁⟩
  · obtain ⟨v, huv⟩ := ex₁ u hu
    rw [g₁ u v huv]; exact ltd _ (List.of_mem_zip huv).2
  · obtain ⟨u, huv⟩ := ex₂ v hv
    rw [g₂ u v huv]; exact lts _ (List.of_mem_zip huv).1
  · obtain ⟨v, huv⟩ := ex₁ u hu
    rw [g₁ u v huv, g₂ u v huv]
  · obtain ⟨u, huv⟩ := ex₂ v hv
    rw [g₂ u v huv, g₁ u v huv]

theorem po_permOfMatch_eq (prs : List (ℕ × ℕ)) :
    permOfMatch m x y prs = (writesArr m ((po_src m x prs).zip (po_dst m y prs)),
      writesArr m ((po_dst m y prs).zip (po_src m x prs))) := rfl

theorem po_mem_zip_getElem {L L' : List ℕ} {j : ℕ} (hj : j < L.length)
    (hj' : j < L'.length) : (L[j], L'[j]) ∈ L.zip L' := by
  have hz : j < (L.zip L').length := by simp [hj, hj']
  have := List.getElem_mem (l := L.zip L') hz
  simpa using this

/-- **The matched permutation is an isomorphism.** -/
theorem po_iso_correct (hx : IsColPart univ t (decPart m x))
    (hy : IsColPart univ t' (decPart m y)) {prs : List (ℕ × ℕ)} (h : matchD m x y = some prs) :
    (permOfMatch m x y prs).Valid m ∧
      PermData.denote m (permOfMatch m x y prs) • decPart m x = decPart m y := by
  obtain ⟨h1, h2, hk⟩ := po_matchD_spec h
  have hlen : ∀ pr ∈ prs, (blkL m x.2 pr.1).length = (blkL m y.2 pr.2).length :=
    fun pr hpr => by
      have := congrArg Prod.snd (hk pr hpr)
      simpa [keyD] using this
  obtain ⟨hv, hget⟩ := po_zip_valid (po_src_perm hx h1) (po_dst_perm hy h2)
  rw [po_permOfMatch_eq]
  refine ⟨hv, ?_⟩
  have happ : ∀ pr (hpr : pr ∈ prs), ∀ j (hj : j < (blkL m x.2 pr.1).length),
      (PermData.denote m (writesArr m ((po_src m x prs).zip (po_dst m y prs)),
        writesArr m ((po_dst m y prs).zip (po_src m x prs)))
        ⟨(blkL m x.2 pr.1)[j], po_lt_of_mem_blkL (List.getElem_mem _)⟩).val =
        (blkL m y.2 pr.2)[j]'(hlen pr hpr ▸ hj) := by
    intro pr hpr j hj
    rw [PermData.val_denote_apply hv]
    apply hget
    rw [po_src, po_dst, po_zip_flatMap _ _ prs hlen]
    exact List.mem_flatMap.2 ⟨pr, hpr, po_mem_zip_getElem hj (hlen pr hpr ▸ hj)⟩
  rw [po_smul_eq_iff]
  intro u
  have hu : u.val ∈ po_src m x prs := (po_src_perm hx h1).symm.subset (List.mem_range.2 u.2)
  obtain ⟨pr, hpr, hu'⟩ := List.mem_flatMap.1 hu
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hu'
  have hpr1 : pr.1 ∈ repsD m x.2 := h1.subset (List.mem_map_of_mem hpr)
  have hpr2 : pr.2 ∈ repsD m y.2 := h2.subset (List.mem_map_of_mem hpr)
  have hσu := happ pr hpr j hj
  rw [show (⟨(blkL m x.2 pr.1)[j], po_lt_of_mem_blkL (List.getElem_mem _)⟩ : Fin m) = u from
    Fin.ext e] at hσu
  have huB : u ∈ (decPart m x).blk ⟨pr.1, po_rep_lt hpr1⟩ := po_mem_blk_iff.2 hu'
  have hσuB : PermData.denote m (writesArr m ((po_src m x prs).zip (po_dst m y prs)),
      writesArr m ((po_dst m y prs).zip (po_src m x prs))) u ∈
      (decPart m y).blk ⟨pr.2, po_rep_lt hpr2⟩ :=
    po_mem_blk_iff.2 (by rw [hσu]; exact List.getElem_mem _)
  refine ⟨?_, ?_⟩
  · rw [po_col_eq hy hσuB, po_col_eq hx huB, po_decPart_col, po_decPart_col]
    exact (congrArg Prod.fst (hk pr hpr)).symm
  · rw [po_blk_eq hy hσuB, po_blk_eq hx huB]
    symm
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_smul_finset.1 hz
      have hw' := po_mem_blk_iff.1 hw
      obtain ⟨j', hj', e'⟩ := List.getElem_of_mem hw'
      have hσw := happ pr hpr j' hj'
      rw [show (⟨(blkL m x.2 pr.1)[j'], po_lt_of_mem_blkL (List.getElem_mem _)⟩ : Fin m) = w
        from Fin.ext e'] at hσw
      rw [Perm.smul_def]
      exact po_mem_blk_iff.2 (by rw [hσw]; exact List.getElem_mem _)
    · rw [Finset.card_smul_finset, po_card_blk, po_card_blk]
      exact (hlen pr hpr).symm.le

end Iso

/-! ### Programs -/

section Programs

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `xs.flatMap f`: map, then concatenate. -/
def poFlatMapProg {a' b' : Ty} (xs : var (.list a')) (f : var a' → Prog S rec var (.list b')) :
    Prog S rec var (.list b') :=
  .bind (mapList xs f) fun rows => .bind (.op1 .reverse rows) fun rr =>
  .bind (.op0 .nil) fun nil => .foldList rr nil fun acc row => .op2 .append row acc

/-- One step of the zip. -/
def poZipStepProg (st : var (.prod (.list .nat) (.list (.prod .nat .nat)))) (a : var .nat) :
    Prog S rec var (.prod (.list .nat) (.list (.prod .nat .nat))) :=
  .bind (.op1 .fst st) fun rest => .bind (.op1 .snd st) fun acc =>
  .caseList rest (.ret st) fun b rest' => .bind (.op2 .pair a b) fun ab =>
    .bind (.op2 .cons ab acc) fun acc' => .op2 .pair rest' acc'

/-- `xs.zip ys`. -/
def poZipProg (xs ys : var (.list .nat)) : Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op0 .nil) fun nl => .bind (.op2 .pair ys nl) fun st₀ =>
  .bind (.foldList xs st₀ fun st a => poZipStepProg st a) fun st =>
  .bind (.op1 .snd st) fun acc => .op1 .reverse acc

/-- `w ≠ r`. -/
def poNeProg (w r : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .natEq w r) fun e => .op1 .not e

/-- The block of `v` (`blkL`). -/
def blkLProg (m : var .nat) (blk : var (.array (.list .nat))) (v : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet blk v) fun l => .bind (.op1 .range m) fun rm =>
  Toolkit.filterList rm fun w => SoJProg.memProg w l

/-- `v` is the least point of its block (`isRepD`). -/
def isRepProg (m : var .nat) (blk : var (.array (.list .nat))) (v : var .nat) :
    Prog S rec var .bool :=
  .bind (blkLProg m blk v) fun l => .caseList l (.op0 (.boolLit false)) fun a _ => .op2 .natEq a v

/-- The representatives (`repsD`). -/
def repsProg (m : var .nat) (blk : var (.array (.list .nat))) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range m) fun rm => Toolkit.filterList rm fun v => isRepProg m blk v

/-- The transpositions of `r` with the other points of its block. -/
def withinRowProg (m : var .nat) (blk : var (.array (.list .nat))) (r : var .nat) :
    Prog S rec var (.list Ty.perm) :=
  .bind (blkLProg m blk r) fun L => .bind (Toolkit.filterList L fun w => poNeProg w r) fun L' =>
  mapList L' fun w => Toolkit.swapPairProg m r w r w

/-- `withinGensD`, from the representatives. -/
def withinProg (m : var .nat) (blk : var (.array (.list .nat))) (reps : var (.list .nat)) :
    Prog S rec var (.list Ty.perm) :=
  poFlatMapProg reps fun r => withinRowProg m blk r

/-- The colour of `r'` equals that of `r`. -/
def sameColProg (col : var (.array .nat)) (r r' : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet col r') fun a => .bind (.op2 .arrayGet col r) fun b => .op2 .natEq a b

/-- `firstRepD`, from the representatives. -/
def firstRepProg (col : var (.array .nat)) (reps : var (.list .nat)) (r : var .nat) :
    Prog S rec var .nat :=
  .bind (SoJProg.findProg reps fun r' => sameColProg col r r') fun o =>
  .caseOption o (.ret r) fun r0 => .ret r0

/-- `exchArr`. -/
def exchArrProg (m : var .nat) (L L' : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (poZipProg L L') fun z₁ => .bind (poZipProg L' L) fun z₂ =>
  .bind (.op2 .append z₁ z₂) fun ws => .bind (.op1 .range m) fun rm =>
  .bind (.op1 .arrayOfList rm) fun base => .op2 .arrayUpdate base ws

/-- `exchD`. -/
def exchDProg (m : var .nat) (L L' : var (.list .nat)) : Prog S rec var Ty.perm :=
  .bind (exchArrProg m L L') fun a => .op2 .pair a a

/-- The test of an exchange generator: `r` is not the first of its colour. -/
def exchTestProg (col : var (.array .nat)) (reps : var (.list .nat)) (r : var .nat) :
    Prog S rec var .bool :=
  .bind (firstRepProg col reps r) fun r0 => poNeProg r0 r

/-- The exchange generator of `r`. -/
def exchRowProg (m : var .nat) (col : var (.array .nat)) (blk : var (.array (.list .nat)))
    (reps : var (.list .nat)) (r : var .nat) : Prog S rec var Ty.perm :=
  .bind (firstRepProg col reps r) fun r0 => .bind (blkLProg m blk r0) fun L0 =>
  .bind (blkLProg m blk r) fun L => exchDProg m L0 L

/-- `exchGensD`, from the representatives. -/
def exchGensProg (m : var .nat) (col : var (.array .nat)) (blk : var (.array (.list .nat)))
    (reps : var (.list .nat)) : Prog S rec var (.list Ty.perm) :=
  .bind (Toolkit.filterList reps fun r => exchTestProg col reps r) fun rs =>
  mapList rs fun r => exchRowProg m col blk reps r

/-- **The stabilizer generators of a colored partition** (`partGensD`). -/
def partGensProg (m : var .nat) (x : var (.prod (.array .nat) (.array (.list .nat)))) :
    Prog S rec var (.list Ty.perm) :=
  .bind (.op1 .fst x) fun col => .bind (.op1 .snd x) fun blk => .bind (repsProg m blk) fun reps =>
  .bind (withinProg m blk reps) fun g₁ => .bind (exchGensProg m col blk reps) fun g₂ =>
  .op2 .append g₁ g₂

/-- The key of a block (`keyD`). -/
def keyProg (m : var .nat) (col : var (.array .nat)) (blk : var (.array (.list .nat)))
    (r : var .nat) : Prog S rec var (.prod .nat .nat) :=
  .bind (.op2 .arrayGet col r) fun c => .bind (blkLProg m blk r) fun l =>
  .bind (.op1 .length l) fun n => .op2 .pair c n

/-- Equality of two keys. -/
def keyEqProg (k k' : var (.prod .nat .nat)) : Prog S rec var .bool :=
  .bind (.op1 .fst k) fun a => .bind (.op1 .fst k') fun a' =>
  .bind (.op1 .snd k) fun b => .bind (.op1 .snd k') fun b' =>
  .bind (.op2 .natEq a a') fun e₁ => .bind (.op2 .natEq b b') fun e₂ => .op2 .and e₁ e₂

/-- The test of the matching search: `r'` has the key `kr`. -/
def keyTestProg (m : var .nat) (cy : var (.array .nat)) (by' : var (.array (.list .nat)))
    (kr : var (.prod .nat .nat)) (r' : var .nat) : Prog S rec var .bool :=
  .bind (keyProg m cy by' r') fun k' => keyEqProg k' kr

/-- One step of the greedy matching (`matchStep`). -/
def matchStepProg (m : var .nat) (cx : var (.array .nat)) (bx : var (.array (.list .nat)))
    (cy : var (.array .nat)) (by' : var (.array (.list .nat)))
    (st : var (.option (.prod (.list .nat) (.list (.prod .nat .nat))))) (r : var .nat) :
    Prog S rec var (.option (.prod (.list .nat) (.list (.prod .nat .nat)))) :=
  .caseOption st (.op0 .none) fun s => .bind (.op1 .fst s) fun rem =>
  .bind (.op1 .snd s) fun acc => .bind (keyProg m cx bx r) fun kr =>
  .bind (SoJProg.findProg rem fun r' => keyTestProg m cy by' kr r') fun f =>
  .caseOption f (.op0 .none) fun r' =>
    .bind (Toolkit.filterList rem fun r'' => poNeProg r'' r') fun rem' =>
    .bind (.op2 .pair r r') fun pr => .bind (.op2 .cons pr acc) fun acc' =>
    .bind (.op2 .pair rem' acc') fun s' => .op1 .some s'

/-- The end of the matching: every block of the second partition used. -/
def matchEndProg (res : var (.option (.prod (.list .nat) (.list (.prod .nat .nat))))) :
    Prog S rec var (.option (.list (.prod .nat .nat))) :=
  .caseOption res (.op0 .none) fun s => .bind (.op1 .fst s) fun rem =>
  .caseList rem (.bind (.op1 .snd s) fun acc => .op1 .some acc) fun _ _ => .op0 .none

/-- **The greedy matching** (`matchD`). -/
def matchProg (m : var .nat) (cx : var (.array .nat)) (bx : var (.array (.list .nat)))
    (cy : var (.array .nat)) (by' : var (.array (.list .nat))) :
    Prog S rec var (.option (.list (.prod .nat .nat))) :=
  .bind (repsProg m bx) fun rx => .bind (repsProg m by') fun ry =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .pair ry nl) fun s₀ => .bind (.op1 .some s₀) fun st₀ =>
  .bind (.foldList rx st₀ fun st r => matchStepProg m cx bx cy by' st r) fun res =>
  matchEndProg res

/-- The block of the first component of a pair. -/
def blkFstProg (m : var .nat) (bx : var (.array (.list .nat))) (pr : var (.prod .nat .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .fst pr) fun a => blkLProg m bx a

/-- The block of the second component of a pair. -/
def blkSndProg (m : var .nat) (by' : var (.array (.list .nat))) (pr : var (.prod .nat .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .snd pr) fun b => blkLProg m by' b

/-- `permOfMatch`. -/
def permOfMatchProg (m : var .nat) (bx by' : var (.array (.list .nat)))
    (prs : var (.list (.prod .nat .nat))) : Prog S rec var Ty.perm :=
  .bind (poFlatMapProg prs fun pr => blkFstProg m bx pr) fun src =>
  .bind (poFlatMapProg prs fun pr => blkSndProg m by' pr) fun dst =>
  .bind (poZipProg src dst) fun z₁ => .bind (poZipProg dst src) fun z₂ =>
  .bind (.op0 (.natLit 0)) fun zero => .bind (.op2 .arrayMk m zero) fun base =>
  .bind (.op2 .arrayUpdate base z₁) fun a₁ => .bind (.op2 .arrayUpdate base z₂) fun a₂ =>
  .op2 .pair a₁ a₂

/-- **An isomorphism of colored partitions** (`isoPartD`). -/
def partIsoProg (m : var .nat) (x y : var (.prod (.array .nat) (.array (.list .nat)))) :
    Prog S rec var (.option Ty.perm) :=
  .bind (.op1 .fst x) fun cx => .bind (.op1 .snd x) fun bx =>
  .bind (.op1 .fst y) fun cy => .bind (.op1 .snd y) fun by' =>
  .bind (matchProg m cx bx cy by') fun mo =>
  .caseOption mo (.op0 .none) fun prs => .bind (permOfMatchProg m bx by' prs) fun d => .op1 .some d

end Programs

/-! ### Specifications of the programs -/

/-- One step of the zip, on data. -/
def poZipStep (st : List ℕ × List (ℕ × ℕ)) (a : ℕ) : List ℕ × List (ℕ × ℕ) :=
  match st.1 with
  | [] => st
  | b :: rest' => (rest', (a, b) :: st.2)

theorem po_zip_fold : ∀ (xs ys : List ℕ) (acc : List (ℕ × ℕ)),
    xs.foldl poZipStep (ys, acc) = (ys.drop xs.length, (xs.zip ys).reverse ++ acc)
  | [], ys, acc => by simp
  | a :: xs, [], acc => by
    simp only [List.foldl_cons, poZipStep]
    have : ∀ (l : List ℕ) (acc' : List (ℕ × ℕ)), l.foldl poZipStep ([], acc') = ([], acc') := by
      intro l acc'
      induction l with
      | nil => rfl
      | cons c l ih => simpa [poZipStep] using ih
    rw [this]
    simp
  | a :: xs, b :: ys, acc => by
    simp only [List.foldl_cons, poZipStep]
    rw [po_zip_fold xs ys]
    simp

/-- The cost of `blkLProg` for lists of at most `L` entries. -/
def blkLCost (m L : ℕ) : ℕ := m * (3 * L + 6) + 5

/-- The cost of `repsProg`. -/
def repsCost (m L : ℕ) : ℕ := m * (blkLCost m L + 6) + m + 4

/-- The cost of `withinRowProg`. -/
def rowCost (m L : ℕ) : ℕ := blkLCost m L + m * (13 * m + 15) + 5

/-- The cost of `withinProg`. -/
def withinCost (m L : ℕ) : ℕ := m * (rowCost m L + m + 6) + 4

section ProgSpecs

open Cost Programs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.poFlatMapProg {a' b' : Ty} {xs : List a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote (.list b')} {F : a'.denote → List b'.denote} {c L : ℕ}
    (hf : ∀ x ∈ xs, RunsWithin X body (f x) (F x) c) (hL : ∀ x ∈ xs, (F x).length ≤ L) :
    RunsWithin X body (Align.poFlatMapProg xs f) (xs.flatMap F) (xs.length * (c + L + 6) + 4) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (a' := .list b')
    (b' := .list b') (I := fun _ => True) (c := L + 1)
    (f := fun acc row => Prog.op2 .append row acc) (F := fun acc row => row ++ acc)
    (xs.map F).reverse [] (fun acc _ row hrow => by
      refine ⟨RunsWithin.prim_le rfl ?_, trivial⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hrow)
      simpa [Prim.cost] using hL x hx) trivial
  rw [SoJProg.foldl_append_rev, List.length_reverse, List.length_map] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapList_le hf)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.1.of_eq (by simp [List.flatMap])
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map, Nat.mul_add, Nat.mul_one]
    omega

theorem RunsWithin.poZipStepProg (st : List ℕ × List (ℕ × ℕ)) (x : ℕ) :
    RunsWithin X body (Align.poZipStepProg st x) (poZipStep st x) 6 := by
  obtain ⟨rest, acc⟩ := st
  rcases rest with _ | ⟨b', rest'⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.caseList_nil (RunsWithin.ret _)
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc => simp [Prim.cost]

theorem RunsWithin.poZipProg (xs ys : List ℕ) :
    RunsWithin X body (Align.poZipProg xs ys) (xs.zip ys) (8 * xs.length + 4) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (I := fun _ => True) (c := 6)
    (f := fun st a => Align.poZipStepProg st a) (F := poZipStep) xs (ys, [])
    (fun st _ x _ => ⟨RunsWithin.poZipStepProg st x, trivial⟩) trivial
  rw [po_zip_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.append_nil, List.length_reverse,
      List.length_zip]
    have := min_le_left xs.length ys.length
    omega

theorem RunsWithin.poNeProg (w r : ℕ) :
    RunsWithin X body (Align.poNeProg w r) (w != r) 2 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.blkLProg (m : ℕ) (blk : Array (List ℕ)) (v : ℕ) {L : ℕ}
    (hL : (blk.getD v []).length ≤ L) :
    RunsWithin X body (Align.blkLProg m blk v) (blkL m blk v) (blkLCost m L) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact Toolkit.RunsWithin.filterList (c := 3 * L + 1) fun w _ =>
      (SoJProg.RunsWithin.memProg w (blk.getD v [])).mono (by omega)
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, blkLCost]
    ring_nf
    omega

theorem po_length_blkL (m : ℕ) (blk : Array (List ℕ)) (v : ℕ) : (blkL m blk v).length ≤ m := by
  unfold blkL
  exact (List.length_filter_le _ _).trans (by simp)

theorem po_length_reps (m : ℕ) (blk : Array (List ℕ)) : (repsD m blk).length ≤ m := by
  unfold repsD
  exact (List.length_filter_le _ _).trans (by simp)

theorem po_isRepD_eq (l : List ℕ) (v : ℕ) :
    (l.head? == some v) = (match l with | [] => false | a :: _ => a == v) := by
  rcases l with _ | ⟨a, l⟩
  · rfl
  · simp

theorem RunsWithin.isRepProg (m : ℕ) (blk : Array (List ℕ)) (v : ℕ) {L : ℕ}
    (hL : (blk.getD v []).length ≤ L) :
    RunsWithin X body (Align.isRepProg m blk v) (isRepD m blk v) (blkLCost m L + 2) := by
  unfold Align.isRepProg isRepD
  rw [po_isRepD_eq]
  rcases h : blkL m blk v with _ | ⟨a, l⟩
  · apply RunsWithin.mono
    case h =>
      run_step (h ▸ RunsWithin.blkLProg m blk v hL)
      exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (h ▸ RunsWithin.blkLProg m blk v hL)
      exact RunsWithin.caseList_cons (RunsWithin.prim _ _)
    case hc => simp [Prim.cost]

theorem RunsWithin.repsProg (m : ℕ) (blk : Array (List ℕ)) {L : ℕ}
    (hL : ∀ v, (blk.getD v []).length ≤ L) :
    RunsWithin X body (Align.repsProg m blk) (repsD m blk) (repsCost m L) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact (Toolkit.RunsWithin.filterList fun v _ => RunsWithin.isRepProg m blk v (hL v)).of_eq
      rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, repsCost]
    ring_nf
    omega

theorem RunsWithin.withinRowProg (m : ℕ) (blk : Array (List ℕ)) (r : ℕ) {L : ℕ}
    (hL : (blk.getD r []).length ≤ L) :
    RunsWithin X body (Align.withinRowProg m blk r)
      (((blkL m blk r).filter fun w => w != r).map (swapD m r)) (rowCost m L) := by
  have h1 := po_length_blkL m blk r
  have h2 : ((blkL m blk r).filter fun w => w != r).length ≤ m :=
    (List.length_filter_le _ _).trans h1
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.blkLProg m blk r hL)
    run_step (Toolkit.RunsWithin.filterList fun w _ => RunsWithin.poNeProg w r)
    exact RunsWithin.mapList_le fun w _ => Toolkit.RunsWithin.swapPairProg m r w r w
  case hc =>
    simp only [rowCost, Toolkit.swapPairCost]
    nlinarith

theorem RunsWithin.withinProg (m : ℕ) (blk : Array (List ℕ)) {L : ℕ}
    (hL : ∀ v, (blk.getD v []).length ≤ L) :
    RunsWithin X body (Align.withinProg m blk (repsD m blk)) (withinGensD m blk)
      (withinCost m L) := by
  have hrow : ∀ r ∈ repsD m blk,
      (((blkL m blk r).filter fun w => w != r).map (swapD m r)).length ≤ m := fun r _ => by
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (po_length_blkL m blk r)
  refine (RunsWithin.poFlatMapProg (fun r _ => RunsWithin.withinRowProg m blk r (hL r))
    hrow).mono ?_
  have := po_length_reps m blk
  simp only [withinCost]
  nlinarith

theorem po_length_flatMap_le {α β : Type*} {f : α → List β} {k : ℕ} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length ≤ k) → (l.flatMap f).length ≤ l.length * k
  | [], _ => by simp
  | a :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := po_length_flatMap_le l fun b hb => h b (List.mem_cons_of_mem _ hb)
    have := h a List.mem_cons_self
    omega

theorem RunsWithin.sameColProg (col : Array ℕ) (r r' : ℕ) :
    RunsWithin X body (Align.sameColProg col r r') (get col r' == get col r) 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.firstRepProg (col : Array ℕ) (reps : List ℕ) (r : ℕ) :
    RunsWithin X body (Align.firstRepProg col reps r)
      ((reps.find? fun r' => get col r' == get col r).getD r) (7 * reps.length + 2) := by
  have hf := SoJProg.RunsWithin.findProg (X := X) (body := body) (t := .nat) reps
    (p := fun r' => Align.sameColProg col r r') (c := 3)
    fun r' _ => RunsWithin.sameColProg col r r'
  rcases h : reps.find? (fun r' => get col r' == get col r) with _ | r0
  · apply RunsWithin.mono
    case h =>
      run_step (h ▸ hf)
      exact RunsWithin.caseOption_none (RunsWithin.ret _)
    case hc => omega
  · apply RunsWithin.mono
    case h =>
      run_step (h ▸ hf)
      exact RunsWithin.caseOption_some (RunsWithin.ret _)
    case hc => omega

/-- The cost of `exchDProg` for lists of at most `K` points. -/
def exchDCost (m K : ℕ) : ℕ := 19 * K + 3 * m + 13

theorem RunsWithin.exchArrProg (m : ℕ) (L L' : List ℕ) {K : ℕ} (hK : L.length ≤ K)
    (hK' : L'.length ≤ K) :
    RunsWithin X body (Align.exchArrProg m L L') (exchArr m L L') (exchDCost m K - 1) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.poZipProg L L')
    run_step (RunsWithin.poZipProg L' L)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.prim _ _).of_eq rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, Args.tail, List.length_range, List.size_toArray,
      List.length_append, List.length_zip, exchDCost]
    have := min_le_left L.length L'.length
    have := min_le_left L'.length L.length
    omega

theorem RunsWithin.exchDProg (m : ℕ) (L L' : List ℕ) {K : ℕ} (hK : L.length ≤ K)
    (hK' : L'.length ≤ K) :
    RunsWithin X body (Align.exchDProg m L L') (exchD m L L') (exchDCost m K) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.exchArrProg m L L' hK hK')
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, exchDCost]
    omega

theorem RunsWithin.exchTestProg (col : Array ℕ) (reps : List ℕ) (r : ℕ) :
    RunsWithin X body (Align.exchTestProg col reps r)
      ((reps.find? fun r' => get col r' == get col r).getD r != r) (7 * reps.length + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.firstRepProg col reps r)
    exact RunsWithin.poNeProg _ r
  case hc => omega

/-- The cost of `exchRowProg`. -/
def exchRowCost (m L R : ℕ) : ℕ := 7 * R + 2 * blkLCost m L + exchDCost m m + 2

/-- The cost of `exchGensProg`. -/
def exchGensCost (m L R : ℕ) : ℕ := R * (7 * R + 8) + R * (exchRowCost m L R + 3) + 5

/-- The cost of `partGensProg`. -/
def partGensCost (m L : ℕ) : ℕ :=
  repsCost m L + withinCost m L + exchGensCost m L m + m * m + 3

theorem RunsWithin.exchRowProg (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) (r : ℕ) {L : ℕ}
    (hL : ∀ v, (blk.getD v []).length ≤ L) :
    RunsWithin X body (Align.exchRowProg m col blk (repsD m blk) r)
      (exchD m (blkL m blk (firstRepD m col blk r)) (blkL m blk r))
      (exchRowCost m L (repsD m blk).length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.firstRepProg col (repsD m blk) r)
    run_step (RunsWithin.blkLProg m blk _ (hL _))
    run_step (RunsWithin.blkLProg m blk r (hL r))
    exact RunsWithin.exchDProg m _ _ (po_length_blkL m blk _) (po_length_blkL m blk r)
  case hc =>
    simp only [exchRowCost]
    omega

theorem RunsWithin.exchGensProg (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) {L : ℕ}
    (hL : ∀ v, (blk.getD v []).length ≤ L) :
    RunsWithin X body (Align.exchGensProg m col blk (repsD m blk)) (exchGensD m col blk)
      (exchGensCost m L (repsD m blk).length) := by
  apply RunsWithin.mono
  case h =>
    run_step (Toolkit.RunsWithin.filterList fun r _ =>
      RunsWithin.exchTestProg col (repsD m blk) r)
    exact (RunsWithin.mapList_le fun r _ => RunsWithin.exchRowProg m col blk r hL).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (List.length_filter_le _ _)) 2)
  case hc =>
    have e : 7 * (repsD m blk).length + 4 + 4 = 7 * (repsD m blk).length + 8 := by omega
    rw [e]
    simp only [exchGensCost]
    omega

theorem RunsWithin.partGensProg (m : ℕ) (x : Array ℕ × Array (List ℕ)) {L : ℕ}
    (hL : ∀ v, (x.2.getD v []).length ≤ L) :
    RunsWithin X body (Align.partGensProg m x) (partGensD m x) (partGensCost m L) := by
  have hR := po_length_reps m x.2
  have hW : (withinGensD m x.2).length ≤ m * m := by
    refine (po_length_flatMap_le _ fun r _ => ?_).trans (Nat.mul_le_mul_right m hR)
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (po_length_blkL m x.2 r)
  have hE : exchGensCost m L (repsD m x.2).length ≤ exchGensCost m L m := by
    simp only [exchGensCost, exchRowCost]
    nlinarith
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.repsProg m x.2 hL)
    run_step (RunsWithin.withinProg m x.2 hL)
    run_step (RunsWithin.exchGensProg m x.1 x.2 hL)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head, partGensCost]
    omega

/-- The cost of `keyProg`. -/
def keyCost (m L : ℕ) : ℕ := blkLCost m L + m + 3

/-- The cost of `matchStepProg` with at most `R` unused representatives. -/
def matchStepCost (m Lx Ly R : ℕ) : ℕ := keyCost m Lx + R * (keyCost m Ly + 11) + 6 * R + 14

/-- The cost of `matchProg`. -/
def matchCost (m Lx Ly : ℕ) : ℕ :=
  repsCost m Lx + repsCost m Ly + m * (matchStepCost m Lx Ly m + 1) + 8

/-- The cost of `permOfMatchProg` for `P` pairs. -/
def permCost (m Lx Ly P : ℕ) : ℕ :=
  P * (blkLCost m Lx + m + 7) + P * (blkLCost m Ly + m + 7) + 18 * (P * m) + 3 * m + 21

/-- The cost of `partIsoProg`. -/
def partIsoCost (m Lx Ly : ℕ) : ℕ := matchCost m Lx Ly + permCost m Lx Ly m + 7

theorem RunsWithin.keyProg (m : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) (r : ℕ) {L : ℕ}
    (hL : (blk.getD r []).length ≤ L) :
    RunsWithin X body (Align.keyProg m col blk r) (keyD m col blk r) (keyCost m L) := by
  have := po_length_blkL m blk r
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.blkLProg m blk r hL)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head, keyCost]
    omega

theorem po_beq_pair (k k' : ℕ × ℕ) : (k.1 == k'.1 && k.2 == k'.2) = (k == k') := by
  obtain ⟨a, b⟩ := k
  obtain ⟨a', b'⟩ := k'
  rw [Bool.eq_iff_iff]
  simp [Prod.ext_iff]

theorem RunsWithin.keyEqProg (k k' : ℕ × ℕ) :
    RunsWithin X body (Align.keyEqProg k k') (k == k') 7 := by
  rw [← po_beq_pair]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.keyTestProg (m : ℕ) (cy : Array ℕ) (by' : Array (List ℕ)) (kr : ℕ × ℕ)
    (r' : ℕ) {L : ℕ} (hL : ∀ v, (by'.getD v []).length ≤ L) :
    RunsWithin X body (Align.keyTestProg m cy by' kr r') (keyD m cy by' r' == kr)
      (keyCost m L + 7) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.keyProg m cy by' r' (hL r'))
    exact RunsWithin.keyEqProg _ kr
  case hc => omega

theorem RunsWithin.matchStepProg (m : ℕ) (cx : Array ℕ) (bx : Array (List ℕ)) (cy : Array ℕ)
    (by' : Array (List ℕ)) {Lx Ly R : ℕ} (hx : ∀ v, (bx.getD v []).length ≤ Lx)
    (hy : ∀ v, (by'.getD v []).length ≤ Ly) (st : Option (List ℕ × List (ℕ × ℕ))) (r : ℕ)
    (hst : ∀ s, st = some s → s.1.length ≤ R) :
    RunsWithin X body (Align.matchStepProg m cx bx cy by' st r)
      (matchStep m (cx, bx) (cy, by') st r) (matchStepCost m Lx Ly R) := by
  rcases st with _ | ⟨rem, acc⟩
  · apply RunsWithin.mono
    case h => exact RunsWithin.caseOption_none (RunsWithin.prim _ _)
    case hc => simp [Prim.cost, matchStepCost]
  · have hR := hst _ rfl
    simp only at hR
    have hf := SoJProg.RunsWithin.findProg (X := X) (body := body) (t := .nat) rem
      (p := fun r' => Align.keyTestProg m cy by' (keyD m cx bx r) r') (c := keyCost m Ly + 7)
      fun r' _ => RunsWithin.keyTestProg m cy by' _ r' hy
    rcases h : rem.find? (fun r' => keyD m cy by' r' == keyD m cx bx r) with _ | r'
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.keyProg m cx bx r (hx r))
        run_step (h ▸ hf)
        exact (RunsWithin.caseOption_none (RunsWithin.prim _ _)).of_eq
          (by simp [matchStep, h, Prim.eval])
      case hc =>
        simp only [Prim.cost, matchStepCost]
        nlinarith [Nat.mul_le_mul_right (keyCost m Ly + 11) hR]
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.keyProg m cx bx r (hx r))
        run_step (h ▸ hf)
        run_with RunsWithin.caseOption_some _
        run_step (Toolkit.RunsWithin.filterList fun r'' _ => RunsWithin.poNeProg r'' r')
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [matchStep, h, Prim.eval])
      case hc =>
        simp only [Prim.cost, Prim.eval, matchStepCost]
        nlinarith [Nat.mul_le_mul_right (keyCost m Ly + 11) hR]

/-- The end of the matching, on data. -/
def matchEndD (res : Option (List ℕ × List (ℕ × ℕ))) : Option (List (ℕ × ℕ)) :=
  match res with
  | some ([], acc) => some acc
  | _ => none

theorem po_matchD_eq_end (m : ℕ) (x y : Array ℕ × Array (List ℕ)) :
    matchD m x y = matchEndD ((repsD m x.2).foldl (matchStep m x y) (some (repsD m y.2, []))) :=
  rfl

theorem RunsWithin.matchEndProg (res : Option (List ℕ × List (ℕ × ℕ))) :
    RunsWithin X body (Align.matchEndProg res) (matchEndD res) 5 := by
  rcases res with _ | ⟨rem, acc⟩
  · exact (RunsWithin.caseOption_none (RunsWithin.prim _ _)).mono (by simp [Prim.cost])
  · rcases rem with _ | ⟨a, rem⟩
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_nil _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_cons _
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]

theorem po_matchStep_len {m : ℕ} {x y : Array ℕ × Array (List ℕ)}
    {st : Option (List ℕ × List (ℕ × ℕ))} {r : ℕ} {s : List ℕ × List (ℕ × ℕ)}
    (h : matchStep m x y st r = some s) : ∃ s₀, st = some s₀ ∧ s.1.length ≤ s₀.1.length := by
  rcases st with _ | s₀
  · simp [matchStep] at h
  · refine ⟨s₀, rfl, ?_⟩
    simp only [matchStep, Option.bind_some, Option.map_eq_some_iff] at h
    obtain ⟨r', -, rfl⟩ := h
    exact List.length_filter_le _ _

theorem RunsWithin.matchProg (m : ℕ) (cx : Array ℕ) (bx : Array (List ℕ)) (cy : Array ℕ)
    (by' : Array (List ℕ)) {Lx Ly : ℕ} (hx : ∀ v, (bx.getD v []).length ≤ Lx)
    (hy : ∀ v, (by'.getD v []).length ≤ Ly) :
    RunsWithin X body (Align.matchProg m cx bx cy by') (matchD m (cx, bx) (cy, by'))
      (matchCost m Lx Ly) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body)
    (I := fun st => ∀ s, st = some s → s.1.length ≤ m) (c := matchStepCost m Lx Ly m)
    (f := fun st r => Align.matchStepProg m cx bx cy by' st r)
    (F := matchStep m (cx, bx) (cy, by')) (repsD m bx) (some (repsD m by', []))
    (fun st hst r _ => ⟨RunsWithin.matchStepProg m cx bx cy by' hx hy st r hst,
      fun s hs => by
        obtain ⟨s₀, rfl, hle⟩ := po_matchStep_len hs
        exact hle.trans (hst s₀ rfl)⟩)
    (fun s hs => by
      cases hs
      exact po_length_reps m by')
  have hR := po_length_reps m bx
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.repsProg m bx hx)
    run_step (RunsWithin.repsProg m by' hy)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    exact (RunsWithin.matchEndProg _).of_eq (po_matchD_eq_end m (cx, bx) (cy, by')).symm
  case hc =>
    simp only [Prim.cost, matchCost]
    nlinarith [Nat.mul_le_mul_right (matchStepCost m Lx Ly m + 1) hR]

theorem RunsWithin.blkFstProg (m : ℕ) (bx : Array (List ℕ)) (pr : ℕ × ℕ) {L : ℕ}
    (hL : ∀ v, (bx.getD v []).length ≤ L) :
    RunsWithin X body (Align.blkFstProg m bx pr) (blkL m bx pr.1) (blkLCost m L + 1) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.blkLProg m bx _ (hL _)
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.blkSndProg (m : ℕ) (by' : Array (List ℕ)) (pr : ℕ × ℕ) {L : ℕ}
    (hL : ∀ v, (by'.getD v []).length ≤ L) :
    RunsWithin X body (Align.blkSndProg m by' pr) (blkL m by' pr.2) (blkLCost m L + 1) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.blkLProg m by' _ (hL _)
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.permOfMatchProg (m : ℕ) (cx : Array ℕ) (bx : Array (List ℕ)) (cy : Array ℕ)
    (by' : Array (List ℕ)) (prs : List (ℕ × ℕ)) {Lx Ly : ℕ}
    (hx : ∀ v, (bx.getD v []).length ≤ Lx) (hy : ∀ v, (by'.getD v []).length ≤ Ly) :
    RunsWithin X body (Align.permOfMatchProg m bx by' prs) (permOfMatch m (cx, bx) (cy, by') prs)
      (permCost m Lx Ly prs.length) := by
  have hs : (prs.flatMap fun pr => blkL m bx pr.1).length ≤ prs.length * m :=
    po_length_flatMap_le _ fun pr _ => po_length_blkL m bx _
  have hd : (prs.flatMap fun pr => blkL m by' pr.2).length ≤ prs.length * m :=
    po_length_flatMap_le _ fun pr _ => po_length_blkL m by' _
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.poFlatMapProg (fun pr _ => RunsWithin.blkFstProg m bx pr hx)
      fun pr _ => po_length_blkL m bx _)
    run_step (RunsWithin.poFlatMapProg (fun pr _ => RunsWithin.blkSndProg m by' pr hy)
      fun pr _ => po_length_blkL m by' _)
    run_step (RunsWithin.poZipProg _ _)
    run_step (RunsWithin.poZipProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.prim _ _).of_eq rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, Args.tail, Array.size_replicate, List.length_zip,
      permCost]
    have := min_le_left (prs.flatMap fun pr => blkL m bx pr.1).length
      (prs.flatMap fun pr => blkL m by' pr.2).length
    have := min_le_left (prs.flatMap fun pr => blkL m by' pr.2).length
      (prs.flatMap fun pr => blkL m bx pr.1).length
    nlinarith

theorem RunsWithin.partIsoProg (m : ℕ) (x y : Array ℕ × Array (List ℕ)) {Lx Ly : ℕ}
    (hx : ∀ v, (x.2.getD v []).length ≤ Lx) (hy : ∀ v, (y.2.getD v []).length ≤ Ly) :
    RunsWithin X body (Align.partIsoProg m x y) (isoPartD m x y) (partIsoCost m Lx Ly) := by
  rcases h : matchD m x y with _ | prs
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (h ▸ RunsWithin.matchProg m x.1 x.2 y.1 y.2 hx hy)
      exact (RunsWithin.caseOption_none (RunsWithin.prim _ _)).of_eq
        (by simp [isoPartD, h, Prim.eval])
    case hc =>
      simp only [Prim.cost, partIsoCost]
      omega
  · have hP : prs.length ≤ m := by
      have := (po_matchD_spec h).1.length_eq
      rw [List.length_map] at this
      rw [this]
      exact po_length_reps m x.2
    have hmono : permCost m Lx Ly prs.length ≤ permCost m Lx Ly m := by
      simp only [permCost]
      nlinarith
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (h ▸ RunsWithin.matchProg m x.1 x.2 y.1 y.2 hx hy)
      run_with RunsWithin.caseOption_some _
      run_step (RunsWithin.permOfMatchProg m x.1 x.2 y.1 y.2 prs hx hy)
      exact (RunsWithin.prim _ _).of_eq (by simp [isoPartD, h, Prim.eval])
    case hc =>
      simp only [Prim.cost, partIsoCost]
      omega

/-- **The generators' cost is polynomial**: at most `200 (m + 1)³ (L + 1)`. -/
theorem partGensCost_le (m L : ℕ) : partGensCost m L ≤ 200 * (m + 1) ^ 3 * (L + 1) := by
  simp only [partGensCost, repsCost, withinCost, rowCost, exchGensCost, exchRowCost, exchDCost,
    blkLCost]
  nlinarith [Nat.zero_le (m * m * L), Nat.zero_le (m * m * m * L), Nat.zero_le (m * m * m),
    Nat.zero_le (m * m), Nat.zero_le (m * L)]

/-- **The isomorphism search's cost is polynomial**: at most `300 (m + 1)⁴ (Lx + Ly + 1)`. -/
theorem partIsoCost_le (m Lx Ly : ℕ) :
    partIsoCost m Lx Ly ≤ 300 * (m + 1) ^ 4 * (Lx + Ly + 1) := by
  simp only [partIsoCost, matchCost, matchStepCost, keyCost, permCost, repsCost, blkLCost]
  nlinarith [Nat.zero_le (m * m * Lx), Nat.zero_le (m * m * Ly), Nat.zero_le (m * m * m * Lx),
    Nat.zero_le (m * m * m * Ly), Nat.zero_le (m * m * m), Nat.zero_le (m * m),
    Nat.zero_le (m * Lx), Nat.zero_le (m * Ly), Nat.zero_le (m * m * m * m),
    Nat.zero_le (m * m * m * m * Lx), Nat.zero_le (m * m * m * m * Ly)]

end ProgSpecs

section Wf

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ : var₁ .nat} {m₂ : var₂ .nat}
  {x₁ y₁ : var₁ (.prod (.array .nat) (.array (.list .nat)))}
  {x₂ y₂ : var₂ (.prod (.array .nat) (.array (.list .nat)))}

theorem wf_partGensProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hx : ⟨.prod (.array .nat) (.array (.list .nat)), x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (partGensProg m₁ x₁) (partGensProg m₂ x₂) := by
  unfold partGensProg repsProg isRepProg blkLProg withinProg withinRowProg poNeProg
    poFlatMapProg Toolkit.swapPairProg Toolkit.spProg exchGensProg exchTestProg firstRepProg
    sameColProg SoJProg.findProg exchRowProg exchDProg exchArrProg poZipProg poZipStepProg
    Toolkit.filterList SoJProg.memProg mapList anyList
  prog_wf

theorem wf_partIsoProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hx : ⟨.prod (.array .nat) (.array (.list .nat)), x₁, x₂⟩ ∈ Γ)
    (hy : ⟨.prod (.array .nat) (.array (.list .nat)), y₁, y₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (partIsoProg m₁ x₁ y₁) (partIsoProg m₂ x₂ y₂) := by
  unfold partIsoProg matchProg matchStepProg keyProg keyTestProg keyEqProg matchEndProg
    permOfMatchProg blkFstProg blkSndProg repsProg isRepProg blkLProg poNeProg poFlatMapProg
    SoJProg.findProg poZipProg poZipStepProg Toolkit.filterList SoJProg.memProg mapList anyList
  prog_wf

end Wf

/-! ### The structure operations -/

/-- **Colored partitions satisfy what Align needs.** -/
theorem partOps_spec (m : ℕ) : (partOps m).Spec (PartValid m) where
  gens_valid := fun _ ⟨_, hx⟩ _ hg => partGens_valid hx hg
  gens_closure := fun _ ⟨_, hx⟩ => partGens_closure hx
  iso_some := fun x y ⟨_, hx⟩ ⟨_, hy⟩ σ h => by
    simp only [partOps, isoPartD, Option.map_eq_some_iff] at h
    obtain ⟨prs, hprs, rfl⟩ := h
    exact po_iso_correct hx hy hprs
  iso_none := fun x y ⟨_, hx⟩ ⟨_, hy⟩ h σ hσ => by
    simp only [partOps, isoPartD, Option.map_eq_none_iff] at h
    have := po_matchD_isSome (po_keys_perm hx hy hσ)
    rw [h] at this
    exact absurd this (by simp)

end GraphIso.Align
