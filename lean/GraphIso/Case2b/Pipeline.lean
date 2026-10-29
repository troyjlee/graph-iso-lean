module

public import GraphIso.SoJTree.Trees
public import GraphIso.Toolkit.Orbital
public import GraphIso.Toolkit.Reduce
public import GraphIso.SoJProg.WLSets
public import GraphIso.Recursion.Primitive
public import GraphIso.Align.Trim

/-!
# Case 2b on data: the pipeline of one choice

Stage 14h, item 3 (`PLAN-14.md` §12), the data level. For a choice of an individualized tuple
`S` and a pair `(a, b)`, the leaves of Case 2b are computed from data:

1. `F_(S)`, the pointwise stabilizer of the positions of `S` (`iterStabModel`);
2. restricted to the positions of `Φ ∖ S`, numbered `0, …, m' − 1` in increasing order of base
   indices (`phiSD`), and generated at degree `m'` (`resModel`);
3. its orbital array (`orbitalModel` with base `[0, m')`) and the colouring of the orbital of
   `(a, b)`, written transposed (`tcolD`) for milestone 10's tuple encoding;
4. the 2-ary Weisfeiler–Leman refinement (`wlA`), transposed back into a row-major `m' × m'`
   colouring (`wlColD`): its entry `(u, v)` is `wlRel` of the orbital relation
   (`colOf_wlColD`);
5. the disconnected colours on data (stage 14c's `disconnD`);
6. if some colour is disconnected, the components of the least one (`compLeafD`); otherwise the
   leaves of `soj` (stage 14d's `sojProg`, data model `sojD`) with `t = (m' + 3) / 2`, trimmed
   (`trimD`).

Every leaf is then extended to the base `Fin m` (`extD`): a colored partition gets colour
`col + 1` on `Φ ∖ S` and the rest of the base as one block of colour `0`; a Johnson embedding is
transported along the numbering. `choiceLeavesD` is the list of one choice, `allLeavesD` the
concatenation over all `(d − 1)`-tuples of distinct points of `Φ` (`tuplesD`) and all pairs of
distinct indices (`pairsD`), and `firstLeafD` the first leaf of the first choice.

Decoding:

* `colOf_wlColD`: the colouring is `wlRel (arrRel L m' a b)`; with stage 14b's
  `arrRel_orbital`, `arrRel` is the orbital of `(a, b)` when the action is transitive;
* `decodeOut_compLeafD`, `disconn_wlCol`: the components leaf and the disconnected colours are
  milestone 11's;
* `sojD_leafMs`: the leaves of `soj`, as multisets (stage 14d's `sojProg_leafMs`);
* `decodeOut_trimD`: trimming is `trimOut`;
* `decodeOut_extD`: the extension is `pipeExt` along the numbering;
* `mem_tuplesD`, `mem_pairsD`: the enumerations.
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv Finset GraphIso GraphIso.Cost GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree
  GraphIso.Toolkit GraphIso.Recursion GraphIso.Coherent

/-! ### The numbering of `Φ ∖ S` -/

/-- The points of `Φ ∖ S` among the base indices `0, …, m − 1`, in increasing order. -/
def phiSD (m : ℕ) (Φ S : List ℕ) : List ℕ :=
  (List.range m).filter fun v => decide (v ∈ Φ ∧ v ∉ S)

/-- The positions of base indices: `n + v`. -/
def ptsD (n : ℕ) (l : List ℕ) : List ℕ := l.map (n + ·)

/-! ### The group of one choice -/

section Group

variable {D : Ty}

/-- `F_(S)`: the pointwise stabilizer of the positions of `S`. -/
def fsModel (O : Oracle (groupSig D)) (n : ℕ) (F : GroupData D.denote) (S : List ℕ) :
    GroupData D.denote :=
  iterStabModel O F (ptsD n S)

/-- The generators of a group restricted to the positions of `ΦS`, renumbered `0, …, |ΦS| − 1`. -/
def rgensD (N n : ℕ) (gs : GensData) (ΦS : List ℕ) : GensData :=
  GensData.restrictTo (WinData.pos N (WinData.ofPoints N (ptsD n ΦS))) (ptsD n ΦS) gs

/-- The restricted group, generated at degree `m'`. -/
def resModel (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ S : List ℕ) :
    GroupData D.denote :=
  O.run GroupOp.generate ((phiSD (N - n) Φ S).length,
    rgensD N n (fsModel O n F S).2.1 (phiSD (N - n) Φ S))

/-- The orbital array of the restricted group (base `[0, m')`). -/
def orbArrD (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ S : List ℕ) :
    Array ℕ :=
  orbitalModel O 0 (resModel O N n F Φ S)

end Group

/-! ### Colourings -/

/-- The colouring of the orbital of `(a, b)` of an `m × m` array `L`, transposed: the entry at
`u + v m` is `relCol` at `(u, v)`, milestone 10's encoding of the pair `![u, v]`. -/
def tcolD (L : Array ℕ) (m a b : ℕ) : Array ℕ := matrixOf m fun i j => relColEntry L m a b j i

/-- Transposing an `m × m` array. -/
def transD (m : ℕ) (W : Array ℕ) : Array ℕ := matrixOf m fun u v => get W (v * m + u)

/-- The 2-ary Weisfeiler–Leman refinement of a transposed colouring, row-major. -/
def wlColD (m : ℕ) (T : Array ℕ) : Array ℕ := transD m (wlA 2 m T).1

/-- The colour function of a row-major `m × m` array, as stage 14c reads it. -/
def colFn (m : ℕ) (C : Array ℕ) : ℕ → ℕ → ℕ := fA (offsArr m) C

/-! ### Leaves -/

/-- The components leaf: colour `0`, the components of colour `r` of `C` as blocks. -/
def compLeafD (m : ℕ) (C : Array ℕ) (r : ℕ) : OutD :=
  partD (compPart (colFn m C) m (List.range m) r).2.1.1
    (compPart (colFn m C) m (List.range m) r).2.1.2

/-- The leaves of `soj (colOf m C) t`, as stage 14d's `sojProg` computes them. -/
def sojD (m t : ℕ) (C : Array ℕ) : List OutD :=
  worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t C)).2
    (splitI (tr_sojItems m t C)).1

/-- Trim a Johnson leaf on `Fin m`: its cell lists off `V₀` become empty. -/
def trimD (m : ℕ) (o : OutD) : OutD :=
  if o.1 = 2 then
    johnD o.2.2.1 o.2.2.2.1 o.2.2.2.2.1
      ((List.range m).map fun v => if v ∈ o.2.2.1 then o.2.2.2.2.2.getD v [] else []).toArray
  else o

/-- A list of indices of `ΦS` moved to base indices (entries at or above `|ΦS|` dropped). -/
def mapE (ΦS : List ℕ) (l : List ℕ) : List ℕ :=
  (l.filter fun i => decide (i < ΦS.length)).map fun i => ΦS.getD i 0

/-- **The extension of a leaf to the base `Fin m`**, along the numbering `ΦS`. -/
def extD (m : ℕ) (ΦS : List ℕ) (o : OutD) : OutD :=
  if o.1 = 1 then
    partD
      ((List.range m).map fun v =>
        if v ∈ ΦS then get o.2.1.1 (ΦS.idxOf v) + 1 else 0).toArray
      ((List.range m).map fun v =>
        if v ∈ ΦS then mapE ΦS (o.2.1.2.getD (ΦS.idxOf v) [])
        else (List.range m).filter fun w => decide (w ∉ ΦS)).toArray
  else if o.1 = 2 then
    johnD (mapE ΦS o.2.2.1) (o.2.2.2.1.map (mapE ΦS)) o.2.2.2.2.1
      ((List.range m).map fun v =>
        if v ∈ ΦS then o.2.2.2.2.2.getD (ΦS.idxOf v) [] else []).toArray
  else o

/-! ### One choice -/

section Choice

variable {D : Ty}

/-- The colouring of one choice: `wlRel` of the orbital of `(a, b)` on `Φ ∖ S`. -/
def wlColOf (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ S : List ℕ)
    (a b : ℕ) : Array ℕ :=
  wlColD (phiSD (N - n) Φ S).length
    (tcolD (orbArrD O N n F Φ S) (phiSD (N - n) Φ S).length a b)

/-- The leaves on `Fin m'` of a colouring `C`: the components leaf if a colour is disconnected,
else the trimmed leaves of `soj`. -/
def leavesOfD (m' : ℕ) (C : Array ℕ) : List OutD :=
  match disconnD (colFn m' C) (List.range m') with
  | r :: rs => [compLeafD m' C (minD (r :: rs))]
  | [] => (sojD m' ((m' + 3) / 2) C).map (trimD m')

/-- **The leaves of one choice**, extended to the base. -/
def choiceLeavesD (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ S : List ℕ)
    (a b : ℕ) : List OutD :=
  (leavesOfD (phiSD (N - n) Φ S).length (wlColOf O N n F Φ S a b)).map
    (extD (N - n) (phiSD (N - n) Φ S))

/-- One extension step of the tuples: put in front every entry of `l` not yet in the tuple. -/
def tupStep (l : List ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap fun T => (l.filter fun x => decide (x ∉ T)).map (· :: T)

/-- The `j`-tuples of distinct entries of `l` (all orders), built by `j` steps. -/
def tuplesD (l : List ℕ) (j : ℕ) : List (List ℕ) :=
  (List.range j).foldl (fun acc _ => tupStep l acc) [[]]

/-- The pairs of distinct indices below `m`. -/
def pairsD (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun a => ((List.range m).filter fun b => b != a).map (a, ·)

/-- **All leaves**: every `j`-tuple `S` of distinct points of `Φ`, every pair of distinct
indices of `Φ ∖ S`. -/
def allLeavesD (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ : List ℕ)
    (j : ℕ) : List OutD :=
  (tuplesD Φ j).flatMap fun S =>
    (pairsD (phiSD (N - n) Φ S).length).flatMap fun ab => choiceLeavesD O N n F Φ S ab.1 ab.2

/-- **The first leaf**: the first leaf of the first tuple and the pair `(0, 1)`. -/
def firstLeafD (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ : List ℕ)
    (j : ℕ) : Option OutD :=
  match tuplesD Φ j with
  | S :: _ => (choiceLeavesD O N n F Φ S 0 1).head?
  | [] => none

end Choice

/-! ### Decoding -/

section Decode

/-- An entry of the orbital colouring is `relCol` of `arrRel`. -/
theorem relColEntry_eq (L : Array ℕ) {m : ℕ} (a b : ℕ) (u v : Fin m) :
    relColEntry L m a b u v = relCol (arrRel L m a b) u v := by
  have := relColModel_spec L a b u v
  rwa [relColModel, get_matrixOf u.2 v.2] at this

theorem cp2_enc_two {m : ℕ} (y : Coherent.Tup 2 m) : enc y = (y 1).val * m + (y 0).val := by
  rw [enc_eq_sum, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one]
  ring

/-- **The colouring of one choice is `wlRel` of the orbital relation.** -/
theorem colOf_wlColD (L : Array ℕ) {m : ℕ} (a b : ℕ) (u v : Fin m) :
    colOf m (wlColD m (tcolD L m a b)) u v = wlRel (arrRel L m a b) u v := by
  unfold colOf wlColD transD
  rw [get_matrixOf u.2 v.2]
  have henc : enc (k := 2) (m := m) ![u, v] = v.val * m + u.val := by
    rw [cp2_enc_two]
    rfl
  rw [← henc, get_wlA_eq_wlOn (f := id) Function.bijective_id
    (fun x => relCol (arrRel L m a b) (x 0) (x 1)) ?_ ![u, v]]
  · rfl
  · intro y
    unfold toFun tcolD
    rw [cp2_enc_two, get_matrixOf (y 1).2 (y 0).2, relColEntry_eq]
    rfl

theorem setOf_range (m : ℕ) : setOf m (List.range m) = univ := by
  ext x
  simp [mem_setOf, x.isLt]

/-- **The components leaf** decodes to milestone 11's. -/
theorem decodeOut_compLeafD (m : ℕ) (C : Array ℕ) (r : ℕ) :
    decodeOut m (compLeafD m C r) = some (.inl ⟨fun _ => 0, comp univ (colOf m C) r⟩) := by
  unfold compLeafD
  rw [decodeOut_partD]
  simp only [compPart, partLeaf, cpartOf, Option.some.injEq, Sum.inl.injEq, CPart.mk.injEq]
  refine ⟨funext fun x => get_replicate_zero x.val, funext fun x => ?_⟩
  rw [getD_toArray_range _ _ x.isLt, ← setOf_range m,
    comp_eq (fA_offsArr m C) List.nodup_range (fun y hy => List.mem_range.1 hy)]
  rfl

/-- **The disconnected colours** are milestone 11's. -/
theorem disconn_wlCol (m : ℕ) (C : Array ℕ) :
    disconn univ (colOf m C) = (disconnD (colFn m C) (List.range m)).toFinset := by
  rw [← setOf_range m]
  exact disconn_eq (fA_offsArr m C) List.nodup_range fun y hy => List.mem_range.1 hy

/-- **The leaves of `soj`**, as multisets. -/
theorem sojD_leafMs (m t : ℕ) (C : Array ℕ) :
    ((sojD m t C).map (decodeOut m) : Multiset (Option (Out (Fin m)))) =
      (soj (colOf m C) t).leafMs :=
  sojProg_leafMs m t C

theorem cp2_decodeOut_not_two {m : ℕ} {o : OutD} (h : o.1 ≠ 2) :
    GraphIso.Align.trimOut (decodeOut m o) = decodeOut m o := by
  unfold decodeOut
  split_ifs <;> rfl

/-- **Trimming on data is `trimOut`.** -/
theorem decodeOut_trimD (m : ℕ) (o : OutD) :
    decodeOut m (trimD m o) = GraphIso.Align.trimOut (decodeOut m o) := by
  unfold trimD
  split_ifs with h
  · have hd : decodeOut m o = some (.inr (jembOf m o.2.2.1 o.2.2.2.1 o.2.2.2.2.1 o.2.2.2.2.2)) := by
      unfold decodeOut
      simp [h]
    rw [decodeOut_johnD, hd]
    simp only [GraphIso.Align.trimOut, GraphIso.Align.trimJ, jembOf, Option.some.injEq,
      Sum.inr.injEq, JEmb.mk.injEq, true_and]
    funext x
    rw [getD_toArray_range _ _ x.isLt]
    by_cases hx : x.val ∈ o.2.2.1
    · simp [hx, mem_setOf]
    · simp [hx, mem_setOf, famIdx]
  · exact (cp2_decodeOut_not_two h).symm

/-! ### The extension along the numbering -/

/-- The numbering of `ΦS` as a map into the base. -/
def eFin {m : ℕ} (ΦS : List ℕ) (h : ∀ v ∈ ΦS, v < m) (i : Fin ΦS.length) : Fin m :=
  ⟨ΦS[i], h _ (List.getElem_mem _)⟩

/-- Its partial inverse. -/
def eInv {m : ℕ} (ΦS : List ℕ) (v : Fin m) : Option (Fin ΦS.length) :=
  if h : v.val ∈ ΦS then some ⟨ΦS.idxOf v.val, List.idxOf_lt_length_of_mem h⟩ else none

/-- **The extension of a leaf** on `Fin m'` to `Fin m` along `e` with partial inverse `ei`: a
colored partition gets colour `col + 1` on the image and the rest as one block of colour `0`;
a Johnson embedding is moved by `e`, with no cells off the image. -/
def pipeExt {m m' : ℕ} (e : Fin m' → Fin m) (ei : Fin m → Option (Fin m')) :
    Option (Out (Fin m')) → Option (Out (Fin m))
  | some (.inl p) => some (.inl ⟨fun v => match ei v with
      | some i => p.col i + 1
      | none => 0, fun v => match ei v with
      | some i => (p.blk i).image e
      | none => univ.filter fun w => ei w = none⟩)
  | some (.inr J) => some (.inr ⟨J.V0.image e, J.Λ.image (Finset.image e), J.s,
      fun v => match ei v with
      | some i => (J.f i).image (Finset.image e)
      | none => ∅⟩)
  | none => none

variable {m : ℕ} {ΦS : List ℕ}

theorem cp2_eInv_some (h : ∀ v ∈ ΦS, v < m) {v : Fin m} (hv : v.val ∈ ΦS) :
    ∃ i, eInv ΦS v = some i ∧ i.val = ΦS.idxOf v.val ∧ eFin ΦS h i = v := by
  refine ⟨⟨ΦS.idxOf v.val, List.idxOf_lt_length_of_mem hv⟩, by simp [eInv, hv], rfl, ?_⟩
  exact Fin.ext (List.getElem_idxOf _)

theorem cp2_eInv_none {v : Fin m} (hv : v.val ∉ ΦS) : eInv ΦS v = none := by
  simp [eInv, hv]

theorem cp2_eInv_none_iff {v : Fin m} : eInv ΦS v = none ↔ v.val ∉ ΦS := by
  unfold eInv
  split_ifs with h <;> simp [h]

/-- Moved index lists decode to images. -/
theorem setOf_mapE (h : ∀ v ∈ ΦS, v < m) (l : List ℕ) :
    setOf m (mapE ΦS l) = (setOf ΦS.length l).image (eFin ΦS h) := by
  ext x
  simp only [mem_setOf, mapE, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_image]
  constructor
  · rintro ⟨i, ⟨hil, hi⟩, hx⟩
    refine ⟨⟨i, hi⟩, hil, Fin.ext ?_⟩
    simp only [eFin]
    rw [← hx, List.getD_eq_getElem _ _ hi]
    rfl
  · rintro ⟨i, hil, rfl⟩
    exact ⟨i.val, ⟨hil, i.isLt⟩, by simp [eFin]⟩

theorem cp2_get_toArray {g : ℕ → ℕ} {v : ℕ} (hv : v < m) :
    get ((List.range m).map g).toArray v = g v := by
  unfold get
  exact getD_toArray_range g 0 hv

theorem cp2_famOf_map (h : ∀ v ∈ ΦS, v < m) (cs : List (List ℕ)) :
    famOf m (cs.map (mapE ΦS)) = (famOf ΦS.length cs).image (Finset.image (eFin ΦS h)) := by
  unfold famOf
  rw [List.map_map]
  ext t
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Function.comp_apply,
    setOf_mapE h]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem cp2_famIdx_map (h : ∀ v ∈ ΦS, v < m) (cs : List (List ℕ)) (js : List ℕ) :
    famIdx m (cs.map (mapE ΦS)) js =
      (famIdx ΦS.length cs js).image (Finset.image (eFin ΦS h)) := by
  have hcell : ∀ j, cellAt m (cs.map (mapE ΦS)) j = (cellAt ΦS.length cs j).image (eFin ΦS h) := by
    intro j
    simp only [cellAt]
    have : (cs.map (mapE ΦS)).getD j [] = mapE ΦS (cs.getD j []) :=
      List.getD_map (f := mapE ΦS) (l := cs) (n := j) (d := [])
    rw [this, setOf_mapE h]
  unfold famIdx
  ext t
  simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, hcell]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨j, hj, rfl⟩

/-- **The extension on data decodes to `pipeExt`.** -/
theorem decodeOut_extD (h : ∀ v ∈ ΦS, v < m) (o : OutD) :
    decodeOut m (extD m ΦS o) = pipeExt (eFin ΦS h) (eInv ΦS) (decodeOut ΦS.length o) := by
  unfold extD
  split_ifs with h1 h2
  · have hd : decodeOut ΦS.length o = some (.inl (cpartOf ΦS.length o.2.1.1 o.2.1.2)) := by
      unfold decodeOut
      simp [h1]
    rw [decodeOut_partD, hd]
    simp only [pipeExt, cpartOf, Option.some.injEq, Sum.inl.injEq, CPart.mk.injEq]
    constructor
    · funext v
      rw [cp2_get_toArray v.isLt]
      by_cases hv : v.val ∈ ΦS
      · obtain ⟨i, hi, hiv, -⟩ := cp2_eInv_some h hv
        simp only [hv, ↓reduceIte, hi, hiv]
      · simp only [hv, ↓reduceIte, cp2_eInv_none hv]
    · funext v
      rw [getD_toArray_range _ _ v.isLt]
      by_cases hv : v.val ∈ ΦS
      · obtain ⟨i, hi, hiv, -⟩ := cp2_eInv_some h hv
        simp only [hv, ↓reduceIte, hi]
        rw [setOf_mapE h, hiv]
      · simp only [hv, ↓reduceIte, cp2_eInv_none hv]
        ext w
        simp [mem_setOf, cp2_eInv_none_iff, w.isLt]
  · have hd : decodeOut ΦS.length o =
        some (.inr (jembOf ΦS.length o.2.2.1 o.2.2.2.1 o.2.2.2.2.1 o.2.2.2.2.2)) := by
      unfold decodeOut
      simp [h2]
    rw [decodeOut_johnD, hd]
    simp only [pipeExt, jembOf, Option.some.injEq, Sum.inr.injEq, JEmb.mk.injEq, true_and]
    refine ⟨setOf_mapE h _, cp2_famOf_map h _, funext fun v => ?_⟩
    rw [getD_toArray_range _ _ v.isLt]
    by_cases hv : v.val ∈ ΦS
    · obtain ⟨i, hi, hiv, -⟩ := cp2_eInv_some h hv
      simp only [hv, ↓reduceIte, hi]
      rw [cp2_famIdx_map h, hiv]
    · simp only [hv, ↓reduceIte, cp2_eInv_none hv]
      simp [famIdx]
  · have hd : decodeOut ΦS.length o = none := by
      unfold decodeOut
      simp [h1, h2]
    have hd' : decodeOut m o = none := by
      unfold decodeOut
      simp [h1, h2]
    rw [hd, hd']
    rfl

end Decode

/-! ### The enumerations -/

section Enum

theorem tuplesD_zero (l : List ℕ) : tuplesD l 0 = [[]] := rfl

theorem tuplesD_succ (l : List ℕ) (j : ℕ) : tuplesD l (j + 1) = tupStep l (tuplesD l j) := by
  simp only [tuplesD, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **The tuples**: the `j`-tuples of distinct entries of `l`. -/
theorem mem_tuplesD (l : List ℕ) : ∀ (j : ℕ) {S : List ℕ},
    S ∈ tuplesD l j ↔ S.length = j ∧ S.Nodup ∧ ∀ x ∈ S, x ∈ l
  | 0, S => by
    rw [tuplesD_zero, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, -, -⟩
      exact List.length_eq_zero_iff.1 h
  | j + 1, S => by
    rw [tuplesD_succ]
    simp only [tupStep, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨T, hT, x, ⟨hx, hxT⟩, rfl⟩
      obtain ⟨hTl, hTn, hTm⟩ := (mem_tuplesD l j).1 hT
      refine ⟨by simp [hTl], List.nodup_cons.2 ⟨hxT, hTn⟩, fun y hy => ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hTm y hy
    · rintro ⟨hlen, hnd, hmem⟩
      match S, hlen, hnd, hmem with
      | x :: T, hlen, hnd, hmem =>
        refine ⟨T, (mem_tuplesD l j).2 ⟨by simpa using hlen, (List.nodup_cons.1 hnd).2,
          fun y hy => hmem y (List.mem_cons_of_mem _ hy)⟩, x,
          ⟨hmem x List.mem_cons_self, (List.nodup_cons.1 hnd).1⟩, rfl⟩

theorem tuplesD_nodup {l : List ℕ} (hl : l.Nodup) : ∀ j, (tuplesD l j).Nodup
  | 0 => List.nodup_singleton _
  | j + 1 => by
    rw [tuplesD_succ]
    refine List.nodup_flatMap.2 ⟨fun T _ => ?_, ?_⟩
    · exact (hl.filter _).map fun _ _ h => (List.cons_eq_cons.1 h).1
    · refine (tuplesD_nodup hl j).pairwise_of_forall_ne fun T _ T' _ hTT => ?_
      simp only [Function.onFun, List.disjoint_left, List.mem_map]
      rintro _ ⟨x, -, rfl⟩ ⟨y, -, h⟩
      exact hTT (List.cons_eq_cons.1 h).2.symm

theorem length_tuplesD_le (l : List ℕ) : ∀ j, (tuplesD l j).length ≤ l.length ^ j
  | 0 => by simp [tuplesD_zero]
  | j + 1 => by
    rw [tuplesD_succ, tupStep, List.length_flatMap]
    calc ((tuplesD l j).map fun T =>
            ((l.filter fun x => decide (x ∉ T)).map (· :: T)).length).sum ≤
          ((tuplesD l j).map fun _ => l.length).sum := by
          refine List.sum_le_sum fun T _ => ?_
          rw [List.length_map]
          exact List.length_filter_le _ _
      _ = (tuplesD l j).length * l.length := by
          rw [List.map_const', List.sum_replicate, smul_eq_mul]
      _ ≤ l.length ^ j * l.length := Nat.mul_le_mul_right _ (length_tuplesD_le l j)
      _ = l.length ^ (j + 1) := (pow_succ _ _).symm

/-- **The pairs**: distinct indices below `m`. -/
theorem mem_pairsD {m a b : ℕ} : (a, b) ∈ pairsD m ↔ a < m ∧ b < m ∧ a ≠ b := by
  simp only [pairsD, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    bne_iff_ne, ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', b', ⟨hb', hne⟩, rfl, rfl⟩
    exact ⟨ha', hb', fun h => hne h.symm⟩
  · rintro ⟨ha, hb, hne⟩
    exact ⟨a, ha, b, ⟨hb, fun h => hne h.symm⟩, rfl, rfl⟩

theorem pairsD_nodup (m : ℕ) : (pairsD m).Nodup := by
  unfold pairsD
  refine List.nodup_flatMap.2 ⟨fun a _ => ?_, ?_⟩
  · exact ((List.nodup_range).filter _).map fun _ _ h => (Prod.mk.inj h).2
  · refine List.nodup_range.pairwise_of_forall_ne fun a _ a' _ haa => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨b, -, rfl⟩ ⟨b', -, h⟩
    exact haa (Prod.mk.inj h).1.symm

theorem length_pairsD_le (m : ℕ) : (pairsD m).length ≤ m * m := by
  unfold pairsD
  rw [List.length_flatMap]
  calc ((List.range m).map fun a =>
          (((List.range m).filter fun b => b != a).map (a, ·)).length).sum ≤
        ((List.range m).map fun _ => m).sum := by
        refine List.sum_le_sum fun a _ => ?_
        simp only [List.length_map]
        exact (List.length_filter_le _ _).trans (by simp)
    _ = m * m := by simp

end Enum

end GraphIso.Case2b
