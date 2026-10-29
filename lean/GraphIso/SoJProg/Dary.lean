module

public import GraphIso.SoJProg.WLSets
public import GraphIso.Toolkit.Labels

/-!
# The `d`-ary structure on data

Step 3 of milestone 11's `bstep` (`PLAN-14.md` §7 item 5) on data: the points are `Fin m`, the
cells are a list `cs` of index lists, distinct as sets (`v = |cs|`), and families of cells are
lists of cell indices, decoded by `cellsOf`.

* `arity v s n₁ = min s (6 ⌈log_v n₁⌉)`: `clogD`, by at most `n₁` multiplications
  (`clogD_eq`).
* The colouring `daryCol V₂ H d` on the codes of `d`-tuples of cell indices, with the
  hyperedges `H` given as index lists (`daryArr`, `toFun_daryArr`).
* The cells with a twin class of more than half of `V₂` (`bigTwinsD`, `bigTwins_decode`), by
  the twin test on codes (`twinB_iff`).
* Exercise 5.5's choice of side (`pickSideD`, `pickSide_decode`).
-/

@[expose] public section

namespace GraphIso.SoJProg

open Finset GraphIso GraphIso.Coherent GraphIso.SplitJohnson GraphIso.Cost GraphIso.Programs

/-! ### `⌈log_v n⌉` -/

/-- One step of the search for `⌈log_v n⌉`: multiply while the power is below `n`. -/
def clogStep (v n : ℕ) (st : ℕ × ℕ) : ℕ × ℕ := if st.1 < n then (v * st.1, st.2 + 1) else st

/-- `⌈log_v n⌉` by at most `n` multiplications (`0` if `v < 2`). -/
def clogD (v n : ℕ) : ℕ :=
  if v < 2 then 0 else ((List.range n).foldl (fun st _ => clogStep v n st) (1, 0)).2

theorem foldl_clogStep {v n : ℕ} (hv : 1 < v) (i : ℕ) :
    (List.range i).foldl (fun st _ => clogStep v n st) (1, 0) =
      (v ^ min i (Nat.clog v n), min i (Nat.clog v n)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, clogStep]
    rcases Nat.lt_or_ge i (Nat.clog v n) with h | h
    · rw [Nat.min_eq_left h.le, Nat.min_eq_left h]
      simp [Nat.pow_lt_of_lt_clog h, pow_succ, mul_comm]
    · rw [Nat.min_eq_right h, Nat.min_eq_right (by omega)]
      simp [Nat.not_lt.2 (Nat.le_pow_clog hv n)]

theorem clogD_eq (v n : ℕ) : clogD v n = Nat.clog v n := by
  unfold clogD
  split_ifs with hv
  · exact (Nat.clog_of_left_le_one (by omega) n).symm
  · rw [foldl_clogStep (by omega)]
    exact Nat.min_eq_right (Nat.clog_le_of_le_pow (Nat.lt_pow_self (by omega)).le)

/-! ### Families of cells -/

/-- The cells with the listed indices. -/
def cellsOf (m : ℕ) (cs : List (List ℕ)) (js : List ℕ) : Finset (Finset (Fin m)) :=
  (js.map fun j => setOf m (cs.getD j [])).toFinset

theorem getD_eq_get (cs : List (List ℕ)) (j : Fin cs.length) : cs.getD j [] = cs.get j := by
  simp [List.getD_eq_getElem?_getD]

/-- A listed cell is in a family of listed cells exactly when its index is listed. -/
theorem setOf_mem_cellsOf {m : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    {js : List ℕ} (hjs : ∀ j ∈ js, j < cs.length) {i : ℕ} (hi : i < cs.length) :
    setOf m (cs.getD i []) ∈ cellsOf m cs js ↔ i ∈ js := by
  simp only [cellsOf, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨j, hj, h⟩
    rwa [getD_inj_of_nodup hcs j (hjs j hj) i hi h] at hj
  · exact fun h => ⟨i, h, rfl⟩

/-! ### The colouring `daryCol` -/

/-- The colour of the tuple of cells with digits `ds`, for the masks of the hyperedges. -/
def daryEntry (masks : List (Array Bool)) (ds : List ℕ) : ℕ :=
  if ds.all (fun i => (ds.filter (· == i)).length == 1) then
    1 + (masks.filter fun mk => ds.all (getB mk)).length
  else 0

/-- **The colouring `daryCol`** on the codes of the `d`-tuples of `v` cells, for hyperedges
given as index lists. -/
def daryArr (v d : ℕ) (hs : List (List ℕ)) : Array ℕ :=
  ((tupList d v).map (daryEntry (hs.map (Toolkit.markArr v)))).toArray

theorem all_count_iff_nodup (ds : List ℕ) :
    ds.all (fun i => (ds.filter (· == i)).length == 1) = true ↔ ds.Nodup := by
  rw [List.nodup_iff_count_eq_one, List.all_eq_true]
  simp [List.count_eq_length_filter]

theorem nodup_digits_iff {d v : ℕ} (y : Tup d v) : (digits y).Nodup ↔ Function.Injective y := by
  rw [digits, List.nodup_ofFn]
  exact ⟨fun h a b hab => h (congrArg Fin.val hab), fun h a b hab => h (Fin.ext hab)⟩

theorem card_image_cells_iff {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    (y : Tup d cs.length) :
    (univ.image fun i => ((cellSub m cs ∘ y) i).val).card = d ↔ Function.Injective y := by
  have hinj : Function.Injective fun j => (cellSub m cs j).val :=
    Subtype.val_injective.comp (cellSub_bijective hcs).1
  calc _ ↔ (univ.image fun i => ((cellSub m cs ∘ y) i).val).card = (univ : Finset (Fin d)).card :=
        by rw [Finset.card_univ, Fintype.card_fin]
    _ ↔ Set.InjOn (fun i => ((cellSub m cs ∘ y) i).val) ↑(univ : Finset (Fin d)) :=
        Finset.card_image_iff
    _ ↔ Function.Injective y := by
        rw [Finset.coe_univ, Set.injOn_univ]
        exact ⟨fun h => Function.Injective.of_comp (f := fun j => (cellSub m cs j).val) h,
          fun h => hinj.comp h⟩

theorem subset_cellsOf_iff {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    {h : List ℕ} (hlt : ∀ j ∈ h, j < cs.length) (y : Tup d cs.length) :
    (univ.image fun i => ((cellSub m cs ∘ y) i).val) ⊆ cellsOf m cs h ↔
      (digits y).all (getB (Toolkit.markArr cs.length h)) = true := by
  rw [List.all_eq_true, Finset.image_subset_iff]
  simp only [digits, List.mem_ofFn, Function.comp_apply, Finset.mem_univ, forall_const,
    forall_exists_index, forall_apply_eq_imp_iff, Toolkit.getB_markArr]
  refine forall_congr' fun i => ?_
  rw [coe_cellSub, ← getD_eq_get, setOf_mem_cellsOf hcs hlt (y i).2]
  exact ⟨fun h' => ⟨(y i).2, h'⟩, fun h' => h'.2⟩

/-- **The colouring on codes is `daryCol`**, for duplicate-free cells and hyperedges `hs`
(index lists) that are distinct as families of cells. -/
theorem toFun_daryArr {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    {hs : List (List ℕ)} (hlt : ∀ h ∈ hs, ∀ j ∈ h, j < cs.length)
    (hnd : (hs.map (cellsOf m cs)).Nodup) (y : Tup d cs.length) :
    toFun (daryArr cs.length d hs) y =
      daryCol (famOf m cs) (hs.map (cellsOf m cs)).toFinset d (cellSub m cs ∘ y) := by
  rw [toFun, daryArr, get_tupMap, daryEntry, daryCol]
  have hA := (all_count_iff_nodup (digits y)).trans
    ((nodup_digits_iff y).trans (card_image_cells_iff hcs y).symm)
  by_cases h : (univ.image fun i => ((cellSub m cs ∘ y) i).val).card = d
  · simp only [hA.2 h, h, ↓reduceIte]
    congr 1
    have e : ((hs.map (cellsOf m cs)).toFinset.filter fun e =>
        (univ.image fun i => ((cellSub m cs ∘ y) i).val) ⊆ e) =
        ((hs.map (cellsOf m cs)).filter fun e =>
          decide ((univ.image fun i => ((cellSub m cs ∘ y) i).val) ⊆ e)).toFinset := by
      ext e
      simp
    rw [e, List.toFinset_card_of_nodup (hnd.filter _), List.filter_map, List.filter_map,
      List.length_map, List.length_map]
    congr 1
    refine List.filter_congr fun e he => ?_
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact subset_cellsOf_iff hcs (hlt e he) y |>.symm
  · have h' : ¬ ((digits y).all fun i => ((digits y).filter (· == i)).length == 1) = true :=
      fun h' => h (hA.1 h')
    simp only [h, h', Bool.false_eq_true, ↓reduceIte]

/-! ### The twin test and `bigTwins` -/

/-- The transposition of `u` and `w`, on indices. -/
def swapN (u w i : ℕ) : ℕ := if i == u then w else if i == w then u else i

theorem swapN_val {v : ℕ} (u w z : Fin v) : swapN u w z = (Equiv.swap u w z).val := by
  rw [Equiv.swap_apply_def, swapN]
  by_cases h1 : z = u
  · simp [h1]
  · by_cases h2 : z = w
    · have hwu : w ≠ u := h2 ▸ h1
      simp [h2, Fin.val_inj, hwu]
    · simp [h1, h2, Fin.val_inj]

theorem digits_swap {d v : ℕ} (u w : Fin v) (y : Tup d v) :
    (digits y).map (swapN u w) = digits (Equiv.swap u w ∘ y) := by
  simp [digits, List.map_ofFn, Function.comp_def, swapN_val]

theorem range_eq_digits_id (d : ℕ) : List.range d = digits (id : Tup d d) := by
  apply List.ext_getElem <;> simp [digits]

/-- The code of a list of `d` digits below `v`, by the table of products. -/
def codeOfD (v d : ℕ) (ds : List ℕ) : ℕ := codeM (pwTab d v) ds.toArray (List.range d).toArray d

theorem codeOfD_digits {d v : ℕ} (y : Tup d v) : codeOfD v d (digits y) = enc y := by
  rw [codeOfD, range_eq_digits_id, codeM_eq]
  rfl

theorem digitsOf_enc {d v : ℕ} (y : Tup d v) : digitsOf d v (enc y) = digits y := by
  have h := digits_symm (k := d) (m := v) ⟨enc y, enc_lt y⟩
  rw [symm_enc] at h
  exact h.symm

/-- A test over the digit lists is a test over the tuples. -/
theorem all_tupList_iff {d v : ℕ} (P : List ℕ → Bool) :
    (tupList d v).all P = true ↔ ∀ y : Tup d v, P (digits y) = true := by
  rw [List.all_eq_true, tupList_eq]
  constructor
  · intro h y
    exact h _ (List.mem_map.2 ⟨enc y, List.mem_range.2 (enc_lt y), digitsOf_enc y⟩)
  · intro h ds hds
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hds
    have := h (finFunctionFinEquiv.symm ⟨t, List.mem_range.1 ht⟩)
    rwa [digits_symm] at this

/-- The twin test of `u` and `w` for the colouring `col` of the codes of the `d`-tuples. -/
def twinB (v d : ℕ) (col : Array ℕ) (u w : ℕ) : Bool :=
  (tupList d v).all fun ds =>
    get col (codeOfD v d (ds.map (swapN u w))) == get col (codeOfD v d ds)

theorem twinB_iff {d v : ℕ} (col : Array ℕ) (u w : Fin v) :
    twinB v d col u w = true ↔ ∀ y : Tup d v, toFun col (Equiv.swap u w ∘ y) = toFun col y := by
  rw [twinB, all_tupList_iff]
  refine forall_congr' fun y => ?_
  rw [digits_swap, codeOfD_digits, codeOfD_digits, beq_iff_eq]
  rfl

/-- **The twin test decodes to `IsTwin`** on the numbered cells. -/
theorem isTwin_cellSub_iff {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    (c : (Fin d → ↥(famOf m cs)) → ℕ) {col : Array ℕ}
    (hcol : ∀ y : Tup d cs.length, toFun col y = c (cellSub m cs ∘ y)) (u w : Fin cs.length) :
    IsTwin c (cellSub m cs u) (cellSub m cs w) ↔ twinB cs.length d col u w = true := by
  rw [twinB_iff]
  have hb := cellSub_bijective hcs
  have key : ∀ y : Tup d cs.length, ⇑(Equiv.swap (cellSub m cs u) (cellSub m cs w)) ∘
      (cellSub m cs ∘ y) = cellSub m cs ∘ (⇑(Equiv.swap u w) ∘ y) := fun y =>
    funext fun i => hb.1.swap_apply u w (y i)
  constructor
  · intro h y
    rw [hcol, hcol, ← key]
    exact h _
  · intro h x
    have hx : cellSub m cs ∘ (fun i => (Equiv.ofBijective _ hb).symm (x i)) = x :=
      funext fun i => Equiv.ofBijective_apply_symm_apply _ hb (x i)
    rw [← hx, key, ← hcol, ← hcol, h]

/-- Counting a test on `Fin v` is counting it on `0, …, v - 1`. -/
theorem card_filter_fin (v : ℕ) (Q : ℕ → Bool) :
    (univ.filter fun w : Fin v => Q w.val = true).card = ((List.range v).filter Q).length := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hn, hq⟩
    exact ⟨⟨n, hn⟩, hq, rfl⟩

/-- The cells with a twin class of more than half of the cells, for the colouring `col`. -/
def bigTwinsD (v d : ℕ) (col : Array ℕ) : List ℕ :=
  (List.range v).filter fun u => decide (v < 2 * ((List.range v).filter (twinB v d col u)).length)

/-- **`bigTwinsD` is `bigTwins`**, for any colouring `c` of the `d`-tuples of cells given on
codes by `col`. -/
theorem bigTwins_decode {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    (c : (Fin d → ↥(famOf m cs)) → ℕ) {col : Array ℕ}
    (hcol : ∀ y : Tup d cs.length, toFun col y = c (cellSub m cs ∘ y)) :
    cellsOf m cs (bigTwinsD cs.length d col) = bigTwins (famOf m cs) c := by
  have hb := cellSub_bijective hcs
  have hcard : (famOf m cs).card = cs.length := card_famOf (getD_inj_of_nodup hcs)
  have hcnt : ∀ u : Fin cs.length, (univ.filter fun w => IsTwin c (cellSub m cs u) w).card =
      ((List.range cs.length).filter (twinB cs.length d col u)).length := by
    intro u
    rw [← card_filter_fin]
    symm
    refine Finset.card_equiv (Equiv.ofBijective _ hb) fun w => ?_
    simp [isTwin_cellSub_iff hcs c hcol]
  ext s
  simp only [cellsOf, bigTwinsD, List.mem_toFinset, List.mem_map, List.mem_filter,
    List.mem_range, bigTwins, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype, decide_eq_true_eq]
  constructor
  · rintro ⟨j, ⟨hj, hlt⟩, rfl⟩
    refine ⟨cellSub m cs ⟨j, hj⟩, ?_, by rw [coe_cellSub, ← getD_eq_get]⟩
    rw [hcard, hcnt]
    exact hlt
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨j, rfl⟩ := hb.2 u
    refine ⟨j.val, ⟨j.2, ?_⟩, by rw [coe_cellSub, getD_eq_get]⟩
    rw [hcard, hcnt] at hu
    exact hu

/-! ### The choice of side -/

/-- The number of the points (given by their row offsets `rws` in the relation array `a`) that
agree with the row at offset `r` on the cells `S`. -/
def twinCntD (a : Array Bool) (S rws : List ℕ) (r : ℕ) : ℕ :=
  (rws.filter fun r' => S.all fun j => getB a (r + j) == getB a (r' + j)).length

/-- **Exercise 5.5's choice** between the cells `S` and the other cells, for the points `ps`,
`q` cells and the relation array `a`. -/
def pickSideD (ps : List ℕ) (q : ℕ) (a : Array Bool) (S : List ℕ) : List ℕ :=
  if (ps.map (· * q)).all fun r => decide (2 * twinCntD a S (ps.map (· * q)) r < ps.length + 2)
  then S
  else (List.range q).filter fun j => !getB (Toolkit.markArr q S) j

/-- Counting a test on a listed set of points is counting it on the list. -/
theorem card_setOf_filter {m : ℕ} {ps : List ℕ} (hps : ∀ i ∈ ps, i < m) (hpn : ps.Nodup)
    (Q : ℕ → Bool) : ((setOf m ps).filter fun x => Q x.val = true).card = (ps.filter Q).length := by
  have e : ((setOf m ps).filter fun x => Q x.val = true) = setOf m (ps.filter Q) := by
    ext x
    simp [mem_setOf]
  rw [e, card_setOf (hpn.filter _) fun i hi => hps i (List.mem_of_mem_filter hi)]

/-- The twin class of a point, for the cells `S`, read from the relation array. -/
theorem card_twinCls_eq {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} (hps : ∀ i ∈ ps, i < m)
    (hpn : ps.Nodup) (hcs : (cs.map (setOf m)).Nodup) (a : Array Bool) {S : List ℕ}
    (hS : ∀ j ∈ S, j < cs.length) (x : Fin m) :
    (twinCls (setOf m ps) (cellsOf m cs S) (relOf m cs a) x).card =
      twinCntD a S (ps.map (· * cs.length)) (x.val * cs.length) := by
  have e : twinCls (setOf m ps) (cellsOf m cs S) (relOf m cs a) x =
      (setOf m ps).filter fun x' => (S.all fun j =>
        getB a (x.val * cs.length + j) == getB a (x'.val * cs.length + j)) = true := by
    ext x'
    rw [mem_twinCls, Finset.mem_filter]
    refine and_congr_right fun _ => ?_
    simp only [cellsOf, List.mem_toFinset, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, List.all_eq_true, beq_iff_eq]
    refine forall₂_congr fun j hj => ?_
    rw [relOf_cell (getD_inj_of_nodup hcs) (hS j hj), relOf_cell (getD_inj_of_nodup hcs) (hS j hj)]
    rfl
  rw [e, card_setOf_filter hps hpn (fun x' => S.all fun j =>
    getB a (x.val * cs.length + j) == getB a (x' * cs.length + j)), twinCntD, List.filter_map,
    List.length_map]
  rfl

theorem cellsOf_compl {m : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    {S : List ℕ} (hS : ∀ j ∈ S, j < cs.length) :
    cellsOf m cs ((List.range cs.length).filter fun j => !getB (Toolkit.markArr cs.length S) j) =
      famOf m cs \ cellsOf m cs S := by
  ext s
  rw [Finset.mem_sdiff]
  constructor
  · intro hs
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
    obtain ⟨hjq, hjS⟩ := List.mem_filter.1 hj
    have hjq' := List.mem_range.1 hjq
    refine ⟨mem_famOf.2 ⟨cs.getD j [], ?_, rfl⟩, ?_⟩
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjq']
      exact List.getElem_mem hjq'
    · rw [setOf_mem_cellsOf hcs hS hjq']
      intro hjS'
      rw [(Toolkit.getB_markArr _ _ _).2 ⟨hjq', hjS'⟩] at hjS
      simp at hjS
  · rintro ⟨hs, hsS⟩
    obtain ⟨l, hl, rfl⟩ := mem_famOf.1 hs
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    have hg : cs[j] = cs.getD j [] := by simp [List.getD_eq_getElem?_getD, hj]
    rw [hg, setOf_mem_cellsOf hcs hS hj] at hsS
    rw [hg]
    refine List.mem_toFinset.2
      (List.mem_map.2 ⟨j, List.mem_filter.2 ⟨List.mem_range.2 hj, ?_⟩, rfl⟩)
    have h' : getB (Toolkit.markArr cs.length S) j ≠ true := fun h' =>
      hsS ((Toolkit.getB_markArr _ _ _).1 h').2
    simpa using h'

/-- **`pickSideD` is `pickSide`**: for duplicate-free points `ps` below `m`, duplicate-free
cells and listed cells `S`, the chosen side decodes to milestone 11's choice. -/
theorem pickSide_decode {m : ℕ} {ps : List ℕ} {cs : List (List ℕ)} (hps : ∀ i ∈ ps, i < m)
    (hpn : ps.Nodup) (hcs : (cs.map (setOf m)).Nodup) (a : Array Bool) {S : List ℕ}
    (hS : ∀ j ∈ S, j < cs.length) :
    cellsOf m cs (pickSideD ps cs.length a S) =
      pickSide (setOf m ps) (famOf m cs) (cellsOf m cs S) (relOf m cs a) := by
  have hcond : ((ps.map (· * cs.length)).all fun r =>
      decide (2 * twinCntD a S (ps.map (· * cs.length)) r < ps.length + 2)) = true ↔
      ∀ x ∈ setOf m ps,
        2 * (twinCls (setOf m ps) (cellsOf m cs S) (relOf m cs a) x).card <
          (setOf m ps).card + 2 := by
    rw [List.all_eq_true, card_setOf hpn hps]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      decide_eq_true_eq, mem_setOf]
    constructor
    · intro h x hx
      rw [card_twinCls_eq hps hpn hcs a hS]
      exact h x.val hx
    · intro h x hx
      have := h ⟨x, hps x hx⟩ hx
      rwa [card_twinCls_eq hps hpn hcs a hS] at this
  unfold pickSideD pickSide
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (hcond.1 h₁) h₂
  · exact absurd (hcond.2 h₂) h₁
  · exact cellsOf_compl hcs hS

/-! ### Composite statements -/

/-- **`bigTwins` of `daryCol`**, as computed on codes. -/
theorem bigTwins_daryCol {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    {hs : List (List ℕ)} (hlt : ∀ h ∈ hs, ∀ j ∈ h, j < cs.length)
    (hnd : (hs.map (cellsOf m cs)).Nodup) :
    cellsOf m cs (bigTwinsD cs.length d (daryArr cs.length d hs)) =
      bigTwins (famOf m cs) (daryCol (famOf m cs) (hs.map (cellsOf m cs)).toFinset d) :=
  bigTwins_decode hcs _ (toFun_daryArr hcs hlt hnd)

/-- **`wlOn d` of `daryCol`**, as computed on codes by `wlProg`. -/
theorem wlOn_daryCol_eq {m d : ℕ} {cs : List (List ℕ)} (hcs : (cs.map (setOf m)).Nodup)
    {hs : List (List ℕ)} (hlt : ∀ h ∈ hs, ∀ j ∈ h, j < cs.length)
    (hnd : (hs.map (cellsOf m cs)).Nodup) (y : Tup d cs.length) :
    get (wlA d cs.length (daryArr cs.length d hs)).1 (enc y) =
      wlOn d (daryCol (famOf m cs) (hs.map (cellsOf m cs)).toFinset d) (cellSub m cs ∘ y) :=
  get_wlA_cells hcs _ (toFun_daryArr hcs hlt hnd) y

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One step of the search for `⌈log_v n⌉`. -/
def clogStepProg (v n one : var .nat) (st : var (.prod .nat .nat)) :
    Prog S rec var (.prod .nat .nat) :=
  .bind (.op1 .fst st) fun p => .bind (.op2 .natLt p n) fun b =>
  .ite b
    (.bind (Coherent.mulNProg v p) fun p' => .bind (.op1 .snd st) fun k =>
     .bind (.op2 .add k one) fun k' => .op2 .pair p' k')
    (.ret st)

/-- **`⌈log_v n⌉`** (`0` if `v < 2`). -/
def clogProg (v n : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natLt v two) fun small =>
  .ite small (.op0 (.natLit 0))
    (.bind (.op1 .range n) fun rn => .bind (.op0 (.natLit 1)) fun one =>
     .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .pair one z) fun st₀ =>
     .bind (.foldList rn st₀ fun st _ => clogStepProg v n one st) fun st => .op1 .snd st)

/-- **The arity** `min s (6 ⌈log_v n⌉)`. -/
def arityProg (v s n : var .nat) : Prog S rec var .nat :=
  .bind (clogProg v n) fun c => .bind (.op2 .add c c) fun c2 => .bind (.op2 .add c2 c2) fun c4 =>
  .bind (.op2 .add c4 c2) fun c6 => .bind (.op2 .natLt s c6) fun b => .ite b (.ret s) (.ret c6)

/-- The colour of the tuple of cells with digits `ds`, for the masks of the hyperedges. -/
def daryEntryProg (masks : var (.list (.array .bool))) (ds : var (.list .nat)) :
    Prog S rec var .nat :=
  .bind (allList ds fun i =>
    .bind (Toolkit.countList ds fun j => .op2 .natEq j i) fun c =>
    .bind (.op0 (.natLit 1)) fun one => .op2 .natEq c one) fun nd =>
  .ite nd
    (.bind (Toolkit.countList masks fun mk => allList ds fun i => .op2 .arrayGet mk i) fun c =>
     .bind (.op0 (.natLit 1)) fun one => .op2 .add one c)
    (.op0 (.natLit 0))

/-- **The colouring `daryCol`** on the codes of the `d`-tuples of `v` cells. -/
def daryArrProg (v d : var .nat) (hs : var (.list (.list .nat))) :
    Prog S rec var (.array .nat) :=
  .bind (mapList hs fun h => Toolkit.markProg v h) fun masks =>
  .bind (Coherent.tupsProg d v) fun tups =>
  .bind (mapList tups fun ds => daryEntryProg masks ds) fun es => .op1 .arrayOfList es

/-- **`wlOn d` of `daryCol`** on the codes of the `d`-tuples of `v` cells. -/
def daryWLProg (v d : var .nat) (hs : var (.list (.list .nat))) :
    Prog S rec var (.prod (.array .nat) (.list .nat)) :=
  .bind (daryArrProg v d hs) fun col => Coherent.wlProg d v col

/-- The transposition of `u` and `w`, on indices. -/
def swapNProg (u w i : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natEq i u) fun bu => .ite bu (.ret w)
    (.bind (.op2 .natEq i w) fun bw => .ite bw (.ret u) (.ret i))

/-- The code of a digit list, from the table of products `pw` and the identity digits. -/
def codeOfProg (pw : var (.array (.array .nat))) (idA : var (.array .nat))
    (rk ds : var (.list .nat)) : Prog S rec var .nat :=
  .bind (.op1 .arrayOfList ds) fun dA => Coherent.codeProg pw dA idA rk

/-- The twin test of `u` and `w` over the digit lists `tups`. -/
def twinBProg (pw : var (.array (.array .nat))) (idA : var (.array .nat))
    (rk : var (.list .nat)) (col : var (.array .nat)) (tups : var (.list (.list .nat)))
    (u w : var .nat) : Prog S rec var .bool :=
  allList tups fun ds =>
    .bind (mapList ds fun i => swapNProg u w i) fun sds =>
    .bind (codeOfProg pw idA rk sds) fun c₁ => .bind (codeOfProg pw idA rk ds) fun c₀ =>
    .bind (.op2 .arrayGet col c₁) fun x₁ => .bind (.op2 .arrayGet col c₀) fun x₀ =>
    .op2 .natEq x₁ x₀

/-- The test of `u`: more than half of the `v` cells `rv` are twins of `u`. -/
def bigTestProg (pw : var (.array (.array .nat))) (idA : var (.array .nat))
    (rk : var (.list .nat)) (col : var (.array .nat)) (tups : var (.list (.list .nat)))
    (v : var .nat) (rv : var (.list .nat)) (u : var .nat) : Prog S rec var .bool :=
  .bind (Toolkit.countList rv fun w => twinBProg pw idA rk col tups u w) fun cnt =>
  .bind (.op2 .add cnt cnt) fun c2 => .op2 .natLt v c2

/-- **The cells with a twin class of more than half of the cells**, for the colouring `col` of
the codes of the `d`-tuples of `v` cells. -/
def bigTwinsProg (v d : var .nat) (col : var (.array .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range d) fun rk => .bind (.op1 .range v) fun rv =>
  .bind (Coherent.pwTabProg v rk rv) fun pw => .bind (.op1 .arrayOfList rk) fun idA =>
  .bind (Coherent.tupsProg d v) fun tups =>
  Toolkit.filterList rv fun u => bigTestProg pw idA rk col tups v rv u

/-- Agreement of two Booleans. -/
def beqProg (b₁ b₂ : var .bool) : Prog S rec var .bool := .ite b₁ (.ret b₂) (.op1 .not b₂)

/-- Agreement of the rows at offsets `r` and `r'` of the relation array `a` at the cell `j`. -/
def agreeProg (a : var (.array .bool)) (r r' j : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .add r j) fun i₁ => .bind (.op2 .add r' j) fun i₂ =>
  .bind (.op2 .arrayGet a i₁) fun b₁ => .bind (.op2 .arrayGet a i₂) fun b₂ => beqProg b₁ b₂

/-- The number of the rows `rws` agreeing with the row at offset `r` on the cells `T`. -/
def twinCntProg (a : var (.array .bool)) (T rws : var (.list .nat)) (r : var .nat) :
    Prog S rec var .nat :=
  Toolkit.countList rws fun r' => allList T fun j => agreeProg a r r' j

/-- The twin class of the row at offset `r` is small: twice its size is below `p2`. -/
def sideOkProg (a : var (.array .bool)) (T rws : var (.list .nat)) (p2 r : var .nat) :
    Prog S rec var .bool :=
  .bind (twinCntProg a T rws r) fun cnt => .bind (.op2 .add cnt cnt) fun c2 => .op2 .natLt c2 p2

/-- The cells `0, …, q - 1` not in `T`. -/
def complProg (q : var .nat) (T : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (Toolkit.markProg q T) fun mk => .bind (.op1 .range q) fun rq =>
  Toolkit.filterList rq fun j => .bind (.op2 .arrayGet mk j) fun b => .op1 .not b

/-- **Exercise 5.5's choice of side**, for the points `ps`, `q` cells, the relation array `a`
and the cells `T`. -/
def pickSideProg (ps : var (.list .nat)) (q : var .nat) (a : var (.array .bool))
    (T : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (mapList ps fun x => Coherent.mulNProg x q) fun rws =>
  .bind (.op1 .length ps) fun p => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .add p two) fun p2 =>
  .bind (allList rws fun r => sideOkProg a T rws p2 r) fun ok =>
  .ite ok (.ret T) (complProg q T)

end Prog

/-! ### Costs -/

/-- The cost of `clogProg v n`. -/
def clogCost (v n : ℕ) : ℕ := n * (3 * v + 10) + 8

/-- The cost of the colour of a `d`-tuple, for `h` hyperedges. -/
def daryEntryCost (d h : ℕ) : ℕ := d * (5 * d + 5) + h * (3 * d + 5) + 5

/-- The cost of `daryArrProg` for `v` cells, arity `d` and `h` hyperedges. -/
def daryArrCost (v d h : ℕ) : ℕ :=
  h * (8 * v + 8) + Coherent.tupsCost d v + v ^ d * (daryEntryCost d h + 4) + 5

/-- The cost of the twin test of two cells, for arity `d` and `v` cells. -/
def twinBCost (v d : ℕ) : ℕ := v ^ d * (21 * d + 11) + 1

/-- The cost of `bigTwinsProg` for `v` cells and arity `d`. -/
def bigTwinsCost (v d : ℕ) : ℕ :=
  2 * d + v + 6 + Coherent.pwTabCost d v + Coherent.tupsCost d v +
    v * (v * (twinBCost v d + 4) + 7)

/-- The cost of `pickSideProg` for `p` points below `m`, `q` cells and `t` cells in `T`. -/
def pickCost (m p q t : ℕ) : ℕ :=
  p * (3 * m + 6) + p * (p * (8 * t + 5) + 5) + 9 * q + 6 * t + 16

theorem length_of_mem_tupList {d v : ℕ} {ds : List ℕ} (h : ds ∈ tupList d v) : ds.length = d := by
  rw [tupList_eq] at h
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 h
  simp [digitsOf]

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.clogStepProg (v n : ℕ) (st : ℕ × ℕ) :
    RunsWithin X body (SoJProg.clogStepProg v n 1 st) (clogStep v n st) (3 * v + 8) := by
  unfold SoJProg.clogStepProg
  by_cases h : st.1 < n
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, h, decide_true, Bool.cond_true]
      run_step (Coherent.RunsWithin.mulNProg v st.1)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      refine RunsWithin.prim_le ?_ le_rfl
      simp [Prim.eval, clogStep, h]
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, h, decide_false, Bool.cond_false]
      refine (RunsWithin.ret _).of_eq ?_
      simp [clogStep, h]
    case hc =>
      simp only [Prim.cost]
      omega

/-- **`⌈log_v n⌉`**. -/
theorem RunsWithin.clogProg (v n : ℕ) :
    RunsWithin X body (SoJProg.clogProg v n) (Nat.clog v n) (clogCost v n) := by
  unfold SoJProg.clogProg
  by_cases hv : v < 2
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, hv, decide_true, Bool.cond_true]
      refine RunsWithin.prim_le ?_ le_rfl
      simp [Prim.eval, Nat.clog_of_left_le_one (by omega : v ≤ 1)]
    case hc =>
      simp only [Prim.cost, clogCost]
      omega
  · have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
      (b' := .prod .nat .nat) (cf := fun _ => 3 * v + 8) (F := fun st _ => clogStep v n st)
      (f := fun st _ => SoJProg.clogStepProg v n 1 st) (List.range n) (1, 0)
      fun st _ _ => RunsWithin.clogStepProg v n st
    rw [sum_map_const, List.length_range] at hfold
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, hv, decide_false, Bool.cond_false]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      refine RunsWithin.prim_le ?_ le_rfl
      rw [← clogD_eq, clogD]
      simp [Prim.eval, hv]
    case hc =>
      simp only [Prim.cost, Args.head, clogCost]
      have e : n * (3 * v + 10) = n * (3 * v + 8 + 1) + n := by ring
      omega

/-- **The arity** `min s (6 ⌈log_v n⌉)` of milestone 11. -/
theorem RunsWithin.arityProg (v s n : ℕ) :
    RunsWithin X body (SoJProg.arityProg v s n) (arity v s n) (clogCost v n + 5) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.arityProg
    run_step (RunsWithin.clogProg v n)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.ite _
    simp only [Prim.eval]
    by_cases h : s < Nat.clog v n + Nat.clog v n + (Nat.clog v n + Nat.clog v n) +
        (Nat.clog v n + Nat.clog v n)
    · simp only [h, decide_true, Bool.cond_true]
      refine (RunsWithin.ret _).of_eq ?_
      show s = arity v s n
      rw [arity, Nat.min_def]
      split_ifs <;> omega
    · simp only [h, decide_false, Bool.cond_false]
      refine (RunsWithin.ret _).of_eq ?_
      show _ = arity v s n
      rw [arity, Nat.min_def]
      split_ifs <;> omega
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.daryEntryProg (masks : List (Array Bool)) (ds : List ℕ) :
    RunsWithin X body (SoJProg.daryEntryProg masks ds) (daryEntry masks ds)
      (daryEntryCost ds.length masks.length) := by
  have hcnt : ∀ i ∈ ds, RunsWithin X body
      (.bind (Toolkit.countList (a' := .nat) ds fun j => .op2 .natEq j i) fun c =>
        .bind (.op0 (.natLit 1)) fun one => .op2 .natEq c one)
      ((ds.filter (· == i)).length == 1) (5 * ds.length + 3) := by
    intro i _
    apply RunsWithin.mono
    case h =>
      run_step (Toolkit.RunsWithin.countList (P := fun j => j == i) (c := 1) fun j _ =>
        RunsWithin.prim_le rfl le_rfl)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost]
      omega
  have hnd : RunsWithin X body (allList (a' := .nat) ds fun i =>
      .bind (Toolkit.countList (a' := .nat) ds fun j => .op2 .natEq j i) fun c =>
        .bind (.op0 (.natLit 1)) fun one => .op2 .natEq c one)
      (ds.all fun i => (ds.filter (· == i)).length == 1)
      (ds.length * (5 * ds.length + 3 + 2) + 1) := RunsWithin.allList_le hcnt
  have hall : ∀ mk ∈ masks, RunsWithin X body
      (allList (a' := .nat) ds fun i => .op2 (Prim.arrayGet (a := .bool)) mk i)
      (ds.all (getB mk)) (ds.length * 3 + 1) := fun mk _ =>
    (RunsWithin.allList_le (c := 1) fun i _ => RunsWithin.prim_le rfl le_rfl).mono (by omega)
  have hc : RunsWithin X body (Toolkit.countList (a' := .array .bool) masks fun mk =>
      allList (a' := .nat) ds fun i => .op2 (Prim.arrayGet (a := .bool)) mk i)
      (masks.filter fun mk => ds.all (getB mk)).length
      (masks.length * (ds.length * 3 + 1 + 4) + 1) := Toolkit.RunsWithin.countList hall
  unfold SoJProg.daryEntryProg
  by_cases hd : (ds.all fun i => (ds.filter (· == i)).length == 1) = true
  · apply RunsWithin.mono
    case h =>
      run_step hnd
      run_with RunsWithin.ite _
      simp only [hd, Bool.cond_true]
      run_step hc
      run_step (RunsWithin.prim _ _)
      refine RunsWithin.prim_le ?_ le_rfl
      simp [Prim.eval, daryEntry, hd]
    case hc =>
      simp only [Prim.cost, daryEntryCost]
      have e : ds.length * (5 * ds.length + 3 + 2) = ds.length * (5 * ds.length + 5) := by ring
      have e' : masks.length * (ds.length * 3 + 1 + 4) = masks.length * (3 * ds.length + 5) := by
        ring
      omega
  · apply RunsWithin.mono
    case h =>
      run_step hnd
      run_with RunsWithin.ite _
      simp only [hd, Bool.cond_false]
      refine RunsWithin.prim_le ?_ le_rfl
      simp [Prim.eval, daryEntry, hd]
    case hc =>
      simp only [Prim.cost, daryEntryCost]
      have e : ds.length * (5 * ds.length + 3 + 2) = ds.length * (5 * ds.length + 5) := by ring
      omega

/-- **The colouring `daryCol` on codes**, for hyperedges of at most `v` cells. -/
theorem RunsWithin.daryArrProg (v d : ℕ) (hs : List (List ℕ))
    (hlen : ∀ h ∈ hs, h.length ≤ v) :
    RunsWithin X body (SoJProg.daryArrProg v d hs) (daryArr v d hs)
      (daryArrCost v d hs.length) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat)
    (b' := .array .bool) (xs := hs) (f := fun h => Toolkit.markProg v h)
    (F := Toolkit.markArr v) (c := Toolkit.markCost v v) fun h hh =>
      (Toolkit.RunsWithin.markProg v h).mono (by
        have := hlen h hh
        simp only [Toolkit.markCost]
        omega)
  have he := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := .nat)
    (xs := tupList d v) (f := fun ds => SoJProg.daryEntryProg (hs.map (Toolkit.markArr v)) ds)
    (F := daryEntry (hs.map (Toolkit.markArr v))) (c := daryEntryCost d hs.length)
    fun ds hds => by
      have := RunsWithin.daryEntryProg (X := X) (body := body) (hs.map (Toolkit.markArr v)) ds
      rwa [length_of_mem_tupList hds, List.length_map] at this
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.daryArrProg
    run_step hm
    run_step (Coherent.RunsWithin.tupsProg d v)
    run_step he
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map, length_tupList, daryArrCost,
      Toolkit.markCost]
    have e : hs.length * (2 * v + 6 * v + 5 + 3) = hs.length * (8 * v + 8) := by ring
    have e' : v ^ d * (daryEntryCost d hs.length + 4) =
        v ^ d * (daryEntryCost d hs.length + 3) + v ^ d := by ring
    omega

theorem RunsWithin.swapNProg (u w i : ℕ) :
    RunsWithin X body (SoJProg.swapNProg u w i) (swapN u w i) 4 := by
  unfold SoJProg.swapNProg
  by_cases h₁ : (i == u) = true
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite _
      simp only [Prim.eval, h₁, Bool.cond_true]
      refine (RunsWithin.ret _).of_eq ?_
      simp [swapN, h₁]
    case hc =>
      simp only [Prim.cost]
      omega
  · by_cases h₂ : (i == w) = true
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite _
        simp only [Prim.eval, h₁, Bool.cond_false]
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite _
        simp only [Prim.eval, h₂, Bool.cond_true]
        refine (RunsWithin.ret _).of_eq ?_
        simp [swapN, h₁, h₂]
      case hc =>
        simp only [Prim.cost]
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite _
        simp only [Prim.eval, h₁, Bool.cond_false]
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite _
        simp only [Prim.eval, h₂, Bool.cond_false]
        refine (RunsWithin.ret _).of_eq ?_
        simp [swapN, h₁, h₂]
      case hc =>
        simp only [Prim.cost]
        omega

theorem RunsWithin.codeOfProg (v d : ℕ) (ds : List ℕ) (hd : ds.length = d) :
    RunsWithin X body
      (SoJProg.codeOfProg (pwTab d v) (List.range d).toArray (List.range d) ds)
      (codeOfD v d ds) (7 * d + 2) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.codeOfProg
    run_step (RunsWithin.prim _ _)
    exact Coherent.RunsWithin.codeProg _ _ _ d
  case hc =>
    simp only [Prim.cost, Args.head, hd]
    omega

/-- **The twin test** of `u` and `w` on codes. -/
theorem RunsWithin.twinBProg (v d : ℕ) (col : Array ℕ) (u w : ℕ) :
    RunsWithin X body
      (SoJProg.twinBProg (pwTab d v) (List.range d).toArray (List.range d) col (tupList d v) u w)
      (twinB v d col u w) (twinBCost v d) := by
  unfold SoJProg.twinBProg
  refine (RunsWithin.allList_le (c := 21 * d + 9) fun ds hds => ?_).mono ?_
  · have hl := length_of_mem_tupList hds
    have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat) (xs := ds)
      (f := fun i => SoJProg.swapNProg u w i) (F := swapN u w) (c := 4) fun i _ =>
        RunsWithin.swapNProg u w i
    apply RunsWithin.mono
    case h =>
      run_step hm
      run_step (RunsWithin.codeOfProg v d _ (by simp [hl]))
      run_step (RunsWithin.codeOfProg v d ds hl)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, hl]
      omega
  · simp only [twinBCost, length_tupList]
    have e : v ^ d * (21 * d + 9 + 2) = v ^ d * (21 * d + 11) := by ring
    omega

theorem RunsWithin.bigTestProg (v d : ℕ) (col : Array ℕ) (u : ℕ) :
    RunsWithin X body
      (SoJProg.bigTestProg (pwTab d v) (List.range d).toArray (List.range d) col (tupList d v) v
        (List.range v) u)
      (decide (v < 2 * ((List.range v).filter (twinB v d col u)).length))
      (v * (twinBCost v d + 4) + 3) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.bigTestProg
    run_step (Toolkit.RunsWithin.countList (c := twinBCost v d) fun w _ =>
      RunsWithin.twinBProg v d col u w)
    run_step (RunsWithin.prim _ _)
    refine RunsWithin.prim_le ?_ le_rfl
    simp [Prim.eval, two_mul]
  case hc =>
    simp only [Prim.cost, List.length_range]
    omega

/-- **The cells with a twin class of more than half of the cells**. -/
theorem RunsWithin.bigTwinsProg (v d : ℕ) (col : Array ℕ) :
    RunsWithin X body (SoJProg.bigTwinsProg v d col) (bigTwinsD v d col) (bigTwinsCost v d) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.bigTwinsProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.pwTabProg d v)
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.tupsProg d v)
    exact Toolkit.RunsWithin.filterList fun u _ => RunsWithin.bigTestProg v d col u
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, bigTwinsCost]
    have e : v * (v * (twinBCost v d + 4) + 3 + 4) = v * (v * (twinBCost v d + 4) + 7) := by ring
    omega

theorem RunsWithin.beqProg (b₁ b₂ : Bool) :
    RunsWithin X body (SoJProg.beqProg b₁ b₂) (b₁ == b₂) 2 := by
  unfold SoJProg.beqProg
  cases b₁
  · exact (RunsWithin.ite_false (RunsWithin.prim_le (by cases b₂ <;> rfl) le_rfl)).mono
      (by simp [Prim.cost])
  · exact (RunsWithin.ite_true ((RunsWithin.ret (t := .bool) b₂).of_eq
      (by cases b₂ <;> rfl))).mono (by omega)

theorem RunsWithin.agreeProg (a' : Array Bool) (r r' j : ℕ) :
    RunsWithin X body (SoJProg.agreeProg a' r r' j) (getB a' (r + j) == getB a' (r' + j)) 6 := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.agreeProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.beqProg _ _
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.twinCntProg (a' : Array Bool) (T rws : List ℕ) (r : ℕ) :
    RunsWithin X body (SoJProg.twinCntProg a' T rws r) (twinCntD a' T rws r)
      (rws.length * (8 * T.length + 5) + 1) := by
  unfold SoJProg.twinCntProg
  refine (Toolkit.RunsWithin.countList (a' := .nat) (xs := rws)
    (p := fun r' => allList (a' := .nat) T fun j => SoJProg.agreeProg a' r r' j)
    (P := fun r' => T.all fun j => getB a' (r + j) == getB a' (r' + j))
    (c := T.length * 8 + 1) fun r' _ =>
    (RunsWithin.allList_le (a' := .nat) (xs := T) (p := fun j => SoJProg.agreeProg a' r r' j)
      (P := fun j => getB a' (r + j) == getB a' (r' + j)) (c := 6) fun j _ =>
        RunsWithin.agreeProg a' r r' j).mono (by omega)).mono ?_
  have e : rws.length * (T.length * 8 + 1 + 4) = rws.length * (8 * T.length + 5) := by ring
  omega

theorem RunsWithin.sideOkProg (a' : Array Bool) (T rws : List ℕ) (p2 r : ℕ) :
    RunsWithin X body (SoJProg.sideOkProg a' T rws p2 r)
      (decide (2 * twinCntD a' T rws r < p2)) (rws.length * (8 * T.length + 5) + 3) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.sideOkProg
    run_step (RunsWithin.twinCntProg a' T rws r)
    run_step (RunsWithin.prim _ _)
    refine RunsWithin.prim_le ?_ le_rfl
    simp [Prim.eval, two_mul]
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.complProg (q : ℕ) (T : List ℕ) :
    RunsWithin X body (SoJProg.complProg q T)
      ((List.range q).filter fun j => !getB (Toolkit.markArr q T) j)
      (9 * q + 6 * T.length + 9) := by
  apply RunsWithin.mono
  case h =>
    unfold SoJProg.complProg
    run_step (Toolkit.RunsWithin.markProg q T)
    run_step (RunsWithin.prim _ _)
    exact Toolkit.RunsWithin.filterList (c := 2) fun j _ =>
      (RunsWithin.prim _ _).bind_le (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, Toolkit.markCost]
    omega

/-- **Exercise 5.5's choice of side**, for points below `m`. -/
theorem RunsWithin.pickSideProg {m : ℕ} (ps : List ℕ) (hps : ∀ i ∈ ps, i < m) (q : ℕ)
    (a' : Array Bool) (T : List ℕ) :
    RunsWithin X body (SoJProg.pickSideProg ps q a' T) (pickSideD ps q a' T)
      (pickCost m ps.length q T.length) := by
  have hrows := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := ps) (f := fun x => Coherent.mulNProg x q) (F := (· * q)) (c := 3 * m + 2)
    fun x hx => (RunsWithin.mulNProg x q).mono (by have := hps x hx; omega)
  have hok := RunsWithin.allList_le (X := X) (body := body) (a' := .nat) (xs := ps.map (· * q))
    (p := fun r => SoJProg.sideOkProg a' T (ps.map (· * q)) (ps.length + 2) r)
    (P := fun r => decide (2 * twinCntD a' T (ps.map (· * q)) r < ps.length + 2))
    (c := ps.length * (8 * T.length + 5) + 3) fun r _ => by
      have := RunsWithin.sideOkProg (X := X) (body := body) a' T (ps.map (· * q))
        (ps.length + 2) r
      rwa [List.length_map] at this
  unfold SoJProg.pickSideProg pickSideD
  by_cases hc : ((ps.map (· * q)).all fun r =>
      decide (2 * twinCntD a' T (ps.map (· * q)) r < ps.length + 2)) = true
  · apply RunsWithin.mono
    case h =>
      run_step hrows
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hok
      run_with RunsWithin.ite _
      simp only [hc, Bool.cond_true, ↓reduceIte]
      exact RunsWithin.ret _
    case hc =>
      simp only [Prim.cost, Args.head, List.length_map, pickCost]
      have e : ps.length * (ps.length * (8 * T.length + 5) + 3 + 2) =
          ps.length * (ps.length * (8 * T.length + 5) + 5) := by ring
      have e' : ps.length * (3 * m + 2 + 3) + ps.length = ps.length * (3 * m + 6) := by ring
      omega
  · apply RunsWithin.mono
    case h =>
      run_step hrows
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hok
      run_with RunsWithin.ite _
      simp only [hc, Bool.cond_false, Bool.false_eq_true, ↓reduceIte]
      exact RunsWithin.complProg q T
    case hc =>
      simp only [Prim.cost, Args.head, List.length_map, pickCost]
      have e : ps.length * (ps.length * (8 * T.length + 5) + 3 + 2) =
          ps.length * (ps.length * (8 * T.length + 5) + 5) := by ring
      have e' : ps.length * (3 * m + 2 + 3) + ps.length = ps.length * (3 * m + 6) := by ring
      omega

/-- **`wlOn d` of `daryCol` on codes**. -/
theorem RunsWithin.daryWLProg (v d : ℕ) (hs : List (List ℕ))
    (hlen : ∀ h ∈ hs, h.length ≤ v) :
    RunsWithin X body (SoJProg.daryWLProg v d hs) (wlA d v (daryArr v d hs))
      (daryArrCost v d hs.length + wlCost d v) :=
  (RunsWithin.daryArrProg v d hs hlen).bind (Coherent.RunsWithin.wlProg d v _)

end Specs

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_clogProg {v₁ n₁ : var₁ .nat} {v₂ n₂ : var₂ .nat} (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (clogProg v₁ n₁) (clogProg v₂ n₂) := by
  unfold clogProg clogStepProg Coherent.mulNProg
  prog_wf

theorem wf_arityProg {v₁ s₁ n₁ : var₁ .nat} {v₂ s₂ n₂ : var₂ .nat} (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ)
    (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (arityProg v₁ s₁ n₁) (arityProg v₂ s₂ n₂) := by
  unfold arityProg
  exact .bind (wf_clogProg hv hn) fun _ _ => by prog_wf

theorem wf_daryEntryProg {k₁ : var₁ (.list (.array .bool))} {k₂ : var₂ (.list (.array .bool))}
    {ds₁ : var₁ (.list .nat)} {ds₂ : var₂ (.list .nat)}
    (hk : ⟨.list (.array .bool), k₁, k₂⟩ ∈ Γ) (hds : ⟨.list .nat, ds₁, ds₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (daryEntryProg k₁ ds₁) (daryEntryProg k₂ ds₂) := by
  unfold daryEntryProg allList Toolkit.countList
  prog_wf

theorem wf_daryArrProg {v₁ d₁ : var₁ .nat} {v₂ d₂ : var₂ .nat}
    {hs₁ : var₁ (.list (.list .nat))} {hs₂ : var₂ (.list (.list .nat))}
    (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ)
    (hhs : ⟨.list (.list .nat), hs₁, hs₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (daryArrProg v₁ d₁ hs₁) (daryArrProg v₂ d₂ hs₂) := by
  unfold daryArrProg
  exact .bind (wf_mapList hhs fun _ hΓ _ _ hh => Toolkit.wf_markProg (hΓ hv) hh) fun _ _ =>
    .bind (Coherent.wf_tupsProg (by simp [hd]) (by simp [hv])) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ hΓ _ _ hds => wf_daryEntryProg (hΓ (by simp)) hds)
    fun _ _ => .prim _ (.cons (by simp) .nil)

theorem wf_daryWLProg {v₁ d₁ : var₁ .nat} {v₂ d₂ : var₂ .nat}
    {hs₁ : var₁ (.list (.list .nat))} {hs₂ : var₂ (.list (.list .nat))}
    (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ)
    (hhs : ⟨.list (.list .nat), hs₁, hs₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (daryWLProg v₁ d₁ hs₁) (daryWLProg v₂ d₂ hs₂) := by
  unfold daryWLProg
  exact .bind (wf_daryArrProg hv hd hhs) fun _ _ =>
    Coherent.wf_wlProg (by simp [hd]) (by simp [hv]) (by simp)

theorem wf_twinBProg {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {idA₁ col₁ : var₁ (.array .nat)} {idA₂ col₂ : var₂ (.array .nat)}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)}
    {tups₁ : var₁ (.list (.list .nat))} {tups₂ : var₂ (.list (.list .nat))}
    {u₁ w₁ : var₁ .nat} {u₂ w₂ : var₂ .nat} (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hid : ⟨.array .nat, idA₁, idA₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) (htups : ⟨.list (.list .nat), tups₁, tups₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) (hw : ⟨.nat, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinBProg pw₁ idA₁ rk₁ col₁ tups₁ u₁ w₁)
      (twinBProg pw₂ idA₂ rk₂ col₂ tups₂ u₂ w₂) := by
  unfold twinBProg allList mapList swapNProg codeOfProg Coherent.codeProg Coherent.codeStepProg
    Coherent.get2Prog
  prog_wf

theorem wf_bigTwinsProg {v₁ d₁ : var₁ .nat} {v₂ d₂ : var₂ .nat} {col₁ : var₁ (.array .nat)}
    {col₂ : var₂ (.array .nat)} (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (bigTwinsProg v₁ d₁ col₁) (bigTwinsProg v₂ d₂ col₂) := by
  unfold bigTwinsProg
  exact .bind (.prim _ (.cons hd .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hv]) .nil)) fun _ _ =>
    .bind (Coherent.wf_pwTabProg (by simp [hv]) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Coherent.wf_tupsProg (by simp [hd]) (by simp [hv])) fun _ _ =>
    Toolkit.wf_filterList (by simp) fun _ hΓ _ _ hu => by
      have hv' := hΓ (a := ⟨.nat, v₁, v₂⟩) (by simp [hv])
      unfold bigTestProg
      exact .bind (Toolkit.wf_countList (hΓ (by simp)) fun _ hΓ' _ _ hw =>
        wf_twinBProg (hΓ' (hΓ (by simp))) (hΓ' (hΓ (by simp))) (hΓ' (hΓ (by simp)))
          (hΓ' (hΓ (by simp [hcol]))) (hΓ' (hΓ (by simp))) (hΓ' hu) hw) fun _ _ =>
        .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
        .prim _ (.cons (by simp [hv']) (.cons (by simp) .nil))

theorem wf_complProg {q₁ : var₁ .nat} {q₂ : var₂ .nat} {T₁ : var₁ (.list .nat)}
    {T₂ : var₂ (.list .nat)} (hq : ⟨.nat, q₁, q₂⟩ ∈ Γ) (hT : ⟨.list .nat, T₁, T₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (complProg q₁ T₁) (complProg q₂ T₂) := by
  unfold complProg Toolkit.markProg Toolkit.filterList mapList
  prog_wf

theorem wf_pickSideProg {ps₁ T₁ : var₁ (.list .nat)} {ps₂ T₂ : var₂ (.list .nat)}
    {q₁ : var₁ .nat} {q₂ : var₂ .nat} {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ) (hq : ⟨.nat, q₁, q₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hT : ⟨.list .nat, T₁, T₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pickSideProg ps₁ q₁ a₁ T₁) (pickSideProg ps₂ q₂ a₂ T₂) := by
  have hm : WfFun r Γ (fun x => Coherent.mulNProg (S := S) (rec := rec) x q₁)
      (fun x => Coherent.mulNProg x q₂) := by
    intro Γ' hΓ x₁ x₂ hx
    have hq' := hΓ hq
    unfold Coherent.mulNProg
    prog_wf
  unfold pickSideProg
  refine .bind (wf_mapList hps hm) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hps]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind ?_ fun _ _ => .ite (by simp) (.ret (by simp [hT])) (wf_complProg (by simp [hq])
    (by simp [hT]))
  unfold allList sideOkProg twinCntProg Toolkit.countList agreeProg beqProg
  prog_wf

end Wf
