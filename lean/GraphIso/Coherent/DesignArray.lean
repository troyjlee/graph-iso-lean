module

public import GraphIso.Coherent.Design
public import GraphIso.Coherent.WLArray

/-!
# The Design Lemma search on arrays

The functional model of the search of `GraphIso/Coherent/DesignProg.lean`, for a colouring of
the `k`-tuples of `Fin m` stored as an array `c` indexed by codes, and a list `x` of fewer than
`k` points given by its digits `xd`:

* `codePad1` and `codePad2` are the codes of `(x, u, …, u)` and `(x, u, v, …, v)`, summed from
  the table of products `pwTab` (`codePad1_eq`, `codePad2_eq`);
* `col1A` is the individualized vertex colouring (`col1A_eq`), `domA` the first point of a class
  of more than `t` points (`domA_eq_none`, `domA_eq_some`), `cliqueA` whether the individualized
  2-skeleton is a clique on that class (`cliqueA_iff`);
* `goodA` is the conclusion of the Design Lemma at `x` (`goodA_iff`, for `m ≤ 2 t`), and
  `searchA` returns the first candidate where it holds, with its vertex colouring; the
  candidates are all lists of fewer than `k` points (`mem_cands`).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

variable {k m : ℕ}

/-- The conclusion of the Design Lemma at `x`. -/
def DesignGood {V : Type*} [Fintype V] (c : (Fin k → V) → ℕ) (t : ℕ) (x : List V) : Prop :=
  (∀ u, (cls1 c x u).card ≤ t) ∨
    (x.length + 2 ≤ k ∧ ∃ u, t < (cls1 c x u).card ∧ ¬ IsClique (skel2 c x) (cls1 c x u))

/-! ### Codes of individualized tuples -/

/-- The code of `(x, u, …, u)` from the digits `xA` of `x`, of length `l`. -/
def codePad1 (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ) (u : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => acc + get2 pw i (if i < l then get xA i else u)) 0

/-- The code of `(x, u, v, …, v)` from the digits `xA` of `x`, of length `l`. -/
def codePad2 (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ) (u v : ℕ) : ℕ :=
  (List.range k).foldl
    (fun acc i => acc + get2 pw i (if i < l then get xA i else if i = l then u else v)) 0

theorem get_map_val (x : List (Fin m)) {i : ℕ} (hi : i < x.length) :
    get (x.map Fin.val).toArray i = (x[i] : ℕ) := by
  simp [get, hi]

theorem codePad1_eq (x : List (Fin m)) (u : Fin m) :
    codePad1 (pwTab k m) k x.length (x.map Fin.val).toArray u = enc (pad1 k x u) := by
  unfold codePad1
  rw [foldl_add_eq, Nat.zero_add, enc_eq_sum, Fin.sum_univ_def, ← map_finRange_eq_range k]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [pad1]
  split_ifs with h
  · rw [get_map_val x h, get2_pwTab i.2 (x[i.val]).2]
  · rw [get2_pwTab i.2 u.2]

theorem codePad2_eq (x : List (Fin m)) (u v : Fin m) :
    codePad2 (pwTab k m) k x.length (x.map Fin.val).toArray u v = enc (pad2 k x u v) := by
  unfold codePad2
  rw [foldl_add_eq, Nat.zero_add, enc_eq_sum, Fin.sum_univ_def, ← map_finRange_eq_range k]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [pad2]
  split_ifs with h h'
  · rw [get_map_val x h, get2_pwTab i.2 (x[i.val]).2]
  · rw [get2_pwTab i.2 u.2]
  · rw [get2_pwTab i.2 v.2]

/-! ### The vertex colouring and its classes -/

/-- The individualized vertex colouring. -/
def col1A (c : Array ℕ) (pw : Array (Array ℕ)) (k m l : ℕ) (xA : Array ℕ) : List ℕ :=
  (List.range m).map fun u => get c (codePad1 pw k l xA u)

/-- The size of the class of `u`. -/
def cntA (col : List ℕ) (u : ℕ) : ℕ := (col.filter (· = col.getD u 0)).length

/-- The first point of a class of more than `t` points. -/
def domA (col : List ℕ) (t : ℕ) : Option ℕ := (List.range col.length).find? fun u => t < cntA col u

/-- The class of `u`. -/
def classA (col : List ℕ) (u : ℕ) : List ℕ :=
  (List.range col.length).filter fun w => col.getD w 0 = col.getD u 0

/-- The colours of the pairs of distinct points of `C` in the individualized 2-skeleton. -/
def pairCols (c : Array ℕ) (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ) (C : List ℕ) :
    List ℕ :=
  C.flatMap fun v => (C.filter (· ≠ v)).map fun w => get c (codePad2 pw k l xA v w)

/-- Whether the individualized 2-skeleton has one colour on the pairs of distinct points of
`C`. -/
def cliqueA (c : Array ℕ) (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ) (C : List ℕ) : Bool :=
  (pairCols c pw k l xA C).all fun a => a = (pairCols c pw k l xA C).headD 0

/-- The conclusion of the Design Lemma at the digits `xd`. -/
def goodA (c : Array ℕ) (pw : Array (Array ℕ)) (k m t : ℕ) (xd : List ℕ) : Bool :=
  match domA (col1A c pw k m xd.length xd.toArray) t with
  | none => true
  | some u₀ => decide (xd.length + 2 ≤ k) &&
      !cliqueA c pw k xd.length xd.toArray (classA (col1A c pw k m xd.length xd.toArray) u₀)

variable (k m) in
/-- The candidates: the digit lists of length `0, 1, …, k − 1`. -/
def cands : List (List ℕ) := (List.range k).flatMap fun l => tupList l m

/-- The first candidate where the Design Lemma's conclusion holds, with its vertex colouring. -/
def searchA (c : Array ℕ) (k m t : ℕ) : Option (List ℕ × Array ℕ) :=
  ((cands k m).find? (goodA c (pwTab k m) k m t)).map fun xd =>
    (xd, (col1A c (pwTab k m) k m xd.length xd.toArray).toArray)

/-! ### Meaning -/

theorem col1A_eq (c : Array ℕ) (x : List (Fin m)) :
    col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray =
      (List.finRange m).map fun u => skel1 (toFun (k := k) c) x u := by
  rw [col1A, ← map_finRange_eq_range m]
  refine List.map_congr_left fun u _ => ?_
  rw [codePad1_eq]
  rfl

theorem getD_col1A (c : Array ℕ) (x : List (Fin m)) (u : Fin m) :
    (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray).getD u 0 =
      skel1 (toFun (k := k) c) x u := by
  rw [col1A_eq]
  simp

theorem length_col1A (c : Array ℕ) (pw : Array (Array ℕ)) (k m l : ℕ) (xA : Array ℕ) :
    (col1A c pw k m l xA).length = m := by
  simp [col1A]

theorem card_filter_finRange {f : Fin m → ℕ} (a : ℕ) :
    (univ.filter fun w => f w = a).card = (((List.finRange m).map f).filter (· = a)).length := by
  rw [List.filter_map, List.length_map, ← List.toFinset_card_of_nodup
    ((List.nodup_finRange m).filter _)]
  congr 1
  ext w
  simp

theorem cntA_eq (c : Array ℕ) (x : List (Fin m)) (u : Fin m) :
    cntA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) u =
      (cls1 (toFun (k := k) c) x u).card := by
  rw [cntA, getD_col1A, col1A_eq, cls1, card_filter_finRange]

theorem domA_eq_none {col : List ℕ} {t : ℕ} :
    domA col t = none ↔ ∀ u < col.length, cntA col u ≤ t := by
  rw [domA, List.find?_eq_none]
  simp only [List.mem_range, decide_eq_true_eq, not_lt]

theorem domA_eq_some {col : List ℕ} {t u₀ : ℕ} (h : domA col t = some u₀) :
    u₀ < col.length ∧ t < cntA col u₀ := by
  rw [domA] at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_range, decide_eq_true_eq] at hm hp
  exact ⟨hm, hp⟩

/-- Two classes of more than `t ≥ m/2` points are equal. -/
theorem cls1_eq_of_large {V : Type*} [Fintype V] {c : (Fin k → V) → ℕ} {x : List V} {t : ℕ}
    (ht : Fintype.card V ≤ 2 * t) {u v : V} (hu : t < (cls1 c x u).card)
    (hv : t < (cls1 c x v).card) : cls1 c x u = cls1 c x v := by
  classical
  by_cases h : skel1 c x u = skel1 c x v
  · simp only [cls1, h]
  · exfalso
    have hd : Disjoint (cls1 c x u) (cls1 c x v) := by
      rw [Finset.disjoint_left]
      intro w hwu hwv
      simp only [cls1, mem_filter] at hwu hwv
      exact h (hwu.2.symm.trans hwv.2)
    have := Finset.card_union_of_disjoint hd
    have := Finset.card_le_univ (cls1 c x u ∪ cls1 c x v)
    omega

theorem mem_classA_col1A (c : Array ℕ) (x : List (Fin m)) (u : Fin m) (w : ℕ) :
    w ∈ classA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) u ↔
      ∃ hw : w < m, skel1 (toFun (k := k) c) x ⟨w, hw⟩ = skel1 (toFun (k := k) c) x u := by
  simp only [classA, List.mem_filter, List.mem_range, length_col1A, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, he⟩
    refine ⟨hw, ?_⟩
    have h1 := getD_col1A (k := k) c x ⟨w, hw⟩
    have h2 := getD_col1A (k := k) c x u
    simp only at h1 h2
    rw [← h1, ← h2, he]
  · rintro ⟨hw, he⟩
    refine ⟨hw, ?_⟩
    have h1 := getD_col1A (k := k) c x ⟨w, hw⟩
    have h2 := getD_col1A (k := k) c x u
    simp only at h1 h2
    rw [h1, h2, he]

theorem mem_pairCols (c : Array ℕ) (x : List (Fin m)) (C : List ℕ) (hC : ∀ v ∈ C, v < m)
    (a : ℕ) :
    a ∈ pairCols c (pwTab k m) k x.length (x.map Fin.val).toArray C ↔
      ∃ v ∈ C, ∃ w ∈ C, ∃ (hv : v < m) (hw : w < m), v ≠ w ∧
        a = skel2 (toFun (k := k) c) x ⟨v, hv⟩ ⟨w, hw⟩ := by
  simp only [pairCols, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv, w, ⟨hw, hne⟩, rfl⟩
    refine ⟨v, hv, w, hw, hC v hv, hC w hw, Ne.symm hne, ?_⟩
    have := codePad2_eq (k := k) x ⟨v, hC v hv⟩ ⟨w, hC w hw⟩
    simp only at this
    rw [this]
    rfl
  · rintro ⟨v, hv, w, hw, hv', hw', hne, rfl⟩
    refine ⟨v, hv, w, ⟨hw, Ne.symm hne⟩, ?_⟩
    have := codePad2_eq (k := k) x ⟨v, hv'⟩ ⟨w, hw'⟩
    simp only at this
    rw [this]
    rfl

theorem cliqueA_iff (c : Array ℕ) (x : List (Fin m)) (u : Fin m) :
    cliqueA c (pwTab k m) k x.length (x.map Fin.val).toArray
        (classA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) u) = true ↔
      IsClique (skel2 (toFun (k := k) c) x) (cls1 (toFun (k := k) c) x u) := by
  set C := classA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) u with hC
  have hCm : ∀ v ∈ C, v < m := fun v hv => ((mem_classA_col1A c x u v).1 hv).1
  have hmem : ∀ w : Fin m, (w : ℕ) ∈ C ↔ w ∈ cls1 (toFun (k := k) c) x u := fun w => by
    rw [hC, mem_classA_col1A]
    simp [cls1]
  set P := pairCols c (pwTab k m) k x.length (x.map Fin.val).toArray C with hP
  have hPm := mem_pairCols (k := k) c x C hCm
  unfold cliqueA
  rw [← hP, List.all_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · intro hall v hv v' hv' w hw w' hw' hne hne'
    have h1 := hall _ ((hPm _).2 ⟨v, (hmem v).2 hv, v', (hmem v').2 hv', v.2, v'.2,
      fun h => hne (Fin.ext h), rfl⟩)
    have h2 := hall _ ((hPm _).2 ⟨w, (hmem w).2 hw, w', (hmem w').2 hw', w.2, w'.2,
      fun h => hne' (Fin.ext h), rfl⟩)
    exact h1.trans h2.symm
  · intro hcl a ha
    rcases hPe : P with _ | ⟨b, P'⟩
    · rw [hPe] at ha
      simp at ha
    · have hb : b ∈ P := by rw [hPe]; exact List.mem_cons_self
      obtain ⟨v, hv, v', hv', hvm, hv'm, hne, rfl⟩ := (hPm a).1 ha
      obtain ⟨w, hw, w', hw', hwm, hw'm, hne', rfl⟩ := (hPm b).1 hb
      simp only [List.headD_cons]
      exact hcl _ ((hmem ⟨v, hvm⟩).1 hv) _ ((hmem ⟨v', hv'm⟩).1 hv') _ ((hmem ⟨w, hwm⟩).1 hw) _
        ((hmem ⟨w', hw'm⟩).1 hw') (fun h => hne (Fin.ext_iff.1 h))
        (fun h => hne' (Fin.ext_iff.1 h))

/-- **The search tests the conclusion of the Design Lemma.** -/
theorem goodA_iff (c : Array ℕ) {t : ℕ} (ht : m ≤ 2 * t) (x : List (Fin m)) :
    goodA c (pwTab k m) k m t (x.map Fin.val) = true ↔ DesignGood (toFun (k := k) c) t x := by
  have hlen : (x.map Fin.val).length = x.length := List.length_map _
  unfold goodA
  rw [hlen]
  rcases hd : domA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) t with _ | u₀
  · simp only [true_iff]
    left
    intro u
    rw [← cntA_eq]
    exact (domA_eq_none.1 hd) u (by rw [length_col1A]; exact u.2)
  · obtain ⟨hu₀, hdom⟩ := domA_eq_some hd
    rw [length_col1A] at hu₀
    have hdom' : t < (cls1 (toFun (k := k) c) x ⟨u₀, hu₀⟩).card := by
      rw [← cntA_eq]
      exact hdom
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true]
    rw [show classA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) u₀ =
      classA (col1A c (pwTab k m) k m x.length (x.map Fin.val).toArray) (⟨u₀, hu₀⟩ : Fin m)
      from rfl]
    rw [Bool.eq_false_iff, ne_eq, cliqueA_iff]
    constructor
    · rintro ⟨hk, hnc⟩
      exact Or.inr ⟨hk, _, hdom', hnc⟩
    · rintro (hall | ⟨hk, u, hu, hnc⟩)
      · exact absurd (hall ⟨u₀, hu₀⟩) (not_le.2 hdom')
      · refine ⟨hk, ?_⟩
        rwa [cls1_eq_of_large (by simpa using ht) hdom' hu]

theorem lt_of_mem_digitsOf {l m t d : ℕ} (hm : 0 < m) (hd : d ∈ digitsOf l m t) : d < m := by
  simp only [digitsOf, List.mem_ofFn] at hd
  obtain ⟨j, rfl⟩ := hd
  exact Nat.mod_lt _ hm

/-- **The candidates are the lists of fewer than `k` points.** -/
theorem mem_cands {xd : List ℕ} :
    xd ∈ cands k m ↔ ∃ x : List (Fin m), x.length < k ∧ xd = x.map Fin.val := by
  simp only [cands, List.mem_flatMap, List.mem_range, tupList_eq, List.mem_map]
  constructor
  · rintro ⟨l, hl, t, ht, rfl⟩
    have hm : 0 < m ∨ l = 0 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rcases Nat.eq_zero_or_pos l with rfl | hl'
        · exact Or.inr rfl
        · rw [Nat.zero_pow hl'] at ht
          omega
      · exact Or.inl hm
    rcases hm with hm | rfl
    · refine ⟨(digitsOf l m t).attach.map fun d =>
        ⟨d.1, lt_of_mem_digitsOf hm d.2⟩, by simpa [digitsOf] using hl, ?_⟩
      simp
    · exact ⟨[], hl, by simp [digitsOf]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.length, hx, enc (fun j : Fin x.length => x[j]), enc_lt _, ?_⟩
    rw [← digits_symm ⟨_, enc_lt _⟩, symm_enc]
    simp [digits, List.ofFn_getElem_eq_map]

theorem searchA_eq_some {c : Array ℕ} {t : ℕ} {xd : List ℕ} {col : Array ℕ}
    (h : searchA c k m t = some (xd, col)) :
    ∃ x : List (Fin m), x.length < k ∧ xd = x.map Fin.val ∧
      goodA c (pwTab k m) k m t xd = true ∧
      col = (col1A c (pwTab k m) k m xd.length xd.toArray).toArray := by
  unfold searchA at h
  rcases hf : (cands k m).find? (goodA c (pwTab k m) k m t) with _ | xd'
  · rw [hf] at h
    cases h
  · rw [hf] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, hx, rfl⟩ := mem_cands.1 (List.mem_of_find?_eq_some hf)
    exact ⟨x, hx, rfl, List.find?_some hf, rfl⟩

theorem searchA_eq_none {c : Array ℕ} {t : ℕ} (h : searchA c k m t = none) (x : List (Fin m))
    (hx : x.length < k) : goodA c (pwTab k m) k m t (x.map Fin.val) = false := by
  unfold searchA at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using h _ (mem_cands.2 ⟨x, hx, rfl⟩)

end GraphIso.Coherent
