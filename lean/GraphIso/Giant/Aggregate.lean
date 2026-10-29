module

public import GraphIso.CertProg.CertIso
public import GraphIso.Giant.FullGroup
public import GraphIso.Recursion.Pullback
public import GraphIso.Solver.Sims

/-!
# Aggregating the certificates

Stage 14g, item 2 (`PLAN-14.md` §11).

* **The `k`-subsets of the base.** `ksubsD m k` lists the `k`-subsets of `[0, m)` as increasing
  lists (`mem_ksubsD`), each once (`ksubsD_finsetOf`: as `finsetOf`, exactly the `k`-subsets
  of `Fin m`; `length_ksubsD`: `C(m, k)` of them). `ksubsProg` computes it at a cost polynomial
  times `C(m, k)` when `2 k ≤ m` (`RunsWithin.ksubsProg`), through the partial subsets
  `agParts` (`agParts_length_le`).
* **The full group.** `fullProg sub n N k x G` runs `certProg` on every `k`-subset and joins
  (by `generate`, so the group in hand always has at most `s` generators) the certificates
  `K(A)` whose test `Alt(A) ≤ ψ_A(K(A))` passes. `RunsWithin.fullProg`: the result is valid,
  has at most `s` generators, and denotes exactly the preimage in `G` of `fullGroupK φ k x`
  (`Denotes`); its cost is `fullCost`: the enumeration, one `generate`, and `C(m, k)` steps of
  at most `certCost` plus the join each. The preimages are `agPre` (`ag_denotes_iff`); the
  certificates of a list of test sets are `agPart`, and those of all `k`-subsets are
  `fullGroupK` (`agPart_ksubsD`).
* **The charges.** The backend charges are premises only on the inputs that occur: the setwise
  stabilizers of the enumerated `k`-subsets (`hBgs`) and the joins, lists of at most `2 s`
  generators (`hBF`): `K(A)` has at most `s` generators (`ag_certProg_gens`, the run of
  `certProg` with the generator bound of its iterated stabilizer). For the Schreier–Sims
  backend both premises hold with explicit values (`ag_ss_charges`).
* **The case decision.** `caseProg n N F` asks the backend for `F`'s orbits on the base
  positions, shifts them to base indices (`agShiftD`), and decides the case (`caseD`): `2` with
  the orbit `Φ` if some orbit has more than `m/2` points, else `3` if the support has fewer
  than `m/2` points, else `1`. `RunsWithin.caseProg` with `caseD_spec`: the case is decided
  exactly in terms of the orbits of the base action `(baseHom F n hF).range`, `Φ` lists such an
  orbit, and the support count is the number of points in orbits of more than one point
  (`ag_card_supp`).
* **For `φ`.** If `F` denotes `C`, its base action is `C.map φ` (`ag_range_eq`), and a point is
  in milestone 13's `supp φ C` exactly when its orbit under `C.map φ` has more than one point
  (`ag_mem_supp_iff`).
-/

@[expose] public section

namespace GraphIso.Giant

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates GraphIso.CertProg
  Cost GraphIso.Programs GraphIso.Solver

/-! ### The `k`-subsets of `[0, m)` -/

section Subsets

/-- One step of the enumeration: keep every partial subset, and add `j` to those with fewer
than `k` points. Partial subsets are `(size, points in decreasing order)`. -/
def ag_ext (k j : ℕ) (acc : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  acc ++ (acc.filter fun p => decide (p.1 < k)).map fun p => (p.1 + 1, j :: p.2)

/-- The subsets of `[0, j)` with at most `k` points. -/
def agParts (k : ℕ) : ℕ → List (ℕ × List ℕ)
  | 0 => [(0, [])]
  | j + 1 => ag_ext k j (agParts k j)

/-- **The `k`-subsets of `[0, m)`**, as increasing lists. -/
def ksubsD (m k : ℕ) : List (List ℕ) :=
  ((agParts k m).filter fun p => p.1 == k).map fun p => p.2.reverse

theorem ag_mem_ext {k j : ℕ} {acc : List (ℕ × List ℕ)} {p : ℕ × List ℕ} :
    p ∈ ag_ext k j acc ↔ p ∈ acc ∨ ∃ q ∈ acc, q.1 < k ∧ p = (q.1 + 1, j :: q.2) := by
  simp only [ag_ext, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨q, ⟨hq, hk⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, hq, hk, rfl⟩
  · rintro (h | ⟨q, hq, hk, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨q, ⟨hq, hk⟩, rfl⟩

/-- The partial subsets: decreasing lists of points below `j`, with at most `k` points. -/
theorem mem_agParts {k : ℕ} : ∀ (j : ℕ) (p : ℕ × List ℕ), p ∈ agParts k j ↔
    p.1 = p.2.length ∧ p.2.Pairwise (· > ·) ∧ (∀ i ∈ p.2, i < j) ∧ p.1 ≤ k
  | 0, p => by
    simp only [agParts, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h1, -, h3, -⟩
      obtain ⟨a, l⟩ := p
      cases l with
      | nil => simp_all
      | cons i l => exact absurd (h3 i List.mem_cons_self) (Nat.not_lt_zero _)
  | j + 1, p => by
    rw [agParts, ag_mem_ext, mem_agParts j]
    constructor
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨q, hq, hk, rfl⟩)
      · exact ⟨h1, h2, fun i hi => Nat.lt_succ_of_lt (h3 i hi), h4⟩
      · obtain ⟨h1, h2, h3, -⟩ := (mem_agParts j q).1 hq
        refine ⟨by simp [h1], List.pairwise_cons.2 ⟨fun i hi => h3 i hi, h2⟩, ?_, by omega⟩
        intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (h3 i hi)
    · rintro ⟨h1, h2, h3, h4⟩
      obtain ⟨a, l⟩ := p
      by_cases hj : j ∈ l
      · cases l with
        | nil => exact absurd hj List.not_mem_nil
        | cons i rest =>
          have hpw := List.pairwise_cons.1 h2
          have hij : i = j := by
            rcases List.mem_cons.1 hj with h | h
            · exact h.symm
            · have := hpw.1 j h
              have := h3 i List.mem_cons_self
              omega
          subst hij
          refine Or.inr ⟨(a - 1, rest), ?_, ?_, ?_⟩
          · refine (mem_agParts i _).2 ⟨?_, hpw.2, fun r hr => hpw.1 r hr, by simp at h1 ⊢; omega⟩
            simp only [List.length_cons] at h1
            simp only
            omega
          · simp only [List.length_cons] at h1
            simp only
            omega
          · simp only [List.length_cons] at h1
            simp only [Prod.mk.injEq, and_true]
            omega
      · refine Or.inl ⟨h1, h2, fun i hi => ?_, h4⟩
        have := h3 i hi
        have : i ≠ j := fun e => hj (e ▸ hi)
        omega

theorem agParts_nodup (k : ℕ) : ∀ j, (agParts k j).Nodup
  | 0 => by simp [agParts]
  | j + 1 => by
    rw [agParts, ag_ext]
    refine List.Nodup.append (agParts_nodup k j) ?_ ?_
    · refine ((agParts_nodup k j).filter _).map ?_
      intro p q h
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
      exact Prod.ext (by omega) h.2
    · intro p hp hp'
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp'
      have := ((mem_agParts j _).1 hp).2.2.1 j List.mem_cons_self
      exact Nat.lt_irrefl _ this

/-- **The enumerated lists are exactly the increasing `k`-lists below `m`.** -/
theorem mem_ksubsD {m k : ℕ} {l : List ℕ} :
    l ∈ ksubsD m k ↔ l.Pairwise (· < ·) ∧ l.length = k ∧ ∀ i ∈ l, i < m := by
  simp only [ksubsD, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨p, ⟨hp, hk⟩, rfl⟩
    obtain ⟨h1, h2, h3, -⟩ := (mem_agParts m p).1 hp
    refine ⟨List.pairwise_reverse.2 h2, by simp [← h1, hk], fun i hi => h3 i (by simpa using hi)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(k, l.reverse), ⟨(mem_agParts m _).2 ⟨by simp [h2], ?_, fun i hi => h3 i (by
      simpa using hi), le_rfl⟩, rfl⟩, by simp⟩
    exact List.pairwise_reverse.2 h1

theorem ksubsD_nodup (m k : ℕ) : (ksubsD m k).Nodup := by
  unfold ksubsD
  refine ((agParts_nodup k m).filter _).map_on ?_
  intro p hp q hq h
  simp only [List.mem_filter, beq_iff_eq] at hp hq
  have h' : p.2 = q.2 := List.reverse_injective h
  have hp1 := ((mem_agParts m p).1 hp.1).1
  have hq1 := ((mem_agParts m q).1 hq.1).1
  exact Prod.ext (by rw [hp1, hq1, h']) h'

/-- Increasing lists with the same points are equal. -/
theorem ag_eq_of_finsetOf {m : ℕ} {l l' : List ℕ} (hl : l.Pairwise (· < ·))
    (hl' : l'.Pairwise (· < ·)) (hlm : ∀ i ∈ l, i < m) (hlm' : ∀ i ∈ l', i < m)
    (h : finsetOf m l = finsetOf m l') : l = l' := by
  have hmem : ∀ i, i ∈ l ↔ i ∈ l' := by
    intro i
    constructor
    · intro hi
      have := (Finset.ext_iff.1 h ⟨i, hlm i hi⟩).1 (mem_finsetOf.2 hi)
      exact mem_finsetOf.1 this
    · intro hi
      have := (Finset.ext_iff.1 h ⟨i, hlm' i hi⟩).2 (mem_finsetOf.2 hi)
      exact mem_finsetOf.1 this
  exact List.SortedLT.eq_of_mem_iff hl.sortedLT hl'.sortedLT hmem

/-- **Every `k`-subset of `Fin m` is enumerated exactly once.** -/
theorem ksubsD_finsetOf (m k : ℕ) :
    ((ksubsD m k).map (finsetOf m)).Nodup ∧
      ∀ A : Finset (Fin m), A ∈ (ksubsD m k).map (finsetOf m) ↔ A.card = k := by
  refine ⟨(ksubsD_nodup m k).map_on fun l hl l' hl' h => ?_, fun A => ?_⟩
  · obtain ⟨h1, -, h3⟩ := mem_ksubsD.1 hl
    obtain ⟨h1', -, h3'⟩ := mem_ksubsD.1 hl'
    exact ag_eq_of_finsetOf h1 h1' h3 h3' h
  · constructor
    · rintro hA
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hA
      obtain ⟨h1, h2, h3⟩ := mem_ksubsD.1 hl
      rw [card_finsetOf (h1.imp ne_of_lt) h3, h2]
    · intro hA
      refine List.mem_map.2 ⟨Finset.sort (A.image Fin.val), mem_ksubsD.2 ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (Finset.sortedLT_sort _).pairwise
      · rw [Finset.length_sort, Finset.card_image_of_injective _ Fin.val_injective, hA]
      · intro i hi
        rw [Finset.mem_sort, Finset.mem_image] at hi
        obtain ⟨j, -, rfl⟩ := hi
        exact j.2
      · ext j
        rw [mem_finsetOf, Finset.mem_sort, Finset.mem_image]
        exact ⟨fun ⟨j', hj', e⟩ => Fin.ext e ▸ hj', fun hj => ⟨j, hj, rfl⟩⟩

/-- There are `C(m, k)` of them. -/
theorem length_ksubsD (m k : ℕ) : (ksubsD m k).length = m.choose k := by
  obtain ⟨hnd, hmem⟩ := ksubsD_finsetOf m k
  have h1 : ((ksubsD m k).map (finsetOf m)).toFinset =
      (Finset.univ : Finset (Fin m)).powersetCard k := by
    ext A
    rw [List.mem_toFinset, hmem, Finset.mem_powersetCard]
    simp
  have h2 := congrArg Finset.card h1
  rw [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin] at h2
  exact h2

/-! #### The number of partial subsets -/

theorem ag_count_filter_map {k j i : ℕ} (acc : List (ℕ × List ℕ)) :
    (((acc.filter fun p => decide (p.1 < k)).map fun p => (p.1 + 1, j :: p.2)).filter
      fun p => p.1 == i + 1).length =
      (acc.filter fun p => decide (p.1 < k) && p.1 == i).length := by
  rw [List.filter_map, List.length_map, List.filter_filter]
  congr 1
  refine List.filter_congr fun p _ => ?_
  have e : (p.1 + 1 == i + 1) = (p.1 == i) := by
    by_cases h : p.1 = i <;> simp [h]
  simp only [Function.comp_apply, e, Bool.and_comm]

/-- The partial subsets of size `i`: `C(j, i)` of them for `i ≤ k`. -/
theorem ag_count (k : ℕ) : ∀ (j i : ℕ),
    ((agParts k j).filter fun p => p.1 == i).length = if i ≤ k then j.choose i else 0
  | 0, i => by
    rcases i with _ | i <;> simp [agParts]
  | j + 1, 0 => by
    rw [agParts, ag_ext, List.filter_append, List.length_append, ag_count k j 0]
    have : (((agParts k j).filter fun p => decide (p.1 < k)).map fun p =>
        (p.1 + 1, j :: p.2)).filter (fun p => p.1 == 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro p hp
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
      simp
    rw [this]
    simp
  | j + 1, i + 1 => by
    rw [agParts, ag_ext, List.filter_append, List.length_append, ag_count k j (i + 1),
      ag_count_filter_map]
    by_cases hik : i < k
    · have e : ((agParts k j).filter fun p => decide (p.1 < k) && p.1 == i) =
          (agParts k j).filter fun p => p.1 == i := by
        refine List.filter_congr fun p _ => ?_
        by_cases h : p.1 = i
        · simp [h, hik]
        · simp [h]
      rw [e, ag_count k j i]
      simp only [show i + 1 ≤ k from by omega, show i ≤ k from by omega, ↓reduceIte,
        Nat.choose_succ_succ']
      omega
    · have e : ((agParts k j).filter fun p => decide (p.1 < k) && p.1 == i) = [] := by
        rw [List.filter_eq_nil_iff]
        intro p _
        by_cases h : p.1 = i
        · simp [h, hik]
        · simp [h]
      simp only [e, show ¬ i + 1 ≤ k from by omega, ↓reduceIte]
      rfl

/-- A list of pairs with first components at most `k`, counted by first component. -/
theorem ag_length_eq_sum {k : ℕ} :
    ∀ (L : List (ℕ × List ℕ)), (∀ p ∈ L, p.1 ≤ k) →
      L.length = ∑ i ∈ Finset.range (k + 1), (L.filter fun p => p.1 == i).length
  | [], _ => by simp
  | p :: L, h => by
    rw [List.length_cons, ag_length_eq_sum L fun q hq => h q (List.mem_cons_of_mem _ hq)]
    have hp : p.1 < k + 1 := Nat.lt_succ_of_le (h p List.mem_cons_self)
    have e : ∀ i, ((p :: L).filter fun q => q.1 == i).length =
        (L.filter fun q => q.1 == i).length + if p.1 = i then 1 else 0 := by
      intro i
      rw [List.filter_cons]
      by_cases hi : p.1 = i <;> simp [hi]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_range, hp, ↓reduceIte]

/-- **The partial subsets number at most `(k + 1) C(m, k)`** when `2 k ≤ m`. -/
theorem agParts_length_le {m k j : ℕ} (h2k : 2 * k ≤ m) (hj : j ≤ m) :
    (agParts k j).length ≤ (k + 1) * m.choose k := by
  rw [ag_length_eq_sum (agParts k j) fun p hp => ((mem_agParts j p).1 hp).2.2.2]
  calc ∑ i ∈ Finset.range (k + 1), ((agParts k j).filter fun p => p.1 == i).length
      ≤ ∑ _i ∈ Finset.range (k + 1), m.choose k := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [ag_count k j i]
        simp only [Nat.lt_succ_iff.1 (Finset.mem_range.1 hi), ↓reduceIte]
        exact (Nat.choose_le_choose i hj).trans
          (Recursion.choose_mono_le_half (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) h2k)
    _ = (k + 1) * m.choose k := by simp

end Subsets

/-! #### The enumeration as a program -/

/-- A partial subset: its size and its points in decreasing order. -/
abbrev agPartTy : Ty := .prod .nat (.list .nat)

section SubsetsProg

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Whether a partial subset has fewer than `k` points. -/
def agLessProg (k : var .nat) (p : var agPartTy) : Prog S rec var .bool :=
  .bind (.op1 .fst p) fun l => .op2 .natLt l k

/-- Add the point `j` to a partial subset. -/
def agGrowProg (j : var .nat) (p : var agPartTy) : Prog S rec var agPartTy :=
  .bind (.op1 .fst p) fun l => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .add l one) fun l' => .bind (.op1 .snd p) fun ps =>
  .bind (.op2 .cons j ps) fun ps' => .op2 .pair l' ps'

/-- One step of the enumeration (`ag_ext`). -/
def agExtProg (k : var .nat) (acc : var (.list agPartTy)) (j : var .nat) :
    Prog S rec var (.list agPartTy) :=
  .bind (Toolkit.filterList acc fun p => agLessProg k p) fun fl =>
  .bind (mapList fl fun p => agGrowProg j p) fun gl =>
  .op2 .append acc gl

/-- Whether a partial subset has `k` points. -/
def agIsKProg (k : var .nat) (p : var agPartTy) : Prog S rec var .bool :=
  .bind (.op1 .fst p) fun l => .op2 .natEq l k

/-- The points of a partial subset in increasing order. -/
def agRevProg (p : var agPartTy) : Prog S rec var (.list .nat) :=
  .bind (.op1 .snd p) fun ps => .op1 .reverse ps

/-- **The `k`-subsets of `[0, m)`** (`ksubsD`). -/
def ksubsProg (m k : var .nat) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range m) fun js =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun e =>
  .bind (.op2 .pair z e) fun p0 => .bind (.op0 .nil) fun nil =>
  .bind (.op2 .cons p0 nil) fun init =>
  .bind (.foldList js init fun acc j => agExtProg k acc j) fun parts =>
  .bind (Toolkit.filterList parts fun p => agIsKProg k p) fun fk =>
  mapList fk fun p => agRevProg p

end SubsetsProg

/-- The cost of one enumeration step on `L` partial subsets. -/
def agExtCost (L : ℕ) : ℕ := 16 * L + 6

/-- The cost of `ksubsProg`. -/
def ksubsCost (m k : ℕ) : ℕ :=
  m * (agExtCost ((k + 1) * m.choose k) + 1) + 6 * ((k + 1) * m.choose k) +
    m.choose k * (k + 5) + m + 20

section SubsetsSpec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.agLessProg (k : ℕ) (p : agPartTy.denote) :
    RunsWithin X body (Giant.agLessProg k p) (decide (p.1 < k)) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])

theorem RunsWithin.agGrowProg (j : ℕ) (p : agPartTy.denote) :
    RunsWithin X body (Giant.agGrowProg j p) (p.1 + 1, j :: p.2) 6 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.agExtProg (k : ℕ) (acc : List agPartTy.denote) (j : ℕ) :
    RunsWithin X body (Giant.agExtProg k acc j) (ag_ext k j acc) (agExtCost acc.length) := by
  have hf := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := agPartTy) (xs := acc)
    (p := fun p => Giant.agLessProg k p) (P := fun p => decide (p.1 < k)) (c := 2)
    fun p _ => RunsWithin.agLessProg k p
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := agPartTy) (b' := agPartTy)
    (xs := acc.filter fun p => decide (p.1 < k)) (f := fun p => Giant.agGrowProg j p)
    (F := fun p => (p.1 + 1, j :: p.2)) (c := 6) fun p _ => RunsWithin.agGrowProg j p
  have hlen := List.length_filter_le (fun p : agPartTy.denote => decide (p.1 < k)) acc
  apply RunsWithin.mono
  case h =>
    run_step hf
    run_step hm
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head, agExtCost]
    nlinarith

theorem RunsWithin.agIsKProg (k : ℕ) (p : agPartTy.denote) :
    RunsWithin X body (Giant.agIsKProg k p) (p.1 == k) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])

theorem RunsWithin.agRevProg (p : agPartTy.denote) :
    RunsWithin X body (Giant.agRevProg p) p.2.reverse (p.2.length + 2) :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _)
    (by simp [Prim.cost, Prim.eval]; omega)

theorem ag_range'_succ (j r : ℕ) : List.range' j (r + 1) = j :: List.range' (j + 1) r := by
  simp [List.range'_succ]

/-- The enumeration loop from step `j`. -/
theorem ag_fold_run {m k : ℕ} (h2k : 2 * k ≤ m) :
    ∀ (r j : ℕ), j + r = m →
      RunsWithin X body (Prog.foldList (a := .nat) (b := .list agPartTy) (List.range' j r)
          (agParts k j) fun acc j => Giant.agExtProg k acc j) (agParts k m)
        (r * (agExtCost ((k + 1) * m.choose k) + 1))
  | 0, j, h => by
    obtain rfl : j = m := by omega
    simpa using RunsWithin.foldList_nil
  | r + 1, j, h => by
    rw [ag_range'_succ]
    have h₁ := RunsWithin.agExtProg (X := X) (body := body) k (agParts k j) j
    have h₂ := ag_fold_run h2k r (j + 1) (by omega)
    have hlen := agParts_length_le h2k (show j ≤ m by omega)
    refine (RunsWithin.foldList_cons (h₁.mono (show agExtCost (agParts k j).length ≤
      agExtCost ((k + 1) * m.choose k) by unfold agExtCost; omega)) h₂).mono ?_
    generalize agExtCost ((k + 1) * m.choose k) = A
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- **The enumeration of the `k`-subsets** as a program, when `2 k ≤ m`. -/
theorem RunsWithin.ksubsProg {m k : ℕ} (h2k : 2 * k ≤ m) :
    RunsWithin X body (Giant.ksubsProg m k) (ksubsD m k) (ksubsCost m k) := by
  have hfold := ag_fold_run (X := X) (body := body) h2k m 0 (by omega)
  have hparts : agParts k 0 = [(0, [])] := rfl
  rw [hparts] at hfold
  have hrange : List.range m = List.range' 0 m := List.range_eq_range'
  have hplen := agParts_length_le (j := m) h2k le_rfl
  have hf := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := agPartTy)
    (xs := agParts k m) (p := fun p => Giant.agIsKProg k p) (P := fun p => p.1 == k) (c := 2)
    fun p _ => RunsWithin.agIsKProg k p
  have hfk : ∀ p ∈ (agParts k m).filter (fun p => p.1 == k), p.2.length + 2 ≤ k + 2 := by
    intro p hp
    rw [List.mem_filter, beq_iff_eq] at hp
    have := ((mem_agParts m p).1 hp.1).1
    omega
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := agPartTy) (b' := .list .nat)
    (xs := (agParts k m).filter fun p => p.1 == k) (f := fun p => Giant.agRevProg p)
    (F := fun p => p.2.reverse) (c := k + 2)
    fun p hp => (RunsWithin.agRevProg p).mono (hfk p hp)
  have hfklen : ((agParts k m).filter fun p => p.1 == k).length = m.choose k := by
    rw [← length_ksubsD m k, ksubsD, List.length_map]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    rw [hrange]
    run_step hfold
    run_step hf
    exact hm
  case hc =>
    simp only [Prim.cost, Args.head, ksubsCost, hfklen]
    nlinarith

end SubsetsSpec

/-! ### The full group -/

section Bridge

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}

/-- The preimage in `G`, as a subgroup of `Perm (Fin N)`, of a subgroup of the restricted
group. -/
def agPre (hC : CertSetting G n) (C : Subgroup (strGroup hC)) : Subgroup (Perm (Fin N)) :=
  (C.comap (strR hC)).map G.subtype

theorem ag_mem_agPre {C : Subgroup (strGroup hC)} {g : Perm (Fin N)} :
    g ∈ agPre hC C ↔ ∃ hg : g ∈ G, strR hC ⟨g, hg⟩ ∈ C := by
  simp only [agPre, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, hh⟩
  · rintro ⟨hg, hgC⟩
    exact ⟨⟨g, hg⟩, hgC, rfl⟩

/-- `Denotes` for subgroups: equality with the preimage. -/
theorem ag_denotes_iff {S : Subgroup (Perm (Fin N))} {C : Subgroup (strGroup hC)} :
    Denotes hC (S : Set (Perm (Fin N))) (C : Set (strGroup hC)) ↔ S = agPre hC C := by
  constructor
  · intro h
    ext g
    rw [ag_mem_agPre]
    exact h g
  · rintro rfl g
    exact ag_mem_agPre

theorem agPre_le (C : Subgroup (strGroup hC)) : agPre hC C ≤ G := by
  intro g hg
  obtain ⟨hgG, -⟩ := ag_mem_agPre.1 hg
  exact hgG

theorem agPre_sup (C D : Subgroup (strGroup hC)) :
    agPre hC (C ⊔ D) = agPre hC C ⊔ agPre hC D := by
  rw [agPre, agPre, agPre, ← Subgroup.comap_sup_eq (strR hC) C D (strR_surjective hC),
    Subgroup.map_sup]

theorem agPre_bot : agPre hC (⊥ : Subgroup (strGroup hC)) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgG, hgC⟩ := ag_mem_agPre.1 hg
  have : (⟨g, hgG⟩ : G) = 1 := strR_injective hC (by rw [map_one]; exact hgC)
  exact Subgroup.mem_bot.2 (congrArg Subtype.val this)

variable (φ : strGroup hC →* Perm (Fin (N - n)))

/-- The certificate of fullness of one test set, if it passes the test `Alt(A) ≤ ψ_A(K(A))`,
and the trivial group otherwise. -/
def agTerm (x : Fin n → ℕ) (al : List ℕ) : Subgroup (strGroup hC) :=
  ⨆ (_ : IsGiantOn φ (finsetOf (N - n) al) (certK φ (finsetOf (N - n) al) x)),
    (certK φ (finsetOf (N - n) al) x).map (stabA φ (finsetOf (N - n) al)).subtype

/-- The group generated by the certificates of the listed test sets that pass the test. -/
def agPart (x : Fin n → ℕ) : List (List ℕ) → Subgroup (strGroup hC)
  | [] => ⊥
  | al :: rest => agTerm φ x al ⊔ agPart x rest

theorem agPart_append_single (x : Fin n → ℕ) (al : List ℕ) :
    ∀ l : List (List ℕ), agPart φ x (l ++ [al]) = agPart φ x l ⊔ agTerm φ x al
  | [] => by simp [agPart]
  | a :: l => by
    simp only [List.cons_append, agPart, agPart_append_single x al l, sup_assoc]

theorem le_agPart (x : Fin n → ℕ) {al : List ℕ} :
    ∀ {l : List (List ℕ)}, al ∈ l → agTerm φ x al ≤ agPart φ x l
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_sup_left
    · exact (le_agPart x h).trans le_sup_right

theorem agTerm_le (x : Fin n → ℕ) {k : ℕ} {al : List ℕ}
    (hk : (finsetOf (N - n) al).card = k) : agTerm φ x al ≤ fullGroupK φ k x :=
  iSup_le fun hg => le_iSup₂_of_le (f := fun (A : Finset (Fin (N - n)))
    (_ : A.card = k ∧ IsGiantOn φ A (certK φ A x)) => (certK φ A x).map (stabA φ A).subtype)
    (finsetOf (N - n) al) ⟨hk, hg⟩ le_rfl

/-- **The certificates of all `k`-subsets generate `fullGroupK`.** -/
theorem agPart_ksubsD (x : Fin n → ℕ) (k : ℕ) :
    agPart φ x (ksubsD (N - n) k) = fullGroupK φ k x := by
  refine le_antisymm ?_ ?_
  · have key : ∀ l : List (List ℕ), (∀ al ∈ l, al ∈ ksubsD (N - n) k) →
        agPart φ x l ≤ fullGroupK φ k x := by
      intro l
      induction l with
      | nil => intro _; exact bot_le
      | cons al l ih =>
        intro hl
        refine sup_le (agTerm_le φ x ?_) (ih fun a ha => hl a (List.mem_cons_of_mem _ ha))
        exact ((ksubsD_finsetOf (N - n) k).2 _).1
          (List.mem_map.2 ⟨al, hl al List.mem_cons_self, rfl⟩)
    exact key _ fun _ h => h
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨al, hal, rfl⟩ := List.mem_map.1 (((ksubsD_finsetOf (N - n) k).2 A).2 hA.1)
    exact (le_iSup_of_le hA.2 le_rfl : _ ≤ agTerm φ x al).trans (le_agPart φ x hal)

end Bridge

section FoldExists

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- A fold whose steps keep an invariant on the processed prefix and the accumulator, each step
at cost at most `c`. -/
theorem ag_fold_exists {a' b' : Ty} {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    {P : List a'.denote → b'.denote → Prop} {c : ℕ} :
    ∀ (xs done : List a'.denote) (init : b'.denote), P done init →
      (∀ done acc x, x ∈ xs → P done acc →
        ∃ acc', RunsWithin X body (f acc x) acc' c ∧ P (done ++ [x]) acc') →
      ∃ r, RunsWithin X body (.foldList xs init f) r (xs.length * (c + 1)) ∧ P (done ++ xs) r
  | [], done, init, hP, _ => ⟨init, by simpa using RunsWithin.foldList_nil, by simpa using hP⟩
  | x :: xs, done, init, hP, hf => by
    obtain ⟨acc', h₁, hP₁⟩ := hf done init x List.mem_cons_self hP
    obtain ⟨r, h₂, hP₂⟩ := ag_fold_exists xs (done ++ [x]) acc' hP₁
      fun d acc y hy hd => hf d acc y (List.mem_cons_of_mem _ hy) hd
    refine ⟨r, (RunsWithin.foldList_cons h₁ h₂).mono ?_, by simpa using hP₂⟩
    simp only [List.length_cons, Nat.succ_mul]
    omega

end FoldExists

section FullProgram

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- `n + a`. -/
def agAddProg {S : Signature} (n a : var .nat) : Prog S rec var .nat := .op2 .add n a

/-- Join the certificate `K(A)` to the group generated so far, and generate. -/
def agJoinProg (N : var .nat) (Fc : var (Ty.group D)) (t₁ : var (.prod (Ty.group D) .bool)) :
    Prog (groupSig D) rec var (Ty.group D) :=
  .bind (.op1 .fst t₁) fun KA => .bind (.op1 .snd KA) fun kd => .bind (.op1 .fst kd) fun kgs =>
  .bind (.op1 .snd Fc) fun fd => .bind (.op1 .fst fd) fun fgs =>
  .bind (.op2 .append fgs kgs) fun gs' => .bind (.op2 .pair N gs') fun a =>
  Prog.call (S := groupSig D) GroupOp.generate a

/-- One test set: its certificate, joined to the group if it passes the test. -/
def fullStep (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N : var .nat) (xy : var Ty.strs) (G : var (Ty.group D)) (Fc : var (Ty.group D))
    (al : var (.list .nat)) : Prog (groupSig D) rec var (Ty.group D) :=
  .bind (mapList al fun a => agAddProg n a) fun pA =>
  .bind (Programs.posProg N pA) fun pos =>
  .bind (certProg sub n pos pA xy G al) fun res =>
  .caseOption res (.ret Fc) fun c =>
    .bind (.op1 .snd c) fun t₂ => .bind (.op1 .snd t₂) fun t₁ =>
    .bind (.op1 .snd t₁) fun full =>
    .ite full (agJoinProg N Fc t₁) (.ret Fc)

/-- **The full group** `F`: the certificates of all `k`-subsets of the base that pass the
test, generated at degree `N`. -/
def fullProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N k : var .nat) (x : var Ty.str) (G : var (Ty.group D)) :
    Prog (groupSig D) rec var (Ty.group D) :=
  .bind (.op2 .pair x x) fun xy =>
  .bind (.op2 .sub N n) fun m =>
  .bind (ksubsProg m k) fun als =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .pair N nil) fun a₀ =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a₀) fun F₀ =>
  .foldList als F₀ fun Fc al => fullStep sub n N xy G Fc al

end FullProgram

/-- The cost of one step of `fullProg`. -/
def fullStepCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs BF : ℕ) : ℕ :=
  certCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs + 2 * N + 13 * k + s + BF + 30

/-- **The cost of `fullProg`**: `C(m, k)` certificates and joins, the enumeration, and the first
`generate`. -/
def fullCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs BF : ℕ) : ℕ :=
  ksubsCost (N - n) k + BF + (N - n).choose k *
    (fullStepCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs BF + 1) + 10

section FullSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- Backend bounds transported along an equality of degrees keep their charges. -/
theorem ag_cast_bounds {k k' sk : ℕ} (h : k = k') (Bk : BackendBounds X DV k sk ⊤) :
    (h ▸ Bk : BackendBounds X DV k' sk ⊤).Bgen = Bk.Bgen ∧
      (h ▸ Bk : BackendBounds X DV k' sk ⊤).Borb = Bk.Borb ∧
      (h ▸ Bk : BackendBounds X DV k' sk ⊤).Bstab = Bk.Bstab := by
  subst h
  exact ⟨rfl, rfl, rfl⟩

variable {N n : ℕ} {gs : GensData} {hC : CertSetting (GensData.denote N gs) n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

theorem RunsWithin.agAddProg (n a : ℕ) :
    RunsWithin X body (Giant.agAddProg (S := groupSig D) n a) (n + a) 1 := RunsWithin.prim _ _

theorem RunsWithin.agJoinProg (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (N : ℕ)
    (Fc KA : GroupData D.denote) (full : Bool) (hv : GensData.AllValid N (Fc.2.1 ++ KA.2.1)) :
    RunsWithin X body (Giant.agJoinProg N Fc (KA, full))
      (X.O.run GroupOp.generate (N, Fc.2.1 ++ KA.2.1))
      (Fc.2.1.length + 7 + X.B.call GroupOp.generate (N, Fc.2.1 ++ KA.2.1)
        (X.O.run GroupOp.generate (N, Fc.2.1 ++ KA.2.1))) := by
  have hpre : X.Pre GroupOp.generate (N, Fc.2.1 ++ KA.2.1) :=
    hPre _ _ (by simp [certOps]) hv
  apply RunsWithin.mono
  case h =>
    unfold Giant.agJoinProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.call hpre
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head]
    omega

/-- The invariant of the aggregation loop: the group generated so far is valid, has at most `s`
generators, and is the preimage of the certificates of the processed test sets that pass. -/
def AggInv (DV : ℕ → GensData → D.denote → Prop) (hC : CertSetting (GensData.denote N gs) n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (xs : Fin n → ℕ) (s : ℕ) (done : List (List ℕ))
    (Fc : GroupData D.denote) : Prop :=
  Fc.1 = N ∧ GroupValid DV N Fc.2.1 Fc.2.2 ∧ Fc.2.1.length ≤ s ∧
    GensData.denote N Fc.2.1 = agPre hC (agPart φ xs done)

/-- **`K(A)` has at most `s` generators** in the run of `certProg`: the same run as
`RunsWithin.certProg` (whose proof this repeats), keeping the generator bound of the iterated
stabilizer (`iterStab_gens_le`), which `RunsWithin.certProg` does not state. -/
theorem ag_certProg_gens (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (h5 : 5 ≤ al.length)
    (hk : al.length + 2 ≤ N - n) {xy : StrData × StrData} (hxy : xy.2 = xy.1) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) {Bgen Bl Bgs : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ al.length.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ b₁ b₂, X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
      (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) xy n al.length s) (fun _ => Cb) s) :
    ∃ res, RunsWithin X body (CertProg.certProg sub n (WinData.pos N (winA N n al))
          (winA N n al).1 xy (N, gs, d) al) res
        (certCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl Bgs) ∧
      ∃ Wl K KA full, res = some (Wl, K, KA, full) ∧ KA.2.1.length ≤ s := by
  set A := finsetOf (N - n) al with hA
  set x := strOn hC.le (xy.1.denote N) with hx
  have hnN := hC.le
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- operations
  have hOgi : MeetsContractOn DV giantOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hPgi : ∀ op y, giantOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hOst : MeetsContractOn DV stepOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hPst : ∀ op y, stepOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hOs : MeetsContractOn DV stabOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h <;> simp [certOps, h]) hy
  have hPs : ∀ op y, stabOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h <;> simp [certOps, h]) hy
  have hOg : MeetsContractOn DV giantAOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h <;> simp [certOps, h]) hy
  have hPg : ∀ op y, giantAOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h <;> simp [certOps, h]) hy
  -- `G_A`
  obtain ⟨hsrun, hsN, hsv, hsden⟩ := RunsWithin.stabSetProg (X := X) (body := body) hOgi hPgi
    hGv hC.base hgiant hal halm hk B hs hGG₀ hBl hBgs
  have hsgen := stabSet_gens_le (X := X) hOgi hPgi hGv hC.base hgiant hal halm hk B hs hGG₀ hBl
  rcases hGA : stabSetModel X.O n (N, gs, d) al with ⟨N₁, gas, ga⟩
  rw [hGA] at hsrun hsN hsv hsden hsgen
  change N₁ = N at hsN
  subst hsN
  -- the initial coset
  have hden₀ : Denotes hC (PermData.denote N₁ (PermData.one N₁) •
      (GensData.denote N₁ gas : Set (Perm (Fin N₁))))
      (pairCoset φ A A x (strOn hC.le (xy.2.denote N₁)) 0) := by
    rw [PermData.denote_one]
    exact denotes_pairCoset_zero hφ (one_mem _) (by rw [show (⟨1, one_mem _⟩ :
      GensData.denote N₁ gs) = 1 from rfl, map_one, one_smul]) hsden
  -- the loop
  obtain ⟨res, hlrun, hat⟩ := RunsWithin.pairLoopProg (X := X) (body := body) hOst hPst hφ hal
    halm h5 (A' := A) (xy := xy) B hGG₀ Bk hsk hBg hsub (PermData.valid_one N₁) hsv hsgen hden₀
  have hnone := atRound_none_iff hat
  rw [hxy] at hnone
  have hne : pairCoset φ A A x x n ≠ ∅ := by
    rw [pairCoset_self]
    exact Set.nonempty_iff_ne_empty.1 ⟨1, (beardG φ A x n).one_mem⟩
  obtain ⟨Wl, ans⟩ := res
  rcases hans : ans with _ | c
  · exact absurd (hnone.1 hans) hne
  obtain ⟨τ, N₂, ks, e⟩ := c
  obtain ⟨hτ, hN₂, hKv, hKs, hKden, hWnd, hWmem⟩ := hat.2 _ hans
  change N₂ = N₁ at hN₂
  subst hN₂
  rw [hxy] at hKden
  obtain ⟨-, hKG, -, hKb⟩ := denotes_group hKden
  have hKtoStab := toStab_eq_beard hKden
  have hbeardH : beardH φ A x = (beard φ A x n).2 := by
    rw [beardH, hcard]
  have hbeardW : beardW φ A x = (beard φ A x n).1 := by
    rw [beardW, hcard]
  -- `K(A)`
  set comp := (List.range n).filter fun j => !Wl.any (· == j) with hcomp_def
  have hcomp : ∀ j, j ∈ comp ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∉ beardW φ A x := by
    intro j
    rw [hcomp_def, List.mem_filter, List.mem_range, hbeardW]
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    constructor
    · rintro ⟨hj, hnot⟩
      exact ⟨hj, fun hW => hnot j ((hWmem j).2 ⟨hj, hW⟩) rfl⟩
    · rintro ⟨hj, hnot⟩
      exact ⟨hj, fun y hy e => hnot (by obtain ⟨_, h⟩ := (hWmem y).1 hy; subst e; exact h)⟩
  have hcompN : ∀ u ∈ comp, u < N₂ := fun u hu => by
    obtain ⟨hu', -⟩ := (hcomp u).1 hu
    omega
  have hWlen : Wl.length ≤ n := length_le_of_lt hWnd fun j hj => ((hWmem j).1 hj).1
  have hcomplen : comp.length ≤ n := by
    rw [hcomp_def]
    exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨hirun, hiN, hiv, hiden⟩ := RunsWithin.iterStabProg (X := X) (body := body) hOs hPs hKv
    hcompN B hKs (hKG.trans hGG₀)
  have higen := iterStab_gens_le (X := X) hOs B comp (N₂, ks, e) hcompN rfl hKv hKs
    (hKG.trans hGG₀)
  rcases hKA : iterStabModel X.O (N₂, ks, e) comp with ⟨N₃, kas, ka⟩
  rw [hKA] at hirun hiN hiv hiden higen
  change N₃ = N₂ at hiN
  subst hiN
  have hKAtoStab : toStab φ A (GensData.denote N₃ kas) = certK φ A x := by
    rw [hiden, toStab_pointwiseStab_compl hcomp, hKtoStab, ← hbeardH, certK]
  have hKAstabs : StabsA hC al (GensData.denote N₃ kas) := by
    refine ⟨fun g hg => hKG (by rw [hiden] at hg; exact hg.1), fun g hg => ?_⟩
    rw [hiden] at hg
    obtain ⟨t, -, ht⟩ := (hKb g).1 hg.1
    rw [← mem_stabA_strR hφ, ← ht]
    exact t.2
  -- exact preimages
  have hKden' : Denotes hC (GensData.denote N₃ ks : Set (Perm (Fin N₃)))
      ((beardH φ A x).map (stabA φ A).subtype) :=
    denotes_toStab hKG (fun g hg => by obtain ⟨t, -, ht⟩ := (hKb g).1 hg; rw [← ht]; exact t.2)
      (by rw [hKtoStab, hbeardH])
  have hKAden : Denotes hC (GensData.denote N₃ kas : Set (Perm (Fin N₃)))
      ((certK φ A x).map (stabA φ A).subtype) :=
    denotes_toStab hKAstabs.1 (fun g hg => (mem_stabA_strR hφ g).2 (hKAstabs.2 g hg)) hKAtoStab
  -- the fullness test
  obtain ⟨hgrun, hgiff⟩ := RunsWithin.giantAProg (X := X) (body := body) hOg hPg
    (winA_valid hal halm) hiv.1 (isInvariant_winA hKAstabs) Bk (higen.trans hsk)
  have hgiff' := giantAModel_iff hφ hal halm hKAstabs hgiff
  rw [hKAtoStab] at hgiff'
  replace hgrun := hgrun.mono ((le_of_eq (congrArg (fun k => giantACost k kas.length Bk.Bgen
    Bk.Borb Bk.Bstab) (length_winA al))).trans (giantACost_mono higen _ _ _))
  refine ⟨some (Wl, (N₃, ks, e), (N₃, kas, ka),
    giantAModel X.O (WinData.pos N₃ (winA N₃ n al)) (winA N₃ n al).1 kas), ?_,
    Wl, (N₃, ks, e), (N₃, kas, ka), _, rfl, higen⟩
  apply RunsWithin.mono
  case h =>
    unfold CertProg.certProg
    run_step hsrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permOne _)
    run_step hlrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    rw [hans]
    run_with RunsWithin.caseOption_some _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.complProg n Wl)
    run_step hirun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hgrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    have h1 : Wl.length * 3 ≤ n * 3 := by omega
    have h2 : n * (3 * Wl.length + 6) ≤ n * (3 * n + 6) := Nat.mul_le_mul_left _ (by omega)
    have h3 : comp.length * (B.Bstab + 2) ≤ n * (B.Bstab + 2) := Nat.mul_le_mul_right _ hcomplen
    simp only [Prim.cost, Prim.eval, certCost]
    omega

/-- **One step of the aggregation**: the certificate of a `k`-subset, joined if it passes. -/
theorem ag_fullStep (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (x : StrData) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk : BackendBounds X DV k sk ⊤)
    (hsk : s ≤ k * (sk + 1)) {Bgen Bl Bgs BF : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al ∈ ksubsD (N - n) k, ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * s →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ BF)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (x, x) n k s) (fun _ => Cb) s)
    {done : List (List ℕ)} {Fc : GroupData D.denote}
    (hinv : AggInv DV hC φ (strOn hC.le (x.denote N)) s done Fc) {al : List ℕ}
    (hal : al ∈ ksubsD (N - n) k) :
    ∃ Fc', RunsWithin X body (Giant.fullStep sub n N (x, x) (N, gs, d) Fc al) Fc'
        (fullStepCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl Bgs BF) ∧
      AggInv DV hC φ (strOn hC.le (x.denote N)) s (done ++ [al]) Fc' := by
  obtain ⟨hpw, hlen, hlt⟩ := mem_ksubsD.1 hal
  have hnd : al.Nodup := hpw.imp ne_of_lt
  subst hlen
  have hwl : al.length = (winA N n al).1.length := (length_winA al).symm
  obtain ⟨e1, e2, e3⟩ := ag_cast_bounds hwl Bk
  have hsk' : s ≤ (winA N n al).1.length * (sk + 1) := by rw [← hwl]; exact hsk
  obtain ⟨res, hrun, Wl, K, KA, full, hres, -, -, -, -, -, -, -, hKAv, -, hKAden, hfull⟩ :=
    RunsWithin.certProg (X := X) (body := body) hO hPre hφ hGv hgiant hnd hlt h5 hk
      (xy := (x, x)) rfl B hs hGG₀ (hwl ▸ Bk) hsk' hBg hBl (hBgs al hal) hsub
  obtain ⟨res', hrun', Wl', K', KA', full', hres', hKAlen'⟩ :=
    ag_certProg_gens (X := X) (body := body) hO hPre hφ hGv hgiant hnd hlt h5 hk
      (xy := (x, x)) rfl B hs hGG₀ (hwl ▸ Bk) hsk' hBg hBl (hBgs al hal) hsub
  have hKAlen : KA.2.1.length ≤ s := by
    obtain ⟨tr, hr, -, -⟩ := hrun
    have e := RunsWithin.unique hrun' hr
    rw [hres', hres] at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.2.2.1]
    exact hKAlen'
  rw [e1, e2, e3] at hrun
  subst hres
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat) (xs := al)
    (f := fun a => Giant.agAddProg n a) (F := fun a => n + a) (c := 1)
    fun a _ => RunsWithin.agAddProg n a
  have hpos : RunsWithin X body (Programs.posProg N (al.map fun a => n + a))
      (WinData.pos N (winA N n al)) (2 * N + 9 * al.length + 8) := by
    have := RunsWithin.posProg (X := X) (body := body) N (winA N n al)
    rw [length_winA] at this
    exact this
  obtain ⟨hFN, hFv, hFlen, hFden⟩ := hinv
  have hKAden' := ag_denotes_iff.1 hKAden
  have hterm_le : agPre hC (agPart φ (strOn hC.le (x.denote N)) done) ≤ GensData.denote N gs :=
    agPre_le _
  rcases full with _ | _
  · -- the test fails: nothing is joined
    have hng : ¬ IsGiantOn φ (finsetOf (N - n) al)
        (certK φ (finsetOf (N - n) al) (strOn hC.le (x.denote N))) := fun h =>
      Bool.false_ne_true (hfull.2 h)
    refine ⟨Fc, ?_, hFN, hFv, hFlen, ?_⟩
    · apply RunsWithin.mono
      case h =>
        unfold Giant.fullStep
        run_step hmap
        run_step hpos
        run_step hrun
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_false (RunsWithin.ret _)
      case hc =>
        simp only [Prim.cost, fullStepCost]
        omega
    · rw [hFden, agPart_append_single, agTerm, iSup_neg hng, sup_bot_eq]
  · -- the test passes: join `K(A)`
    have hg : IsGiantOn φ (finsetOf (N - n) al)
        (certK φ (finsetOf (N - n) al) (strOn hC.le (x.denote N))) := hfull.1 rfl
    have hv : GensData.AllValid N (Fc.2.1 ++ KA.2.1) := by
      intro g hg'
      rcases List.mem_append.1 hg' with h | h
      · exact hFv.1 g h
      · exact hKAv.1 g h
    have hle : GensData.denote N (Fc.2.1 ++ KA.2.1) ≤ GensData.denote N gs := by
      rw [GensData.denote_append, hFden, hKAden']
      exact sup_le (agPre_le _) (agPre_le _)
    have hpost := hO .generate (N, Fc.2.1 ++ KA.2.1) (by simp [certOps]) hv
    have hgl := B.genOut _ hv (hle.trans hGG₀)
    have hjoin := RunsWithin.agJoinProg (X := X) (body := body) hPre N Fc KA true hv
    have hBFj := hBF _ hv (by rw [List.length_append]; omega) hle
    rcases hR : X.O.run GroupOp.generate (N, Fc.2.1 ++ KA.2.1) with ⟨N', fs', e'⟩
    rw [hR] at hpost hgl hjoin hBFj
    obtain ⟨hN', hv', hden'⟩ := hpost
    refine ⟨(N', fs', e'), ?_, hN', hv', hgl, ?_⟩
    · apply RunsWithin.mono
      case h =>
        unfold Giant.fullStep
        run_step hmap
        run_step hpos
        run_step hrun
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_true hjoin
      case hc =>
        simp only [Prim.cost, fullStepCost]
        omega
    · rw [hden', GensData.denote_append, hFden, hKAden', agPart_append_single, agTerm,
        iSup_pos hg, agPre_sup]

/-- **The full group.** For a giant base action, test sets of size `k` (`5 ≤ k`, `2 k ≤ m`,
`k + 2 ≤ m`) and the sub-solver hypothesis of `certProg`: the program generates a valid group
with at most `s` generators whose elements are exactly the preimages in `G` of
`fullGroupK φ k x`, the group generated by the certificates `K(A)` of the `k`-subsets passing
the test `Alt(A) ≤ ψ_A(K(A))`. -/
theorem RunsWithin.fullProg (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n) (h2k : 2 * k ≤ N - n) (x : StrData) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk : BackendBounds X DV k sk ⊤)
    (hsk : s ≤ k * (sk + 1)) {Bgen Bl Bgs BF : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al ∈ ksubsD (N - n) k, ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    (hBF : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 2 * s →
      GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ BF)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (x, x) n k s) (fun _ => Cb) s) :
    ∃ F : GroupData D.denote,
      RunsWithin X body (Giant.fullProg sub n N k x (N, gs, d)) F
        (fullCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl Bgs BF) ∧
      F.1 = N ∧ GroupValid DV N F.2.1 F.2.2 ∧ F.2.1.length ≤ s ∧
      Denotes hC (GensData.denote N F.2.1 : Set (Perm (Fin N)))
        (fullGroupK φ k (strOn hC.le (x.denote N)) : Set (strGroup hC)) := by
  set xs := strOn hC.le (x.denote N) with hxs
  have hgenOp : certOps .generate := by simp [certOps]
  -- the first group
  have hv0 : GensData.AllValid N ([] : GensData) := fun g hg => absurd hg List.not_mem_nil
  have hpost0 := hO .generate (N, ([] : GensData)) hgenOp hv0
  rcases hF0 : X.O.run GroupOp.generate (N, ([] : GensData)) with ⟨N₀, fs₀, e₀⟩
  rw [hF0] at hpost0
  obtain ⟨hN₀, hv₀, hden₀⟩ := hpost0
  have hlen₀ : fs₀.length ≤ s := by
    have := B.genOut [] hv0 (by simp)
    rw [hF0] at this
    exact this
  have hinv₀ : AggInv DV hC φ xs s [] (N₀, fs₀, e₀) :=
    ⟨hN₀, hv₀, hlen₀, by rw [hden₀, GensData.denote_nil]; exact agPre_bot.symm⟩
  have hBF0 : X.B.call GroupOp.generate (N, ([] : GensData))
      (X.O.run GroupOp.generate (N, ([] : GensData))) ≤ BF := hBF [] hv0 (by simp) (by simp)
  rw [hF0] at hBF0
  have hcall : RunsWithin X body (Prog.call (S := groupSig D) GroupOp.generate (N, ([] : GensData)))
      (N₀, fs₀, e₀) BF := by
    have := RunsWithin.call (X := X) (body := body) (op := GroupOp.generate)
      (x := (N, ([] : GensData))) (hPre _ _ hgenOp hv0)
    rw [hF0] at this
    exact this.mono hBF0
  obtain ⟨F, hfold, hinvF⟩ := ag_fold_exists (X := X) (body := body) (a' := .list .nat)
    (b' := Ty.group D) (P := AggInv DV hC φ xs s)
    (f := fun Fc al => Giant.fullStep sub n N (x, x) (N, gs, d) Fc al)
    (c := fullStepCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl Bgs BF)
    (ksubsD (N - n) k) [] (N₀, fs₀, e₀) hinv₀
    fun done acc al hal hP => ag_fullStep hO hPre hφ hGv hgiant h5 hk x B hs hGG₀ Bk hsk hBg
      hBl hBgs hBF hsub hP hal
  rw [List.nil_append] at hinvF
  obtain ⟨hFN, hFv, hFlen, hFden⟩ := hinvF
  refine ⟨F, ?_, hFN, hFv, hFlen, ag_denotes_iff.2 (by rw [hFden, agPart_ksubsD])⟩
  apply RunsWithin.mono
  case h =>
    unfold Giant.fullProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step (RunsWithin.ksubsProg h2k)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step hcall
    exact hfold
  case hc =>
    simp only [Prim.cost, fullCost, length_ksubsD]
    omega

end FullSpec

/-! ### The charges for the Schreier–Sims backend -/

section SimsCharges

open GraphIso.Sims

/-- **The charge premises of `RunsWithin.fullProg` hold for the Schreier–Sims backend**, with
explicit values: `genCost N (2 s) + 2` for every join of at most `2 s` generators (`hBF`), and
`genCost N (k + N²) + 2` for the setwise stabilizers of the enumerated `k`-subsets (`hBgs`),
for a group with at most `N²` generators (as `ssBounds` keeps them). -/
theorem ag_ss_charges {N n k s : ℕ} {gs : GensData} (hgv : GensData.AllValid N gs)
    (hs : gs.length ≤ N * N) :
    (∀ gs' : GensData, gs'.length ≤ 2 * s →
      ssCtx.B.call GroupOp.generate (N, gs') (ssCtx.O.run GroupOp.generate (N, gs')) ≤
        genCost N (2 * s) + 2) ∧
    (∀ al ∈ ksubsD (N - n) k, ∀ b₁ b₂,
      ssCtx.B.call GroupOp.generate (N, giantGens ssCtx.O n (N, gs, ()) al b₁ b₂)
        (giantSetStabModel ssCtx.O n (N, gs, ()) al b₁ b₂) ≤ genCost N (k + N * N) + 2) := by
  refine ⟨fun gs' h => ?_, fun al hal b₁ b₂ => ?_⟩
  · change genCost N gs'.length + 2 ≤ genCost N (2 * s) + 2
    exact Nat.add_le_add_right (genCost_mono h) 2
  · change genCost N (giantGens ssCtx.O n (N, gs, ()) al b₁ b₂).length + 2 ≤
      genCost N (k + N * N) + 2
    refine Nat.add_le_add_right (genCost_mono ?_) 2
    obtain ⟨-, hlen, hlt⟩ := mem_ksubsD.1 hal
    have hps : ∀ u ∈ al.map (n + ·), u < N := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
      have := hlt x hx
      omega
    have hit := iterStab_gens_le (X := ssCtx) (DV := ssDV) (fun op y _ hy => ssOracle_meets op y hy)
      (ssBounds N ⊤) (al.map (n + ·)) (N, gs, ()) hps rfl ⟨hgv, trivial⟩ hs le_top
    have hlift : (giantLifts ssCtx.O n (N, gs, ()) b₁ b₂ al).length ≤ k := by
      rcases al with _ | ⟨a₀, rest⟩
      · simp [giantLifts]
      · simp only [giantLifts, List.length_map]
        simp only [List.length_cons] at hlen
        omega
    rw [giantGens, List.length_append]
    omega

end SimsCharges

/-! ### The case decision -/

section CaseData

/-- The first listed orbit of more than `m/2` points. -/
def agFindD (m : ℕ) (bos : List (List ℕ)) : Option (List ℕ) :=
  bos.foldl (fun acc o => match acc with
    | none => if m < o.length + o.length then some o else none
    | some v => some v) none

/-- The number of points in orbits of more than one point. -/
def agSuppD (bos : List (List ℕ)) : ℕ :=
  bos.foldl (fun acc o => if 1 < o.length then acc + o.length else acc) 0

/-- **The case**: `2` with the orbit `Φ` of more than `m/2` points if there is one; otherwise
`3` if the support has fewer than `m/2` points, `1` if not. -/
def caseD (m : ℕ) (bos : List (List ℕ)) : ℕ × List ℕ :=
  match agFindD m bos with
  | some o => (2, o)
  | none => if agSuppD bos + agSuppD bos < m then (3, []) else (1, [])

theorem ag_foldFind {m : ℕ} : ∀ (bos : List (List ℕ)) (init : Option (List ℕ)),
    (∀ o, bos.foldl (fun acc o => match acc with
        | none => if m < o.length + o.length then some o else none
        | some v => some v) init = some o →
      init = some o ∨ (o ∈ bos ∧ m < o.length + o.length)) ∧
    (bos.foldl (fun acc o => match acc with
        | none => if m < o.length + o.length then some o else none
        | some v => some v) init = none →
      init = none ∧ ∀ o ∈ bos, ¬ m < o.length + o.length)
  | [], init => ⟨fun o h => Or.inl h, fun h => ⟨h, fun _ h' => absurd h' List.not_mem_nil⟩⟩
  | o :: bos, init => by
    obtain ⟨h1, h2⟩ := ag_foldFind bos (match init with
      | none => if m < o.length + o.length then some o else none
      | some v => some v)
    simp only [List.foldl_cons]
    refine ⟨fun o' h => ?_, fun h => ?_⟩
    · rcases h1 o' h with h | h
      · rcases init with _ | v
        · simp only at h
          split_ifs at h with hb
          · cases h
            exact Or.inr ⟨List.mem_cons_self, hb⟩
        · exact Or.inl h
      · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩
    · obtain ⟨hi, hall⟩ := h2 h
      rcases init with _ | v
      · simp only at hi
        split_ifs at hi with hb
        refine ⟨rfl, fun o' ho' => ?_⟩
        rcases List.mem_cons.1 ho' with rfl | ho'
        · exact hb
        · exact hall o' ho'
      · simp at hi

theorem agFindD_some {m : ℕ} {bos : List (List ℕ)} {o : List ℕ} (h : agFindD m bos = some o) :
    o ∈ bos ∧ m < o.length + o.length := by
  rcases (ag_foldFind bos none).1 o h with h' | h'
  · cases h'
  · exact h'

theorem agFindD_none {m : ℕ} {bos : List (List ℕ)} (h : agFindD m bos = none) :
    ∀ o ∈ bos, ¬ m < o.length + o.length :=
  ((ag_foldFind bos none).2 h).2

theorem ag_foldSupp : ∀ (bos : List (List ℕ)) (acc : ℕ),
    bos.foldl (fun acc o => if 1 < o.length then acc + o.length else acc) acc =
      acc + ((bos.filter fun o => decide (1 < o.length)).map List.length).sum
  | [], acc => by simp
  | o :: bos, acc => by
    rw [List.foldl_cons, ag_foldSupp bos, List.filter_cons]
    by_cases h : 1 < o.length
    · simp only [h, ↓reduceIte, decide_true, List.map_cons, List.sum_cons]
      omega
    · simp [h]

theorem agSuppD_eq (bos : List (List ℕ)) :
    agSuppD bos = ((bos.filter fun o => decide (1 < o.length)).map List.length).sum := by
  rw [agSuppD, ag_foldSupp, Nat.zero_add]

end CaseData

section CaseSemantics

variable {N n : ℕ} {F : Subgroup (Perm (Fin N))} (hF : IsInvariant F (baseSet n N))

/-- **Orbits of the base action** are orbits of base positions. -/
theorem ag_mem_orbit_iff (γ δ : Fin (N - n)) :
    δ ∈ orbit (baseHom F n hF).range γ ↔ SameOrbit F (n + γ.val) (n + δ.val) := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨p, ⟨g, rfl⟩⟩, hp⟩
    have hp' : baseHom F n hF g γ = δ := hp
    refine ⟨by omega, by omega, g.1, g.2, ?_⟩
    have := baseHom_apply (hG := hF) g γ
    rw [hp'] at this
    exact this.symm
  · rintro ⟨hi, hj, g, hg, e⟩
    refine ⟨⟨baseHom F n hF ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩, ?_⟩
    show baseHom F n hF ⟨g, hg⟩ γ = δ
    have := baseHom_apply (hG := hF) ⟨g, hg⟩ γ
    have h2 : basePos (n := n) (baseHom F n hF ⟨g, hg⟩ γ) = basePos δ := by
      rw [this]
      exact e
    apply Fin.ext
    have := congrArg Fin.val h2
    simp only [basePos] at this
    omega

variable {os : List (List ℕ)} (hos : IsOrbitPartition F (baseWin n N) os)

include hos in
theorem ag_os_range {o : List ℕ} (ho : o ∈ os) {u : ℕ} (hu : u ∈ o) : n ≤ u ∧ u < N := by
  have : u ∈ os.flatten := List.mem_flatten.2 ⟨o, ho, hu⟩
  rw [hos.1.mem_iff] at this
  exact mem_basePts.1 this

include hos in
theorem ag_os_flatten_nodup : os.flatten.Nodup :=
  hos.1.nodup_iff.2 (basePts_nodup n N)

/-- The orbits as lists of base indices. -/
def agShiftD (n : ℕ) (os : List (List ℕ)) : List (List ℕ) := os.map fun o => o.map (· - n)

include hos in
theorem ag_bos_flatten : (agShiftD n os).flatten.Perm (List.range (N - n)) := by
  have h1 : (agShiftD n os).flatten = os.flatten.map (· - n) := by
    simp [agShiftD, List.map_flatten]
  have h2 : (basePts n N).map (· - n) = List.range (N - n) := by
    simp [basePts, List.map_map, Function.comp_def]
  rw [h1, ← h2]
  exact hos.1.map _

include hos in
theorem ag_bos_nodup {o' : List ℕ} (ho : o' ∈ agShiftD n os) :
    o'.Nodup ∧ ∀ i ∈ o', i < N - n := by
  obtain ⟨o, hoo, rfl⟩ := List.mem_map.1 ho
  have hnd : o.Nodup := (List.nodup_flatten.1 (ag_os_flatten_nodup hos)).1 o hoo
  refine ⟨hnd.map_on fun u hu v hv e => ?_, fun i hi => ?_⟩
  · have := ag_os_range hos hoo hu
    have := ag_os_range hos hoo hv
    omega
  · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hi
    have := ag_os_range hos hoo hu
    omega

include hos in
/-- **Each listed orbit is the orbit of each of its points.** -/
theorem ag_bos_orbit {o' : List ℕ} (ho : o' ∈ agShiftD n os) {γ : Fin (N - n)}
    (hγ : γ.val ∈ o') (δ : Fin (N - n)) : δ.val ∈ o' ↔ δ ∈ orbit (baseHom F n hF).range γ := by
  obtain ⟨o, hoo, rfl⟩ := List.mem_map.1 ho
  have hmem : ∀ i : Fin (N - n), i.val ∈ o.map (· - n) ↔ n + i.val ∈ o := by
    intro i
    constructor
    · intro hi
      obtain ⟨u, hu, e⟩ := List.mem_map.1 hi
      have := ag_os_range hos hoo hu
      rw [show n + i.val = u by omega]
      exact hu
    · intro hi
      exact List.mem_map.2 ⟨n + i.val, hi, by simp⟩
  rw [hmem, ag_mem_orbit_iff hF]
  exact (hos.2 o hoo).2 _ ((hmem γ).1 hγ) _

include hos in
theorem ag_bos_cover (γ : Fin (N - n)) : ∃ o' ∈ agShiftD n os, γ.val ∈ o' := by
  have : γ.val ∈ (agShiftD n os).flatten := by
    rw [(ag_bos_flatten hos).mem_iff, List.mem_range]
    exact γ.2
  exact List.mem_flatten.1 this

include hos in
/-- **The size of an orbit** is the length of its list. -/
theorem ag_card_orbit {o' : List ℕ} (ho : o' ∈ agShiftD n os) {γ : Fin (N - n)}
    (hγ : γ.val ∈ o') : Nat.card (orbit (baseHom F n hF).range γ) = o'.length := by
  obtain ⟨hnd, hlt⟩ := ag_bos_nodup hos ho
  have hset : orbit (baseHom F n hF).range γ = ((finsetOf (N - n) o' : Finset _) : Set _) := by
    ext δ
    rw [Finset.mem_coe, mem_finsetOf, ag_bos_orbit hF hos ho hγ]
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, card_finsetOf hnd hlt]

include hos in
/-- **The support**: the points in orbits of more than one point number `agSuppD`. -/
theorem ag_card_supp :
    Nat.card {γ : Fin (N - n) // 1 < Nat.card (orbit (baseHom F n hF).range γ)} =
      agSuppD (agShiftD n os) := by
  set bos := agShiftD n os
  set L := (bos.filter fun o => decide (1 < o.length)).flatten with hL
  have hnd : L.Nodup := by
    have hflat := (ag_bos_flatten hos).nodup_iff.2 (List.nodup_range)
    rw [List.nodup_flatten] at hflat ⊢
    exact ⟨fun l hl => hflat.1 l (List.mem_filter.1 hl).1, hflat.2.filter _⟩
  have hmem : ∀ i, i ∈ L ↔ ∃ h : i < N - n,
      1 < Nat.card (orbit (baseHom F n hF).range (⟨i, h⟩ : Fin (N - n))) := by
    intro i
    rw [hL, List.mem_flatten]
    constructor
    · rintro ⟨o', ho', hi⟩
      rw [List.mem_filter, decide_eq_true_eq] at ho'
      have hlt := (ag_bos_nodup hos ho'.1).2 i hi
      refine ⟨hlt, ?_⟩
      rw [ag_card_orbit hF hos ho'.1 (γ := ⟨i, hlt⟩) hi]
      exact ho'.2
    · rintro ⟨h, hc⟩
      obtain ⟨o', ho', hi⟩ := ag_bos_cover hos (⟨i, h⟩ : Fin (N - n))
      refine ⟨o', List.mem_filter.2 ⟨ho', ?_⟩, hi⟩
      rw [ag_card_orbit hF hos ho' (γ := ⟨i, h⟩) hi] at hc
      exact decide_eq_true hc
  have hlen : L.length = agSuppD bos := by
    rw [hL, List.length_flatten, agSuppD_eq]
  rw [← hlen, ← List.toFinset_card_of_nodup hnd, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, List.mem_toFinset, hmem]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ.2, hγ⟩
  · rintro ⟨h, hc⟩
    exact ⟨⟨i, h⟩, hc, rfl⟩

include hos in
/-- **The case decision.** -/
theorem caseD_spec :
    ((caseD (N - n) (agShiftD n os)).1 = 2 ↔
        ∃ γ : Fin (N - n), N - n < 2 * Nat.card (orbit (baseHom F n hF).range γ)) ∧
      ((caseD (N - n) (agShiftD n os)).1 = 2 →
        (caseD (N - n) (agShiftD n os)).2.Nodup ∧
        (∀ i ∈ (caseD (N - n) (agShiftD n os)).2, i < N - n) ∧
        N - n < 2 * (caseD (N - n) (agShiftD n os)).2.length ∧
        ∃ γ : Fin (N - n), γ.val ∈ (caseD (N - n) (agShiftD n os)).2 ∧
          ∀ δ : Fin (N - n), δ.val ∈ (caseD (N - n) (agShiftD n os)).2 ↔
            δ ∈ orbit (baseHom F n hF).range γ) ∧
      ((caseD (N - n) (agShiftD n os)).1 = 1 ↔
        (∀ γ : Fin (N - n), 2 * Nat.card (orbit (baseHom F n hF).range γ) ≤ N - n) ∧
          N - n ≤ 2 * Nat.card {γ : Fin (N - n) // 1 < Nat.card (orbit (baseHom F n hF).range γ)})
      ∧
      ((caseD (N - n) (agShiftD n os)).1 = 3 ↔
        (∀ γ : Fin (N - n), 2 * Nat.card (orbit (baseHom F n hF).range γ) ≤ N - n) ∧
          2 * Nat.card {γ : Fin (N - n) // 1 < Nat.card (orbit (baseHom F n hF).range γ)} <
            N - n) := by
  rw [ag_card_supp hF hos]
  unfold caseD
  rcases hf : agFindD (N - n) (agShiftD n os) with _ | o
  · have hall := agFindD_none hf
    have hsmall : ∀ γ : Fin (N - n), 2 * Nat.card (orbit (baseHom F n hF).range γ) ≤ N - n := by
      intro γ
      obtain ⟨o', ho', hγ⟩ := ag_bos_cover hos γ
      rw [ag_card_orbit hF hos ho' hγ]
      have := hall o' ho'
      omega
    refine ⟨⟨fun h => ?_, fun ⟨γ, hγ⟩ => absurd (hsmall γ) (by omega)⟩, fun h => ?_, ?_, ?_⟩
    · split_ifs at h <;> simp at h
    · split_ifs at h <;> simp at h
    · split_ifs with hs
      · exact ⟨fun h => absurd h (by decide), fun ⟨_, h⟩ => by omega⟩
      · exact ⟨fun _ => ⟨hsmall, by omega⟩, fun _ => rfl⟩
    · split_ifs with hs
      · exact ⟨fun _ => ⟨hsmall, by omega⟩, fun _ => rfl⟩
      · exact ⟨fun h => absurd h (by decide), fun ⟨_, h⟩ => by omega⟩
  · obtain ⟨ho, hbig⟩ := agFindD_some hf
    obtain ⟨hnd, hlt⟩ := ag_bos_nodup hos ho
    obtain ⟨i, hi⟩ : ∃ i, i ∈ o := by
      rcases o with _ | ⟨i, _⟩
      · simp at hbig
      · exact ⟨i, List.mem_cons_self⟩
    set γ : Fin (N - n) := ⟨i, hlt i hi⟩
    have hγ : γ.val ∈ o := hi
    have hcard := ag_card_orbit hF hos ho hγ
    dsimp only
    refine ⟨⟨fun _ => ⟨γ, by rw [hcard]; omega⟩, fun _ => rfl⟩, fun _ =>
      ⟨hnd, hlt, by omega, γ, hγ, ag_bos_orbit hF hos ho hγ⟩,
      ⟨fun h => absurd h (by decide), fun ⟨h, _⟩ => ?_⟩,
      ⟨fun h => absurd h (by decide), fun ⟨h, _⟩ => ?_⟩⟩
    · have := h γ
      rw [hcard] at this
      omega
    · have := h γ
      rw [hcard] at this
      omega

end CaseSemantics

/-! #### The case decision as a program -/

section CaseProgram

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- `u - n`. -/
def agSubProg {S : Signature} (n u : var .nat) : Prog S rec var .nat := .op2 .sub u n

/-- An orbit's positions as base indices. -/
def agShiftProg {S : Signature} (n : var .nat) (o : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  mapList o fun u => agSubProg n u

/-- One step of the search for an orbit of more than `m/2` points. -/
def agFindStep {S : Signature} (m : var .nat) (acc : var (.option (.list .nat)))
    (o : var (.list .nat)) : Prog S rec var (.option (.list .nat)) :=
  .caseOption acc
    (.bind (.op1 .length o) fun l => .bind (.op2 .add l l) fun l2 =>
      .bind (.op2 .natLt m l2) fun big => .ite big (.op1 .some o) (.op0 .none))
    fun _ => .ret acc

/-- One step of the count of the support. -/
def agSuppStep {S : Signature} (acc : var .nat) (o : var (.list .nat)) : Prog S rec var .nat :=
  .bind (.op1 .length o) fun l => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natLt one l) fun mv => .ite mv (.op2 .add acc l) (.ret acc)

/-- The case decision on the orbits (`caseD`). -/
def caseDecProg {S : Signature} (m : var .nat) (bos : var (.list (.list .nat))) :
    Prog S rec var (.prod .nat (.list .nat)) :=
  .bind (.op0 .none) fun nn =>
  .bind (.foldList bos nn fun acc o => agFindStep m acc o) fun fo =>
  .caseOption fo
    (.bind (.op0 (.natLit 0)) fun z =>
      .bind (.foldList bos z fun acc o => agSuppStep acc o) fun sp =>
      .bind (.op2 .add sp sp) fun sp2 => .bind (.op2 .natLt sp2 m) fun small =>
      .bind (.op0 .nil) fun e =>
      .ite small (.bind (.op0 (.natLit 3)) fun three => .op2 .pair three e)
        (.bind (.op0 (.natLit 1)) fun one => .op2 .pair one e))
    fun o => .bind (.op0 (.natLit 2)) fun two => .op2 .pair two o

/-- **The case of the full group** `F`: its orbits on the base, as base indices, and the case
(`1`, `2` with the large orbit `Φ`, or `3`). -/
def caseProg (n N : var .nat) (F : var (Ty.group D)) :
    Prog (groupSig D) rec var (.prod (.prod .nat (.list .nat)) (.list (.list .nat))) :=
  .bind (baseWinProg n N) fun bw =>
  .bind (.op2 .pair F bw) fun a => .bind (Prog.call (S := groupSig D) GroupOp.orbits a) fun os =>
  .bind (mapList os fun o => agShiftProg n o) fun bos =>
  .bind (.op2 .sub N n) fun m =>
  .bind (caseDecProg m bos) fun cs => .op2 .pair cs bos

end CaseProgram

/-- The cost of `caseProg`. -/
def caseCost (n N Borb : ℕ) : ℕ := baseWinCost n N + Borb + 24 * (N - n) + 30

section CaseSpec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.agShiftProg (n : ℕ) (o : List ℕ) :
    RunsWithin X body (Giant.agShiftProg n o) (o.map (· - n)) (4 * o.length + 2) :=
  (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 1) (F := (· - n))
    fun u _ => RunsWithin.prim _ _).mono (by omega)

theorem RunsWithin.agFindStep (m : ℕ) (acc : Option (List ℕ)) (o : List ℕ) :
    RunsWithin X body (Giant.agFindStep m acc o)
      (match acc with
        | none => if m < o.length + o.length then some o else none
        | some v => some v) (o.length + 6) := by
  rcases acc with _ | v
  · by_cases hb : m < o.length + o.length
    · simp only [hb, ↓reduceIte]
      apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_none _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval, hb, decide_true]
        exact RunsWithin.ite_true (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost, Args.head]
        omega
    · simp only [hb, ↓reduceIte]
      apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_none _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval, hb, decide_false]
        exact RunsWithin.ite_false (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost, Args.head]
        omega
  · refine (RunsWithin.caseOption_some (k := 0)
      (RunsWithin.ret (t := .option (.list .nat)) (some v))).mono ?_
    omega

theorem RunsWithin.agSuppStep (acc : ℕ) (o : List ℕ) :
    RunsWithin X body (Giant.agSuppStep acc o)
      (if 1 < o.length then acc + o.length else acc) (o.length + 5) := by
  by_cases hb : 1 < o.length
  · simp only [hb, ↓reduceIte]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval, hb, decide_true]
      exact RunsWithin.ite_true (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost, Args.head]
      omega
  · simp only [hb, ↓reduceIte]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval, hb, decide_false]
      exact RunsWithin.ite_false (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost, Args.head]
      omega

theorem ag_sum_map_add (bos : List (List ℕ)) (c : ℕ) :
    (bos.map fun o => o.length + c).sum = (bos.map List.length).sum + bos.length * c := by
  induction bos with
  | nil => simp
  | cons o bos ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    ring

theorem RunsWithin.caseDecProg (m : ℕ) (bos : List (List ℕ)) :
    RunsWithin X body (Giant.caseDecProg m bos) (caseD m bos)
      (2 * (bos.map List.length).sum + 13 * bos.length + 20) := by
  have hfind : RunsWithin X body
      (Prog.foldList (a := .list .nat) (b := .option (.list .nat)) bos none
        fun acc o => Giant.agFindStep m acc o) (agFindD m bos)
      ((bos.map fun o => o.length + 6 + 1).sum) :=
    RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat)
      (b' := .option (.list .nat)) (f := fun acc o => Giant.agFindStep m acc o)
      (F := fun acc o => match acc with
        | none => if m < o.length + o.length then some o else none
        | some v => some v) (cf := fun o => o.length + 6) bos none
      fun acc o _ => RunsWithin.agFindStep m acc o
  have hsupp : RunsWithin X body
      (Prog.foldList (a := .list .nat) (b := .nat) bos 0 fun acc o => Giant.agSuppStep acc o)
      (agSuppD bos) ((bos.map fun o => o.length + 5 + 1).sum) :=
    RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat) (b' := .nat)
      (f := fun acc o => Giant.agSuppStep acc o)
      (F := fun acc o => if 1 < o.length then acc + o.length else acc)
      (cf := fun o => o.length + 5) bos 0 fun acc o _ => RunsWithin.agSuppStep acc o
  have e1 := ag_sum_map_add bos (6 + 1)
  have e2 := ag_sum_map_add bos (5 + 1)
  simp only [Nat.add_assoc] at e1 e2 hfind hsupp
  unfold caseD
  rcases hf : agFindD m bos with _ | o
  · rw [hf] at hfind
    by_cases hs : agSuppD bos + agSuppD bos < m
    · simp only [hs, ↓reduceIte]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step hfind
        run_with RunsWithin.caseOption_none _
        run_step (RunsWithin.prim _ _)
        run_step hsupp
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval, hs, decide_true]
        exact RunsWithin.ite_true (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.prim _ _))
      case hc =>
        simp only [Prim.cost]
        omega
    · simp only [hs, ↓reduceIte]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step hfind
        run_with RunsWithin.caseOption_none _
        run_step (RunsWithin.prim _ _)
        run_step hsupp
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval, hs, decide_false]
        exact RunsWithin.ite_false (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.prim _ _))
      case hc =>
        simp only [Prim.cost]
        omega
  · rw [hf] at hfind
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hfind
      run_with RunsWithin.caseOption_some _
      exact RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost]
      omega

end CaseSpec

theorem ag_sum_map_affine (L : List (List ℕ)) (p q : ℕ) :
    (L.map fun o => p * o.length + q).sum = p * (L.map List.length).sum + L.length * q := by
  induction L with
  | nil => simp
  | cons o L ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
    ring

theorem ag_length_le_sum : ∀ L : List (List ℕ), (∀ o ∈ L, o ≠ []) →
    L.length ≤ (L.map List.length).sum
  | [], _ => by simp
  | o :: L, h => by
    have := ag_length_le_sum L fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    have ho : o ≠ [] := h o List.mem_cons_self
    have : 1 ≤ o.length := List.length_pos_iff.2 ho
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

section CaseProgSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operation used by `caseProg`. -/
def caseOps (op : GroupOp) : Prop := op = .orbits

/-- **The case decision as a program.** For a valid group `F` preserving the base, the program
returns `caseD` of the backend's orbits on the base (as base indices) and those orbits, which
form the orbit partition of the base positions; `caseD_spec` gives the meaning of the case. -/
theorem RunsWithin.caseProg (hO : MeetsContractOn DV caseOps X.O)
    (hPre : ∀ op x, caseOps op → GroupPre DV op x → X.Pre op x) {N n : ℕ} {fs : GensData}
    {fd : D.denote} (hFv : GroupValid DV N fs fd)
    (hF : IsInvariant (GensData.denote N fs) (baseSet n N)) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : fs.length ≤ s)
    (hG₀ : GensData.denote N fs ≤ G₀) :
    RunsWithin X body (Giant.caseProg n N (N, fs, fd))
        (caseD (N - n) (agShiftD n (X.O.run GroupOp.orbits ((N, fs, fd), baseWin n N))),
          agShiftD n (X.O.run GroupOp.orbits ((N, fs, fd), baseWin n N)))
        (caseCost n N B.Borb) ∧
      IsOrbitPartition (GensData.denote N fs) (baseWin n N)
        (X.O.run GroupOp.orbits ((N, fs, fd), baseWin n N)) := by
  have hpre : GroupPre DV .orbits ((N, fs, fd), baseWin n N) :=
    ⟨hFv, baseWin_valid n N, by rw [baseWin_denote]; exact hF⟩
  have hos := hO .orbits _ rfl hpre
  have hB := B.orbits fs fd (baseWin n N) hs hG₀ hpre
  refine ⟨?_, hos⟩
  set os : List (List ℕ) := X.O.run GroupOp.orbits ((N, fs, fd), baseWin n N) with hos_def
  have hsum : (os.map List.length).sum = N - n := by
    rw [← List.length_flatten, hos.1.length_eq]
    exact length_basePts n N
  have hlen : os.length ≤ N - n := hsum ▸ ag_length_le_sum os fun o ho => (hos.2 o ho).1
  have hmap := RunsWithin.mapList (X := X) (body := body) (a' := .list .nat) (b' := .list .nat)
    (xs := os) (f := fun o => Giant.agShiftProg n o) (F := fun o => o.map (· - n))
    (cf := fun o => 4 * o.length + 2) fun o _ => RunsWithin.agShiftProg n o
  have e1 : (os.map fun o => 4 * o.length + 2 + 2).sum = 4 * (N - n) + os.length * 4 := by
    rw [← hsum, ← ag_sum_map_affine os 4 4]
  have hsum' : ((agShiftD n os).map List.length).sum = N - n := by
    simp only [agShiftD, List.map_map, Function.comp_def, List.length_map]
    exact hsum
  have hlen' : (agShiftD n os).length = os.length := by simp [agShiftD]
  apply RunsWithin.mono
  case h =>
    unfold Giant.caseProg
    run_step (RunsWithin.baseWinProg n N)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step (RunsWithin.call (hPre _ _ rfl hpre))
    run_step hmap
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    run_step (RunsWithin.caseDecProg (N - n) (os.map fun o => o.map (· - n)))
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, caseCost]
    have : (os.map fun o => o.map (· - n)) = agShiftD n os := rfl
    rw [this, hsum', hlen', e1]
    have hB' : X.B.call GroupOp.orbits ((N, fs, fd), baseWin n N)
        (X.O.run GroupOp.orbits ((N, fs, fd), baseWin n N)) ≤ B.Borb := hB
    omega

end CaseProgSpec

/-! ### The meaning of the orbits and of the support for `φ` -/

section PhiBridge

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **The base action of a group denoting `C` is `φ(C)`.** -/
theorem ag_range_eq (hφ : IsPhi hC φ) {F : Subgroup (Perm (Fin N))} {C : Subgroup (strGroup hC)}
    (hden : Denotes hC (F : Set (Perm (Fin N))) (C : Set (strGroup hC)))
    (hF : IsInvariant F (baseSet n N)) : (baseHom F n hF).range = C.map φ := by
  have hbase : ∀ (g : Perm (Fin N)) (hgF : g ∈ F) (hgG : g ∈ G),
      baseHom F n hF ⟨g, hgF⟩ = baseHom G n hC.base ⟨g, hgG⟩ := fun g _ _ => rfl
  ext p
  simp only [MonoidHom.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨g, hgF⟩, rfl⟩
    obtain ⟨hgG, hgC⟩ := (hden g).1 hgF
    exact ⟨strR hC ⟨g, hgG⟩, hgC, by rw [hφ, hbase g hgF hgG]⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨⟨g, hgG⟩, rfl⟩ := strR_surjective hC c
    have hgF : g ∈ F := (hden g).2 ⟨hgG, hc⟩
    exact ⟨⟨g, hgF⟩, by rw [hφ, hbase g hgF hgG]⟩

/-- **The support**: a point is moved by `C` exactly when its orbit under `φ(C)` has more than
one point. -/
theorem ag_mem_supp_iff (C : Subgroup (strGroup hC)) (γ : Fin (N - n)) :
    γ ∈ supp φ C ↔ 1 < Nat.card (orbit (C.map φ) γ) := by
  rw [Nat.card_coe_set_eq, Set.one_lt_ncard_iff (Set.toFinite _)]
  constructor
  · rintro ⟨g, hg, hne⟩
    refine ⟨γ, φ g γ, MulAction.mem_orbit_self γ, ?_, hne.symm⟩
    exact MulAction.mem_orbit_iff.2 ⟨⟨φ g, Subgroup.mem_map_of_mem φ hg⟩, rfl⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    obtain ⟨⟨p, hp⟩, rfl⟩ := MulAction.mem_orbit_iff.1 hu
    obtain ⟨⟨q, hq⟩, rfl⟩ := MulAction.mem_orbit_iff.1 hv
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hp
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hq
    by_cases hgγ : φ g γ = γ
    · refine ⟨h, hh, fun e => huv ?_⟩
      show φ g γ = φ h γ
      rw [hgγ, e]
    · exact ⟨g, hg, hgγ⟩

end PhiBridge

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_agLessProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {p₁ : var₁ agPartTy} {p₂ : var₂ agPartTy}
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hp : ⟨agPartTy, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agLessProg k₁ p₁) (agLessProg k₂ p₂) := by
  unfold agLessProg
  prog_wf

theorem wf_agGrowProg {j₁ : var₁ .nat} {j₂ : var₂ .nat} {p₁ : var₁ agPartTy} {p₂ : var₂ agPartTy}
    (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) (hp : ⟨agPartTy, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agGrowProg j₁ p₁) (agGrowProg j₂ p₂) := by
  unfold agGrowProg
  prog_wf

theorem wf_agIsKProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {p₁ : var₁ agPartTy} {p₂ : var₂ agPartTy}
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hp : ⟨agPartTy, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agIsKProg k₁ p₁) (agIsKProg k₂ p₂) := by
  unfold agIsKProg
  prog_wf

theorem wf_agRevProg {p₁ : var₁ agPartTy} {p₂ : var₂ agPartTy} (hp : ⟨agPartTy, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agRevProg p₁) (agRevProg p₂) := by
  unfold agRevProg
  prog_wf

theorem wf_agExtProg {k₁ j₁ : var₁ .nat} {k₂ j₂ : var₂ .nat} {acc₁ : var₁ (.list agPartTy)}
    {acc₂ : var₂ (.list agPartTy)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hacc : ⟨.list agPartTy, acc₁, acc₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agExtProg k₁ acc₁ j₁) (agExtProg k₂ acc₂ j₂) := by
  unfold agExtProg
  refine .bind (Toolkit.wf_filterList hacc fun _ hΓ _ _ hp => wf_agLessProg (hΓ hk) hp)
    fun _ _ => ?_
  refine .bind (wf_mapList (by simp) fun _ hΓ _ _ hp =>
    wf_agGrowProg (hΓ (by simp [hj])) hp) fun _ _ => ?_
  exact .prim _ (.cons (by simp [hacc]) (.cons (by simp) .nil))

theorem wf_ksubsProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (ksubsProg m₁ k₁) (ksubsProg m₂ k₂) := by
  unfold ksubsProg
  refine .bind (.prim _ (.cons hm .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.foldList (by simp) (by simp) fun _ _ _ _ =>
    wf_agExtProg (by simp [hk]) (by simp) (by simp)) fun _ _ => ?_
  refine .bind (Toolkit.wf_filterList (by simp) fun _ hΓ _ _ hp =>
    wf_agIsKProg (hΓ (by simp [hk])) hp) fun _ _ => ?_
  exact wf_mapList (by simp) fun _ _ _ _ hp => wf_agRevProg hp

theorem ag_wf_posProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {L₁ : var₁ (.list .nat)}
    {L₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (Programs.posProg N₁ L₁) (Programs.posProg N₂ L₂) := by
  unfold Programs.posProg mapList
  prog_wf

theorem wf_agAddProg {n₁ a₁ : var₁ .nat} {n₂ a₂ : var₂ .nat} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agAddProg n₁ a₁) (agAddProg n₂ a₂) := by
  unfold agAddProg
  prog_wf

theorem wf_agJoinProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {F₁ : var₁ (Ty.group D)}
    {F₂ : var₂ (Ty.group D)} {t₁ : var₁ (.prod (Ty.group D) .bool)}
    {t₂ : var₂ (.prod (Ty.group D) .bool)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) (ht : ⟨.prod (Ty.group D) .bool, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (agJoinProg N₁ F₁ t₁) (agJoinProg N₂ F₂ t₂) := by
  unfold agJoinProg
  prog_wf

theorem wf_fullStep {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {F₁ : var₁ (Ty.group D)} {F₂ : var₂ (Ty.group D)} {al₁ : var₁ (.list .nat)}
    {al₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) :
    Prog.Wf r Γ (fullStep sub₁ n₁ N₁ xy₁ G₁ F₁ al₁) (fullStep sub₂ n₂ N₂ xy₂ G₂ F₂ al₂) := by
  unfold fullStep
  refine .bind (wf_mapList hal fun _ hΓ _ _ ha => wf_agAddProg (hΓ hn) ha) fun _ _ => ?_
  refine .bind (ag_wf_posProg (by simp [hN]) (by simp)) fun _ _ => ?_
  refine .bind (wf_certProg (hsub.mono fun _ h => by simp [h]) (by simp [hn]) (by simp)
    (by simp) (by simp [hxy]) (by simp [hG]) (by simp [hal])) fun _ _ => ?_
  refine .caseOption (by simp) (.ret (by simp [hF])) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  exact .ite (by simp) (wf_agJoinProg (by simp [hN]) (by simp [hF]) (by simp))
    (.ret (by simp [hF]))

theorem wf_fullProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ k₁ : var₁ .nat} {n₂ N₂ k₂ : var₂ .nat}
    {x₁ : var₁ Ty.str} {x₂ : var₂ Ty.str} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hx : ⟨Ty.str, x₁, x₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf r Γ (fullProg sub₁ n₁ N₁ k₁ x₁ G₁) (fullProg sub₂ n₂ N₂ k₂ x₂ G₂) := by
  unfold fullProg
  refine .bind (.prim _ (.cons hx (.cons hx .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_ksubsProg (by simp) (by simp [hk])) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  exact .foldList (by simp) (List.Mem.head _) fun _ _ _ _ =>
    wf_fullStep (hsub.mono fun _ h => by simp [h]) (by simp [hn]) (by simp [hN]) (by simp)
      (by simp [hG]) (List.Mem.head _) (by simp)

theorem wf_agShiftProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {o₁ : var₁ (.list .nat)}
    {o₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agShiftProg n₁ o₁) (agShiftProg n₂ o₂) := by
  unfold agShiftProg
  exact wf_mapList ho fun _ hΓ _ _ hu => by unfold agSubProg; exact .prim _ (.cons hu
    (.cons (hΓ hn) .nil))

theorem wf_agFindStep {m₁ : var₁ .nat} {m₂ : var₂ .nat} {acc₁ : var₁ (.option (.list .nat))}
    {acc₂ : var₂ (.option (.list .nat))} {o₁ : var₁ (.list .nat)} {o₂ : var₂ (.list .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hacc : ⟨.option (.list .nat), acc₁, acc₂⟩ ∈ Γ)
    (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agFindStep m₁ acc₁ o₁) (agFindStep m₂ acc₂ o₂) := by
  unfold agFindStep
  prog_wf

theorem wf_agSuppStep {acc₁ : var₁ .nat} {acc₂ : var₂ .nat} {o₁ : var₁ (.list .nat)}
    {o₂ : var₂ (.list .nat)} (hacc : ⟨.nat, acc₁, acc₂⟩ ∈ Γ) (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (agSuppStep acc₁ o₁) (agSuppStep acc₂ o₂) := by
  unfold agSuppStep
  prog_wf

theorem wf_caseDecProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {bos₁ : var₁ (.list (.list .nat))}
    {bos₂ : var₂ (.list (.list .nat))} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hb : ⟨.list (.list .nat), bos₁, bos₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (caseDecProg m₁ bos₁) (caseDecProg m₂ bos₂) := by
  unfold caseDecProg
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.foldList (by simp [hb]) (by simp) fun _ _ _ _ =>
    wf_agFindStep (by simp [hm]) (by simp) (by simp)) fun _ _ => ?_
  refine .caseOption (by simp) ?_ fun _ _ => ?_
  · refine .bind (.prim _ .nil) fun _ _ => ?_
    refine .bind (.foldList (by simp [hb]) (by simp) fun _ _ _ _ =>
      wf_agSuppStep (by simp) (by simp)) fun _ _ => ?_
    prog_wf
  · prog_wf

theorem wf_caseProg {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat} {F₁ : var₁ (Ty.group D)}
    {F₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hF : ⟨Ty.group D, F₁, F₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (caseProg n₁ N₁ F₁) (caseProg n₂ N₂ F₂) := by
  unfold caseProg
  refine .bind (wf_baseWinProg hn hN) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hF]) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.call _ (List.Mem.head _)) fun _ _ => ?_
  refine .bind (wf_mapList (List.Mem.head _) fun _ hΓ _ _ ho =>
    wf_agShiftProg (hΓ (by simp [hn])) ho) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hN]) (.cons (by simp [hn]) .nil))) fun _ _ => ?_
  refine .bind (wf_caseDecProg (by simp) (by simp)) fun _ _ => ?_
  exact .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.Giant
