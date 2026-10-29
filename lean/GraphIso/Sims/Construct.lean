module

public import GraphIso.Sims.Table

/-!
# The construction of a complete table

`build n b gs` (`GraphIso/Sims/Basic.lean`) processes a worklist. Its invariant `Inv`:

* the table satisfies the slot conditions for `G = ⟨gs⟩`;
* the entry list lists exactly the filled slots, once each (`key`);
* pending items are valid elements of `G` fixing the base points before their row;
* every requirement of the closure criterion (`τ σ ∈ Γ_k` for entries `σ` in row `k` and `τ`
  in a row `≥ k`) and every generator (`g ∈ Γ₀`) is `Met`: it holds, or an item for it is
  pending.

Filled slots never change, so a requirement that holds keeps holding (`InGamma.mono`). A step
either sifts its item successfully, or inserts the residue into an empty slot, after which the
item holds, and queues every new requirement.

**Termination without group orders.** At most `n²` slots exist, an insertion queues at most
`2n²` items, and the potential `pot = |pending| + 2n² (n² − |entries|)` drops at every step
(`step_spec`). So `fuel n L` steps suffice (`build_spec`), and at the end nothing is pending:
the table is complete for `⟨gs⟩` (`complete_build`).
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv

/-! ### Slots of the initial table and of a filled table -/

section Slots

variable {n : ℕ} {b : Array ℕ}

theorem size_fill (T : Table) (k j : ℕ) (h : PermData) : (fill T k j h).size = T.size := by
  simp [fill]

theorem rowSize_fill (T : Table) (k j : ℕ) (h : PermData) (k' : ℕ) :
    ((fill T k j h).getD k' #[]).size = (T.getD k' #[]).size := by
  unfold fill
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  split_ifs with h₁ h₂
  · subst h₁
    simp [h₂]
  · subst h₁
    rw [Array.getElem?_eq_none (by omega)]
  · rfl

theorem slot_fill {T : Table} {k j : ℕ} {h : PermData} (hk : k < T.size)
    (hj : j < (T.getD k #[]).size) (k' j' : ℕ) :
    slot (fill T k j h) k' j' = if k' = k ∧ j' = j then some h else slot T k' j' := by
  unfold slot fill
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hkk : k = k'
  · subst hkk
    simp only [hk, ↓reduceIte, Option.getD_some, true_and]
    by_cases hjj : j = j'
    · subst hjj
      simp only [Array.getD_eq_getD_getElem?] at hj
      simp [hj]
    · simp [hjj, Ne.symm hjj]
  · simp [hkk, Ne.symm hkk]

theorem initTable_size (hb : BaseOrder n b) : (initTable n b).size = n := by
  simp [initTable, hb.size]

theorem initTable_getD (hb : BaseOrder n b) (k : ℕ) :
    (initTable n b).getD k #[] =
      if k < n then (Array.replicate n none).setIfInBounds (get b k) (some (PermData.one n))
      else #[] := by
  unfold initTable
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map]
  split_ifs with hk
  · have hk' : k < b.toList.length := by rw [Array.length_toList, hb.size]; exact hk
    rw [List.getElem?_eq_getElem hk', Option.map_some, Option.getD_some, Array.getElem_toList,
      get_eq_getElem (by rw [hb.size]; exact hk)]
  · rw [List.getElem?_eq_none (by rw [Array.length_toList, hb.size]; omega)]
    rfl

theorem slot_initTable (hb : BaseOrder n b) (k j : ℕ) :
    slot (initTable n b) k j = if k < n ∧ j = get b k then some (PermData.one n) else none := by
  unfold slot
  rw [initTable_getD hb]
  by_cases hk : k < n
  · simp only [hk, ↓reduceIte, true_and, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds, Array.size_replicate, hb.lt k hk, Array.getElem?_replicate]
    by_cases hj : get b k = j
    · simp [hj]
    · simp only [hj, ↓reduceIte, Ne.symm hj]
      split_ifs <;> rfl
  · simp [hk]

theorem initTable_wf (hb : BaseOrder n b) (G : Subgroup (Perm (Fin n))) :
    TableWF n b G (initTable n b) := by
  have hs := slot_initTable hb
  have one_of {k j : ℕ} {σ : PermData} (h : slot (initTable n b) k j = some σ) :
      k < n ∧ j = get b k ∧ σ = PermData.one n := by
    rw [hs] at h
    split_ifs at h with hkj
    · cases h
      exact ⟨hkj.1, hkj.2, rfl⟩
  refine ⟨hb, initTable_size hb, fun k hk => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_, fun k hk => ?_⟩
  · simp [initTable_getD hb, hk]
  · obtain ⟨-, -, rfl⟩ := one_of h
    exact PermData.valid_one n
  · obtain ⟨-, -, rfl⟩ := one_of h
    rw [PermData.denote_one]
    exact one_mem G
  · obtain ⟨-, -, rfl⟩ := one_of h
    intro i _
    rw [PermData.denote_one, act_one]
  · obtain ⟨-, rfl, rfl⟩ := one_of h
    rw [PermData.denote_one, act_one]
  · simp [hs, hk]

end Slots

/-! ### Queued items -/

section NewItems

theorem mem_newItemsStep {k : ℕ} {h : PermData} {acc : List Item} {e it : Item} :
    it ∈ newItemsStep k h acc e ↔
      it ∈ acc ∨ ((e.1 ≤ k ∧ it = (e.1, h.mul e.2)) ∨ (k ≤ e.1 ∧ it = (k, e.2.mul h))) := by
  unfold newItemsStep
  by_cases h₁ : k < e.1 <;> by_cases h₂ : e.1 < k
  · omega
  · have hA : ¬ e.1 ≤ k := by omega
    have hB : k ≤ e.1 := by omega
    simp only [h₁, h₂, hA, hB, ↓reduceIte, List.mem_cons, true_and, false_and, false_or]
    tauto
  · have hA : e.1 ≤ k := by omega
    have hB : ¬ k ≤ e.1 := by omega
    simp only [h₁, h₂, hA, hB, ↓reduceIte, List.mem_cons, true_and, false_and, or_false]
    tauto
  · have hA : e.1 ≤ k := by omega
    have hB : k ≤ e.1 := by omega
    simp only [h₁, h₂, hA, hB, ↓reduceIte, List.mem_cons, true_and]
    tauto

theorem mem_foldl_newItemsStep (k : ℕ) (h : PermData) :
    ∀ (ent acc : List Item) (it : Item),
      it ∈ ent.foldl (newItemsStep k h) acc ↔
        it ∈ acc ∨ ∃ e ∈ ent, (e.1 ≤ k ∧ it = (e.1, h.mul e.2)) ∨ (k ≤ e.1 ∧ it = (k, e.2.mul h))
  | [], acc, it => by simp
  | e :: ent, acc, it => by
    rw [List.foldl_cons, mem_foldl_newItemsStep k h ent, mem_newItemsStep,
      List.exists_mem_cons_iff, or_assoc]

theorem mem_newItems {k : ℕ} {h : PermData} {ent : List Item} {it : Item} :
    it ∈ newItems k h ent ↔
      ∃ e ∈ ent, (e.1 ≤ k ∧ it = (e.1, h.mul e.2)) ∨ (k ≤ e.1 ∧ it = (k, e.2.mul h)) := by
  rw [newItems, mem_foldl_newItemsStep]
  simp

theorem length_foldl_newItemsStep (k : ℕ) (h : PermData) :
    ∀ (ent acc : List Item),
      (ent.foldl (newItemsStep k h) acc).length ≤ acc.length + 2 * ent.length
  | [], acc => by simp
  | e :: ent, acc => by
    rw [List.foldl_cons]
    refine (length_foldl_newItemsStep k h ent _).trans ?_
    simp only [newItemsStep, List.length_cons]
    split_ifs <;> simp <;> omega

theorem length_newItems_le (k : ℕ) (h : PermData) (ent : List Item) :
    (newItems k h ent).length ≤ 2 * ent.length := by
  have := length_foldl_newItemsStep k h ent []
  rw [List.length_nil, Nat.zero_add] at this
  exact this

end NewItems

/-! ### The invariant -/

/-- The slot of an entry: its row and its image of the row's base point. -/
def key (b : Array ℕ) (e : Item) : ℕ × ℕ := (e.1, get e.2.1 (get b e.1))

/-- A requirement `x ∈ Γ_k` is met: it holds, or an item for it is pending. -/
def Met (n : ℕ) (T : Table) (pend : List Item) (k : ℕ) (x : Perm (Fin n)) : Prop :=
  InGamma n T k x ∨ ∃ it ∈ pend, it.1 = k ∧ it.2.denote n = x

/-- An item to sift: a valid element of `G` fixing the base points before its row. -/
structure ItemOK (n : ℕ) (b : Array ℕ) (G : Subgroup (Perm (Fin n))) (it : Item) : Prop where
  valid : it.2.Valid n
  le : it.1 ≤ n
  mem : it.2.denote n ∈ G
  fixes : ∀ i < it.1, act (it.2.denote n) (get b i) = get b i

/-- The invariant of the construction for `G = ⟨gs⟩`. -/
structure Inv (n : ℕ) (b : Array ℕ) (gs : GensData) (st : State) : Prop where
  wf : TableWF n b (GensData.denote n gs) st.1
  ent_slot : ∀ e ∈ st.2.1, slot st.1 e.1 (get e.2.1 (get b e.1)) = some e.2
  slot_ent : ∀ {k j : ℕ} {σ : PermData}, slot st.1 k j = some σ → (k, σ) ∈ st.2.1
  nodup : (st.2.1.map (key b)).Nodup
  items : ∀ it ∈ st.2.2, ItemOK n b (GensData.denote n gs) it
  pairs : ∀ e₁ ∈ st.2.1, ∀ e₂ ∈ st.2.1, e₁.1 ≤ e₂.1 →
    Met n st.1 st.2.2 e₁.1 (e₂.2.denote n * e₁.2.denote n)
  gens : ∀ g ∈ gs, Met n st.1 st.2.2 0 (g.denote n)

/-- The potential: pending items, plus `2n²` for each slot that can still be filled. -/
def pot (n : ℕ) (st : State) : ℕ := st.2.2.length + 2 * (n * n) * (n * n - st.2.1.length)

section Invariant

variable {n : ℕ} {b : Array ℕ} {gs : GensData}

/-- A duplicate-free list of slots of an `n × n` table has at most `n²` elements. -/
theorem length_le_of_keys {ent : List Item} (hnd : (ent.map (key b)).Nodup)
    (hlt : ∀ e ∈ ent, e.1 < n ∧ get e.2.1 (get b e.1) < n) : ent.length ≤ n * n := by
  have hsub : (ent.map (key b)).toFinset ⊆ Finset.range n ×ˢ Finset.range n := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hp)
    simp only [key, Finset.mem_product, Finset.mem_range]
    exact hlt e he
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, List.length_map, Finset.card_product,
    Finset.card_range] at this

/-- Facts about an entry of a table satisfying the slot conditions. -/
theorem entry_facts_of {G : Subgroup (Perm (Fin n))} {T : Table} {ent : List Item}
    (hwf : TableWF n b G T) (hent : ∀ e ∈ ent, slot T e.1 (get e.2.1 (get b e.1)) = some e.2)
    {e : Item} (he : e ∈ ent) :
    e.1 < n ∧ e.2.Valid n ∧ e.2.denote n ∈ G ∧
      (∀ i < e.1, act (e.2.denote n) (get b i) = get b i) ∧
      get e.2.1 (get b e.1) < n := by
  have hs := hent e he
  have hk := hwf.row_lt hs
  have hv := hwf.valid hs
  exact ⟨hk, hv, hwf.mem hs, hwf.fixes hs, hv.fwd_lt _ (hwf.base.lt _ hk)⟩

theorem Inv.entry_facts {st : State} (hI : Inv n b gs st) {e : Item} (he : e ∈ st.2.1) :
    e.1 < n ∧ e.2.Valid n ∧ e.2.denote n ∈ GensData.denote n gs ∧
      (∀ i < e.1, act (e.2.denote n) (get b i) = get b i) ∧
      get e.2.1 (get b e.1) < n :=
  entry_facts_of hI.wf hI.ent_slot he

theorem Inv.length_le {st : State} (hI : Inv n b gs st) : st.2.1.length ≤ n * n :=
  length_le_of_keys hI.nodup fun _ he =>
    ⟨(hI.entry_facts he).1, (hI.entry_facts he).2.2.2.2⟩

/-- Carry a met requirement across a step that keeps or settles the popped item. -/
theorem Met.carry {T T' : Table} {it : Item} {rest pend' : List Item} {k : ℕ}
    {x : Perm (Fin n)} (h : Met n T (it :: rest) k x) (hTT : Extends T T')
    (hit : InGamma n T' it.1 (it.2.denote n)) (hrest : ∀ y ∈ rest, y ∈ pend') :
    Met n T' pend' k x := by
  rcases h with h | ⟨y, hy, rfl, rfl⟩
  · exact Or.inl (h.mono hTT)
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact Or.inl hit
    · exact Or.inr ⟨y, hrest y hy, rfl, rfl⟩

theorem init_inv (hb : BaseOrder n b) (hgs : GensData.AllValid n gs) :
    Inv n b gs (init n b gs) := by
  have hwf := initTable_wf hb (GensData.denote n gs)
  have hs := slot_initTable hb
  refine ⟨hwf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 he
    rw [List.mem_range] at hk
    show slot (initTable n b) k (get (Array.range n) (get b k)) = some (PermData.one n)
    rw [get_range (hb.lt k hk), hs]
    simp [hk]
  · intro k j σ h
    change slot (initTable n b) k j = some σ at h
    rw [hs] at h
    split_ifs at h with hkj
    cases h
    exact List.mem_map.2 ⟨k, List.mem_range.2 hkj.1, rfl⟩
  · simp only [init, List.map_map]
    refine List.Nodup.map_on ?_ List.nodup_range
    intro x _ y _ hxy
    simp only [Function.comp, key, Prod.mk.injEq] at hxy
    exact hxy.1
  · intro it hit
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hit
    exact ⟨hgs g hg, Nat.zero_le _, GensData.mem_denote_of_mem hg, fun i hi => absurd hi (by omega)⟩
  · intro e₁ he₁ e₂ he₂ _
    obtain ⟨k₁, -, rfl⟩ := List.mem_map.1 he₁
    obtain ⟨k₂, -, rfl⟩ := List.mem_map.1 he₂
    left
    simp only [PermData.denote_one, mul_one]
    exact inGamma_one hwf k₁
  · intro g hg
    exact Or.inr ⟨(0, g), List.mem_map.2 ⟨g, hg, rfl⟩, rfl, rfl⟩

theorem pot_init (n : ℕ) (b : Array ℕ) (gs : GensData) :
    pot n (init n b gs) < fuel n gs.length := by
  simp only [pot, init, List.length_map, List.length_range, fuel]
  have : n * n - n ≤ n * n := Nat.sub_le _ _
  have : 2 * (n * n) * (n * n - n) ≤ 2 * (n * n) * (n * n) := Nat.mul_le_mul_left _ this
  omega

/-- **One step**: it keeps the invariant, decreases the potential and extends the table. -/
theorem step_spec {st : State} (hI : Inv n b gs st) {it : Item} {rest : List Item}
    (hp : st.2.2 = it :: rest) :
    ∃ st', step n b st = some st' ∧ Inv n b gs st' ∧ pot n st' + 1 ≤ pot n st ∧
      Extends st.1 st'.1 := by
  obtain ⟨T, ent, pend⟩ := st
  simp only at hp
  subst hp
  have hit := hI.items it List.mem_cons_self
  have hwf₀ : TableWF n b (GensData.denote n gs) T := hI.wf
  have hr := siftResult hwf₀ hit.valid hit.le
  have hb := hwf₀.base
  by_cases hlt : (sift n b T it.1 it.2).1 < n
  · -- the item does not sift: insert the residue
    rcases hr_eq : sift n b T it.1 it.2 with ⟨k', h⟩
    rw [hr_eq] at hr hlt
    simp only at hlt
    have hbk := hb.lt k' hlt
    have hv : h.Valid n := hr.valid
    have hact : act (h.denote n) (get b k') = get h.1 (get b k') := act_denote hv hbk
    have hempty : slot T k' (get h.1 (get b k')) = none := hact ▸ hr.empty hlt
    have hj'n : get h.1 (get b k') < n := hv.fwd_lt _ hbk
    have hk'T : k' < T.size := by rw [hwf₀.size]; exact hlt
    have hj'T : get h.1 (get b k') < (T.getD k' #[]).size := by
      rw [hwf₀.rowSize k' hlt]; exact hj'n
    have hs' := slot_fill (h := h) hk'T hj'T
    set j' := get h.1 (get b k') with hj'_def
    set T' := fill T k' j' h with hT'_def
    have hext : Extends T T' := by
      intro k j σ hσ
      rw [hs']
      split_ifs with hkj
      · obtain ⟨rfl, rfl⟩ := hkj
        rw [hempty] at hσ
        cases hσ
      · exact hσ
    have hmem : h.denote n ∈ GensData.denote n gs := hr.mem_iff.2 hit.mem
    have hfix : ∀ i < k', act (h.denote n) (get b i) = get b i := hr.fixes hit.fixes
    have hcase : ∀ {k j : ℕ} {σ : PermData}, slot T' k j = some σ →
        (k = k' ∧ j = j' ∧ σ = h) ∨ slot T k j = some σ := by
      intro k j σ hσ
      rw [hs'] at hσ
      split_ifs at hσ with hkj
      · cases hσ
        exact Or.inl ⟨hkj.1, hkj.2, rfl⟩
      · exact Or.inr hσ
    have hwf : TableWF n b (GensData.denote n gs) T' := by
      refine ⟨hb, by rw [size_fill]; exact hwf₀.size, fun k hk => ?_, fun hσ => ?_,
        fun hσ => ?_, fun hσ => ?_, fun hσ => ?_, fun k hk => ?_⟩
      · rw [rowSize_fill]
        exact hwf₀.rowSize k hk
      · rcases hcase hσ with ⟨-, -, rfl⟩ | hσ
        · exact hv
        · exact hwf₀.valid hσ
      · rcases hcase hσ with ⟨-, -, rfl⟩ | hσ
        · exact hmem
        · exact hwf₀.mem hσ
      · rcases hcase hσ with ⟨rfl, -, rfl⟩ | hσ
        · exact hfix
        · exact hwf₀.fixes hσ
      · rcases hcase hσ with ⟨rfl, rfl, rfl⟩ | hσ
        · exact hact
        · exact hwf₀.image hσ
      · exact hext (hwf₀.ident k hk)
    have hnew : slot T' k' j' = some h := by
      rw [hs']
      simp
    -- the popped item now holds
    have hitg : InGamma n T' it.1 (it.2.denote n) := by
      refine hr.to_gamma hext ?_
      have := InGamma.cons hlt (hact ▸ hnew) (inGamma_one hwf (k' + 1))
      rwa [mul_one] at this
    set ent' := (k', h) :: ent with hent'_def
    set pend' := newItems k' h ent' ++ rest with hpend'_def
    have hstep : step n b (T, ent, it :: rest) = some (T', ent', pend') := by
      simp only [step, hr_eq, hlt, ↓reduceIte]
      rfl
    have hent' : ∀ e ∈ ent', slot T' e.1 (get e.2.1 (get b e.1)) = some e.2 := by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hnew
      · exact hext (hI.ent_slot e he)
    have hef := fun {e} (he : e ∈ ent') => entry_facts_of hwf hent' he
    have hh : (k', h) ∈ ent' := List.mem_cons_self
    have hI' : Inv n b gs (T', ent', pend') := by
      refine ⟨hwf, hent', fun {k j σ} hσ => ?_, ?_, fun y hy => ?_, ?_, ?_⟩
      · rcases hcase hσ with ⟨rfl, -, rfl⟩ | hσ
        · exact hh
        · exact List.mem_cons_of_mem _ (hI.slot_ent hσ)
      · refine List.nodup_cons.2 ⟨?_, hI.nodup⟩
        intro hk
        obtain ⟨e, he, hke⟩ := List.mem_map.1 hk
        have := hI.ent_slot e he
        simp only [key, Prod.mk.injEq] at hke
        rw [hke.2, hke.1, hempty] at this
        cases this
      · rcases List.mem_append.1 hy with hy | hy
        · obtain ⟨e, he, ⟨hle, rfl⟩ | ⟨hle, rfl⟩⟩ := mem_newItems.1 hy
          · obtain ⟨hek, hev, hem, hefix, -⟩ := hef he
            refine ⟨hv.mul hev, by omega, ?_, fun i hi => ?_⟩
            · rw [PermData.denote_mul hv hev]
              exact mul_mem hmem hem
            · rw [PermData.denote_mul hv hev, act_mul, hefix i hi, hfix i (by omega)]
          · obtain ⟨hek, hev, hem, hefix, -⟩ := hef he
            refine ⟨hev.mul hv, by omega, ?_, fun i hi => ?_⟩
            · rw [PermData.denote_mul hev hv]
              exact mul_mem hem hmem
            · rw [PermData.denote_mul hev hv, act_mul, hfix i hi, hefix i (by omega)]
        · exact hI.items y (List.mem_cons_of_mem _ hy)
      · intro e₁ he₁ e₂ he₂ hle
        rcases List.mem_cons.1 he₂ with rfl | he₂'
        · -- the new entry on the left
          refine Or.inr ⟨(e₁.1, h.mul e₁.2), List.mem_append_left _
            (mem_newItems.2 ⟨e₁, he₁, Or.inl ⟨hle, rfl⟩⟩), rfl, ?_⟩
          exact PermData.denote_mul hv (hef he₁).2.1
        · rcases List.mem_cons.1 he₁ with rfl | he₁'
          · -- the new entry on the right
            refine Or.inr ⟨(k', e₂.2.mul h), List.mem_append_left _
              (mem_newItems.2 ⟨e₂, he₂, Or.inr ⟨hle, rfl⟩⟩), rfl, ?_⟩
            exact PermData.denote_mul (hef he₂).2.1 hv
          · exact (hI.pairs e₁ he₁' e₂ he₂' hle).carry hext hitg
              fun y hy => List.mem_append_right _ hy
      · intro g hg
        exact (hI.gens g hg).carry hext hitg fun y hy => List.mem_append_right _ hy
    refine ⟨_, hstep, hI', ?_, hext⟩
    have hlen : ent.length + 1 ≤ n * n := hI'.length_le
    have hnl : (newItems k' h ent').length ≤ 2 * (ent.length + 1) := length_newItems_le k' h ent'
    show (newItems k' h ent' ++ rest).length + 2 * (n * n) * (n * n - (ent.length + 1)) + 1 ≤
      (rest.length + 1) + 2 * (n * n) * (n * n - ent.length)
    rw [List.length_append]
    obtain ⟨d, hd⟩ : ∃ d, n * n - ent.length = d + 1 := ⟨n * n - ent.length - 1, by omega⟩
    have hd' : n * n - (ent.length + 1) = d := by omega
    rw [hd, hd', Nat.mul_succ]
    have : 2 * (ent.length + 1) ≤ 2 * (n * n) := by omega
    omega
  · -- the item sifts
    have heq : (sift n b T it.1 it.2).1 = n := le_antisymm hr.le_n (by omega)
    have hitg : InGamma n T it.1 (it.2.denote n) :=
      (sift_eq_iff hwf₀ hit.valid hit.le hit.fixes).1 heq
    have hstep : step n b (T, ent, it :: rest) = some (T, ent, rest) := by
      simp only [step, hlt, ↓reduceIte]
    refine ⟨_, hstep, ⟨hwf₀, hI.ent_slot, hI.slot_ent, hI.nodup,
      fun y hy => hI.items y (List.mem_cons_of_mem _ hy), ?_, ?_⟩, ?_, Extends.refl T⟩
    · intro e₁ he₁ e₂ he₂ hle
      exact (hI.pairs e₁ he₁ e₂ he₂ hle).carry (Extends.refl T) hitg fun y hy => hy
    · intro g hg
      exact (hI.gens g hg).carry (Extends.refl T) hitg fun y hy => hy
    · simp [pot]

/-- The worklist runs to completion within the potential. -/
theorem iter_step_spec :
    ∀ (m : ℕ) (st : State), Inv n b gs st → pot n st < m →
      Inv n b gs (iter (step n b) m st) ∧ (iter (step n b) m st).2.2 = [] ∧
        Extends st.1 (iter (step n b) m st).1
  | 0, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, st, hI, hm => by
    rcases hp : st.2.2 with _ | ⟨it, rest⟩
    · have hstep : step n b st = none := by simp [step, hp]
      simp only [iter, hstep]
      exact ⟨hI, hp, Extends.refl _⟩
    · obtain ⟨st', hstep, hI', hpot, hext⟩ := step_spec hI hp
      simp only [iter, hstep]
      obtain ⟨h₁, h₂, h₃⟩ := iter_step_spec m st' hI' (by omega)
      exact ⟨h₁, h₂, hext.trans h₃⟩

/-- **The construction terminates with nothing pending.** -/
theorem build_spec (hb : BaseOrder n b) (hgs : GensData.AllValid n gs) :
    Inv n b gs (build n b gs) ∧ (build n b gs).2.2 = [] :=
  let h := iter_step_spec (n := n) (b := b) (gs := gs) (fuel n gs.length) (init n b gs)
    (init_inv hb hgs) (pot_init n b gs)
  ⟨h.1, h.2.1⟩

/-- **The constructed table is complete for `⟨gs⟩`.** -/
theorem complete_build (hb : BaseOrder n b) (hgs : GensData.AllValid n gs) :
    Complete n b (GensData.denote n gs) (build n b gs).1 := by
  obtain ⟨hI, hp⟩ := build_spec hb hgs
  have hmet : ∀ {k : ℕ} {x : Perm (Fin n)}, Met n (build n b gs).1 (build n b gs).2.2 k x →
      InGamma n (build n b gs).1 k x := by
    intro k x h
    rcases h with h | ⟨it, hit, -⟩
    · exact h
    · rw [hp] at hit
      cases hit
  refine complete_of_closed hI.wf (fun {k j l j' σ τ} hσ hkl hτ => ?_) ?_
  · exact hmet (hI.pairs (k, σ) (hI.slot_ent hσ) (l, τ) (hI.slot_ent hτ) hkl)
  · rintro _ ⟨g, hg, rfl⟩
    exact hmet (hI.gens g hg)

/-- The entries in rows `≥ k`, as a list, denote the entries of the table in those rows. -/
theorem Inv.denoteSet_filter {st : State} (hI : Inv n b gs st) (k : ℕ) :
    GensData.denoteSet n ((st.2.1.filter fun e => decide (k ≤ e.1)).map Prod.snd) =
      entries n st.1 k := by
  ext x
  simp only [GensData.denoteSet, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Set.mem_ofPred_eq, entries]
  constructor
  · rintro ⟨σ, ⟨e, ⟨he, hk⟩, rfl⟩, rfl⟩
    exact ⟨e.1, _, e.2, hk, hI.ent_slot e he, rfl⟩
  · rintro ⟨l, j, σ, hk, hs, rfl⟩
    exact ⟨σ, ⟨(l, σ), ⟨hI.slot_ent hs, hk⟩, rfl⟩, rfl⟩

end Invariant

end GraphIso.Sims
