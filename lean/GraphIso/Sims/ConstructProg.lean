module

public import GraphIso.Sims.SiftProg
public import Mathlib.Tactic.Linarith

/-!
# The construction in the cost language

`buildProg n b gs` computes `build n b gs` (`RunsWithin.buildProg`) at cost at most
`buildCost n |gs|`, a polynomial of degree 6 in `n` plus `O(n²)` per generator, for a base
order `b` and valid generators of degree `n`.

The loop is paid by an amortized potential (`buildPot`):

* each pending item carries `A = siftCost n + 14`, the cost of an iteration that sifts it
  successfully;
* each slot that can still be filled carries `2n² A + Ins`: the items an insertion queues (at
  most `2n²`, by the entry bound of `Inv.length_le`) and the insertion's own work `Ins`
  (filling a slot copies two arrays of length `n`; queueing composes at most `2n²` pairs).

Iterations are counted by `pot`, which the potential dominates.
-/

@[expose] public section

namespace GraphIso.Sims

open Cost Programs

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Fill slot `(k, j)` of `T` with `h`: two array updates. -/
def fillProg (T : var Ty.table) (k j : var .nat) (h : var Ty.perm) : Prog S rec var Ty.table :=
  .bind (.op2 .arrayGet T k) fun row =>
  .bind (.op1 .some h) fun sh => .bind (.op2 .pair j sh) fun w =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .cons w nil) fun ws =>
  .bind (.op2 .arrayUpdate row ws) fun row' =>
  .bind (.op2 .pair k row') fun w' => .bind (.op0 .nil) fun nil' =>
  .bind (.op2 .cons w' nil') fun ws' => .op2 .arrayUpdate T ws'

/-- The items of one entry `e = (l, σ)` for a new entry `h` at row `k`. -/
def newItemsBody (k : var .nat) (h : var Ty.perm) (acc : var (.list Ty.item))
    (e : var Ty.item) : Prog S rec var (.list Ty.item) :=
  .bind (.op1 .fst e) fun l => .bind (.op1 .snd e) fun σ =>
  .bind (.op2 .natLt k l) fun c₁ =>
  .bind (.ite c₁ (.ret acc)
    (.bind (permMul h σ) fun hσ => .bind (.op2 .pair l hσ) fun it => .op2 .cons it acc))
    fun acc₁ =>
  .bind (.op2 .natLt l k) fun c₂ =>
  .ite c₂ (.ret acc₁)
    (.bind (permMul σ h) fun σh => .bind (.op2 .pair k σh) fun it => .op2 .cons it acc₁)

/-- The items queued for a new entry `h` at row `k`. -/
def newItemsProg (k : var .nat) (h : var Ty.perm) (ent : var (.list Ty.item)) :
    Prog S rec var (.list Ty.item) :=
  .bind (.op0 .nil) fun nil => .foldList ent nil fun acc e => newItemsBody k h acc e

/-- One iteration of the construction. -/
def stepBody (n : var .nat) (b : var (.array .nat)) (st : var Ty.state) :
    Prog S rec var (.option Ty.state) :=
  .bind (.op1 .fst st) fun T => .bind (.op1 .snd st) fun ep =>
  .bind (.op1 .fst ep) fun ent => .bind (.op1 .snd ep) fun pend =>
  .caseList pend (.op0 .none) fun it rest =>
    .bind (.op1 .fst it) fun k => .bind (.op1 .snd it) fun x =>
    .bind (siftProg n b T k x) fun r =>
    .bind (.op1 .fst r) fun k' =>
    .bind (.op2 .natLt k' n) fun failed =>
    .ite failed
      (.bind (.op1 .snd r) fun h =>
        .bind (.op2 .arrayGet b k') fun bk => .bind (permApply h bk) fun j =>
        .bind (fillProg T k' j h) fun T' =>
        .bind (.op2 .cons r ent) fun ent' =>
        .bind (newItemsProg k' h ent') fun new =>
        .bind (.op2 .append new rest) fun pend' =>
        .bind (.op2 .pair ent' pend') fun ep' => .bind (.op2 .pair T' ep') fun st' =>
        .op1 .some st')
      (.bind (.op2 .pair ent rest) fun ep' => .bind (.op2 .pair T ep') fun st' => .op1 .some st')

/-- The table of identities: one row per base point. -/
def initTableProg (n : var .nat) (b : var (.array .nat)) (e : var Ty.perm) :
    Prog S rec var Ty.table :=
  .bind (.op1 .some e) fun se =>
  .bind (.op0 .none) fun nn => .bind (.op2 .arrayMk n nn) fun emptyRow =>
  .bind (.op1 .arrayToList b) fun bl =>
  .bind (mapList bl fun p =>
      .bind (.op2 .pair p se) fun w => .bind (.op0 .nil) fun nl =>
      .bind (.op2 .cons w nl) fun ws => .op2 .arrayUpdate emptyRow ws) fun rows =>
  .op1 .arrayOfList rows

/-- The initial state. -/
def initProg (n : var .nat) (b : var (.array .nat)) (gs : var Ty.gens) :
    Prog S rec var Ty.state :=
  .bind (permOne n) fun e =>
  .bind (initTableProg n b e) fun T =>
  .bind (.op1 .range n) fun ks => .bind (mapList ks fun k => .op2 .pair k e) fun ent =>
  .bind (.op0 (.natLit 0)) fun z => .bind (mapList gs fun g => .op2 .pair z g) fun pend =>
  .bind (.op2 .pair ent pend) fun ep => .op2 .pair T ep

/-- The construction: the initial state, then the worklist loop. -/
def buildProg (n : var .nat) (b : var (.array .nat)) (gs : var Ty.gens) :
    Prog S rec var Ty.state :=
  .bind (initProg n b gs) fun st₀ => .loop st₀ fun st => stepBody n b st

end Prog

/-! ### Costs -/

/-- Charge per pending item: one successful iteration. -/
def itemCost (n : ℕ) : ℕ := siftCost n + 14

/-- The extra work of an insertion. -/
def insCost (n : ℕ) : ℕ := n * n * (24 * n + 39) + 2 * n + 40

/-- Charge per slot that can still be filled. -/
def slotCost (n : ℕ) : ℕ := 2 * (n * n) * itemCost n + insCost n

/-- The potential paying for the loop. -/
def buildPot (n : ℕ) (st : State) : ℕ :=
  itemCost n * st.2.2.length + slotCost n * (n * n - st.2.1.length) + 7

/-- The cost of the initial state. -/
def initCost (n L : ℕ) : ℕ := n * (n + 8) + 4 * L + 16 * n + 30

/-- **The cost bound of the construction**, for `L` generators in degree `n`. -/
def buildCost (n L : ℕ) : ℕ := initCost n L + itemCost n * L + slotCost n * (n * n) + 7

section Specs

variable {S : Signature} {a b' : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b') Ty.denote b'}
  {n : ℕ} {b : Array ℕ} {gs : GensData}

theorem RunsWithin.fillProg {T : Table} {k j : ℕ} {h : PermData} (hT : T.size = n)
    (hrow : (T.getD k #[]).size = n) :
    RunsWithin X body (Sims.fillProg T k j h) (fill T k j h) (2 * n + 12) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Prim.applyWrites,
      List.foldl_cons, List.foldl_nil, List.length_cons, List.length_nil]
    change 1 + (1 + (1 + (1 + (1 + ((T.getD k #[]).size + (0 + 1) + 1 +
      (1 + (1 + (1 + (T.size + (0 + 1) + 1))))))))) ≤ _
    rw [hT, hrow]
    omega

theorem RunsWithin.newItemsBody {k : ℕ} {h : PermData} (hh : h.Valid n) (acc : List Item)
    {e : Item} (he : e.2.Valid n) :
    RunsWithin X body (Sims.newItemsBody k h acc e) (newItemsStep k h acc e) (24 * n + 36) := by
  obtain ⟨l, σ⟩ := e
  simp only at he
  -- the first conditional
  have h₁ : RunsWithin X body
      (Prog.ite (t := .list Ty.item) (decide (k < l)) (.ret acc)
        (.bind (permMul h σ) fun hσ => .bind (.op2 .pair l hσ) fun it => .op2 .cons it acc))
      (if k < l then acc else (l, h.mul σ) :: acc) (12 * n + 16) := by
    by_cases hc : k < l
    · simp only [hc, decide_true, ↓reduceIte]
      exact (RunsWithin.ite_true (RunsWithin.ret _)).mono (by omega)
    · simp only [hc, decide_false, ↓reduceIte]
      refine (RunsWithin.ite_false (k := 12 * n + 15) ?_).mono (by omega)
      exact RunsWithin.bind_le (c₂ := 2) (RunsWithin.permMul hh he)
        (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
        (by omega)
  have h₂ : ∀ acc₁ : List Item, RunsWithin X body
      (Prog.ite (t := .list Ty.item) (decide (l < k)) (.ret acc₁)
        (.bind (permMul σ h) fun σh => .bind (.op2 .pair k σh) fun it => .op2 .cons it acc₁))
      (if l < k then acc₁ else (k, σ.mul h) :: acc₁) (12 * n + 16) := by
    intro acc₁
    by_cases hc : l < k
    · simp only [hc, decide_true, ↓reduceIte]
      exact (RunsWithin.ite_true (RunsWithin.ret _)).mono (by omega)
    · simp only [hc, decide_false, ↓reduceIte]
      refine (RunsWithin.ite_false (k := 12 * n + 15) ?_).mono (by omega)
      exact RunsWithin.bind_le (c₂ := 2) (RunsWithin.permMul he hh)
        (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
        (by omega)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step h₁
    run_step (RunsWithin.prim _ _)
    exact h₂ _
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.newItemsProg {k : ℕ} {h : PermData} (hh : h.Valid n) {ent : List Item}
    (hent : ∀ e ∈ ent, e.2.Valid n) :
    RunsWithin X body (Sims.newItemsProg k h ent) (newItems k h ent)
      (ent.length * (24 * n + 37) + 1) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body)
    (f := fun acc e => Sims.newItemsBody k h acc e) (F := newItemsStep k h)
    (cf := fun _ => 24 * n + 36) ent []
    (fun acc e he => RunsWithin.newItemsBody hh acc (hent e he))
  rw [sum_map_const, show 24 * n + 36 + 1 = 24 * n + 37 by omega] at hfold
  exact RunsWithin.bind_le (RunsWithin.prim _ _) hfold (by simp [Prim.cost]; omega)

theorem RunsWithin.stepBody_empty {T : Table} {ent : List Item} :
    RunsWithin X body (Sims.stepBody n b (T, ent, [])) none 6 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.stepBody_insert {T : Table} {ent rest : List Item} {it : Item} {k' : ℕ}
    {h : PermData} (hsift : RunsWithin X body (Sims.siftProg n b T it.1 it.2) (k', h) (siftCost n))
    (hlt : k' < n) (hTs : T.size = n) (hrow : (T.getD k' #[]).size = n) (hhv : h.Valid n)
    (hent : ∀ e ∈ (k', h) :: ent, e.2.Valid n) :
    RunsWithin X body (Sims.stepBody n b (T, ent, it :: rest))
      (some (fill T k' (get h.1 (get b k')) h, (k', h) :: ent,
        newItems k' h ((k', h) :: ent) ++ rest))
      (siftCost n + 2 * n + 40 + (ent.length + 1) * (24 * n + 37) +
        (newItems k' h ((k', h) :: ent)).length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.caseList_cons _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hsift
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.ite_pos (decide_eq_true hlt) _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permApply _ _)
    run_step (RunsWithin.fillProg (T := T) (k := k') (j := get h.1 (get b k')) (h := h) hTs hrow)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.newItemsProg (k := k') hhv hent)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_cons]
    omega

theorem RunsWithin.stepBody_sift {T : Table} {ent rest : List Item} {it : Item} {k' : ℕ}
    {h : PermData} (hsift : RunsWithin X body (Sims.siftProg n b T it.1 it.2) (k', h) (siftCost n))
    (hlt : ¬ k' < n) :
    RunsWithin X body (Sims.stepBody n b (T, ent, it :: rest)) (some (T, ent, rest))
      (siftCost n + 13) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.caseList_cons _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hsift
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.ite_neg (decide_eq_false hlt) _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost]
    omega

private theorem pot_drop {A K c N r d : ℕ} (h : c + 1 + A * N ≤ A + K) :
    c + 1 + (A * (N + r) + K * d + 7) ≤ A * (r + 1) + K * (d + 1) + 7 := by
  rw [Nat.mul_add, Nat.mul_add_one, Nat.mul_add_one]
  omega

theorem RunsWithin.stepBody {st : State} (hI : Inv n b gs st) :
    ∃ c, RunsWithin X body (Sims.stepBody n b st) (step n b st) c ∧
      (step n b st = none → c + 1 ≤ buildPot n st) ∧
      ∀ st', step n b st = some st' → Inv n b gs st' ∧ c + 1 + buildPot n st' ≤ buildPot n st := by
  obtain ⟨T, ent, pend⟩ := st
  rcases pend with _ | ⟨it, rest⟩
  · -- nothing pending
    have hF : step n b (T, ent, []) = none := rfl
    refine ⟨6, hF ▸ RunsWithin.stepBody_empty, (fun _ => by simp only [buildPot]; omega),
      (fun st' h => by rw [hF] at h; cases h)⟩
  · obtain ⟨st', hstep, hI', -, -⟩ := step_spec hI rfl
    have hit := hI.items it List.mem_cons_self
    have hTv : SlotsValid n T := hI.wf.slotsValid
    have hsift := RunsWithin.siftProg (X := X) (body := body) (b := b) hTv hit.le hit.valid
    rcases hr : sift n b T it.1 it.2 with ⟨k', h⟩
    rw [hr] at hsift
    by_cases hlt : k' < n
    · -- insertion
      have hF : step n b (T, ent, it :: rest) = some (fill T k' (get h.1 (get b k')) h,
          (k', h) :: ent, newItems k' h ((k', h) :: ent) ++ rest) := by
        simp [step, hr, hlt]
      rw [hF] at hstep
      cases hstep
      have hent'v : ∀ e ∈ (k', h) :: ent, e.2.Valid n := fun e he => (hI'.entry_facts he).2.1
      have hhv : h.Valid n := hent'v _ List.mem_cons_self
      have hlen : ent.length + 1 ≤ n * n := hI'.length_le
      have hnl : (newItems k' h ((k', h) :: ent)).length ≤ 2 * (ent.length + 1) :=
        length_newItems_le k' h _
      refine ⟨_, hF ▸ RunsWithin.stepBody_insert hsift hlt hI.wf.size (hI.wf.rowSize k' hlt) hhv
        hent'v, (fun h => by rw [hF] at h; cases h), fun st' h => ?_⟩
      rw [hF] at h
      cases h
      refine ⟨hI', ?_⟩
      simp only [buildPot, List.length_append, List.length_cons]
      obtain ⟨d, hd⟩ : ∃ d, n * n - ent.length = d + 1 := ⟨n * n - ent.length - 1, by omega⟩
      have hd' : n * n - (ent.length + 1) = d := by omega
      rw [hd, hd']
      refine pot_drop ?_
      have h₁ : (ent.length + 1) * (24 * n + 37) ≤ n * n * (24 * n + 37) :=
        Nat.mul_le_mul_right _ hlen
      have h₂ : itemCost n * (newItems k' h ((k', h) :: ent)).length ≤
          2 * (n * n) * itemCost n := by
        rw [Nat.mul_comm (2 * (n * n))]
        exact Nat.mul_le_mul_left _ (by omega)
      have hK : slotCost n = 2 * (n * n) * itemCost n + insCost n := rfl
      have hIns : insCost n = n * n * (24 * n + 37) + 2 * (n * n) + 2 * n + 40 := by
        simp only [insCost]
        ring
      have hA : itemCost n = siftCost n + 14 := rfl
      omega
    · -- the item sifts
      have hF : step n b (T, ent, it :: rest) = some (T, ent, rest) := by
        simp [step, hr, hlt]
      rw [hF] at hstep
      cases hstep
      refine ⟨_, hF ▸ RunsWithin.stepBody_sift hsift hlt, (fun h => by rw [hF] at h; cases h),
        fun st' h => ?_⟩
      rw [hF] at h
      cases h
      refine ⟨hI', ?_⟩
      simp only [buildPot, List.length_cons]
      rw [Nat.mul_add_one]
      have hA : itemCost n = siftCost n + 14 := rfl
      omega

theorem RunsWithin.initTableProg (hb : BaseOrder n b) :
    RunsWithin X body (Sims.initTableProg n b (PermData.one n)) (initTable n b)
      (n * (n + 8) + 3 * n + 7) := by
  have hrows : RunsWithin X body
      (mapList (a' := .nat) (b' := Ty.array (.option Ty.perm)) b.toList fun p =>
        .bind (.op2 .pair p (some (PermData.one n))) fun w => .bind (.op0 .nil) fun nl =>
        .bind (.op2 .cons w nl) fun ws =>
          .op2 .arrayUpdate (Array.replicate n (none : Option PermData)) ws)
      (b.toList.map fun p =>
        (Array.replicate n (none : Option PermData)).setIfInBounds p (some (PermData.one n)))
      (b.toList.length * (n + 5 + 3) + 2) :=
    RunsWithin.mapList_le fun p _ =>
      RunsWithin.bind_le (c₂ := n + 4) (RunsWithin.prim _ _)
        (RunsWithin.bind_le (c₂ := n + 3) (RunsWithin.prim _ _)
          (RunsWithin.bind_le (c₂ := n + 2) (RunsWithin.prim _ _)
            (RunsWithin.prim_le rfl (by simp [Prim.cost, Prim.eval]))
            (by simp [Prim.cost]; omega))
          (by simp [Prim.cost]; omega)) (by simp [Prim.cost]; omega)
  have hlen : b.toList.length = n := by rw [Array.length_toList, hb.size]
  rw [hlen] at hrows
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hrows
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, hb.size,
      hlen, show n + 5 + 3 = n + 8 by omega]
    omega

theorem RunsWithin.initProg (hb : BaseOrder n b) :
    RunsWithin X body (Sims.initProg n b gs) (init n b gs) (initCost n gs.length) := by
  have hent := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := Ty.item)
    (xs := List.range n) (f := fun k => .op2 .pair k (PermData.one n))
    (F := fun k => (k, PermData.one n)) (c := 1) fun k _ => RunsWithin.prim_le rfl le_rfl
  have hpend := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.item)
    (xs := gs) (f := fun g => .op2 .pair (0 : ℕ) g) (F := fun g => ((0 : ℕ), g)) (c := 1)
    fun g _ => RunsWithin.prim_le rfl le_rfl
  rw [List.length_range] at hent
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.permOne n)
    run_step (RunsWithin.initTableProg hb)
    run_step (RunsWithin.prim _ _)
    run_step hent
    run_step (RunsWithin.prim _ _)
    run_step hpend
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    simp only [initCost]
    omega

/-- The cost potential dominates the step counter. -/
theorem pot_le_buildPot (st : State) : pot n st ≤ buildPot n st := by
  simp only [pot, buildPot, slotCost, itemCost]
  have h₁ : st.2.2.length ≤ (siftCost n + 14) * st.2.2.length :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h₂ : 2 * (n * n) * (n * n - st.2.1.length) ≤
      (2 * (n * n) * (siftCost n + 14) + insCost n) * (n * n - st.2.1.length) := by
    apply Nat.mul_le_mul_right
    have : 2 * (n * n) ≤ 2 * (n * n) * (siftCost n + 14) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  omega

/-- **The construction program computes `build` within `buildCost`.** -/
theorem RunsWithin.buildProg (hb : BaseOrder n b) (hgs : GensData.AllValid n gs) :
    RunsWithin X body (Sims.buildProg n b gs) (build n b gs) (buildCost n gs.length) := by
  have hI₀ := init_inv hb hgs
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (f := Sims.stepBody n b)
    (I := Inv n b gs) (Φ := buildPot n) (fun st hst => RunsWithin.stepBody hst)
    (buildPot n (init n b gs) + 1) (init n b gs) hI₀ (Nat.lt_succ_self _)
  have hdone := iter_step_spec (pot n (init n b gs) + 1) (init n b gs) hI₀ (Nat.lt_succ_self _)
  have hfix : step n b (iter (step n b) (pot n (init n b gs) + 1) (init n b gs)) = none := by
    simp [step, hdone.2.1]
  have h₁ := iter_eq_of_fix _ _ hfix (buildPot n (init n b gs) + 1)
    (by have := pot_le_buildPot (n := n) (init n b gs); omega)
  have h₂ := iter_eq_of_fix _ _ hfix (fuel n gs.length) (pot_init n b gs)
  rw [h₁, ← h₂] at hloop
  refine RunsWithin.bind_le (RunsWithin.initProg hb) hloop ?_
  simp only [buildCost, buildPot, init, List.length_map, List.length_range]
  have : slotCost n * (n * n - n) ≤ slotCost n * (n * n) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  omega

end Specs

end GraphIso.Sims
