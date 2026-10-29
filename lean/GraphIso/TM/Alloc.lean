module

public import GraphIso.TM.Lookup

/-!
# Allocation in the heap

Stage 17c (`PLAN-17.md` §6).

* **`moveNums a b`** (`moveNums_sat`): moves the numbers of `a` down to the marker `mk 2` onto
  `b`, each reversed and in reverse order, and drops the marker.
* **`HeapAt h c`**: the configuration holds the heap `h`. It is well formed and on `heap`,
  `scan` is empty, and the allocation counter on `cnt` has value `h.length` (and length at most
  `h.length + 1`).
* **`alloc t`** (`alloc_sat`): from `HeapAt h`, with fields `fs` on `work` above the marker
  `mk 2`, appends the cell `⟨l, t, fs⟩` with `ofBits l = h.length` (and `l` of length at most
  `h.length + 1`, a copy of the counter), so that `HeapAt (h ++ [_])` holds. It replaces the
  fields and the marker on `work` by the address `l` and leaves every other stack as it was,
  within `allocBound (encFields fs).length h.length` steps.
-/

@[expose] public section

namespace GraphIso.TM

open Function

variable {K P : Type} [DecidableEq K] {prog : Program K Sym Rg P}

/-! ### Moving lists of numbers -/

/-- Numbers, one after another (the fields of a cell). -/
theorem encFields_nil : encFields [] = [] := rfl

theorem encFields_cons (f : List Bool) (fs : List (List Bool)) :
    encFields (f :: fs) = bits f ++ .nd :: encFields fs := rfl

theorem encFields_append (fs gs : List (List Bool)) :
    encFields (fs ++ gs) = encFields fs ++ encFields gs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [encFields, ih]

theorem length_encFields_cons (f : List Bool) (fs : List (List Bool)) :
    (encFields (f :: fs)).length = f.length + 1 + (encFields fs).length := by
  simp [encFields]; omega

theorem length_le_encFields : ∀ fs : List (List Bool), fs.length ≤ (encFields fs).length
  | [] => le_rfl
  | f :: fs => by rw [length_encFields_cons]; have := length_le_encFields fs; simp; omega

theorem encFields_reverse_map (fs : List (List Bool)) :
    (fs.reverse.map List.reverse).reverse.map List.reverse = fs := by
  simp [List.map_reverse]

/-- Move the numbers of `a` down to the marker `mk 2` onto `b` (each reversed, in reverse
order), and drop the marker. -/
def moveNums (a b : K) : Code K Sym Rg P :=
  .seq (.act (.peek a 0))
    (.seq (.loop (.not (.is 0 (some (.mk 2))))
        (.seq (.act (.set 0 none)) (.seq (moveBits a b) (.act (.peek a 0)))))
      (.seq (.act (.pop a 0)) (.act (.set 0 none))))

theorem moveNums_sat {a b : K} (hab : a ≠ b) {c : Cfg K Sym Rg} {fs : List (List Bool)}
    {rest : List Sym} (hv : c.regs = Regs.empty) (ha : c.stk a = encFields fs ++ .mk 2 :: rest) :
    Sat prog (moveNums a b) c ((encFields fs).length * (6 * (encFields fs).length + 14) + 8)
      fun c' => c'.regs = Regs.empty ∧ c'.stk a = rest ∧
        c'.stk b = encFields (fs.reverse.map List.reverse) ++ c.stk b ∧
        ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  set L := (encFields fs).length with hL
  have hloop := Sat.loop (prog := prog) (b := .not (.is 0 (some (.mk 2))))
    (x := .seq (.act (.set 0 none)) (.seq (moveBits a b) (.act (.peek a 0)))) (t := 6 * L + 13)
    (I := fun m c₁ => ∃ fs₁ fs₂, fs₁ ++ fs₂ = fs ∧ fs₂.length = m ∧
      c₁.regs = rv (c₁.stk a).head? none none none ∧ c₁.stk a = encFields fs₂ ++ .mk 2 :: rest ∧
      c₁.stk b = encFields (fs₁.reverse.map List.reverse) ++ c.stk b ∧
      ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some (.mk 2)) none none none ∧ c₁.stk a = .mk 2 :: rest ∧
      c₁.stk b = encFields (fs.reverse.map List.reverse) ++ c.stk b ∧
      ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (fun m c₁ ⟨fs₁, fs₂, hfs, hlen, hr, ha₁, hb₁, hj₁⟩ => by
      obtain ⟨f, fs₂, rfl⟩ : ∃ f fs₂', fs₂ = f :: fs₂' := by
        cases fs₂ with
        | nil => simp at hlen
        | cons f fs₂' => exact ⟨f, fs₂', rfl⟩
      refine ⟨?_, ?_⟩
      · rw [ha₁] at hr
        cases f with
        | nil => simp [Cond.eval, hr, encFields]
        | cons x f => simp [Cond.eval, hr, encFields]
      refine Sat.act_seq (by omega) ?_
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        simp [Act.run, hr, empty_eq_rv]
      have ha₂ : (Act.run (.set 0 none) c₁).stk a =
          bits f ++ .nd :: (encFields fs₂ ++ .mk 2 :: rest) := by
        simp [Act.run, ha₁, encFields]
      have hfL : f.length + 1 ≤ L := by
        have h₁ : encFields fs = encFields fs₁ ++ encFields (f :: fs₂) := by
          rw [← hfs, encFields_append]
        have h₂ := congrArg List.length h₁
        rw [List.length_append, length_encFields_cons] at h₂
        omega
      refine Sat.seq_le (moveBits_sat hab hv₂ ha₂) (by omega) fun c₃ ⟨hr₃, ha₃, hb₃, hj₃⟩ =>
        Sat.act_le (by omega)
          ⟨fs₁ ++ [f], fs₂, by simp [← hfs], by simpa using hlen, ?_, ?_, ?_, ?_⟩
      · simp [Act.run, hr₃, empty_eq_rv]
      · simp [Act.run, ha₃]
      · simp only [Act.run]
        rw [hb₃]
        simp [Act.run, hb₁, encFields]
      · intro j hja hjb
        simp only [Act.run]
        rw [hj₃ j hja hjb]
        simp [Act.run, hj₁ j hja hjb])
    (fun c₁ ⟨fs₁, fs₂, hfs, hlen, hr, ha₁, hb₁, hj₁⟩ => by
      obtain rfl : fs₂ = [] := List.eq_nil_of_length_eq_zero hlen
      simp only [List.append_nil] at hfs
      subst hfs
      rw [ha₁] at hr
      exact ⟨by simp [Cond.eval, hr, encFields], by simpa [encFields] using hr,
        by simpa [encFields] using ha₁, hb₁, hj₁⟩)
  have hk : fs.length * (6 * L + 13 + 1) ≤ L * (6 * L + 14) :=
    Nat.mul_le_mul_right _ (length_le_encFields fs)
  unfold moveNums
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop fs.length _ ⟨[], fs, by simp, rfl, ?_, ?_, ?_,
    ?_⟩) (by omega) fun c₃ ⟨hr₃, ha₃, hb₃, hj₃⟩ =>
      Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_⟩))
  · simp [Act.run, hv]
  · simp [Act.run, ha]
  · simp [Act.run, encFields]
  · intro j _ _; simp [Act.run]
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · simp [Act.run, hb₃, update_of_ne (Ne.symm hab)]
  · intro j hja hjb; simp [Act.run, update_of_ne hja, hj₃ j hja hjb]

theorem length_encFields_reverse_map (fs : List (List Bool)) :
    (encFields (fs.reverse.map List.reverse)).length = (encFields fs).length := by
  have key : ∀ gs : List (List Bool),
      (encFields (gs.map List.reverse)).length = (encFields gs).length := by
    intro gs
    induction gs with
    | nil => rfl
    | cons g gs ih => simp [length_encFields_cons, ih]
  rw [key]
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [encFields_append, length_encFields_cons, encFields_nil, ih]; omega

/-! ### Allocation -/

/-- The machine holds the heap `h`: well formed, on `heap`, with `scan` empty and the
allocation counter on `cnt` (its value is the number of cells, its length at most one more). -/
structure HeapAt (h : List Cell) (c : Cfg Stk Sym Rg) : Prop where
  wf : HeapWF h
  heap : c.stk .heap = encHeap h
  scan : c.stk .scan = []
  cnt : ∃ l, c.stk .cnt = bits l ++ [.nd] ∧ ofBits l = h.length ∧ l.length ≤ h.length + 1

/-- Allocate a cell with tag `t` and the fields on `work` (down to the marker `mk 2`), and push
its address onto `work`. -/
def alloc (t : Tag) : Code Stk Sym Rg P :=
  .seq (.act (.push .t0 (.mk 2)))
    (.seq (moveNums .work .t0)
      (.seq (.act (.push .heap (.mk 0)))
        (.seq (moveNums .t0 .heap)
          (.seq (.act (.push .heap (.tag t)))
            (.seq (copyNum .cnt .heap .t3)
              (.seq (.act (.push .heap (.mk 1)))
                (.seq (copyNum .cnt .work .t3)
                  (.seq (incNum .cnt .t1 .t2 .t3)
                    (.seq (moveBits .t2 .t0) (moveBits .t0 .cnt))))))))))

/-- The step bound of `alloc` for fields of `Lf` symbols and a heap of `n` cells. -/
def allocBound (Lf n : ℕ) : ℕ := 2 * (Lf * (6 * Lf + 14)) + 63 * n + 300

theorem alloc_sat {P : Type} {prog : Program Stk Sym Rg P} (t : Tag) {h : List Cell}
    {c : Cfg Stk Sym Rg} {fs : List (List Bool)} {rest : List Sym} (hH : HeapAt h c)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = encFields fs ++ .mk 2 :: rest) :
    Sat prog (alloc t) c (allocBound (encFields fs).length h.length) fun c' =>
      c'.regs = Regs.empty ∧ ∃ l, HeapAt (h ++ [⟨l, t, fs⟩]) c' ∧ ofBits l = h.length ∧
        l.length ≤ h.length + 1 ∧ c'.stk .work = bits l ++ .nd :: rest ∧
        ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c.stk j := by
  obtain ⟨hwf, hh, hs, l, hc, hlv, hll⟩ := hH
  have hLf' := length_encFields_reverse_map fs
  have hal := length_addBits l [true]
  simp only [List.length_singleton] at hal
  unfold alloc
  refine Sat.act_seq (by unfold allocBound; omega) ?_
  set c₁ := Act.run (.push .t0 (.mk 2)) c with hc₁
  have hw₁ : c₁.stk .work = encFields fs ++ .mk 2 :: rest := by simp [hc₁, Act.run, hw]
  refine Sat.seq_le (moveNums_sat (by decide) hv hw₁) (by unfold allocBound; omega)
    fun c₂ ⟨hr₂, hw₂, ht₂, hj₂⟩ => ?_
  refine Sat.act_seq (by unfold allocBound; omega) ?_
  set c₃ := Act.run (.push .heap (.mk 0)) c₂ with hc₃
  have ht₃ : c₃.stk .t0 = encFields (fs.reverse.map List.reverse) ++ .mk 2 :: c.stk .t0 := by
    simp [hc₃, Act.run, ht₂, hc₁]
  refine Sat.seq_le (moveNums_sat (by decide) hr₂ ht₃) (by unfold allocBound; rw [hLf']; omega)
    fun c₄ ⟨hr₄, ht₄, hh₄, hj₄⟩ => ?_
  refine Sat.act_seq (by unfold allocBound; rw [hLf']; omega) ?_
  set c₅ := Act.run (.push .heap (.tag t)) c₄ with hc₅
  have hcnt₅ : c₅.stk .cnt = bits l ++ .nd :: [] := by
    simp [hc₅, Act.run, hj₄, hc₃, hj₂, hc₁, hc]
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hr₄ hcnt₅)
    (by unfold allocBound; rw [hLf']; omega) fun c₆ ⟨hr₆, hh₆, hj₆⟩ => ?_
  refine Sat.act_seq (by unfold allocBound; rw [hLf']; omega) ?_
  set c₇ := Act.run (.push .heap (.mk 1)) c₆ with hc₇
  have hcnt₇ : c₇.stk .cnt = bits l ++ .nd :: [] := by
    simp [hc₇, Act.run, hj₆, hcnt₅]
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hr₆ hcnt₇)
    (by unfold allocBound; rw [hLf']; omega) fun c₈ ⟨hr₈, hw₈, hj₈⟩ => ?_
  have hcnt₈ : c₈.stk .cnt = bits l ++ .nd :: [] := by rw [hj₈ .cnt (by decide), hcnt₇]
  refine Sat.seq_le (incNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hr₈ hcnt₈) (by unfold allocBound; rw [hLf']; omega)
    fun c₉ ⟨hr₉, hcnt₉, ht₉, hj₉⟩ => ?_
  refine Sat.seq_le (moveBits_sat (by decide) hr₉ ht₉) (by unfold allocBound; rw [hLf']; omega)
    fun c₁₀ ⟨hr₁₀, ht₁₀, ht0₁₀, hj₁₀⟩ => ?_
  refine (moveBits_sat (by decide) hr₁₀ ht0₁₀).mono
    (by unfold allocBound; rw [hLf']; simp only [List.length_reverse]; omega)
    fun c₁₁ ⟨hr₁₁, ht0₁₁, hcnt₁₁, hj₁₁⟩ => ⟨hr₁₁, l, ⟨?_, ?_, ?_, ?_⟩, hlv, hll, ?_, ?_⟩
  · intro i hi
    rw [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · rw [List.getElem_append_left hi]; exact hwf i hi
    · subst hi; simp [hlv]
  · rw [hj₁₁ .heap (by decide) (by decide), hj₁₀ .heap (by decide) (by decide),
      hj₉ .heap (by decide) (by decide), hj₈ .heap (by decide), hc₇]
    simp only [Act.run, update_self]
    rw [hh₆, hc₅]
    simp only [Act.run, update_self]
    rw [hh₄, hc₃, encFields_reverse_map]
    simp only [Act.run, update_self]
    rw [hj₂ .heap (by decide) (by decide), hc₁]
    simp [Act.run, hh, encHeap_append, encCell, cellBody]
  · rw [hj₁₁ .scan (by decide) (by decide), hj₁₀ .scan (by decide) (by decide),
      hj₉ .scan (by decide) (by decide), hj₈ .scan (by decide), hc₇]
    simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hj₆ .scan (by decide), hc₅]
    simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hj₄ .scan (by decide) (by decide), hc₃]
    simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hj₂ .scan (by decide) (by decide), hc₁]
    simp [Act.run, hs]
  · refine ⟨addBits l [true], ?_, ?_, ?_⟩
    · rw [hcnt₁₁, List.reverse_reverse, hj₁₀ .cnt (by decide) (by decide), hcnt₉]
    · rw [ofBits_addBits, hlv]; simp
    · simp only [List.length_append, List.length_singleton]; omega
  · rw [hj₁₁ .work (by decide) (by decide), hj₁₀ .work (by decide) (by decide),
      hj₉ .work (by decide) (by decide), hw₈, hc₇]
    simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hj₆ .work (by decide), hc₅]
    simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hj₄ .work (by decide) (by decide), hc₃]
    simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hw₂]
  · intro j hjh hjc hjw
    by_cases hj0 : j = .t0
    · subst hj0
      rw [ht0₁₁, hj₉ .t0 (by decide) (by decide), hj₈ .t0 (by decide), hc₇]
      simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
      rw [hj₆ .t0 (by decide), hc₅]
      simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
      rw [ht₄]
    by_cases hj2 : j = .t2
    · subst hj2
      rw [hj₁₁ .t2 (by decide) (by decide), ht₁₀, hj₈ .t2 (by decide), hc₇]
      simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
      rw [hj₆ .t2 (by decide), hc₅]
      simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
      rw [hj₄ .t2 (by decide) (by decide), hc₃]
      simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
      rw [hj₂ .t2 (by decide) (by decide), hc₁]
      simp only [Act.run, ne_eq, reduceCtorEq, not_false_eq_true, update_of_ne]
    rw [hj₁₁ j hj0 hjc, hj₁₀ j hj2 hj0, hj₉ j hjc hj2, hj₈ j hjw, hc₇]
    simp only [Act.run]
    rw [update_of_ne hjh, hj₆ j hjh, hc₅]
    simp only [Act.run]
    rw [update_of_ne hjh, hj₄ j hj0 hjh, hc₃]
    simp only [Act.run]
    rw [update_of_ne hjh, hj₂ j hjw hj0, hc₁]
    simp only [Act.run]
    rw [update_of_ne hj0]

end GraphIso.TM
