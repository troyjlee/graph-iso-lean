module

public import GraphIso.TM.Heap

/-!
# Lookup in the heap

Stage 17c (`PLAN-17.md` §6).

* **`addrTest`** (`addrTest_sat`): compares the address of the top cell of `heap` with the
  pointer on `ptr` and leaves the bit in register `3`; every stack is as it was.
* **`lookup`** (`lookup_sat`): for a well-formed heap `h` on `heap`, an empty `scan` and a
  pointer `p` on `ptr` with `ofBits p < h.length`, pushes a copy of the cell `h[ofBits p]` onto
  `work`, consumes the pointer, and leaves every other stack as it was. It moves the cells above
  the target to `scan` (testing each address), copies the target onto `heap` and `work`, and moves
  the scanned cells back. The step bound `lookupBound N lp` (`N` the heap's length in symbols,
  `lp` the pointer's length) is at most `50 (N + lp + 3)²` (`lookupBound_le`).
-/

@[expose] public section

namespace GraphIso.TM

open Function

variable {P : Type} {prog : Program Stk Sym Rg P}

/-! ### Lookup -/

/-- Compare the address of the top cell of `heap` with the pointer on `ptr`; register `3` gets
the bit. -/
def addrTest : Code Stk Sym Rg P :=
  .seq (.act (.pop .heap 0))
    (.seq (.act (.set 0 none))
      (.seq (copyNum .heap .t0 .t3)
        (.seq (.act (.push .heap (.mk 1)))
          (.seq (copyNum .ptr .t1 .t3)
            (.seq (eqNum .t0 .t1 .t2 .t3) (.act (.pop .t2 3)))))))

theorem addrTest_sat {c : Cfg Stk Sym Rg} {cl : Cell} {rest : List Sym} {p : List Bool}
    {rp : List Sym} (hv : c.regs = Regs.empty) (hh : c.stk .heap = encCell cl ++ rest)
    (hp : c.stk .ptr = bits p ++ .nd :: rp) :
    Sat prog addrTest c (33 * (cl.addr.length + p.length) + 86) fun c' =>
      c'.regs = rv none none none (some (.bit (decide (ofBits cl.addr = ofBits p)))) ∧
        ∀ j, c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv
  unfold addrTest
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  set c₁ := Act.run (.set 0 none) (Act.run (.pop .heap 0) c) with hc₁
  have hv₁ : c₁.regs = Regs.empty := by simp [hc₁, Act.run, hv, empty_eq_rv]
  have hh₁ : c₁.stk .heap =
      bits cl.addr ++ .nd :: (.tag cl.tag :: encFields cl.fields ++ [.mk 0] ++ rest) := by
    simp [hc₁, Act.run, hh, encCell, cellBody]
  have hj₁ : ∀ j, j ≠ .heap → c₁.stk j = c.stk j := by
    intro j hj; simp [hc₁, Act.run, update_of_ne hj]
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hv₁ hh₁) (by omega)
    fun c₂ ⟨hr₂, ht₂, hj₂⟩ => ?_
  refine Sat.act_seq (by omega) ?_
  set c₃ := Act.run (.push .heap (.mk 1)) c₂ with hc₃
  have hp₃ : c₃.stk .ptr = bits p ++ .nd :: rp := by
    simp [hc₃, Act.run, hj₂, hj₁, hp]
  have hv₃ : c₃.regs = Regs.empty := hr₂
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hv₃ hp₃) (by omega)
    fun c₄ ⟨hr₄, ht₄, hj₄⟩ => ?_
  have ht0₄ : c₄.stk .t0 = bits cl.addr ++ .nd :: c.stk .t0 := by
    rw [hj₄ .t0 (by decide)]
    simp [hc₃, Act.run, ht₂, hj₁ .t0 (by decide)]
  refine Sat.seq_le (eqNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hr₄ ht0₄ ht₄) (by omega) fun c₅ ⟨hr₅, h0₅, h1₅, h2₅, hj₅⟩ => ?_
  refine Sat.act_le (by omega) ⟨?_, fun j => ?_⟩
  · rw [empty_eq_rv] at hr₅
    simp [Act.run, hr₅, h2₅]
  · cases j <;> simp [Act.run, hc₃, hc₁, h0₅, h1₅, h2₅, hj₅, hj₄, hj₂, hh, encCell, cellBody]

/-- Look up the cell at the pointer on `ptr`: push a copy of it onto `work` and consume the
pointer. -/
def lookup : Code Stk Sym Rg P :=
  .seq addrTest
    (.seq (.loop (.not (.is 3 (some (.bit true))))
        (.seq (.act (.set 3 none)) (.seq (moveSeg (.mk 0) .heap .scan) addrTest)))
      (.seq (.act (.set 3 none))
        (.seq (moveSeg (.mk 0) .heap .scan)
          (.seq (moveSeg2 (.mk 1) .scan .heap .work)
            (.seq (.act (.peek .scan 3))
              (.seq (.loop (.not (.is 3 none))
                  (.seq (.act (.set 3 none))
                    (.seq (moveSeg (.mk 1) .scan .heap) (.act (.peek .scan 3)))))
                (.seq (.act (.set 3 none)) (dropNum .ptr))))))))

/-- The step bound of `lookup` for a heap of `N` symbols and a pointer of `lp` bits. -/
def lookupBound (N lp : ℕ) : ℕ :=
  N * (37 * N + 33 * lp + 97) + N * (4 * N + 13) + 50 * N + 40 * lp + 150

theorem lookupBound_le (N lp : ℕ) : lookupBound N lp ≤ 50 * (N + lp + 3) ^ 2 := by
  unfold lookupBound
  nlinarith

theorem lookup_sat {h : List Cell} (hwf : HeapWF h) {c : Cfg Stk Sym Rg} {p : List Bool}
    {rp : List Sym} (hv : c.regs = Regs.empty) (hh : c.stk .heap = encHeap h)
    (hs : c.stk .scan = []) (hp : c.stk .ptr = bits p ++ .nd :: rp)
    (hi : ofBits p < h.length) :
    Sat prog lookup c (lookupBound (encHeap h).length p.length) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = encCell h[ofBits p] ++ c.stk .work ∧
        c'.stk .ptr = rp ∧ ∀ j, j ≠ .work → j ≠ .ptr → c'.stk j = c.stk j := by
  set i := ofBits p with hi_def
  set N := (encHeap h).length with hN
  set n := h.length with hn
  set lp := p.length with hlp
  have hnN : n ≤ N := length_le_encHeap h
  have hcell : ∀ j (hj : j < n), (encCell h[j]).length ≤ N := fun j hj => length_encCell_le h j hj
  have hloop₁ := Sat.loop (prog := prog) (b := .not (.is 3 (some (.bit true))))
    (x := .seq (.act (.set 3 none)) (.seq (moveSeg (.mk 0) .heap .scan) addrTest))
    (t := 37 * N + 33 * lp + 96)
    (I := fun m c₁ => c₁.regs = rv none none none (some (.bit (decide (m = 0)))) ∧
      i + m < n ∧ c₁.stk .heap = encHeap (h.take (i + m + 1)) ∧
      c₁.stk .scan = encScan (h.drop (i + m + 1)) ∧
      ∀ j, j ≠ .heap → j ≠ .scan → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv none none none (some (.bit true)) ∧
      c₁.stk .heap = encHeap (h.take (i + 1)) ∧ c₁.stk .scan = encScan (h.drop (i + 1)) ∧
      ∀ j, j ≠ .heap → j ≠ .scan → c₁.stk j = c.stk j)
    (fun m c₁ ⟨hr, hlt, hh₁, hs₁, hj₁⟩ => by
      have e : i + (m + 1) + 1 = i + m + 1 + 1 := by omega
      rw [e] at hh₁ hs₁
      have hlt' : i + m + 1 < n := by omega
      refine ⟨by simp [Cond.eval, hr], ?_⟩
      refine Sat.act_seq (by omega) ?_
      have hv₂ : (Act.run (.set 3 none) c₁).regs = Regs.empty := by
        simp [Act.run, hr, empty_eq_rv]
      have hh₂ : (Act.run (.set 3 none) c₁).stk .heap =
          cellBody h[i + m + 1] ++ .mk 0 :: encHeap (h.take (i + m + 1)) := by
        simp only [Act.run]
        rw [hh₁, encHeap_take_succ h (i + m + 1) hlt']
        simp [encCell]
      have hb := length_cellBody h[i + m + 1]
      have hc₁ := hcell (i + m + 1) hlt'
      refine Sat.seq_le (moveSeg_sat (by decide) (mk0_not_mem_cellBody _) hv₂ hh₂) (by omega)
        fun c₃ ⟨hr₃, hh₃, hs₃, hj₃⟩ => ?_
      have hh₃' : c₃.stk .heap = encCell h[i + m] ++ encHeap (h.take (i + m)) := by
        rw [hh₃, ← encHeap_take_succ h (i + m) (by omega)]
      have hp₃ : c₃.stk .ptr = bits p ++ .nd :: rp := by
        rw [hj₃ .ptr (by decide) (by decide)]
        simp [Act.run, hj₁ .ptr (by decide) (by decide), hp]
      have ha := length_addr_lt h[i + m]
      have hc₂ := hcell (i + m) (by omega)
      refine (addrTest_sat hr₃ hh₃' hp₃).mono (by omega) fun c₄ ⟨hr₄, hj₄⟩ =>
        ⟨?_, by omega, ?_, ?_, ?_⟩
      · have e : (i + m = ofBits p) ↔ m = 0 := by omega
        rw [hr₄, hwf (i + m) (by omega)]
        simp only [e]
      · rw [hj₄, hh₃]
      · rw [hj₄, hs₃]
        simp only [Act.run]
        rw [hs₁, encScan_drop h (i + m + 1) hlt', encCell_reverse]
        simp [cellBody]
      · intro j hjh hjs
        rw [hj₄, hj₃ j hjh hjs]
        simp [Act.run, hj₁ j hjh hjs])
    (fun c₁ ⟨hr, hlt, hh₁, hs₁, hj₁⟩ =>
      ⟨by simp [Cond.eval, hr], by simpa using hr, by simpa using hh₁, by simpa using hs₁, hj₁⟩)
  -- the first test, at the top cell `n - 1`
  have hn1 : 0 < n := by omega
  have hh₀ : c.stk .heap = encCell h[n - 1] ++ encHeap (h.take (n - 1)) := by
    rw [hh, ← encHeap_take_succ h (n - 1) (by omega), Nat.sub_add_cancel hn1, List.take_length]
  have ha₀ := length_addr_lt h[n - 1]
  have hc₀ := hcell (n - 1) (by omega)
  unfold lookup
  refine Sat.seq_le (addrTest_sat hv hh₀ hp) (by unfold lookupBound; omega)
    fun c₁ ⟨hr₁, hj₁⟩ => ?_
  have hI₁ : c₁.regs = rv none none none (some (.bit (decide (n - 1 - i = 0)))) ∧
      i + (n - 1 - i) < n ∧ c₁.stk .heap = encHeap (h.take (i + (n - 1 - i) + 1)) ∧
      c₁.stk .scan = encScan (h.drop (i + (n - 1 - i) + 1)) ∧
      ∀ j, j ≠ .heap → j ≠ .scan → c₁.stk j = c.stk j := by
    have e : i + (n - 1 - i) + 1 = n := by omega
    refine ⟨?_, by omega, ?_, ?_, fun j _ _ => hj₁ j⟩
    · have e' : (n - 1 = ofBits p) ↔ n - 1 - i = 0 := by omega
      rw [hr₁, hwf (n - 1) (by omega)]
      simp only [e']
    · rw [e, hj₁, hh, List.take_length]
    · rw [e, hj₁, hs, List.drop_length]; rfl
  have hk₁ : (n - 1 - i) * (37 * N + 33 * lp + 96 + 1) ≤ N * (37 * N + 33 * lp + 97) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine Sat.seq_le (hloop₁ (n - 1 - i) c₁ hI₁) (by unfold lookupBound; omega)
    fun c₂ ⟨hr₂, hh₂, hs₂, hj₂⟩ => ?_
  refine Sat.act_seq (by unfold lookupBound; omega) ?_
  -- move the target cell to `scan`, then onto `heap` and `work`
  have hv₃ : (Act.run (.set 3 none) c₂).regs = Regs.empty := by
    simp [Act.run, hr₂, empty_eq_rv]
  have hh₃ : (Act.run (.set 3 none) c₂).stk .heap =
      cellBody h[i] ++ .mk 0 :: encHeap (h.take i) := by
    simp only [Act.run]
    rw [hh₂, encHeap_take_succ h i hi]
    simp [encCell]
  have hb₃ := length_cellBody h[i]
  have hci := hcell i hi
  refine Sat.seq_le (moveSeg_sat (by decide) (mk0_not_mem_cellBody _) hv₃ hh₃)
    (by unfold lookupBound; omega) fun c₄ ⟨hr₄, hh₄, hs₄, hj₄⟩ => ?_
  have hs₄' : c₄.stk .scan = (.mk 0 :: (bits h[i].addr ++ .nd :: .tag h[i].tag ::
      encFields h[i].fields).reverse) ++ .mk 1 :: encScan (h.drop (i + 1)) := by
    rw [hs₄]
    simp [Act.run, hs₂, cellBody]
  have hw₄ : (.mk 0 :: (bits h[i].addr ++ .nd :: .tag h[i].tag ::
      encFields h[i].fields).reverse).length + 1 = (encCell h[i]).length := by
    simp [encCell, cellBody]; omega
  refine Sat.seq_le (moveSeg2_sat (by decide) (by decide) (by decide) (mk1_not_mem_reverse _)
    hr₄ hs₄') (by unfold lookupBound; omega) fun c₅ ⟨hr₅, hs₅, hh₅, hw₅, hj₅⟩ => ?_
  have hcopy : ∀ rest : List Sym, Sym.mk 1 :: (Sym.mk 0 :: (bits h[i].addr ++ .nd ::
      .tag h[i].tag :: encFields h[i].fields).reverse).reverse ++ rest = encCell h[i] ++ rest := by
    intro rest; simp [encCell, cellBody]
  refine Sat.act_seq (by unfold lookupBound; omega) ?_
  -- move the scanned cells back
  set c₆ := Act.run (.peek .scan 3) c₅ with hc₆
  have hloop₂ := Sat.loop (prog := prog) (b := .not (.is 3 none))
    (x := .seq (.act (.set 3 none)) (.seq (moveSeg (.mk 1) .scan .heap) (.act (.peek .scan 3))))
    (t := 4 * N + 12)
    (I := fun m c₇ => c₇.regs = rv none none none (c₇.stk .scan).head? ∧ m + i + 1 ≤ n ∧
      c₇.stk .heap = encHeap (h.take (n - m)) ∧ c₇.stk .scan = encScan (h.drop (n - m)) ∧
      ∀ j, j ≠ .heap → j ≠ .scan → c₇.stk j = c₆.stk j)
    (Q := fun c₇ => c₇.regs = rv none none none none ∧ c₇.stk .heap = encHeap h ∧
      c₇.stk .scan = [] ∧ ∀ j, j ≠ .heap → j ≠ .scan → c₇.stk j = c₆.stk j)
    (fun m c₇ ⟨hr, hle, hh₇, hs₇, hj₇⟩ => by
      have hj : n - (m + 1) < n := by omega
      rw [encScan_drop h _ hj, encCell_reverse] at hs₇
      refine ⟨by simp [Cond.eval, hr, hs₇], ?_⟩
      refine Sat.act_seq (by omega) ?_
      have hv₈ : (Act.run (.set 3 none) c₇).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hr, hs₇]
      have hs₈ : (Act.run (.set 3 none) c₇).stk .scan = (.mk 0 :: (bits h[n - (m + 1)].addr ++
          .nd :: .tag h[n - (m + 1)].tag :: encFields h[n - (m + 1)].fields).reverse) ++
          .mk 1 :: encScan (h.drop (n - (m + 1) + 1)) := by
        simp [Act.run, hs₇]
      have hw := length_cellBody h[n - (m + 1)]
      have hc := hcell (n - (m + 1)) hj
      have hw' : (.mk 0 :: (bits h[n - (m + 1)].addr ++ .nd :: .tag h[n - (m + 1)].tag ::
          encFields h[n - (m + 1)].fields).reverse).length + 1 =
          (encCell h[n - (m + 1)]).length := by
        simp [encCell, cellBody]; omega
      refine Sat.seq_le (moveSeg_sat (by decide) (mk1_not_mem_reverse _) hv₈ hs₈) (by omega)
        fun c₉ ⟨hr₉, hs₉, hh₉, hj₉⟩ => Sat.act_le (by omega) ⟨?_, by omega, ?_, ?_, ?_⟩
      · simp [Act.run, hr₉, empty_eq_rv]
      · have e : n - m = n - (m + 1) + 1 := by omega
        simp only [Act.run]
        rw [hh₉, e, encHeap_take_succ h _ hj]
        simp [Act.run, hh₇, encCell, cellBody]
      · have e : n - m = n - (m + 1) + 1 := by omega
        simp only [Act.run]
        rw [hs₉, e]
      · intro j hjh hjs
        simp only [Act.run]
        rw [hj₉ j hjs hjh]
        simp [Act.run, hj₇ j hjh hjs])
    (fun c₇ ⟨hr, hle, hh₇, hs₇, hj₇⟩ => by
      rw [Nat.sub_zero, hn, List.take_length] at hh₇
      rw [Nat.sub_zero, hn, List.drop_length] at hs₇
      have hs₇' : c₇.stk .scan = [] := by rw [hs₇]; rfl
      exact ⟨by simp [Cond.eval, hr, hs₇'], by simp [hr, hs₇'], hh₇, hs₇', hj₇⟩)
  have hI₂ : c₆.regs = rv none none none (c₆.stk .scan).head? ∧ (n - (i + 1)) + i + 1 ≤ n ∧
      c₆.stk .heap = encHeap (h.take (n - (n - (i + 1)))) ∧
      c₆.stk .scan = encScan (h.drop (n - (n - (i + 1)))) ∧
      ∀ j, j ≠ .heap → j ≠ .scan → c₆.stk j = c₆.stk j := by
    have e : n - (n - (i + 1)) = i + 1 := by omega
    refine ⟨?_, by omega, ?_, ?_, fun _ _ _ => rfl⟩
    · simp [hc₆, Act.run, hr₅, empty_eq_rv]
    · rw [e, hc₆]
      simp only [Act.run]
      rw [hh₅, hh₄, hcopy, encHeap_take_succ h i hi]
    · rw [e, hc₆]
      simp only [Act.run]
      rw [hs₅]
  have hk₂ : (n - (i + 1)) * (4 * N + 12 + 1) ≤ N * (4 * N + 13) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine Sat.seq_le (hloop₂ (n - (i + 1)) c₆ hI₂) (by unfold lookupBound; omega)
    fun c₇ ⟨hr₇, hh₇, hs₇, hj₇⟩ => ?_
  refine Sat.act_seq (by unfold lookupBound; omega) ?_
  have hv₈ : (Act.run (.set 3 none) c₇).regs = Regs.empty := by
    simp [Act.run, hr₇, empty_eq_rv]
  have hp₈ : (Act.run (.set 3 none) c₇).stk .ptr = bits p ++ .nd :: rp := by
    simp only [Act.run]
    rw [hj₇ .ptr (by decide) (by decide), hc₆]
    simp only [Act.run]
    rw [hj₅ .ptr (by decide) (by decide) (by decide), hj₄ .ptr (by decide) (by decide)]
    simp [Act.run, hj₂ .ptr (by decide) (by decide), hp]
  refine (dropNum_sat hv₈ hp₈).mono (by unfold lookupBound; omega)
    fun c₉ ⟨hr₉, hp₉, hj₉⟩ => ⟨hr₉, ?_, hp₉, ?_⟩
  · rw [hj₉ .work (by decide)]
    simp only [Act.run]
    rw [hj₇ .work (by decide) (by decide), hc₆]
    simp only [Act.run]
    rw [hw₅, hcopy, hj₄ .work (by decide) (by decide)]
    simp [Act.run, hj₂ .work (by decide) (by decide)]
    rfl
  · intro j hjw hjp
    rw [hj₉ j hjp]
    simp only [Act.run]
    by_cases hjh : j = .heap
    · subst hjh; rw [hh₇, hh]
    by_cases hjs : j = .scan
    · subst hjs; rw [hs₇, hs]
    rw [hj₇ j hjh hjs, hc₆]
    simp only [Act.run]
    rw [hj₅ j hjs hjh hjw, hj₄ j hjh hjs]
    simp [Act.run, hj₂ j hjh hjs]

end GraphIso.TM
