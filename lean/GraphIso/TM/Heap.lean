module

public import GraphIso.TM.Arith

/-!
# The heap

Stage 17c (`PLAN-17.md` §6). The simulator keeps values in an append-only heap of cells on the
stack `heap`, newest on top.

* **Stacks** `Stk`: the input and output, the heap and its scan stack, the allocation counter,
  the work stack, the pointer stack, the environment and loop stacks, and temporaries.
* **Cells** `Cell`: an address (a number), a tag and a list of fields (numbers: addresses of
  other cells, or the bits of a natural). On the stack a cell is
  `mk 1 :: addr ++ nd :: tag :: f₁ ++ nd :: … :: fₖ ++ nd :: [mk 0]` (`encCell`), and a heap
  `h` (oldest first) is `encHeap h`, newest cell on top. In a well-formed heap the cell at index
  `i` has address `i` (`HeapWF`).
* **`moveSeg2 s a b d`**: moves a segment onto two stacks (`moveSeg2_sat`).

Lookup is in `Lookup.lean`, allocation in `Alloc.lean`, the representation of values in
`Rep.lean`.
-/

@[expose] public section

namespace GraphIso.TM

open Function

/-- The simulator's stacks. -/
inductive Stk where
  | inp | out | heap | scan | cnt | work | ptr | env | lst | t0 | t1 | t2 | t3 | t4
  deriving DecidableEq, Repr

instance : Fintype Stk where
  elems := [.inp, .out, .heap, .scan, .cnt, .work, .ptr, .env, .lst, .t0, .t1, .t2, .t3,
    .t4].toFinset
  complete x := by cases x <;> decide

variable {K P : Type} [DecidableEq K] {prog : Program K Sym Rg P}

/-! ### Moving a segment onto two stacks -/

/-- Move the symbols of `a` up to and including the first `s` onto both `b` and `d`. -/
def moveSeg2 (s : Sym) (a b d : K) : Code K Sym Rg P :=
  .seq (.act (.pop a 0))
    (.seq (.act (.pushReg b 0))
      (.seq (.act (.pushReg d 0))
        (.seq (.loop (.not (.is 0 (some s)))
            (.seq (.act (.pop a 0)) (.seq (.act (.pushReg b 0)) (.act (.pushReg d 0)))))
          (.act (.set 0 none)))))

theorem moveSeg2_sat {s : Sym} {a b d : K} (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    {c : Cfg K Sym Rg} {w rest : List Sym} (hw : s ∉ w) (hv : c.regs = Regs.empty)
    (ha : c.stk a = w ++ s :: rest) :
    Sat prog (moveSeg2 s a b d) c (6 * w.length + 10) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ c'.stk b = s :: w.reverse ++ c.stk b ∧
        c'.stk d = s :: w.reverse ++ c.stk d ∧
          ∀ j, j ≠ a → j ≠ b → j ≠ d → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := .not (.is 0 (some s)))
    (x := .seq (.act (.pop a 0)) (.seq (.act (.pushReg b 0)) (.act (.pushReg d 0)))) (t := 5)
    (I := fun m c₁ => ∃ w₁ x w₂, w₁ ++ x :: w₂ = w ++ [s] ∧ w₂.length = m ∧
      c₁.regs = rv (some x) none none none ∧ c₁.stk a = w₂ ++ rest ∧
      c₁.stk b = x :: w₁.reverse ++ c.stk b ∧ c₁.stk d = x :: w₁.reverse ++ c.stk d ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ d → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some s) none none none ∧ c₁.stk a = rest ∧
      c₁.stk b = s :: w.reverse ++ c.stk b ∧ c₁.stk d = s :: w.reverse ++ c.stk d ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ d → c₁.stk j = c.stk j)
    (fun m c₁ ⟨w₁, x, w₂, hl, hlen, hr, ha₁, hb₁, hd₁, hj₁⟩ => by
      obtain ⟨y, w₂, rfl⟩ : ∃ y w₂', w₂ = y :: w₂' := by
        cases w₂ with
        | nil => simp at hlen
        | cons y w₂' => exact ⟨y, w₂', rfl⟩
      have hx : x ≠ s := fun h => List.cons_ne_nil _ _ ((eq_last_iff hw hl).1 h)
      refine ⟨by simp [Cond.eval, hr, hx], ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_le (by omega) ?_))
      refine ⟨w₁ ++ [x], y, w₂, by simp [← hl], by simpa using hlen, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Act.run, ha₁, hr]
      · simp [Act.run, ha₁, update_of_ne hab, update_of_ne had]
      · simp [Act.run, ha₁, hb₁, update_of_ne (Ne.symm hab), update_of_ne hbd]
      · simp [Act.run, ha₁, hd₁, update_of_ne (Ne.symm had), update_of_ne (Ne.symm hbd)]
      · intro j hja hjb hjd
        simp [Act.run, update_of_ne hja, update_of_ne hjb, update_of_ne hjd, hj₁ j hja hjb hjd])
    (fun c₁ ⟨w₁, x, w₂, hl, hlen, hr, ha₁, hb₁, hd₁, hj₁⟩ => by
      obtain rfl : w₂ = [] := List.eq_nil_of_length_eq_zero hlen
      have hxs : x = s := (eq_last_iff hw hl).2 rfl
      subst hxs
      have hw₁ : w₁ = w := (List.append_inj' hl rfl).1
      subst hw₁
      exact ⟨by simp [Cond.eval, hr], hr, by simpa using ha₁, hb₁, hd₁, hj₁⟩)
  obtain ⟨x, w₂, hx⟩ : ∃ x w₂, w ++ [s] = x :: w₂ := by cases w <;> simp
  have h₁ : c.stk a = x :: (w₂ ++ rest) := by rw [ha, ← List.cons_append, ← hx]; simp
  unfold moveSeg2
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega)
    (Sat.seq_le (hloop w.length _ ⟨[], x, w₂, by simp [hx], ?_, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hb₃, hd₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_, ?_⟩)))
  · have := congrArg List.length hx; simp at this; omega
  · simp [Act.run, hv, h₁]
  · simp [Act.run, h₁, update_of_ne hab, update_of_ne had]
  · simp [Act.run, h₁, update_of_ne (Ne.symm hab), update_of_ne hbd]
  · simp [Act.run, h₁, update_of_ne (Ne.symm had), update_of_ne (Ne.symm hbd)]
  · intro j hja hjb hjd; simp [Act.run, update_of_ne hja, update_of_ne hjb, update_of_ne hjd]
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃]
  · simp [Act.run, hb₃]
  · simp [Act.run, hd₃]
  · intro j hja hjb hjd; simp [Act.run, hj₃ j hja hjb hjd]

/-! ### Cells and heaps -/

/-- A heap cell: its address, its tag and its fields. -/
structure Cell where
  /-- The address. -/
  addr : List Bool
  /-- The tag. -/
  tag : Tag
  /-- The fields: addresses of cells, or the bits of a natural. -/
  fields : List (List Bool)

/-- The fields of a cell, each a number. -/
def encFields : List (List Bool) → List Sym
  | [] => []
  | f :: fs => bits f ++ .nd :: encFields fs

/-- A cell without its end marker `mk 0`. -/
def cellBody (c : Cell) : List Sym :=
  .mk 1 :: bits c.addr ++ .nd :: .tag c.tag :: encFields c.fields

/-- A cell on the stack. -/
def encCell (c : Cell) : List Sym := cellBody c ++ [.mk 0]

/-- A heap (oldest cell first) on the stack, newest cell on top. -/
def encHeap (h : List Cell) : List Sym := (h.reverse.map encCell).flatten

/-- The cells moved to the scan stack, each reversed, the oldest on top. -/
def encScan (h : List Cell) : List Sym := (h.map fun c => (encCell c).reverse).flatten

/-- The cell at index `i` has address `i`. -/
def HeapWF (h : List Cell) : Prop := ∀ i (hi : i < h.length), ofBits h[i].addr = i

theorem mk_not_mem_bits (i : Fin 4) (l : List Bool) : Sym.mk i ∉ bits l := by
  simp [bits]

theorem mk_not_mem_encFields (i : Fin 4) : ∀ fs : List (List Bool), Sym.mk i ∉ encFields fs
  | [] => by simp [encFields]
  | f :: fs => by simp [encFields, bits, mk_not_mem_encFields i fs]

theorem mk0_not_mem_cellBody (c : Cell) : Sym.mk 0 ∉ cellBody c := by
  simp [cellBody, bits, mk_not_mem_encFields]

/-- The reversed cell, as `moveSeg (mk 1)` reads it. -/
theorem encCell_reverse (c : Cell) :
    (encCell c).reverse =
      (.mk 0 :: (bits c.addr ++ .nd :: .tag c.tag :: encFields c.fields).reverse) ++ [.mk 1] := by
  simp [encCell, cellBody]

theorem mk1_not_mem_reverse (c : Cell) :
    Sym.mk 1 ∉ .mk 0 :: (bits c.addr ++ .nd :: .tag c.tag :: encFields c.fields).reverse := by
  simp [bits, mk_not_mem_encFields]

theorem encHeap_append (h : List Cell) (c : Cell) :
    encHeap (h ++ [c]) = encCell c ++ encHeap h := by
  simp [encHeap]

theorem encHeap_cons (c : Cell) (h : List Cell) : encHeap (c :: h) = encHeap h ++ encCell c := by
  simp [encHeap]

theorem encHeap_take_succ (h : List Cell) (j : ℕ) (hj : j < h.length) :
    encHeap (h.take (j + 1)) = encCell h[j] ++ encHeap (h.take j) := by
  rw [List.take_succ_eq_append_getElem hj, encHeap_append]

theorem encScan_drop (h : List Cell) (j : ℕ) (hj : j < h.length) :
    encScan (h.drop j) = (encCell h[j]).reverse ++ encScan (h.drop (j + 1)) := by
  rw [List.drop_eq_getElem_cons hj]
  simp only [encScan, List.map_cons, List.flatten_cons]

theorem length_encHeap (h : List Cell) :
    (encHeap h).length = (h.map fun c => (encCell c).length).sum := by
  induction h with
  | nil => simp [encHeap]
  | cons c h ih =>
    simp only [encHeap_cons, List.length_append, ih, List.map_cons, List.sum_cons]
    omega

theorem one_le_length_encCell (c : Cell) : 1 ≤ (encCell c).length := by
  simp [encCell]

theorem le_sum_of_mem_nat {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := ih hx
      omega

theorem length_encCell_le (h : List Cell) (j : ℕ) (hj : j < h.length) :
    (encCell h[j]).length ≤ (encHeap h).length := by
  rw [length_encHeap]
  exact le_sum_of_mem_nat (List.mem_map.2 ⟨h[j], List.getElem_mem hj, rfl⟩)

theorem length_le_encHeap (h : List Cell) : h.length ≤ (encHeap h).length := by
  rw [length_encHeap]
  induction h with
  | nil => simp
  | cons c h ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := one_le_length_encCell c
    omega

theorem length_addr_lt (c : Cell) : c.addr.length < (encCell c).length := by
  simp [encCell, cellBody]
  omega

theorem length_cellBody (c : Cell) : (cellBody c).length + 1 = (encCell c).length := by
  simp [encCell]

end GraphIso.TM
