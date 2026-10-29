module

public import GraphIso.TM.Load
public import Mathlib.Data.List.TakeWhile

/-!
# Writing the output

Stage 17d (`PLAN-17.md` §7). `write t` takes a pointer `p` on `ptr` to a representation of
`v : t.denote` and pushes `ser t v` onto `out` (so that `out` then reads `ser t v` from the
top). The heap is only read.

* **`WriteSpec a wr`**: assume a well-formed heap `h` on `heap`, `scan` empty, empty registers,
  and `bits p ++ nd :: rp` on `ptr` with `Rep h a v (ofBits p)` and `p.length ≤ N`, where `N` is
  the length of `encHeap h`. Then `wr` runs within `wrB a v N` steps to a configuration with
  empty registers, `ser a v` pushed onto `out`, `rp` on `ptr`, and every other stack unchanged.
* **`write_sat t`**: `write t` meets `WriteSpec t` for every type `t`.
* **Bounds**: `wrB_le`, `wrB t v N ≤ wt t * (L + 1) * visB N` with `L = (ser t v).length`, where
  `visB N` (a lookup and work quadratic in `N`) bounds the visit of one cell.

Symbols are pushed last first: the components of a pair in reverse order; the tag `nil` of a
list before its elements, last element first (the elements' pointers are collected on `ptr`
while the list is traversed); the elements of an array first to last (`ser` lists them in
reverse). A natural is written canonically, whatever the length of its field: its leading zero
bits are dropped (`strip_eq_toBits`).

Routines: `moveNum2` moves a number keeping the order of its bits; `xferNums i` moves the
numbers down to the marker `mk i`; `fetchCell` looks up a cell and opens it (its tag in
register `1`, its fields on `work`), `closeCell` drops its end marker; `writeElems` writes the
elements whose pointers are on `ptr`.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost Function

variable {P : Type}

/-! ### Canonical bits -/

/-- A bit list without its trailing `false` bits (the leading zeros of the number). -/
def strip (l : List Bool) : List Bool := (l.reverse.dropWhile (· == false)).reverse

/-! ### Moving numbers -/

section Generic

variable {K : Type} [DecidableEq K]

/-- Move a number from `a` to `b` through `t`, keeping the order of its bits. -/
def moveNum2 (a b t : K) : Code K Sym Rg P := .seq (moveBits a t) (moveBits t b)

/-- Move the numbers of `a` down to the marker `mk i` onto `b` (each reversed, in reverse order),
and drop the marker. -/
def xferNums (i : Fin 4) (a b : K) : Code K Sym Rg P :=
  .seq (.act (.peek a 0))
    (.seq (.loop (.not (.is 0 (some (.mk i))))
        (.seq (.act (.set 0 none)) (.seq (moveBits a b) (.act (.peek a 0)))))
      (.seq (.act (.pop a 0)) (.act (.set 0 none))))

variable {prog : Program K Sym Rg P}

theorem moveNum2_sat {a b t : K} (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) {c : Cfg K Sym Rg}
    {l : List Bool} {rest : List Sym} (hv : c.regs = Regs.empty)
    (ha : c.stk a = bits l ++ .nd :: rest) :
    Sat prog (moveNum2 a b t) c (12 * l.length + 19) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = rest ∧ c'.stk b = bits l ++ .nd :: c.stk b ∧
        ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j := by
  unfold moveNum2
  refine Sat.seq_le (moveBits_sat hat hv ha) (by omega) fun c₁ ⟨hr₁, ha₁, ht₁, hj₁⟩ => ?_
  refine (moveBits_sat (Ne.symm hbt) hr₁ ht₁).mono (by simp; omega)
    fun c₂ ⟨hr₂, ht₂, hb₂, hj₂⟩ => ⟨hr₂, ?_, ?_, ?_⟩
  · rw [hj₂ a hat hab, ha₁]
  · rw [hb₂, List.reverse_reverse, hj₁ b (Ne.symm hab) hbt]
  · intro j hja hjb
    by_cases hjt : j = t
    · subst hjt; exact ht₂
    · rw [hj₂ j hjt hjb, hj₁ j hja hjt]

theorem xferNums_sat {i : Fin 4} {a b : K} (hab : a ≠ b) {c : Cfg K Sym Rg}
    {fs : List (List Bool)}
    {rest : List Sym} (hv : c.regs = Regs.empty) (ha : c.stk a = encFields fs ++ .mk i :: rest) :
    Sat prog (xferNums i a b) c ((encFields fs).length * (6 * (encFields fs).length + 14) + 8)
      fun c' => c'.regs = Regs.empty ∧ c'.stk a = rest ∧
        c'.stk b = encFields (fs.reverse.map List.reverse) ++ c.stk b ∧
        ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  set L := (encFields fs).length with hL
  have hloop := Sat.loop (prog := prog) (b := .not (.is 0 (some (.mk i))))
    (x := .seq (.act (.set 0 none)) (.seq (moveBits a b) (.act (.peek a 0)))) (t := 6 * L + 13)
    (I := fun m c₁ => ∃ fs₁ fs₂, fs₁ ++ fs₂ = fs ∧ fs₂.length = m ∧
      c₁.regs = rv (c₁.stk a).head? none none none ∧ c₁.stk a = encFields fs₂ ++ .mk i :: rest ∧
      c₁.stk b = encFields (fs₁.reverse.map List.reverse) ++ c.stk b ∧
      ∀ j, j ≠ a → j ≠ b → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some (.mk i)) none none none ∧ c₁.stk a = .mk i :: rest ∧
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
          bits f ++ .nd :: (encFields fs₂ ++ .mk i :: rest) := by
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
  unfold xferNums
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


end Generic

variable {prog : Program Stk Sym Rg P}

/-! ### Cells -/

/-- Open the cell on top of `work`: drop its marker `mk 1` and its address, and pop its tag into
register `1`. -/
def openCell : Code Stk Sym Rg P :=
  .seq (.act (.pop .work 0))
    (.seq (.act (.set 0 none)) (.seq (dropNum .work) (.act (.pop .work 1))))

/-- Look up the cell at the pointer on `ptr` and open it. -/
def fetchCell : Code Stk Sym Rg P := .seq lookup openCell

/-- Drop the end marker `mk 0` of a cell from `work`. -/
def closeCell : Code Stk Sym Rg P := .seq (.act (.pop .work 0)) (.act (.set 0 none))

/-- Write the elements whose pointers are on `ptr` down to the marker `mk 3` with `wa`, each
followed by the tag `cons`; drop the marker. -/
def writeElems (wa : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (.act (.peek .ptr 0))
    (.seq (.loop (.not (.is 0 (some (.mk 3))))
        (.seq (.act (.set 0 none)) (.seq wa (.seq (.act (.push .out (.tag .cons)))
          (.act (.peek .ptr 0))))))
      (.seq (.act (.set 0 none)) (.seq (.act (.pop .ptr 0)) (.act (.set 0 none)))))

/-- Write the value of type `t` at the pointer on top of `ptr` onto `out`. -/
def write : Ty → Code Stk Sym Rg P
  | .unit => dropNum .ptr
  | .bool => .seq fetchCell (.seq closeCell
      (.ite (.is 1 (some (.tag .tt))) (.seq (.act (.set 1 none)) (.act (.push .out (.tag .tt))))
        (.seq (.act (.set 1 none)) (.act (.push .out (.tag .ff))))))
  | .nat => .seq fetchCell (.seq (.act (.set 1 none)) (.seq (moveBits .work .t0)
      (.seq closeCell (.seq (.act (.peek .t0 0)) (.seq (.loop (.is 0 (some (.bit false)))
          (.seq (.act (.set 0 none)) (.seq (.act (.pop .t0 0)) (.seq (.act (.set 0 none))
            (.act (.peek .t0 0))))))
        (.seq (.act (.set 0 none)) (moveBits .t0 .out)))))))
  | .prod a b => .seq fetchCell (.seq (.act (.set 1 none))
      (.seq (moveNum2 .work .ptr .t0) (.seq (moveNum2 .work .ptr .t0) (.seq closeCell
        (.seq (write b) (write a))))))
  | .option a => .seq fetchCell
      (.ite (.is 1 (some (.tag .none)))
        (.seq (.act (.set 1 none)) (.seq closeCell (.act (.push .out (.tag .none)))))
        (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .ptr .t0) (.seq closeCell
          (.seq (write a) (.act (.push .out (.tag .some))))))))
  | .list a => .seq (.act (.push .out (.tag .nil))) (.seq (moveBits .ptr .t2)
      (.seq (.act (.push .ptr (.mk 3))) (.seq (moveBits .t2 .ptr) (.seq fetchCell
        (.seq (.loop (.is 1 (some (.tag .cons)))
            (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .ptr .t0)
              (.seq (moveNum2 .work .ptr .t0) (.seq closeCell fetchCell)))))
          (.seq (.act (.set 1 none)) (.seq closeCell (writeElems (write a)))))))))
  | .array a => .seq fetchCell (.seq (.act (.set 1 none))
      (.seq (.act (.push .t0 (.mk 3))) (.seq (xferNums 0 .work .t0)
        (.seq (.act (.push .ptr (.mk 3))) (.seq (xferNums 3 .t0 .ptr)
          (.seq (.act (.push .out (.tag .nil))) (writeElems (write a))))))))

/-! ### Canonical bits, proofs -/

theorem toBits_eq_nil {n : ℕ} : toBits n = [] ↔ n = 0 := by
  cases n with
  | zero => simp [toBits]
  | succ n => simp [toBits]

theorem toBits_bit {b : Bool} {m : ℕ} (h : b.toNat + 2 * m ≠ 0) :
    toBits (b.toNat + 2 * m) = b :: toBits m := by
  obtain ⟨n, hn⟩ : ∃ n, b.toNat + 2 * m = n + 1 := ⟨b.toNat + 2 * m - 1, by omega⟩
  rw [hn, toBits]
  have h₂ : (n + 1) / 2 = m := by cases b <;> simp at hn <;> omega
  have h₁ : ((n + 1) % 2 == 1) = b := by cases b <;> simp at hn ⊢ <;> omega
  rw [h₁, h₂]

theorem strip_cons_of_ne {b : Bool} {l : List Bool} (h : strip l ≠ []) :
    strip (b :: l) = b :: strip l := by
  unfold strip at h ⊢
  rw [List.reverse_cons, List.dropWhile_append]
  cases hX : l.reverse.dropWhile (· == false) with
  | nil => rw [hX] at h; simp at h
  | cons y ys => simp

theorem strip_cons_of_eq {b : Bool} {l : List Bool} (h : strip l = []) :
    strip (b :: l) = if b then [true] else [] := by
  unfold strip at h ⊢
  have hX : l.reverse.dropWhile (· == false) = [] := by simpa using h
  rw [List.reverse_cons, List.dropWhile_append, hX]
  cases b <;> simp

/-- Dropping the leading zeros gives the canonical bits. -/
theorem strip_eq_toBits : ∀ l : List Bool, strip l = toBits (ofBits l)
  | [] => by simp [strip, toBits]
  | b :: l => by
    have ih := strip_eq_toBits l
    rw [ofBits_cons]
    by_cases hs : strip l = []
    · rw [strip_cons_of_eq hs]
      have hm : ofBits l = 0 := toBits_eq_nil.1 (by rw [← ih]; exact hs)
      rw [hm]
      cases b <;> simp [toBits]
    · rw [strip_cons_of_ne hs, toBits_bit, ih]
      intro h0
      have hm : ofBits l = 0 := by omega
      exact hs (by rw [ih, hm]; simp [toBits])

theorem length_strip_le (l : List Bool) : (strip l).length ≤ l.length := by
  unfold strip
  simpa using (List.dropWhile_suffix (l := l.reverse) (· == false)).length_le

/-! ### Cells, proofs -/

theorem openCell_sat {c : Cfg Stk Sym Rg} {cl : Cell} {w : List Sym}
    (hv : c.regs = Regs.empty) (hw : c.stk .work = encCell cl ++ w) :
    Sat prog openCell c (2 * cl.addr.length + 11) fun c' =>
      c'.regs = rv none (some (.tag cl.tag)) none none ∧
        c'.stk .work = encFields cl.fields ++ .mk 0 :: w ∧ ∀ j, j ≠ .work → c'.stk j = c.stk j := by
  unfold openCell
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have hv₁ : (Act.run (.set 0 none) (Act.run (.pop .work 0) c)).regs = Regs.empty := by
    rw [empty_eq_rv] at hv ⊢; simp [Act.run, hv]
  have hw₁ : (Act.run (.set 0 none) (Act.run (.pop .work 0) c)).stk .work =
      bits cl.addr ++ .nd :: (.tag cl.tag :: (encFields cl.fields ++ .mk 0 :: w)) := by
    simp [Act.run, hw, encCell, cellBody]
  refine Sat.seq_le (dropNum_sat hv₁ hw₁) (by omega) fun c₂ ⟨hr₂, hw₂, hj₂⟩ =>
    Sat.act_le (by omega) ⟨?_, ?_, ?_⟩
  · rw [empty_eq_rv] at hr₂; simp [Act.run, hr₂, hw₂]
  · simp [Act.run, hw₂]
  · intro j hj; simp [Act.run, update_of_ne hj, hj₂ j hj]

theorem closeCell_sat {c : Cfg Stk Sym Rg} {w : List Sym} {r : Option Sym}
    (hv : c.regs = rv none r none none) (hw : c.stk .work = .mk 0 :: w) :
    Sat prog closeCell c 3 fun c' => c'.regs = rv none r none none ∧ c'.stk .work = w ∧
      ∀ j, j ≠ .work → c'.stk j = c.stk j :=
  Sat.act_seq (by omega) (Sat.act_le (by omega)
    ⟨by simp [Act.run, hv, hw], by simp [Act.run, hw],
      fun j hj => by simp [Act.run, update_of_ne hj]⟩)

theorem lookupBound_mono {N lp lp' : ℕ} (h : lp ≤ lp') : lookupBound N lp ≤ lookupBound N lp' := by
  unfold lookupBound
  have := Nat.mul_le_mul_left N (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 33 h) (37 * N)) 97)
  omega

/-- The step bound of `fetchCell` for a heap of `N` symbols. -/
def fcB (N : ℕ) : ℕ := lookupBound N N + 2 * N + 12

theorem fetchCell_sat {h : List Cell} {c : Cfg Stk Sym Rg} {p : List Bool} {rp : List Sym}
    {t : Tag} {fs : List (List Bool)} (hwf : HeapWF h) (hh : c.stk .heap = encHeap h)
    (hs : c.stk .scan = []) (hv : c.regs = Regs.empty) (hc : CellAt h (ofBits p) t fs)
    (hpN : p.length ≤ (encHeap h).length) (hp : c.stk .ptr = bits p ++ .nd :: rp) :
    Sat prog fetchCell c (fcB (encHeap h).length) fun c' =>
      c'.regs = rv none (some (.tag t)) none none ∧
        c'.stk .work = encFields fs ++ .mk 0 :: c.stk .work ∧ c'.stk .ptr = rp ∧
        ∀ j, j ≠ .work → j ≠ .ptr → c'.stk j = c.stk j := by
  obtain ⟨hi, ht, hf⟩ := hc
  have hl := lookupBound_mono (N := (encHeap h).length) hpN
  have ha := length_addr_lt h[ofBits p]
  have hN := length_encCell_le h _ hi
  unfold fetchCell fcB
  refine Sat.seq_le (lookup_sat hwf hv hh hs hp hi) (by omega) fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine (openCell_sat hr₁ hw₁).mono (by omega) fun c' ⟨hr', hw', hj'⟩ =>
    ⟨by rw [hr', ht], by rw [hw', hf], by rw [hj' .ptr (by decide), hp₁], fun j hjw hjp => ?_⟩
  rw [hj' j hjw, hj₁ j hjw hjp]

/-! ### Representations, inverted -/

theorem Rep.unit_inv {h : List Cell} {v : Unit} {p : ℕ} (r : Rep h .unit v p) :
    CellAt h p .unit [] := by
  cases r with
  | unit hc => exact hc

theorem Rep.bool_inv {h : List Cell} {v : Bool} {p : ℕ} (r : Rep h .bool v p) :
    CellAt h p (if v then .tt else .ff) [] := by
  cases r with
  | bool _ hc => exact hc

theorem Rep.pair_inv {h : List Cell} {a b : Ty} {v : (Ty.prod a b).denote} {p : ℕ}
    (r : Rep h (.prod a b) v p) : ∃ l₁ l₂, CellAt h p .pair [l₁, l₂] ∧
      Rep h a v.1 (ofBits l₁) ∧ Rep h b v.2 (ofBits l₂) := by
  cases r with
  | pair hc r₁ r₂ => exact ⟨_, _, hc, r₁, r₂⟩

theorem Rep.none_inv {h : List Cell} {a : Ty} {p : ℕ} (r : Rep h (.option a) Option.none p) :
    CellAt h p .none [] := by
  cases r with
  | none hc => exact hc

theorem Rep.some_inv {h : List Cell} {a : Ty} {x : a.denote} {p : ℕ}
    (r : Rep h (.option a) (Option.some x) p) :
    ∃ l, CellAt h p .some [l] ∧ Rep h a x (ofBits l) := by
  cases r with
  | some hc r₁ => exact ⟨_, hc, r₁⟩

theorem Rep.nil_inv {h : List Cell} {a : Ty} {p : ℕ} (r : Rep h (.list a) [] p) :
    CellAt h p .nil [] := by
  cases r with
  | nil hc => exact hc

theorem Rep.cons_inv {h : List Cell} {a : Ty} {x : a.denote} {xs : List a.denote} {p : ℕ}
    (r : Rep h (.list a) (x :: xs) p) : ∃ l₁ l₂, CellAt h p .cons [l₁, l₂] ∧
      Rep h a x (ofBits l₁) ∧ Rep h (.list a) xs (ofBits l₂) := by
  cases r with
  | cons hc r₁ r₂ => exact ⟨_, _, hc, r₁, r₂⟩

theorem Rep.arr_inv {h : List Cell} {a : Ty} {v : Array a.denote} {p : ℕ}
    (r : Rep h (.array a) v p) : ∃ ls, CellAt h p .arr ls ∧ ls.length = v.size ∧
      ∀ i (hi : i < ls.length) (hv : i < v.size), Rep h a v[i] (ofBits ls[i]) := by
  cases r with
  | arr hc hl hr => exact ⟨_, hc, hl, hr⟩

/-- The fields of a cell are shorter than the heap. -/
theorem length_field_le {h : List Cell} {p : ℕ} {t : Tag} {fs : List (List Bool)}
    (hc : CellAt h p t fs) : (encFields fs).length ≤ (encHeap h).length ∧
      ∀ f ∈ fs, f.length ≤ (encHeap h).length := by
  obtain ⟨hi, _, hf⟩ := hc
  have h₁ := length_encCell_le h p hi
  have h₂ : (encFields fs).length ≤ (encCell h[p]).length := by
    rw [← hf]; simp [encCell, cellBody]; omega
  refine ⟨by omega, fun f hf' => ?_⟩
  have h₃ : f.length ≤ (encFields fs).length := by
    clear h₂ hf
    induction fs with
    | nil => simp at hf'
    | cons g gs ih =>
      rw [length_encFields_cons]
      rcases List.mem_cons.1 hf' with rfl | hg
      · omega
      · have := ih hg; omega
  omega

/-! ### The specification -/

/-- The step bound of visiting one cell: a lookup, moving its fields, and constant work. -/
def visB (N : ℕ) : ℕ := lookupBound N N + 2 * (N * (6 * N + 14)) + 60 * N + 100

theorem fcB_visB (N : ℕ) : fcB N + 58 * N + 88 ≤ visB N := by unfold fcB visB; omega

/-- The step bound of `write` for a heap of `N` symbols. -/
def wrB : (t : Ty) → t.denote → ℕ → ℕ
  | .unit, _, N => 2 * N + 5
  | .bool, _, N => visB N
  | .nat, _, N => visB N
  | .prod a b, v, N => visB N + wrB a v.1 N + wrB b v.2 N
  | .option _, none, N => visB N
  | .option a, some x, N => visB N + wrB a x N
  | .list a, xs, N => (xs.map fun x => wrB a x N + 8 + 1).sum + 9 + (xs.length + 1) * visB N +
      12 * N + 40
  | .array a, v, N => (v.toList.map fun x => wrB a x N + 8 + 1).sum + 9 + visB N

/-- The specification of a writer `wr` for the type `a`: from a pointer `p` on `ptr` to a
representation of `v` in a well-formed heap `h` (on `heap`, with `scan` empty), it pushes
`ser a v` onto `out`, consumes the pointer, and leaves every other stack as it was. -/
def WriteSpec (a : Ty) (wr : Code Stk Sym Rg P) : Prop :=
  ∀ (prog : Program Stk Sym Rg P) (v : a.denote) (h : List Cell) (c : Cfg Stk Sym Rg)
    (p : List Bool) (rp : List Sym), HeapWF h → c.stk .heap = encHeap h → c.stk .scan = [] →
    c.regs = Regs.empty → Rep h a v (ofBits p) → p.length ≤ (encHeap h).length →
    c.stk .ptr = bits p ++ .nd :: rp →
    Sat prog wr c (wrB a v (encHeap h).length) fun c' => c'.regs = Regs.empty ∧
      c'.stk .out = ser a v ++ c.stk .out ∧ c'.stk .ptr = rp ∧
      ∀ j, j ≠ .out → j ≠ .ptr → c'.stk j = c.stk j

theorem sum_map_fst_zip {α β : Type} (f : α → ℕ) (xs : List α) (ys : List β)
    (h : xs.length = ys.length) : ((xs.zip ys).map fun pr => f pr.1).sum = (xs.map f).sum := by
  have : ((xs.zip ys).map fun pr => f pr.1) = ((xs.zip ys).map Prod.fst).map f := by
    rw [List.map_map]; rfl
  rw [this, List.map_fst_zip (by omega)]

theorem writeElems_sat {a : Ty} {wa : Code Stk Sym Rg P} (hwa : WriteSpec a wa)
    (xs : List a.denote) (ps : List (List Bool)) {h : List Cell} {c : Cfg Stk Sym Rg}
    {rp : List Sym} (hwf : HeapWF h) (hh : c.stk .heap = encHeap h) (hs : c.stk .scan = [])
    (hv : c.regs = Regs.empty) (hR : RepList h a xs ps)
    (hps : ∀ p ∈ ps, p.length ≤ (encHeap h).length)
    (hp : c.stk .ptr = encFields ps ++ .mk 3 :: rp) :
    Sat prog (writeElems wa) c ((xs.map fun x => wrB a x (encHeap h).length + 8 + 1).sum + 9)
      fun c' => c'.regs = Regs.empty ∧ c'.stk .out = serElems a xs.reverse ++ c.stk .out ∧
        c'.stk .ptr = rp ∧ ∀ j, j ≠ .out → j ≠ .ptr → c'.stk j = c.stk j := by
  have hlen := hR.length_eq
  have hloop := Sat.loop_list (prog := prog) (b := .not (.is 0 (some (.mk 3))))
    (x := .seq (.act (.set 0 none)) (.seq wa (.seq (.act (.push .out (.tag .cons)))
      (.act (.peek .ptr 0)))))
    (f := fun pr : a.denote × List Bool => wrB a pr.1 (encHeap h).length + 8)
    (I := fun rs c₁ => ∃ done, done ++ rs = xs.zip ps ∧
      c₁.stk .ptr = encFields (rs.map Prod.snd) ++ .mk 3 :: rp ∧
      c₁.regs = rv (c₁.stk .ptr).head? none none none ∧
      c₁.stk .out = serElems a (done.map Prod.fst).reverse ++ c.stk .out ∧
      ∀ j, j ≠ .out → j ≠ .ptr → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.stk .ptr = .mk 3 :: rp ∧ c₁.regs = rv (some (.mk 3)) none none none ∧
      c₁.stk .out = serElems a xs.reverse ++ c.stk .out ∧
      ∀ j, j ≠ .out → j ≠ .ptr → c₁.stk j = c.stk j)
    (fun pr rs c₁ ⟨done, hd, hp₁, hr₁, ho₁, hj₁⟩ => by
      obtain ⟨x, q⟩ := pr
      dsimp only
      have hmem : (x, q) ∈ xs.zip ps := by rw [← hd]; simp
      have hRx : Rep h a x (ofBits q) := List.forall₂_zip hR hmem
      have hqN : q.length ≤ (encHeap h).length := hps q (List.of_mem_zip hmem).2
      have hp₁' : c₁.stk .ptr =
          bits q ++ .nd :: (encFields (rs.map Prod.snd) ++ .mk 3 :: rp) := by
        rw [hp₁]; simp [encFields]
      have hhead : (c₁.stk .ptr).head? ≠ some (.mk 3) := by
        rw [hp₁']; cases q <;> simp [bits]
      refine ⟨by simp [Cond.eval, hr₁, hhead], ?_⟩
      refine Sat.act_seq (by omega) ?_
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hr₁]
      have hh₂ : (Act.run (.set 0 none) c₁).stk .heap = encHeap h := by
        simp only [Act.run]; rw [hj₁ .heap (by decide) (by decide), hh]
      have hs₂ : (Act.run (.set 0 none) c₁).stk .scan = [] := by
        simp only [Act.run]; rw [hj₁ .scan (by decide) (by decide), hs]
      refine Sat.seq_le (hwa prog x h _ q _ hwf hh₂ hs₂ hv₂ hRx hqN hp₁') (by omega)
        fun c₃ ⟨hr₃, ho₃, hp₃, hj₃⟩ => Sat.act_seq (by omega) (Sat.act_le (by omega)
          ⟨done ++ [(x, q)], by simp [← hd], ?_, ?_, ?_, ?_⟩)
      · simp [Act.run, hp₃]
      · rw [empty_eq_rv] at hr₃
        simp [Act.run, hr₃, hp₃, update_rv_zero]
      · simp only [Act.run]
        rw [update_self, ho₃]
        simp [Act.run, ho₁, serElems]
      · intro j hjo hjp
        simp only [Act.run]
        rw [update_of_ne hjo, hj₃ j hjo hjp]
        simp [Act.run, hj₁ j hjo hjp])
    (fun c₁ ⟨done, hd, hp₁, hr₁, ho₁, hj₁⟩ => by
      simp only [List.append_nil] at hd
      rw [hd, List.map_fst_zip (by omega)] at ho₁
      simp only [List.map_nil, encFields, List.nil_append] at hp₁
      exact ⟨by simp [Cond.eval, hr₁, hp₁], hp₁, by simp [hr₁, hp₁], ho₁, hj₁⟩)
  have hsum := sum_map_fst_zip (fun x => wrB a x (encHeap h).length + 8 + 1) xs ps hlen
  unfold writeElems
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop (xs.zip ps) _ ⟨[], by simp, ?_, ?_, ?_, ?_⟩)
    (by omega) fun c₁ ⟨hp₁, hr₁, ho₁, hj₁⟩ => Sat.act_seq (by omega)
      (Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_⟩)))
  · simp [Act.run, hp, List.map_snd_zip (by omega : ps.length ≤ xs.length)]
  · rw [empty_eq_rv] at hv; simp [Act.run, hv, update_rv_zero]
  · simp [Act.run, serElems]
  · intro j _ _; simp [Act.run]
  · rw [empty_eq_rv]; simp [Act.run, hr₁, hp₁]
  · simp [Act.run, ho₁]
  · simp [Act.run, hp₁]
  · intro j hjo hjp; simp [Act.run, update_of_ne hjp, hj₁ j hjo hjp]

/-! ### Writing each type -/

/-- Close a step-budget side condition. -/
local macro "budget" : tactic =>
  `(tactic| first | omega | (simp only [List.length_reverse] at *; omega))

theorem write_unit : WriteSpec (P := P) .unit (write .unit) := by
  intro prog v h c p rp hwf hh hs hv hr hpN hp
  simp only [wrB]
  refine (dropNum_sat hv hp).mono (by omega) fun c' ⟨hr', hp', hj'⟩ =>
    ⟨hr', by rw [hj' .out (by decide)]; rfl, hp', fun j _ hjp => hj' j hjp⟩

theorem write_bool : WriteSpec (P := P) .bool (write .bool) := by
  intro prog v h c p rp hwf hh hs hv hr hpN hp
  simp only [wrB]
  have hFV := fcB_visB (encHeap h).length
  unfold write
  refine Sat.seq_le (fetchCell_sat hwf hh hs hv hr.bool_inv hpN hp) (by unfold visB fcB; omega)
    fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine Sat.seq_le (closeCell_sat (w := c.stk .work) hr₁ (by rw [hw₁]; simp [encFields]))
    (by unfold visB fcB; omega) fun c₂ ⟨hr₂, hw₂, hj₂⟩ => ?_
  have e : ∀ j, j ≠ .ptr → c₂.stk j = c.stk j := by
    intro j hjp
    by_cases hjw : j = .work
    · subst hjw; rw [hw₂]
    · rw [hj₂ j hjw, hj₁ j hjw hjp]
  have hp₂ : c₂.stk .ptr = rp := by rw [hj₂ .ptr (by decide), hp₁]
  cases v with
  | true =>
    refine Sat.ite_true_le (by simp [Cond.eval, hr₂]) (by unfold visB fcB; omega)
      (Sat.act_seq (by unfold visB fcB; omega) (Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_⟩))
    · rw [empty_eq_rv]; simp [Act.run, hr₂]
    · simp [Act.run, e .out (by decide), ser]
    · simp [Act.run, hp₂]
    · intro j hjo hjp; simp [Act.run, update_of_ne hjo, e j hjp]
  | false =>
    refine Sat.ite_false_le (by simp [Cond.eval, hr₂]) (by unfold visB fcB; omega)
      (Sat.act_seq (by unfold visB fcB; omega) (Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_⟩))
    · rw [empty_eq_rv]; simp [Act.run, hr₂]
    · simp [Act.run, e .out (by decide), ser]
    · simp [Act.run, hp₂]
    · intro j hjo hjp; simp [Act.run, update_of_ne hjo, e j hjp]

theorem head_dropWhile_false (L : List Bool) :
    (bits (L.dropWhile (· == false)) ++ [Sym.nd]).head? ≠ some (.bit false) := by
  induction L with
  | nil => simp [bits]
  | cons y L ih => cases y <;> simp_all [bits]

theorem write_nat : WriteSpec (P := P) .nat (write .nat) := by
  intro prog v h c p rp hwf hh hs hv hr hpN hp
  simp only [wrB]
  obtain ⟨l, hc, hl⟩ := hr.nat_inv
  have hlN := (length_field_le hc).2 l (by simp)
  unfold write
  refine Sat.seq_le (fetchCell_sat hwf hh hs hv hc hpN hp) (by unfold visB fcB; omega)
    fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine Sat.act_seq (by unfold visB fcB; omega) ?_
  set c₂ := Act.run (.set 1 none) c₁ with hc₂
  have hv₂ : c₂.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₂, Act.run, hr₁]
  have hw₂ : c₂.stk .work = bits l ++ .nd :: (.mk 0 :: c.stk .work) := by
    simp [hc₂, Act.run, hw₁, encFields]
  refine Sat.seq_le (moveBits_sat (by decide) hv₂ hw₂) (by unfold visB fcB; omega)
    fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₃, empty_eq_rv]) hw₃)
    (by unfold visB fcB; budget) fun c₄ ⟨hr₄, hw₄, hj₄⟩ => ?_
  refine Sat.act_seq (by unfold visB fcB; budget) ?_
  set L := l.reverse with hL
  set D := L.dropWhile (· == false) with hD
  have hsplit : L = L.takeWhile (· == false) ++ D := List.takeWhile_append_dropWhile.symm
  have ht₄ : c₄.stk .t0 = bits (L.takeWhile (· == false) ++ D) ++ .nd :: c.stk .t0 := by
    rw [hj₄ .t0 (by decide), ht₃, ← hsplit]
    simp [hc₂, Act.run, hj₁ .t0 (by decide) (by decide)]
  have hloop := Sat.loop (prog := prog) (b := .is 0 (some (.bit false)))
    (x := .seq (.act (.set 0 none)) (.seq (.act (.pop .t0 0)) (.seq (.act (.set 0 none))
      (.act (.peek .t0 0))))) (t := 7)
    (I := fun m c₅ => ∃ pre, pre.length = m ∧ (∀ y ∈ pre, y = false) ∧
      c₅.stk .t0 = bits (pre ++ D) ++ .nd :: c.stk .t0 ∧
      c₅.regs = rv (c₅.stk .t0).head? none none none ∧ ∀ j, j ≠ .t0 → c₅.stk j = c₄.stk j)
    (Q := fun c₅ => c₅.stk .t0 = bits D ++ .nd :: c.stk .t0 ∧
      c₅.regs = rv (c₅.stk .t0).head? none none none ∧ ∀ j, j ≠ .t0 → c₅.stk j = c₄.stk j)
    (fun m c₅ ⟨pre, hlen, hpre, ht₅, hr₅, hj₅⟩ => by
      obtain ⟨y, pre, rfl⟩ : ∃ y pre', pre = y :: pre' := by
        cases pre with
        | nil => simp at hlen
        | cons y pre' => exact ⟨y, pre', rfl⟩
      have hy : y = false := hpre y (by simp)
      subst hy
      refine ⟨by simp [Cond.eval, hr₅, ht₅, bits], ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega)
        (Sat.act_le (by omega) ⟨pre, by simpa using hlen, fun z hz => hpre z (by simp [hz]),
          ?_, ?_, ?_⟩)))
      · simp [Act.run, ht₅, bits]
      · simp [Act.run, hr₅]
      · intro j hj; simp [Act.run, update_of_ne hj, hj₅ j hj])
    (fun c₅ ⟨pre, hlen, hpre, ht₅, hr₅, hj₅⟩ => by
      obtain rfl : pre = [] := List.eq_nil_of_length_eq_zero hlen
      simp only [List.nil_append] at ht₅
      refine ⟨?_, ht₅, hr₅, hj₅⟩
      have := head_dropWhile_false L
      rw [← hD] at this
      simp only [Cond.eval, hr₅, ht₅, rv_zero, decide_eq_false_iff_not]
      simpa [bits] using this)
  have hk : (L.takeWhile (· == false)).length ≤ l.length := by
    have := List.takeWhile_prefix (p := (· == false)) (l := L) |>.length_le
    simpa [hL] using this
  have hDl : D.length ≤ l.length := by
    have := List.dropWhile_suffix (p := (· == false)) (l := L) |>.length_le
    simpa [hL, hD] using this
  refine Sat.seq_le (hloop _ _ ⟨L.takeWhile (· == false), rfl,
    fun y hy => by simpa using List.mem_takeWhile_imp hy,
    by simpa [Act.run] using ht₄, ?_, ?_⟩) (by unfold visB fcB; budget)
    fun c₅ ⟨ht₅, hr₅, hj₅⟩ => ?_
  · simp [Act.run, hr₄]
  · intro j hj; simp [Act.run]
  refine Sat.act_seq (by unfold visB fcB; budget) ?_
  have hv₆ : (Act.run (.set 0 none) c₅).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₅]
  refine (moveBits_sat (by decide) hv₆ ht₅).mono (by unfold visB fcB; budget)
    fun c' ⟨hr', ht', ho', hj'⟩ => ⟨hr', ?_, ?_, ?_⟩
  · rw [ho']
    simp only [Act.run]
    rw [hj₅ .out (by decide), hj₄ .out (by decide), hj₃ .out (by decide) (by decide)]
    have hs : D.reverse = toBits v := by rw [← hl, ← strip_eq_toBits]; rfl
    simp [hc₂, Act.run, hj₁ .out (by decide) (by decide), ser, hs]
  · rw [hj' .ptr (by decide) (by decide)]
    simp only [Act.run]
    rw [hj₅ .ptr (by decide), hj₄ .ptr (by decide), hj₃ .ptr (by decide) (by decide)]
    simp [hc₂, Act.run, hp₁]
  · intro j hjo hjp
    by_cases hj0 : j = .t0
    · subst hj0; rw [ht']
    rw [hj' j hj0 hjo]
    simp only [Act.run]
    rw [hj₅ j hj0]
    by_cases hjw : j = .work
    · subst hjw; rw [hw₄]
    rw [hj₄ j hjw, hj₃ j hjw hj0]
    simp [hc₂, Act.run, hj₁ j hjw hjp]

theorem write_prod {a b : Ty} (ha : WriteSpec (P := P) a (write a))
    (hb : WriteSpec (P := P) b (write b)) : WriteSpec (P := P) (.prod a b) (write (.prod a b)) := by
  intro prog v h c p rp hwf hh hs hv hr hpN hp
  simp only [wrB]
  obtain ⟨l₁, l₂, hc, hR₁, hR₂⟩ := hr.pair_inv
  have hl₁ := (length_field_le hc).2 l₁ (by simp)
  have hl₂ := (length_field_le hc).2 l₂ (by simp)
  unfold write
  refine Sat.seq_le (fetchCell_sat hwf hh hs hv hc hpN hp) (by unfold visB fcB; omega)
    fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine Sat.act_seq (by unfold visB fcB; omega) ?_
  set c₂ := Act.run (.set 1 none) c₁ with hc₂
  have hv₂ : c₂.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₂, Act.run, hr₁]
  have hw₂ : c₂.stk .work = bits l₁ ++ .nd :: (bits l₂ ++ .nd :: .mk 0 :: c.stk .work) := by
    simp [hc₂, Act.run, hw₁, encFields]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv₂ hw₂)
    (by unfold visB fcB; omega) fun c₃ ⟨hr₃, hw₃, hp₃, hj₃⟩ => ?_
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₃ hw₃)
    (by unfold visB fcB; omega) fun c₄ ⟨hr₄, hw₄, hp₄, hj₄⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₄, empty_eq_rv]) hw₄)
    (by unfold visB fcB; omega) fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
  have e : ∀ j, j ≠ .work → j ≠ .ptr → c₅.stk j = c.stk j := by
    intro j hjw hjp
    rw [hj₅ j hjw, hj₄ j hjw hjp, hj₃ j hjw hjp]
    simp [hc₂, Act.run, hj₁ j hjw hjp]
  have hp₅ : c₅.stk .ptr = bits l₂ ++ .nd :: (bits l₁ ++ .nd :: rp) := by
    rw [hj₅ .ptr (by decide), hp₄, hp₃]
    simp [hc₂, Act.run, hp₁]
  have hr₅' : c₅.regs = Regs.empty := by rw [hr₅, empty_eq_rv]
  refine Sat.seq_le (hb prog v.2 h c₅ l₂ _ hwf (by rw [e .heap (by decide) (by decide), hh])
    (by rw [e .scan (by decide) (by decide), hs]) hr₅' hR₂ hl₂ hp₅) (by unfold visB fcB; omega)
    fun c₆ ⟨hr₆, ho₆, hp₆, hj₆⟩ => ?_
  refine (ha prog v.1 h c₆ l₁ rp hwf
    (by rw [hj₆ .heap (by decide) (by decide), e .heap (by decide) (by decide), hh])
    (by rw [hj₆ .scan (by decide) (by decide), e .scan (by decide) (by decide), hs]) hr₆ hR₁ hl₁
    hp₆).mono (by unfold visB fcB; omega) fun c' ⟨hr', ho', hp', hj'⟩ => ⟨hr', ?_, hp', ?_⟩
  · rw [ho', ho₆, e .out (by decide) (by decide)]
    simp [ser]
  · intro j hjo hjp
    rw [hj' j hjo hjp, hj₆ j hjo hjp]
    by_cases hjw : j = .work
    · subst hjw; exact hw₅
    exact e j hjw hjp

theorem write_option {a : Ty} (ha : WriteSpec (P := P) a (write a)) :
    WriteSpec (P := P) (.option a) (write (.option a)) := by
  intro prog v h c p rp hwf hh hs hv hr hpN hp
  have hFV := fcB_visB (encHeap h).length
  unfold write
  cases v with
  | none =>
    simp only [wrB]
    refine Sat.seq_le (fetchCell_sat hwf hh hs hv hr.none_inv hpN hp)
      (by unfold visB fcB; omega) fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
    refine Sat.ite_true_le (by simp [Cond.eval, hr₁]) (by unfold visB fcB; omega)
      (Sat.act_seq (by unfold visB fcB; omega) ?_)
    have hr₂ : (Act.run (.set 1 none) c₁).regs = rv none none none none := by
      simp [Act.run, hr₁]
    refine Sat.seq_le (closeCell_sat (w := c.stk .work) hr₂ (by simp [Act.run, hw₁, encFields]))
      (by unfold visB fcB; omega) fun c₃ ⟨hr₃, hw₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_, ?_, ?_⟩
    · rw [empty_eq_rv]; simp [Act.run, hr₃]
    · simp [Act.run, hj₃ .out (by decide), hj₁ .out (by decide) (by decide), ser]
    · simp [Act.run, hj₃ .ptr (by decide), hp₁]
    · intro j hjo hjp
      simp only [Act.run]
      rw [update_of_ne hjo]
      by_cases hjw : j = .work
      · subst hjw; exact hw₃
      rw [hj₃ j hjw]
      simp [Act.run, hj₁ j hjw hjp]
  | some x =>
    simp only [wrB]
    obtain ⟨l, hc, hR⟩ := hr.some_inv
    have hlN := (length_field_le hc).2 l (by simp)
    refine Sat.seq_le (fetchCell_sat hwf hh hs hv hc hpN hp) (by unfold visB fcB; omega)
      fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
    refine Sat.ite_false_le (by simp [Cond.eval, hr₁]) (by unfold visB fcB; omega)
      (Sat.act_seq (by unfold visB fcB; omega) ?_)
    set c₂ := Act.run (.set 1 none) c₁ with hc₂
    have hv₂ : c₂.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₂, Act.run, hr₁]
    have hw₂ : c₂.stk .work = bits l ++ .nd :: (.mk 0 :: c.stk .work) := by
      simp [hc₂, Act.run, hw₁, encFields]
    refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv₂ hw₂)
      (by unfold visB fcB; omega) fun c₃ ⟨hr₃, hw₃, hp₃, hj₃⟩ => ?_
    refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₃, empty_eq_rv]) hw₃)
      (by unfold visB fcB; omega) fun c₄ ⟨hr₄, hw₄, hj₄⟩ => ?_
    have e : ∀ j, j ≠ .work → j ≠ .ptr → c₄.stk j = c.stk j := by
      intro j hjw hjp
      rw [hj₄ j hjw, hj₃ j hjw hjp]
      simp [hc₂, Act.run, hj₁ j hjw hjp]
    have hp₄ : c₄.stk .ptr = bits l ++ .nd :: rp := by
      rw [hj₄ .ptr (by decide), hp₃]; simp [hc₂, Act.run, hp₁]
    refine Sat.seq_le (ha prog x h c₄ l rp hwf (by rw [e .heap (by decide) (by decide), hh])
      (by rw [e .scan (by decide) (by decide), hs]) (by rw [hr₄, empty_eq_rv]) hR hlN hp₄)
      (by unfold visB fcB; omega) fun c₅ ⟨hr₅, ho₅, hp₅, hj₅⟩ =>
        Sat.act_le (by omega) ⟨hr₅, ?_, by simp [Act.run, hp₅], ?_⟩
    · simp [Act.run, ho₅, e .out (by decide) (by decide), ser]
    · intro j hjo hjp
      simp only [Act.run]
      rw [update_of_ne hjo, hj₅ j hjo hjp]
      by_cases hjw : j = .work
      · subst hjw; exact hw₄
      exact e j hjw hjp

/-- The tag of the cell of a list. -/
def listTag {α : Type} : List α → Tag
  | [] => .nil
  | _ :: _ => .cons

/-- The fields of the cell of a list: none for `nil`; the head and the tail for `cons`. -/
def ListCell (h : List Cell) (a : Ty) : List a.denote → List (List Bool) → Prop
  | [], fs => fs = []
  | y :: ys, fs => ∃ l₁ l₂, fs = [l₁, l₂] ∧ Rep h a y (ofBits l₁) ∧
      Rep h (.list a) ys (ofBits l₂) ∧ l₁.length ≤ (encHeap h).length ∧
      l₂.length ≤ (encHeap h).length

theorem Rep.list_inv {h : List Cell} {a : Ty} {ys : List a.denote} {q : ℕ}
    (r : Rep h (.list a) ys q) : ∃ fs, CellAt h q (listTag ys) fs ∧ ListCell h a ys fs := by
  cases ys with
  | nil => exact ⟨[], r.nil_inv, rfl⟩
  | cons y ys =>
    obtain ⟨l₁, l₂, hc, r₁, r₂⟩ := r.cons_inv
    exact ⟨_, hc, l₁, l₂, rfl, r₁, r₂, (length_field_le hc).2 l₁ (by simp),
      (length_field_le hc).2 l₂ (by simp)⟩

theorem write_list {a : Ty} (ha : WriteSpec (P := P) a (write a)) :
    WriteSpec (P := P) (.list a) (write (.list a)) := by
  intro prog xs h c p rp hwf hh hs hv hr hpN hp
  simp only [wrB]
  obtain ⟨T, hT⟩ : ∃ T, T = fcB (encHeap h).length + 24 * (encHeap h).length + 46 := ⟨_, rfl⟩
  have hFV := fcB_visB (encHeap h).length
  have hTv : T + 1 ≤ visB (encHeap h).length := by omega
  have hexp : (xs.length + 1) * visB (encHeap h).length =
      xs.length * visB (encHeap h).length + visB (encHeap h).length := Nat.succ_mul _ _
  unfold write
  refine Sat.act_seq (by omega) ?_
  set c₁ := Act.run (.push .out (.tag .nil)) c with hc₁
  have hp₁ : c₁.stk .ptr = bits p ++ .nd :: rp := by simp [hc₁, Act.run, hp]
  refine Sat.seq_le (moveBits_sat (by decide) hv hp₁) (by omega)
    fun c₂ ⟨hr₂, hp₂, ht₂, hj₂⟩ => ?_
  refine Sat.act_seq (by omega) ?_
  set c₃ := Act.run (.push .ptr (.mk 3)) c₂ with hc₃
  have ht₃ : c₃.stk .t2 = bits p.reverse ++ .nd :: c₁.stk .t2 := by simp [hc₃, Act.run, ht₂]
  refine Sat.seq_le (moveBits_sat (by decide) hr₂ ht₃) (by budget)
    fun c₄ ⟨hr₄, ht₄, hp₄, hj₄⟩ => ?_
  have e₄ : ∀ j, j ≠ .out → j ≠ .ptr → c₄.stk j = c.stk j := by
    intro j hjo hjp
    by_cases hj2 : j = .t2
    · subst hj2; rw [ht₄]; simp [hc₁, Act.run]
    rw [hj₄ j hj2 hjp]
    simp only [hc₃, Act.run]
    rw [update_of_ne hjp, hj₂ j hjp hj2]
    simp [hc₁, Act.run, update_of_ne hjo]
  have hp₄' : c₄.stk .ptr = bits p ++ .nd :: (.mk 3 :: rp) := by
    rw [hp₄]; simp [hc₃, Act.run, hp₂]
  have hh₄ : c₄.stk .heap = encHeap h := by rw [e₄ .heap (by decide) (by decide), hh]
  have hs₄ : c₄.stk .scan = [] := by rw [e₄ .scan (by decide) (by decide), hs]
  obtain ⟨fs, hc, hL⟩ := hr.list_inv
  refine Sat.seq_le (fetchCell_sat hwf hh₄ hs₄ hr₄ hc hpN hp₄') (by budget)
    fun c₅ ⟨hr₅, hw₅, hp₅, hj₅⟩ => ?_
  have hloop := Sat.loop_list (prog := prog) (b := .is 1 (some (.tag .cons)))
    (x := .seq (.act (.set 1 none)) (.seq (moveNum2 .work .ptr .t0)
      (.seq (moveNum2 .work .ptr .t0) (.seq closeCell fetchCell))))
    (f := fun _ => T)
    (I := fun ys c₆ => ∃ done hs fs, done ++ ys = xs ∧ RepList h a done.reverse hs ∧
      (∀ q ∈ hs, q.length ≤ (encHeap h).length) ∧
      c₆.stk .ptr = encFields hs ++ .mk 3 :: rp ∧
      c₆.regs = rv none (some (.tag (listTag ys))) none none ∧
      c₆.stk .work = encFields fs ++ .mk 0 :: c.stk .work ∧ ListCell h a ys fs ∧
      ∀ j, j ≠ .work → j ≠ .ptr → c₆.stk j = c₄.stk j)
    (Q := fun c₆ => ∃ hs, RepList h a xs.reverse hs ∧
      (∀ q ∈ hs, q.length ≤ (encHeap h).length) ∧
      c₆.stk .ptr = encFields hs ++ .mk 3 :: rp ∧
      c₆.regs = rv none (some (.tag .nil)) none none ∧
      c₆.stk .work = .mk 0 :: c.stk .work ∧ ∀ j, j ≠ .work → j ≠ .ptr → c₆.stk j = c₄.stk j)
    (fun y ys c₆ ⟨done, hs₆, fs, hd, hR, hq, hp₆, hr₆, hw₆, hL₆, hj₆⟩ => by
      obtain ⟨l₁, l₂, rfl, hR₁, hR₂, hl₁, hl₂⟩ := hL₆
      refine ⟨by simp [Cond.eval, hr₆, listTag], ?_⟩
      refine Sat.act_seq (by rw [hT]; unfold fcB; omega) ?_
      set c₇ := Act.run (.set 1 none) c₆ with hc₇
      have hv₇ : c₇.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₇, Act.run, hr₆]
      have hw₇ : c₇.stk .work = bits l₁ ++ .nd :: (bits l₂ ++ .nd :: .mk 0 :: c.stk .work) := by
        simp [hc₇, Act.run, hw₆, encFields]
      refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv₇ hw₇)
        (by rw [hT]; unfold fcB; omega) fun c₈ ⟨hr₈, hw₈, hp₈, hj₈⟩ => ?_
      refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₈ hw₈)
        (by rw [hT]; unfold fcB; omega) fun c₉ ⟨hr₉, hw₉, hp₉, hj₉⟩ => ?_
      refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₉, empty_eq_rv]) hw₉)
        (by rw [hT]; unfold fcB; omega) fun c₁₀ ⟨hr₁₀, hw₁₀, hj₁₀⟩ => ?_
      have e : ∀ j, j ≠ .work → j ≠ .ptr → c₁₀.stk j = c₄.stk j := by
        intro j hjw hjp
        rw [hj₁₀ j hjw, hj₉ j hjw hjp, hj₈ j hjw hjp]
        simp [hc₇, Act.run, hj₆ j hjw hjp]
      have hp₁₀ : c₁₀.stk .ptr = bits l₂ ++ .nd :: (encFields (l₁ :: hs₆) ++ .mk 3 :: rp) := by
        rw [hj₁₀ .ptr (by decide), hp₉, hp₈]
        simp [hc₇, Act.run, hp₆, encFields]
      obtain ⟨fs', hc', hL'⟩ := hR₂.list_inv
      refine (fetchCell_sat hwf (by rw [e .heap (by decide) (by decide), hh₄])
        (by rw [e .scan (by decide) (by decide), hs₄]) (by rw [hr₁₀, empty_eq_rv]) hc' hl₂
        hp₁₀).mono (by rw [hT]; omega) fun c₁₁ ⟨hr₁₁, hw₁₁, hp₁₁, hj₁₁⟩ =>
          ⟨done ++ [y], l₁ :: hs₆, fs', by simp [← hd], ?_, ?_, hp₁₁, hr₁₁, ?_, hL', ?_⟩
      · have r : RepList h a (y :: done.reverse) (l₁ :: hs₆) := List.Forall₂.cons hR₁ hR
        simpa using r
      · intro q hq'
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact hl₁
        · exact hq q hq'
      · rw [hw₁₁, hw₁₀]
      · intro j hjw hjp
        rw [hj₁₁ j hjw hjp, e j hjw hjp])
    (fun c₆ ⟨done, hs₆, fs, hd, hR, hq, hp₆, hr₆, hw₆, hL₆, hj₆⟩ => by
      simp only [List.append_nil] at hd
      subst hd
      obtain rfl : fs = [] := hL₆
      exact ⟨by simp [Cond.eval, hr₆, listTag], hs₆, hR, hq, hp₆, hr₆,
        by simpa [encFields] using hw₆, hj₆⟩)
  beta_reduce at hloop
  have hk : (xs.map fun _ => T + 1).sum + 1 ≤ xs.length * visB (encHeap h).length + 1 := by
    rw [sum_map_const]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hTv) 1
  refine Sat.seq_le (hloop xs c₅ ⟨[], [], fs, by simp, List.Forall₂.nil, by simp,
    by simpa [encFields] using hp₅, hr₅, by rw [hw₅, e₄ .work (by decide) (by decide)], hL,
    fun j hjw hjp => hj₅ j hjw hjp⟩) (by budget)
    fun c₆ ⟨hs₆, hR, hq, hp₆, hr₆, hw₆, hj₆⟩ => ?_
  refine Sat.act_seq (by budget) ?_
  have hr₇ : (Act.run (.set 1 none) c₆).regs = rv none none none none := by simp [Act.run, hr₆]
  refine Sat.seq_le (closeCell_sat (w := c.stk .work) hr₇ (by simp [Act.run, hw₆])) (by budget)
    fun c₈ ⟨hr₈, hw₈, hj₈⟩ => ?_
  have e : ∀ j, j ≠ .out → j ≠ .ptr → c₈.stk j = c.stk j := by
    intro j hjo hjp
    by_cases hjw : j = .work
    · subst hjw; rw [hw₈]
    rw [hj₈ j hjw]
    simp [Act.run, hj₆ j hjw hjp, e₄ j hjo hjp]
  have hRrev : RepList h a xs.reverse hs₆ := hR
  refine (writeElems_sat ha xs.reverse hs₆ hwf (by rw [e .heap (by decide) (by decide), hh])
    (by rw [e .scan (by decide) (by decide), hs]) (by rw [hr₈, empty_eq_rv]) hRrev hq
    (by rw [hj₈ .ptr (by decide)]; simp [Act.run, hp₆])).mono
    (by simp only [List.map_reverse, List.sum_reverse]; budget)
    fun c' ⟨hr', ho', hp', hj'⟩ => ⟨hr', ?_, hp', ?_⟩
  · rw [ho', List.reverse_reverse, hj₈ .out (by decide)]
    simp only [Act.run]
    rw [hj₆ .out (by decide) (by decide), hj₄ .out (by decide) (by decide)]
    simp [hc₃, Act.run, hj₂ .out (by decide) (by decide), hc₁, ser, serElems]
  · intro j hjo hjp
    rw [hj' j hjo hjp, e j hjo hjp]

theorem write_array {a : Ty} (ha : WriteSpec (P := P) a (write a)) :
    WriteSpec (P := P) (.array a) (write (.array a)) := by
  intro prog v h c p rp hwf hh hs hv hr hpN hp
  simp only [wrB]
  obtain ⟨ls, hc, hlen, hR⟩ := hr.arr_inv
  obtain ⟨hLf, hls⟩ := length_field_le hc
  have hxf : (encFields ls).length * (6 * (encFields ls).length + 14) ≤
      (encHeap h).length * (6 * (encHeap h).length + 14) :=
    Nat.mul_le_mul hLf (by omega)
  have hLf' := length_encFields_reverse_map ls
  unfold write
  refine Sat.seq_le (fetchCell_sat hwf hh hs hv hc hpN hp) (by unfold visB fcB; omega)
    fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine Sat.act_seq (by unfold visB fcB; omega) (Sat.act_seq (by unfold visB fcB; omega) ?_)
  set c₂ := Act.run (.push .t0 (.mk 3)) (Act.run (.set 1 none) c₁) with hc₂
  have hv₂ : c₂.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₂, Act.run, hr₁]
  have hw₂ : c₂.stk .work = encFields ls ++ .mk 0 :: c.stk .work := by
    simp [hc₂, Act.run, hw₁]
  refine Sat.seq_le (xferNums_sat (by decide) hv₂ hw₂) (by unfold visB fcB; omega)
    fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => ?_
  refine Sat.act_seq (by unfold visB fcB; omega) ?_
  set c₄ := Act.run (.push .ptr (.mk 3)) c₃ with hc₄
  have ht₄ : c₄.stk .t0 = encFields (ls.reverse.map List.reverse) ++ .mk 3 :: c.stk .t0 := by
    simp [hc₄, Act.run, ht₃, hc₂, hj₁ .t0 (by decide) (by decide)]
  refine Sat.seq_le (xferNums_sat (by decide) hr₃ ht₄) (by unfold visB fcB; rw [hLf']; omega)
    fun c₅ ⟨hr₅, ht₅, hp₅, hj₅⟩ => ?_
  refine Sat.act_seq (by unfold visB fcB; rw [hLf']; omega) ?_
  set c₆ := Act.run (.push .out (.tag .nil)) c₅ with hc₆
  have e : ∀ j, j ≠ .out → j ≠ .ptr → c₆.stk j = c.stk j := by
    intro j hjo hjp
    by_cases hj0 : j = .t0
    · subst hj0; simp [hc₆, Act.run, ht₅]
    simp only [hc₆, Act.run]
    rw [update_of_ne hjo, hj₅ j hj0 hjp]
    simp only [hc₄, Act.run]
    rw [update_of_ne hjp]
    by_cases hjw : j = .work
    · subst hjw; rw [hw₃]
    rw [hj₃ j hjw hj0]
    simp [hc₂, Act.run, update_of_ne hj0, hj₁ j hjw hjp]
  have hp₆ : c₆.stk .ptr = encFields ls ++ .mk 3 :: rp := by
    simp [hc₆, Act.run, hp₅, hc₄, hj₃ .ptr (by decide) (by decide), hc₂,
      hp₁]
  have hRl : RepList h a v.toList ls := by
    refine List.forall₂_iff_get.2 ⟨by simp [hlen], fun i h₁ h₂ => ?_⟩
    simpa using hR i h₂ (by simpa using h₁)
  refine (writeElems_sat ha v.toList ls hwf (by rw [e .heap (by decide) (by decide), hh])
    (by rw [e .scan (by decide) (by decide), hs]) (by simp [hc₆, Act.run, hr₅]) hRl hls hp₆).mono
    (by unfold visB fcB; rw [hLf']; omega) fun c' ⟨hr', ho', hp', hj'⟩ => ⟨hr', ?_, hp', ?_⟩
  · rw [ho']
    simp only [hc₆, Act.run]
    rw [update_self, hj₅ .out (by decide) (by decide)]
    simp [hc₄, Act.run, hj₃ .out (by decide) (by decide), hc₂, hj₁ .out (by decide) (by decide),
      ser, serElems]
  · intro j hjo hjp
    rw [hj' j hjo hjp, e j hjo hjp]

/-- **Writing**: `write t` meets its specification for every type. -/
theorem write_sat : ∀ t : Ty, WriteSpec (P := P) t (write t)
  | .unit => write_unit
  | .bool => write_bool
  | .nat => write_nat
  | .prod a b => write_prod (write_sat a) (write_sat b)
  | .option a => write_option (write_sat a)
  | .list a => write_list (write_sat a)
  | .array a => write_array (write_sat a)

/-! ### Polynomial bounds -/

theorem visB_ge (N : ℕ) : 60 * N + 100 ≤ visB N := by unfold visB; omega

/-- **The steps of writing** are at most `wt t * (L + 1) * visB N`. -/
theorem wrB_le : ∀ (t : Ty) (v : t.denote) (N : ℕ),
    wrB t v N ≤ wt t * ((ser t v).length + 1) * visB N
  | .unit, _, N => by
    have := visB_ge N
    simp only [wrB]
    exact le_wtP (by omega) (one_le_wt _)
  | .bool, _, N => by simp only [wrB]; exact le_wtP le_rfl (one_le_wt _)
  | .nat, _, N => by simp only [wrB]; exact le_wtP le_rfl (one_le_wt _)
  | .prod a b, v, N => by
    have h₁ := wrB_le a v.1 N
    have h₂ := wrB_le b v.2 N
    have hk : wt a * ((ser a v.1).length + 1) + wt b * ((ser b v.2).length + 1) + 1 ≤
        (wt a + wt b + 1) * ((ser a v.1).length + (ser b v.2).length + 1) := by
      nlinarith [Nat.zero_le (wt a * (ser b v.2).length), Nat.zero_le (wt b * (ser a v.1).length)]
    have := wtP_add h₁ h₂ le_rfl hk
    simp only [wrB, wt, ser, List.length_append]
    omega
  | .option a, none, N => by simp only [wrB]; exact le_wtP le_rfl (one_le_wt _)
  | .option a, some x, N => by
    have h₁ := wrB_le a x N
    have hk : wt a * ((ser a x).length + 1) + 1 ≤ (wt a + 1) * ((ser a x).length + 1 + 1) := by
      nlinarith
    have := wtP_add1 h₁ le_rfl hk
    simp only [wrB, wt, ser, List.length_cons]
    omega
  | .list a, xs, N => by
    obtain ⟨S, hS⟩ : ∃ S, S = (xs.map fun x => (ser a x).length + 1).sum := ⟨_, rfl⟩
    have hk : xs.length ≤ S := by rw [hS]; exact length_le_sum_succ _ xs
    have hV := visB_ge N
    have hel : ∀ x ∈ xs, wrB a x N + 9 ≤ (wt a * ((ser a x).length + 1) + 1) * visB N :=
      fun x _ => by
        have h₁ := wrB_le a x N
        rw [Nat.add_mul, Nat.one_mul]; omega
    have hsum := sum_wtP (fun x => wrB a x N) (fun x => (ser a x).length + 1) (wt a) (visB N) xs
      hel
    beta_reduce at hsum
    rw [← hS] at hsum
    have hexp : (xs.length + 1) * visB N = xs.length * visB N + visB N := Nat.succ_mul _ _
    have hk₂ : wt a * S + xs.length + xs.length + 1 + 1 ≤ (wt a + 2) * (S + 1 + 1) := by
      nlinarith
    have e : (wt a * S + xs.length + xs.length + 1 + 1) * visB N =
        (wt a * S + xs.length) * visB N + xs.length * visB N + visB N + visB N := by ring
    simp only [wrB, wt, ser_list, List.length_append, length_serElems, List.length_singleton]
    rw [← hS]
    refine le_mul_of_parts (X := wt a * S + xs.length + xs.length + 1 + 1) ?_ hk₂
    rw [e]; omega
  | .array a, v, N => by
    obtain ⟨S, hS⟩ : ∃ S, S = (v.toList.map fun x => (ser a x).length + 1).sum := ⟨_, rfl⟩
    have hrev : (v.toList.reverse.map fun x => (ser a x).length + 1).sum = S := by
      rw [hS]; simp [List.map_reverse, List.sum_reverse]
    have hk : v.toList.length ≤ S := by rw [hS]; exact length_le_sum_succ _ _
    have hV := visB_ge N
    have hel : ∀ x ∈ v.toList, wrB a x N + 9 ≤ (wt a * ((ser a x).length + 1) + 1) * visB N :=
      fun x _ => by
        have h₁ := wrB_le a x N
        rw [Nat.add_mul, Nat.one_mul]; omega
    have hsum := sum_wtP (fun x => wrB a x N) (fun x => (ser a x).length + 1) (wt a) (visB N)
      v.toList hel
    beta_reduce at hsum
    rw [← hS] at hsum
    have hk₂ : wt a * S + v.toList.length + 2 ≤ (wt a + 2) * (S + 1 + 1) := by nlinarith
    have e : (wt a * S + v.toList.length + 2) * visB N =
        (wt a * S + v.toList.length) * visB N + visB N + visB N := by ring
    simp only [wrB, wt, ser_array, List.length_append, length_serElems, List.length_singleton]
    rw [hrev]
    refine le_mul_of_parts (X := wt a * S + v.toList.length + 2) ?_ hk₂
    rw [e]; omega

end GraphIso.TM
