module

public import GraphIso.TM.Compile

/-!
# Routines for the primitives

Stage 17f (`PLAN-17.md` §9). Routines on the simulator's stacks, as in 17b–17e: each starts with
empty registers, leaves every stack it does not name as it was, and runs within an explicit step
bound. Each ends with empty registers, except `openTop`, which leaves the fetched cell's tag in
register `1` (`openTop_sat`) for the caller to test.

* **Frames** `Fr S c c'`: `c'` agrees with `c` on every stack outside `S` (`Fr.trans`,
  `Fr.mono`, and `Fr.restore` for a stack that ends as it started).
* **Allocation under the size invariant** (`allocB_sat`): a cell with at most `F` fields of at
  most `B` plus the number of cells in bits keeps `HeapBnd B F`. **`allocArgs t n`**
  (`allocArgs_sat`) allocates a cell with tag `t` whose fields are the `n` pointers on top of
  `work`, in order.
* **`openTop`** fetches the cell of the pointer on top of `work` (its tag in register `1`, its
  fields and `mk 0` on `work`); **`natTo s`** moves the bits of the natural it points to onto
  `s`.
* **`moveAll i a b`** moves the numbers of `a` above the marker `mk i` onto `b`, one by one (so
  their order is reversed); **`countAll i a`** drops them, counting them onto `t2`
  (`cntBits k`: `k` increments of the empty number, of value `k` and at most `k + 1` bits).
* **`walkList s`** pushes the pointers of the elements of the list whose pointer is on `ptr`
  onto `s` (`walkList_sat`); **`buildListB s`** conses the elements whose pointers are on `s`
  onto a list, keeping `HeapBnd` (`buildListB_sat`).
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost Function

variable {P : Type} {prog : Program Stk Sym Rg P}

/-! ### Frames -/

/-- `c'` agrees with `c` on every stack outside `S`. -/
def Fr (S : List Stk) (c c' : Cfg Stk Sym Rg) : Prop := ∀ j, j ∉ S → c'.stk j = c.stk j

theorem Fr.refl (S : List Stk) (c : Cfg Stk Sym Rg) : Fr S c c := fun _ _ => rfl

theorem Fr.trans {S T : List Stk} {c c₁ c₂ : Cfg Stk Sym Rg} (h₁ : Fr S c c₁)
    (h₂ : Fr T c₁ c₂) : Fr (S ++ T) c c₂ := fun j hj => by
  simp only [List.mem_append, not_or] at hj
  rw [h₂ j hj.2, h₁ j hj.1]

theorem Fr.mono {S T : List Stk} {c c' : Cfg Stk Sym Rg} (h : Fr S c c') (hST : S ⊆ T) :
    Fr T c c' := fun j hj => h j fun h' => hj (hST h')

/-- A stack that ends as it started leaves the frame. -/
theorem Fr.restore {j₀ : Stk} {S : List Stk} {c c' : Cfg Stk Sym Rg} (h : Fr (j₀ :: S) c c')
    (hj : c'.stk j₀ = c.stk j₀) : Fr S c c' := fun j hjS => by
  by_cases e : j = j₀
  · subst e; exact hj
  · exact h j (by simp [e, hjS])

theorem fr1 {a : Stk} {c c' : Cfg Stk Sym Rg} (h : ∀ j, j ≠ a → c'.stk j = c.stk j) :
    Fr [a] c c' := fun j hj => h j (by simpa using hj)

theorem fr2 {a b : Stk} {c c' : Cfg Stk Sym Rg}
    (h : ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j) : Fr [a, b] c c' := fun j hj => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  exact h j hj.1 hj.2

theorem fr3 {a b d : Stk} {c c' : Cfg Stk Sym Rg}
    (h : ∀ j, j ≠ a → j ≠ b → j ≠ d → c'.stk j = c.stk j) : Fr [a, b, d] c c' := fun j hj => by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  exact h j hj.1 hj.2.1 hj.2.2

theorem fr_push (k : Stk) (s : Sym) (c : Cfg Stk Sym Rg) : Fr [k] c (Act.run (.push k s) c) :=
  fun j hj => by simp only [List.mem_singleton] at hj; simp [Act.run, update_of_ne hj]

theorem fr_pop (k : Stk) (r : Fin Rg) (c : Cfg Stk Sym Rg) : Fr [k] c (Act.run (.pop k r) c) :=
  fun j hj => by simp only [List.mem_singleton] at hj; simp [Act.run, update_of_ne hj]

theorem fr_set (r : Fin Rg) (o : Option Sym) (c : Cfg Stk Sym Rg) :
    Fr [] c (Act.run (.set r o) c) := fun _ _ => rfl

theorem fr_peek (k : Stk) (r : Fin Rg) (c : Cfg Stk Sym Rg) :
    Fr [] c (Act.run (.peek k r) c) := fun _ _ => rfl

theorem HeapAt.fr {h : List Cell} {c c' : Cfg Stk Sym Rg} {S : List Stk} (hH : HeapAt h c)
    (hf : Fr S c c') (h₁ : Stk.heap ∉ S) (h₂ : Stk.scan ∉ S) (h₃ : Stk.cnt ∉ S) : HeapAt h c' :=
  hH.frame (hf _ h₁) (hf _ h₂) (hf _ h₃)

/-! ### Allocation under the size invariant -/

theorem HeapBnd.snoc {B F : ℕ} {h : List Cell} (hB : HeapBnd B F h) {l : List Bool} {t : Tag}
    {fs : List (List Bool)} (hl : l.length ≤ B + h.length) (hF : fs.length ≤ F)
    (hfs : ∀ f ∈ fs, f.length ≤ B + h.length) : HeapBnd B F (h ++ [⟨l, t, fs⟩]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · rw [List.getElem_append_left hi]; exact hB i hi
  · simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
    exact ⟨hl, hF, hfs⟩

/-- **Allocation** keeps the size invariant, for fields of at most `B` plus the number of cells
in bits. -/
theorem allocB_sat (t : Tag) {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {fs : List (List Bool)} {rest : List Sym} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (hv : c.regs = Regs.empty) (hw : c.stk .work = encFields fs ++ .mk 2 :: rest)
    (hF : fs.length ≤ F) (hfs : ∀ f ∈ fs, f.length ≤ B + h.length) :
    Sat prog (alloc t) c (allocBound (encFields fs).length h.length) fun c' =>
      c'.regs = Regs.empty ∧ ∃ l, HeapAt (h ++ [⟨l, t, fs⟩]) c' ∧
        HeapBnd B F (h ++ [⟨l, t, fs⟩]) ∧ CellAt (h ++ [⟨l, t, fs⟩]) (ofBits l) t fs ∧
        l.length ≤ h.length + 1 ∧ c'.stk .work = bits l ++ .nd :: rest ∧
        Fr [.heap, .cnt, .work] c c' :=
  (alloc_sat t hH hv hw).mono le_rfl fun _ ⟨hr, l, hH', hl, hll, hw', hj⟩ =>
    ⟨hr, l, hH', hB.snoc (by omega) hF hfs, cellAt_new hl, hll, hw', fr3 hj⟩

theorem encFields_eq_encNums : ∀ fs : List (List Bool), encFields fs = encNums fs
  | [] => rfl
  | f :: fs => by rw [encFields_cons, encNums_cons, encFields_eq_encNums fs]

/-- Allocate a cell with tag `t` whose fields are the `n` pointers on top of `work` (the last on
top), in order. -/
def allocArgs (t : Tag) (n : ℕ) : Code Stk Sym Rg P :=
  .seq (moveN n .work .t1) (.seq (moveN n .t1 .t2) (.seq (.act (.push .work (.mk 2)))
    (.seq (moveN n .t2 .work) (alloc t))))

/-- The step bound of moving `n` numbers of at most `E` bits. -/
theorem sum_move_le {ls : List (List Bool)} {E : ℕ} (hls : ∀ l ∈ ls, l.length ≤ E) :
    (ls.map fun l => 12 * l.length + 20).sum ≤ ls.length * (12 * E + 20) ∧
      (ls.reverse.map fun l => 12 * l.length + 20).sum ≤ ls.length * (12 * E + 20) := by
  have hS := sum_map_le_mul (fun l : List Bool => 12 * l.length + 20) (12 * E + 20) ls
    fun l hl => by have := hls l hl; omega
  refine ⟨hS, ?_⟩
  rw [List.map_reverse, List.sum_reverse]; exact hS

theorem allocArgs_sat (t : Tag) {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {ls : List (List Bool)} {w : List Sym} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc ls ++ w) (hF : ls.length ≤ F)
    (hls : ∀ l ∈ ls, l.length ≤ B + h.length) :
    Sat prog (allocArgs t ls.length) c
      (3 * (ls.length * (12 * (B + h.length) + 20)) + allocBound (encFields ls).length h.length +
        9) fun c' =>
      c'.regs = Regs.empty ∧ ∃ l, HeapAt (h ++ [⟨l, t, ls⟩]) c' ∧
        HeapBnd B F (h ++ [⟨l, t, ls⟩]) ∧ CellAt (h ++ [⟨l, t, ls⟩]) (ofBits l) t ls ∧
        l.length ≤ h.length + 1 ∧ c'.stk .work = bits l ++ .nd :: w ∧
        Fr [.heap, .cnt, .work] c c' := by
  obtain ⟨hS, hS'⟩ := sum_move_le hls
  unfold allocArgs
  have m₁ := moveN_sat (prog := prog) (a := .work) (b := .t1) (by decide) (by decide) (by decide)
    ls.reverse c w hv hw
  rw [List.length_reverse, List.reverse_reverse] at m₁
  refine Sat.seq_le m₁ (by omega) fun c₁ ⟨hr₁, hw₁, ht₁, hj₁⟩ => ?_
  have m₂ := moveN_sat (prog := prog) (a := .t1) (b := .t2) (by decide) (by decide) (by decide)
    ls c₁ (c.stk .t1) hr₁ ht₁
  refine Sat.seq_le m₂ (by omega) fun c₂ ⟨hr₂, ht₂, ht₂', hj₂⟩ => ?_
  refine Sat.act_seq (by omega) ?_
  have ht₃ : (Act.run (.push .work (.mk 2)) c₂).stk .t2 = encNums ls.reverse ++ c.stk .t2 := by
    simp [Act.run, ht₂', hj₁ .t2 (by decide) (by decide)]
  have m₃ := moveN_sat (prog := prog) (a := .t2) (b := .work) (by decide) (by decide)
    (by decide) ls.reverse (Act.run (.push .work (.mk 2)) c₂) (c.stk .t2) hr₂ ht₃
  rw [List.length_reverse, List.reverse_reverse] at m₃
  refine Sat.seq_le m₃ (by omega) fun c₄ ⟨hr₄, ht₄, hw₄, hj₄⟩ => ?_
  have hw₄' : c₄.stk .work = encFields ls ++ .mk 2 :: w := by
    rw [hw₄, encFields_eq_encNums]
    simp [Act.run, hj₂ .work (by decide) (by decide), hw₁]
  have hf₄ : Fr [.work, .t1, .t2] c c₄ := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hj₄ j hj.2.2 hj.1]
    simp only [Act.run]
    rw [update_of_ne hj.1, hj₂ j hj.2.1 hj.2.2, hj₁ j hj.1 hj.2.1]
  have hH₄ : HeapAt h c₄ := hH.fr hf₄ (by decide) (by decide) (by decide)
  refine (allocB_sat t hH₄ hB h1B hr₄ hw₄' hF hls).mono (by omega)
    fun c' ⟨hr', l, hH', hB', hc', hl', hw', hf'⟩ => ⟨hr', l, hH', hB', hc', hl', hw', ?_⟩
  have e₁ : c'.stk .t1 = c.stk .t1 := by
    rw [hf' .t1 (by decide), hj₄ .t1 (by decide) (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), ht₂]
  have e₂ : c'.stk .t2 = c.stk .t2 := by rw [hf' .t2 (by decide), ht₄]
  have hf : Fr [.t1, .t2, .heap, .cnt, .work] c c' := (hf₄.trans hf').mono (by decide)
  exact (hf.restore e₁).restore e₂

/-! ### Cells and numbers on `work` -/

/-- Fetch the cell whose pointer is on top of `work`: its tag in register `1`, its fields and the
marker `mk 0` on `work`. -/
def openTop : Code Stk Sym Rg P := .seq (moveNum2 .work .ptr .t0) fetchCell

theorem openTop_sat {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c)
    (hv : c.regs = Regs.empty) {p : List Bool} {w : List Sym}
    (hw : c.stk .work = bits p ++ .nd :: w) {tg : Tag} {fs : List (List Bool)}
    (hc : CellAt h (ofBits p) tg fs) {E : ℕ} (hp : p.length ≤ E) :
    Sat prog openTop c (fcE (encHeap h).length E + 12 * E + 20) fun c' =>
      c'.regs = rv none (some (.tag tg)) none none ∧
        c'.stk .work = encFields fs ++ .mk 0 :: w ∧ Fr [.work] c c' := by
  unfold openTop
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw) (by omega)
    fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  have hH₁ : HeapAt h c₁ := hH.fr (fr2 hj₁) (by decide) (by decide) (by decide)
  refine (fetchCellE_sat hH₁.wf hH₁.heap hH₁.scan hr₁ hc hp hp₁).mono (by omega)
    fun c' ⟨hr', hw', hp', hj'⟩ => ⟨hr', by rw [hw', hw₁], fun j hj => ?_⟩
  simp only [List.mem_singleton] at hj
  by_cases hjp : j = .ptr
  · subst hjp; exact hp'
  · rw [hj' j hj hjp, hj₁ j hj hjp]

/-- Fetch the natural whose pointer is on top of `work` and move its bits onto `s`. -/
def natTo (s : Stk) : Code Stk Sym Rg P :=
  .seq openTop (.seq (.act (.set 1 none)) (.seq (moveNum2 .work s .t0) closeCell))

theorem natTo_sat {s : Stk} (hs₁ : s ≠ .work) (hs₂ : s ≠ .t0) {B F : ℕ} {h : List Cell}
    {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
    {p : List Bool} {w : List Sym} (hw : c.stk .work = bits p ++ .nd :: w) {v : ℕ}
    (hr : Rep h .nat v (ofBits p)) {E : ℕ} (hp : p.length ≤ E) (hE : B + h.length ≤ E) :
    Sat prog (natTo s) c (fcE (encHeap h).length E + 24 * E + 50) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = w ∧ Fr [.work, s] c c' ∧ ∃ l, ofBits l = v ∧
        l.length < B + h.length ∧ c'.stk s = bits l ++ .nd :: c.stk s := by
  obtain ⟨l, hc, hl⟩ := hr.nat_inv
  have hlB := hB.field_lt hc l (by simp)
  unfold natTo
  refine Sat.seq_le (openTop_sat hH hv hw hc hp) (by omega) fun c₁ ⟨hr₁, hw₁, hf₁⟩ => ?_
  refine Sat.act_seq (by omega) ?_
  have hv₂ : (Act.run (.set 1 none) c₁).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₁]
  have hw₂ : (Act.run (.set 1 none) c₁).stk .work = bits l ++ .nd :: (.mk 0 :: w) := by
    simp [Act.run, hw₁, encFields]
  refine Sat.seq_le (moveNum2_sat (Ne.symm hs₁) (by decide) hs₂ hv₂ hw₂) (by omega)
    fun c₃ ⟨hr₃, hw₃, hs₃, hj₃⟩ => ?_
  refine (closeCell_sat (r := none) (by rw [hr₃, empty_eq_rv]) hw₃).mono (by omega)
    fun c' ⟨hr', hw', hj'⟩ => ⟨by rw [hr', empty_eq_rv], hw', fun j hj => ?_, l, hl, hlB, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hj' j hj.1, hj₃ j hj.1 hj.2]
    exact hf₁ j (by simpa using hj.1)
  · rw [hj' s hs₁, hs₃]
    simp only [Act.run]
    rw [hf₁ s (by simpa using hs₁)]

/-! ### Counts -/

/-- The bits of a count of `k`: `k` increments of the empty number. -/
def cntBits : ℕ → List Bool
  | 0 => []
  | k + 1 => addBits (cntBits k) [true]

theorem ofBits_cntBits : ∀ k, ofBits (cntBits k) = k
  | 0 => rfl
  | k + 1 => by rw [cntBits, ofBits_addBits, ofBits_cntBits k]; rfl

theorem length_cntBits_le : ∀ k, (cntBits k).length ≤ k + 1
  | 0 => by simp [cntBits]
  | k + 1 => by
    have := length_cntBits_le k
    rw [cntBits, length_addBits]
    simp only [List.length_singleton]
    omega

/-! ### Moving and counting numbers down to a marker -/

theorem head_bits_ne_mk (l : List Bool) (i : Fin 4) : (bits l).head?.getD .nd ≠ .mk i := by
  cases l <;> simp [bits]

/-- Move the numbers on `a` down to the marker `mk i` onto `b`, one by one (so that their order
is reversed); the marker stays. -/
def moveAll (i : Fin 4) (a b : Stk) : Code Stk Sym Rg P :=
  .seq (.act (.peek a 0)) (.seq (.loop (.not (.is 0 (some (.mk i))))
      (.seq (.act (.set 0 none)) (.seq (moveNum2 a b .t0) (.act (.peek a 0)))))
    (.act (.set 0 none)))

theorem moveAll_sat {i : Fin 4} {a b : Stk} (hab : a ≠ b) (ha : a ≠ .t0) (hb : b ≠ .t0)
    {c : Cfg Stk Sym Rg} {ns : List (List Bool)} {rest : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (hc : c.stk a = encNums ns ++ .mk i :: rest)
    (hE : ∀ l ∈ ns, l.length ≤ E) :
    Sat prog (moveAll i a b) c (ns.length * (12 * E + 24) + 5) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = .mk i :: rest ∧
        c'.stk b = encNums ns.reverse ++ c.stk b ∧ Fr [a, b] c c' := by
  have hloop := Sat.loop_list (prog := prog) (b := .not (.is 0 (some (.mk i))))
    (x := .seq (.act (.set 0 none)) (.seq (moveNum2 a b .t0) (.act (.peek a 0))))
    (f := fun l => 12 * l.length + 23)
    (I := fun rs c₁ => ∃ done, done ++ rs = ns ∧ c₁.stk a = encNums rs ++ .mk i :: rest ∧
      c₁.stk b = encNums done.reverse ++ c.stk b ∧ c₁.regs = rv (c₁.stk a).head? none none none ∧
      Fr [a, b] c c₁)
    (Q := fun c₁ => c₁.regs = rv (some (.mk i)) none none none ∧ c₁.stk a = .mk i :: rest ∧
      c₁.stk b = encNums ns.reverse ++ c.stk b ∧ Fr [a, b] c c₁)
    (fun l rs c₁ ⟨done, hd, ha₁, hb₁, hr₁, hf₁⟩ => by
      have ha₁' : c₁.stk a = bits l ++ .nd :: (encNums rs ++ .mk i :: rest) := by
        rw [ha₁]; simp
      refine ⟨by simp [Cond.eval, hr₁, ha₁', head_bits_ne_mk], Sat.act_seq (by omega) ?_⟩
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hr₁]
      refine Sat.seq_le (moveNum2_sat hab ha hb hv₂ ha₁') (by omega)
        fun c₃ ⟨hr₃, ha₃, hb₃, hj₃⟩ => Sat.act_le (by omega)
          ⟨done ++ [l], by simp [← hd], ?_, ?_, ?_, ?_⟩
      · simpa [Act.run] using ha₃
      · simp only [Act.run]
        rw [hb₃]; simp [Act.run, hb₁]
      · rw [empty_eq_rv] at hr₃; simp [Act.run, hr₃]
      · intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        simp only [Act.run]
        rw [hj₃ j hj.1 hj.2]
        exact hf₁ j (by simp [hj.1, hj.2]))
    (fun c₁ ⟨done, hd, ha₁, hb₁, hr₁, hf₁⟩ => by
      simp only [List.append_nil] at hd
      subst hd
      simp only [encNums_nil, List.nil_append] at ha₁
      exact ⟨by simp [Cond.eval, hr₁, ha₁], by rw [hr₁, ha₁]; rfl, ha₁, hb₁, hf₁⟩)
  have hS := sum_map_le_mul (fun l : List Bool => 12 * l.length + 23 + 1) (12 * E + 24) ns
    fun l hl => by have := hE l hl; omega
  unfold moveAll
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop ns _ ⟨[], by simp, ?_, by simp [Act.run],
    by simp [Act.run, hv, empty_eq_rv], fun j _ => rfl⟩) (by omega)
    fun c₂ ⟨hr₂, ha₂, hb₂, hf₂⟩ => Sat.act_le (by omega) ⟨?_, ha₂, hb₂, hf₂⟩)
  · simpa [Act.run] using hc
  · rw [empty_eq_rv]; simp [Act.run, hr₂]

/-- Drop the numbers on `a` down to the marker `mk i` (which stays), counting them onto `t2`. -/
def countAll (i : Fin 4) (a : Stk) : Code Stk Sym Rg P :=
  .seq (.act (.push .t2 .nd)) (.seq (.act (.peek a 0)) (.seq (.loop (.not (.is 0 (some (.mk i))))
      (.seq (.act (.set 0 none)) (.seq (dropNum a) (.seq (incNum .t2 .t1 .t3 .t0)
        (.seq (moveNum2 .t3 .t2 .t0) (.act (.peek a 0)))))))
    (.act (.set 0 none))))

theorem countAll_sat {i : Fin 4} {a : Stk} (ha : a ∉ [.t0, .t1, .t2, .t3])
    {c : Cfg Stk Sym Rg} {ns : List (List Bool)} {rest : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (hc : c.stk a = encNums ns ++ .mk i :: rest)
    (hE : ∀ l ∈ ns, l.length ≤ E) :
    Sat prog (countAll i a) c (ns.length * (2 * E + 35 * ns.length + 150) + 10) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = .mk i :: rest ∧
        c'.stk .t2 = bits (cntBits ns.length) ++ .nd :: c.stk .t2 ∧ Fr [a, .t2] c c' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  obtain ⟨ha₀, ha₁, ha₂, ha₃⟩ := ha
  have hloop := Sat.loop_list (prog := prog) (b := .not (.is 0 (some (.mk i))))
    (x := .seq (.act (.set 0 none)) (.seq (dropNum a) (.seq (incNum .t2 .t1 .t3 .t0)
        (.seq (moveNum2 .t3 .t2 .t0) (.act (.peek a 0))))))
    (f := fun l => 2 * E + 35 * ns.length + 149)
    (I := fun rs c₁ => ∃ done, done ++ rs = ns ∧ c₁.stk a = encNums rs ++ .mk i :: rest ∧
      c₁.stk .t2 = bits (cntBits done.length) ++ .nd :: c.stk .t2 ∧
      c₁.regs = rv (c₁.stk a).head? none none none ∧ Fr [a, .t2] c c₁)
    (Q := fun c₁ => c₁.regs = rv (some (.mk i)) none none none ∧ c₁.stk a = .mk i :: rest ∧
      c₁.stk .t2 = bits (cntBits ns.length) ++ .nd :: c.stk .t2 ∧ Fr [a, .t2] c c₁)
    (fun l rs c₁ ⟨done, hd, ha₁', ht₁, hr₁, hf₁⟩ => by
      have hlE : l.length ≤ E := hE l (by rw [← hd]; simp)
      have hdn : done.length + 1 ≤ ns.length := by
        have := congrArg List.length hd; simp at this; omega
      have hcn := length_cntBits_le done.length
      have ha₁'' : c₁.stk a = bits l ++ .nd :: (encNums rs ++ .mk i :: rest) := by
        rw [ha₁']; simp
      refine ⟨by simp [Cond.eval, hr₁, ha₁'', head_bits_ne_mk], Sat.act_seq (by omega) ?_⟩
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hr₁]
      refine Sat.seq_le (dropNum_sat hv₂ ha₁'') (by omega) fun c₃ ⟨hr₃, ha₃', hj₃⟩ => ?_
      have ht₃ : c₃.stk .t2 = bits (cntBits done.length) ++ .nd :: c.stk .t2 := by
        rw [hj₃ .t2 (Ne.symm ha₂)]; exact ht₁
      refine Sat.seq_le (incNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) hr₃ ht₃) (by omega) fun c₄ ⟨hr₄, ht₄, ho₄, hj₄⟩ => ?_
      have hlen := length_addBits (cntBits done.length) [true]
      simp only [List.length_singleton] at hlen
      refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₄ ho₄)
        (by omega) fun c₅ ⟨hr₅, ho₅, ht₅, hj₅⟩ => Sat.act_le (by omega)
          ⟨done ++ [l], by simp [← hd], ?_, ?_, ?_, ?_⟩
      · simp only [Act.run]
        rw [hj₅ a ha₃ ha₂, hj₄ a ha₂ ha₃]; exact ha₃'
      · simp only [Act.run]
        rw [ht₅, ht₄]
        simp [cntBits]
      · rw [empty_eq_rv] at hr₅
        simp only [Act.run]
        rw [hj₅ a ha₃ ha₂, hj₄ a ha₂ ha₃, ha₃', hr₅]
        simp
      · intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        simp only [Act.run]
        by_cases hj3 : j = .t3
        · subst hj3
          rw [ho₅, hj₃ .t3 (Ne.symm ha₃)]
          exact hf₁ .t3 (by simp [Ne.symm ha₃])
        rw [hj₅ j hj3 hj.2, hj₄ j hj.2 hj3, hj₃ j hj.1]
        exact hf₁ j (by simp [hj.1, hj.2]))
    (fun c₁ ⟨done, hd, ha₁', ht₁, hr₁, hf₁⟩ => by
      simp only [List.append_nil] at hd
      subst hd
      simp only [encNums_nil, List.nil_append] at ha₁'
      exact ⟨by simp [Cond.eval, hr₁, ha₁'], by rw [hr₁, ha₁']; rfl, ha₁', ht₁, hf₁⟩)
  have hS : (ns.map fun _ => 2 * E + 35 * ns.length + 149 + 1).sum =
      ns.length * (2 * E + 35 * ns.length + 150) := by
    rw [sum_map_const]
  unfold countAll
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.seq_le (hloop ns _ ⟨[], by simp,
    ?_, ?_, ?_, ?_⟩) (by omega) fun c₂ ⟨hr₂, ha₂', ht₂, hf₂⟩ =>
      Sat.act_le (by omega) ⟨?_, ha₂', ht₂, hf₂⟩))
  · simpa [Act.run, update_of_ne ha₂] using hc
  · simp [Act.run, cntBits]
  · simp [Act.run, hv, empty_eq_rv, update_of_ne ha₂]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp [Act.run, update_of_ne hj.2]
  · rw [empty_eq_rv]; simp [Act.run, hr₂]

/-! ### Walking and building lists -/

/-- Walk the list whose pointer is on `ptr`, pushing the pointers of its elements onto `s` (the
last on top). -/
def walkList (s : Stk) : Code Stk Sym Rg P :=
  .seq fetchCell (.seq (.loop (.is 1 (some (.tag .cons)))
      (.seq (.act (.set 1 none)) (.seq (moveNum2 .work s .t0) (.seq (moveNum2 .work .ptr .t0)
        (.seq closeCell fetchCell)))))
    (.seq (.act (.set 1 none)) closeCell))

theorem walkList_sat {s : Stk} (hs : s ∉ [.work, .ptr, .t0, .heap, .scan, .cnt]) {B F : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) {a : Ty} {xs : List a.denote} {q : List Bool} {rp : List Sym}
    (hp : c.stk .ptr = bits q ++ .nd :: rp) (hr : Rep h (.list a) xs (ofBits q)) {E : ℕ}
    (hq : q.length ≤ E) (hE : B + h.length ≤ E) :
    Sat prog (walkList s) c ((xs.length + 1) * (fcE (encHeap h).length E + 24 * E + 50))
      fun c' => c'.regs = Regs.empty ∧ c'.stk .ptr = rp ∧ Fr [.ptr, s] c c' ∧ ∃ psr,
        RepList h a xs.reverse psr ∧ (∀ p ∈ psr, p.length < B + h.length) ∧
        c'.stk s = encNums psr ++ c.stk s := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
  obtain ⟨hsw, hsp, hs0, hsh, hss, hsc⟩ := hs
  have hloop := Sat.loop_list (prog := prog) (b := .is 1 (some (.tag .cons)))
    (x := .seq (.act (.set 1 none)) (.seq (moveNum2 .work s .t0) (.seq (moveNum2 .work .ptr .t0)
        (.seq closeCell fetchCell))))
    (f := fun _ => fcE (encHeap h).length E + 24 * E + 46)
    (I := fun rs c₁ => ∃ done psr fs, done ++ rs = xs ∧ RepList h a done.reverse psr ∧
      (∀ p ∈ psr, p.length < B + h.length) ∧ c₁.stk s = encNums psr ++ c.stk s ∧
      c₁.regs = rv none (some (.tag (listTag rs))) none none ∧
      c₁.stk .work = encFields fs ++ .mk 0 :: c.stk .work ∧ ListCell h a rs fs ∧
      (∀ f ∈ fs, f.length < B + h.length) ∧ c₁.stk .ptr = rp ∧ Fr [.work, .ptr, s] c c₁)
    (Q := fun c₁ => ∃ psr, RepList h a xs.reverse psr ∧ (∀ p ∈ psr, p.length < B + h.length) ∧
      c₁.stk s = encNums psr ++ c.stk s ∧ c₁.regs = rv none (some (.tag .nil)) none none ∧
      c₁.stk .work = .mk 0 :: c.stk .work ∧ c₁.stk .ptr = rp ∧ Fr [.work, .ptr, s] c c₁)
    (fun x rs c₁ ⟨done, psr, fs, hd, hR, hpB, hs₁, hr₁, hw₁, hL, hfB, hp₁, hf₁⟩ => by
      obtain ⟨l₁, l₂, rfl, r₁, r₂, -, -⟩ := hL
      have hl₁ := hfB l₁ (by simp)
      have hl₂ := hfB l₂ (by simp)
      refine ⟨by simp [Cond.eval, hr₁, listTag], Sat.act_seq (by omega) ?_⟩
      have hv₂ : (Act.run (.set 1 none) c₁).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hr₁]
      have hw₂ : (Act.run (.set 1 none) c₁).stk .work =
          bits l₁ ++ .nd :: (bits l₂ ++ .nd :: .mk 0 :: c.stk .work) := by
        simp [Act.run, hw₁, encFields]
      refine Sat.seq_le (moveNum2_sat (Ne.symm hsw) (by decide) hs0 hv₂ hw₂) (by omega)
        fun c₃ ⟨hr₃, hw₃, hs₃, hj₃⟩ => ?_
      refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₃ hw₃) (by omega)
        fun c₄ ⟨hr₄, hw₄, hp₄, hj₄⟩ => ?_
      refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₄, empty_eq_rv]) hw₄) (by omega)
        fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
      obtain ⟨fs', hc', hL'⟩ := r₂.list_inv
      have hp₅ : c₅.stk .ptr = bits l₂ ++ .nd :: rp := by
        rw [hj₅ .ptr (by decide), hp₄, hj₃ .ptr (by decide) (Ne.symm hsp)]
        simpa [Act.run] using hp₁
      have hH₅ : HeapAt h c₅ := by
        refine hH.frame ?_ ?_ ?_ <;>
          rw [hj₅ _ (by decide), hj₄ _ (by decide) (by decide), hj₃ _ (by decide) (by
            first | exact Ne.symm hsh | exact Ne.symm hss | exact Ne.symm hsc)] <;>
          simp only [Act.run] <;> exact hf₁ _ (by simp [Ne.symm hsh, Ne.symm hss, Ne.symm hsc])
      refine (fetchCellE_sat (E := E) hH₅.wf hH₅.heap hH₅.scan (by rw [hr₅, empty_eq_rv]) hc'
        (by omega) hp₅).mono (by omega) fun c₆ ⟨hr₆, hw₆, hp₆, hj₆⟩ =>
          ⟨done ++ [x], l₁ :: psr, fs', by simp [← hd], ?_, ?_, ?_, hr₆, ?_, hL',
            hB.field_lt hc', hp₆, ?_⟩
      · have r : RepList h a (x :: done.reverse) (l₁ :: psr) := List.Forall₂.cons r₁ hR
        simpa using r
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hl₁
        · exact hpB p hp
      · rw [hj₆ s hsw hsp, hj₅ s hsw, hj₄ s hsw hsp, hs₃]
        simp [Act.run, hs₁]
      · rw [hw₆, hw₅]
      · intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        rw [hj₆ j hj.1 hj.2.1, hj₅ j hj.1, hj₄ j hj.1 hj.2.1, hj₃ j hj.1 hj.2.2]
        simp only [Act.run]
        exact hf₁ j (by simp [hj.1, hj.2.1, hj.2.2]))
    (fun c₁ ⟨done, psr, fs, hd, hR, hpB, hs₁, hr₁, hw₁, hL, hfB, hp₁, hf₁⟩ => by
      simp only [List.append_nil] at hd
      subst hd
      simp only [ListCell] at hL
      subst hL
      exact ⟨by simp [Cond.eval, hr₁, listTag], psr, hR, hpB, hs₁, hr₁,
        by simpa [encFields] using hw₁,
        hp₁, hf₁⟩)
  obtain ⟨fs, hc, hL⟩ := hr.list_inv
  have hS : (xs.map fun _ => fcE (encHeap h).length E + 24 * E + 46 + 1).sum =
      xs.length * (fcE (encHeap h).length E + 24 * E + 47) :=
    sum_map_const _ _
  have hM : (xs.length + 1) * (fcE (encHeap h).length E + 24 * E + 50) =
      xs.length * (fcE (encHeap h).length E + 24 * E + 47) + 3 * xs.length +
        (fcE (encHeap h).length E + 24 * E + 50) := by ring
  unfold walkList
  refine Sat.seq_le (fetchCellE_sat hH.wf hH.heap hH.scan hv hc hq hp) (by omega)
    fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine Sat.seq_le (hloop xs c₁ ⟨[], [], fs, by simp, List.Forall₂.nil, by simp, ?_, hr₁, hw₁,
    hL, hB.field_lt hc, hp₁, ?_⟩) (by omega) fun c₂ ⟨psr, hR, hpB, hs₂, hr₂, hw₂, hp₂, hf₂⟩ => ?_
  · rw [hj₁ s hsw hsp]; simp
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    exact hj₁ j hj.1 hj.2.1
  refine Sat.act_seq (by omega) ?_
  refine (closeCell_sat (r := none) (w := c.stk .work) (by simp [Act.run, hr₂])
    (by simpa [Act.run] using hw₂)).mono
    (by omega) fun c' ⟨hr', hw', hj'⟩ => ⟨by rw [hr', empty_eq_rv], ?_, ?_, psr, hR, hpB, ?_⟩
  · rw [hj' .ptr (by decide)]; simpa [Act.run] using hp₂
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    by_cases hjw : j = .work
    · subst hjw; rw [hw']
    rw [hj' j hjw]
    simp only [Act.run]
    exact hf₂ j (by simp [hjw, hj.1, hj.2])
  · rw [hj' s hsw]; simpa [Act.run] using hs₂

/-- From the pointers `psr` of the elements `ys` on `s` (the first on top) above the marker
`mk 3`, and the pointer of a list `bs` on `work`, the cons cells of `ys.reverse ++ bs` (the top
of `s` is consed first); the marker is dropped. -/
def buildListB (s : Stk) : Code Stk Sym Rg P :=
  .seq (.act (.peek s 0)) (.seq (.loop (.not (.is 0 (some (.mk 3))))
      (.seq (.act (.set 0 none)) (.seq (moveNum2 .work .t1 .t0) (.seq (.act (.push .work (.mk 2)))
        (.seq (moveNum2 .t1 .work .t0) (.seq (moveNum2 s .work .t0)
          (.seq (alloc .cons) (.act (.peek s 0)))))))))
    (.seq (.act (.pop s 0)) (.act (.set 0 none))))

theorem buildListB_sat {s : Stk} (hs : s ∉ [.work, .t0, .t1, .heap, .scan, .cnt]) {B F : ℕ}
    (h1B : 1 ≤ B) (h2F : 2 ≤ F) {a : Ty} {ys : List a.denote} {psr : List (List Bool)}
    {bs : List a.denote} {q : List Bool} {h : List Cell} {c : Cfg Stk Sym Rg} {w rest : List Sym}
    (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
    (hs' : c.stk s = encNums psr ++ .mk 3 :: rest) (hw : c.stk .work = bits q ++ .nd :: w)
    (hR : RepList h a ys psr) (hq : Rep h (.list a) bs (ofBits q))
    (hpB : ∀ p ∈ psr, p.length ≤ B + h.length) (hqB : q.length ≤ B + h.length) :
    Sat prog (buildListB s) c (psr.length * (36 * (B + h.length + psr.length) +
      allocBound (2 * (B + h.length + psr.length) + 2) (B + h.length + psr.length) + 72) + 8)
      fun c' => c'.regs = Regs.empty ∧ c'.stk s = rest ∧ ∃ h' q', HeapAt (h ++ h') c' ∧
        HeapBnd B F (h ++ h') ∧ h'.length = psr.length ∧ q'.length ≤ B + (h ++ h').length ∧
        Rep (h ++ h') (.list a) (ys.reverse ++ bs) (ofBits q') ∧
        c'.stk .work = bits q' ++ .nd :: w ∧ Fr [.heap, .cnt, .work, s] c c' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
  obtain ⟨hsw, hs0, hs1, hsh, hss, hsc⟩ := hs
  obtain ⟨U, hU⟩ : ∃ U, U = B + h.length + psr.length := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = allocBound (2 * U + 2) U := ⟨_, rfl⟩
  rw [← hU, ← hA]
  have hloop := Sat.loop_list (prog := prog) (b := .not (.is 0 (some (.mk 3))))
    (x := .seq (.act (.set 0 none)) (.seq (moveNum2 .work .t1 .t0)
      (.seq (.act (.push .work (.mk 2))) (.seq (moveNum2 .t1 .work .t0) (.seq (moveNum2 s .work .t0)
        (.seq (alloc .cons) (.act (.peek s 0))))))))
    (f := fun _ => 36 * U + A + 71)
    (I := fun prs c₁ => ∃ dp dy rys q₁ h₁, dp ++ prs = psr ∧ dy ++ rys = ys ∧
      RepList h a rys prs ∧ HeapAt (h ++ h₁) c₁ ∧ HeapBnd B F (h ++ h₁) ∧
      h₁.length = dp.length ∧ q₁.length ≤ B + (h ++ h₁).length ∧
      Rep (h ++ h₁) (.list a) (dy.reverse ++ bs) (ofBits q₁) ∧
      c₁.stk .work = bits q₁ ++ .nd :: w ∧ c₁.stk s = encNums prs ++ .mk 3 :: rest ∧
      c₁.regs = rv (c₁.stk s).head? none none none ∧ Fr [.heap, .cnt, .work, s] c c₁)
    (Q := fun c₁ => ∃ q₁ h₁, HeapAt (h ++ h₁) c₁ ∧ HeapBnd B F (h ++ h₁) ∧
      h₁.length = psr.length ∧ q₁.length ≤ B + (h ++ h₁).length ∧
      Rep (h ++ h₁) (.list a) (ys.reverse ++ bs) (ofBits q₁) ∧
      c₁.stk .work = bits q₁ ++ .nd :: w ∧ c₁.stk s = .mk 3 :: rest ∧
      c₁.regs = rv (some (.mk 3)) none none none ∧ Fr [.heap, .cnt, .work, s] c c₁)
    (fun p prs c₁ ⟨dp, dy, rys, q₁, h₁, hdp, hdy, hR₁, hH₁, hB₁, hl₁, hq₁, hr₁, hw₁, hs₁, hv₁,
        hf₁⟩ => by
      obtain ⟨y, rys', hy, hR₁', rfl⟩ := List.forall₂_cons_right_iff.1 hR₁
      have hpU : p.length ≤ B + h.length := hpB p (by rw [← hdp]; simp)
      have hdl : dp.length + 1 ≤ psr.length := by
        have := congrArg List.length hdp; simp at this; omega
      have hs₁' : c₁.stk s = bits p ++ .nd :: (encNums prs ++ .mk 3 :: rest) := by
        rw [hs₁]; simp
      refine ⟨by simp [Cond.eval, hv₁, hs₁', head_bits_ne_mk], Sat.act_seq (by omega) ?_⟩
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hv₁]
      simp only [List.length_append] at hq₁
      refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv₂ hw₁) (by omega)
        fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => Sat.act_seq (by omega) ?_
      refine Sat.seq_le (moveNum2_sat (l := q₁) (rest := c₁.stk .t1) (by decide) (by decide)
        (by decide)
        hr₃ (by simpa [Act.run] using ht₃)) (by omega) fun c₄ ⟨hr₄, ht₄, hw₄, hj₄⟩ => ?_
      have hs₄ : c₄.stk s = bits p ++ .nd :: (encNums prs ++ .mk 3 :: rest) := by
        rw [hj₄ s hs1 hsw]
        simp only [Act.run]
        rw [update_of_ne hsw, hj₃ s hsw hs1]
        simpa [Act.run] using hs₁'
      refine Sat.seq_le (moveNum2_sat hsw hs0 (by decide) hr₄ hs₄) (by omega)
        fun c₅ ⟨hr₅, hs₅, hw₅, hj₅⟩ => ?_
      have hw₅' : c₅.stk .work = encFields [p, q₁] ++ .mk 2 :: w := by
        rw [hw₅, hw₄]
        simp [Act.run, hw₃, encFields]
      have hf₅ : Fr [.work, .t1, s] c₁ c₅ := fun j hj => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        rw [hj₅ j hj.2.2 hj.1, hj₄ j hj.2.1 hj.1]
        simp only [Act.run]
        rw [update_of_ne hj.1, hj₃ j hj.1 hj.2.1]
        rfl
      have hH₅ : HeapAt (h ++ h₁) c₅ := hH₁.fr hf₅ (by simp [Ne.symm hsh]) (by simp [Ne.symm hss])
        (by simp [Ne.symm hsc])
      have hbnd := allocBound_mono (a := (encFields [p, q₁]).length) (b := 2 * U + 2)
        (by simp [encFields]; omega) (by simp; omega : (h ++ h₁).length ≤ U)
      rw [← hA] at hbnd
      refine Sat.seq_le (allocB_sat .cons hH₅ hB₁ h1B hr₅ hw₅' (by simp; omega) ?_) (by omega)
        fun c₆ ⟨hr₆, l, hH₆, hB₆, hc₆, hl₆, hw₆, hf₆⟩ => Sat.act_le (by omega)
          ⟨dp ++ [p], dy ++ [y], rys', l, h₁ ++ [⟨l, .cons, [p, q₁]⟩], by simp [← hdp],
            by simp [← hdy], hR₁', by rw [← List.append_assoc]; exact hH₆.frame rfl rfl rfl,
            by simpa using hB₆, by simp [hl₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · simp only [List.length_append]; omega
        · simp only [List.length_append]; omega
      · simp only [List.length_append, List.length_singleton] at hl₆ ⊢; omega
      · have r := Rep.cons hc₆ (hy.mono.mono (h' := [⟨l, .cons, [p, q₁]⟩]))
          (hr₁.mono (h' := [⟨l, .cons, [p, q₁]⟩]))
        simpa [List.append_assoc] using r
      · simpa [Act.run] using hw₆
      · simp only [Act.run]
        rw [hf₆ s (by simp [hsh, hsc, hsw]), hs₅]
      · simp only [Act.run]
        rw [hr₆, empty_eq_rv, update_rv_zero]
      · intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        simp only [Act.run]
        rw [hf₆ j (by simp [hj.1, hj.2.1, hj.2.2.1])]
        by_cases hj1 : j = .t1
        · subst hj1
          rw [hj₅ .t1 (Ne.symm hs1) (by decide), ht₄]
          exact hf₁ .t1 (by simp [Ne.symm hs1])
        · rw [hf₅ j (by simp [hj.2.2.1, hj1, hj.2.2.2])]
          exact hf₁ j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2]))
    (fun c₁ ⟨dp, dy, rys, q₁, h₁, hdp, hdy, hR₁, hH₁, hB₁, hl₁, hq₁, hr₁, hw₁, hs₁, hv₁,
        hf₁⟩ => by
      simp only [List.append_nil] at hdp
      subst hdp
      obtain rfl := List.forall₂_nil_right_iff.1 hR₁
      simp only [List.append_nil] at hdy
      subst hdy
      simp only [encNums_nil, List.nil_append] at hs₁
      exact ⟨by simp [Cond.eval, hv₁, hs₁], q₁, h₁, hH₁, hB₁, hl₁, hq₁, hr₁, hw₁, hs₁,
        by rw [hv₁, hs₁]; rfl, hf₁⟩)
  have hS : (psr.map fun _ => 36 * U + A + 71 + 1).sum = psr.length * (36 * U + A + 72) :=
    sum_map_const _ _
  unfold buildListB
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop psr _ ⟨[], [], ys, q, [], by simp, by simp,
    hR, by rw [List.append_nil]; exact hH.frame rfl rfl rfl, by simpa using hB, rfl,
    by simpa using hqB, by simpa using hq, ?_, ?_,
    ?_, fun j _ => rfl⟩) (by omega) fun c₂ ⟨q₁, h₁, hH₂, hB₂, hl₂, hq₂, hr₂, hw₂, hs₂, hv₂,
      hf₂⟩ => Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_, h₁, q₁, ?_, hB₂, hl₂, hq₂,
        hr₂, ?_, ?_⟩))
  · simpa [Act.run] using hw
  · simpa [Act.run] using hs'
  · simp [Act.run, hv, empty_eq_rv]
  · rw [empty_eq_rv]; simp [Act.run, hv₂]
  · simp [Act.run, hs₂]
  · exact hH₂.frame (by simp [Act.run, update_of_ne (Ne.symm hsh)])
      (by simp [Act.run, update_of_ne (Ne.symm hss)])
      (by simp [Act.run, update_of_ne (Ne.symm hsc)])
  · simp [Act.run, update_of_ne (Ne.symm hsw), hw₂]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [Act.run]
    rw [update_of_ne hj.2.2.2]
    exact hf₂ j (by simp [hj.1, hj.2.1, hj.2.2.1, hj.2.2.2])

end GraphIso.TM
