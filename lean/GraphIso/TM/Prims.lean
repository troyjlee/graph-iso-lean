module

public import GraphIso.TM.PrimLib

/-!
# The primitives

Stage 17f (`PLAN-17.md` §9): code for each of the 27 primitives (`primCode`) and its
specification **`primCode_spec`** : `PrimSpec prog primCode B F K Q`, for every program `prog`,
under `F + 1 ≤ B`, `2 ≤ F` and `primB (B + N) ≤ Q N` for every `N`.

The arguments' pointers are on `work` (the last on top), and the code replaces them by the
pointer of the result:
* `unit`, `boolLit`, `none`, `nil`, `pair`, `some`, `cons`: one cell from the arguments
  (`allocArgs`); `natLit k`: one cell with the bits of `k` (`natLitCode`);
* `fst`, `snd`: a field of the pair (`fstCode`, `sndCode`); `and`, `or`: one of the arguments,
  by the tag of the second (`boolSel`); no new cell; `not`: one cell (`notCode`);
* `add`, `sub` (`arithCode`), `natEq`, `natLt` (`cmpCode`): the 17b arithmetic on the bits of
  the arguments, one cell;
* `length` (walk the list, count: `lengthCode`), `reverse` (walk, reverse the pointers, cons
  them onto a new `nil`: `reverseCode`), `append` (walk the first list, cons its elements onto
  the second: `appendCode`), `range k` (count up to `k`, a natural per count, cons onto a new
  `nil`: `rangeCode`);
* `arrayMk k v` (`k` copies of the pointer of `v`, one cell: `arrayMkCode`), `arraySize`
  (count the fields: `arraySizeCode`), `arrayGet` (drop fields while counting the index down;
  past the fields, new cells for the default value, `allocDefault`: `arrayGetCode`),
  `arrayUpdate` (the fields above `mk 2`, each write applied in order by `setAt`, then one cell:
  `arrayUpdateCode`), `arrayOfList`, `arrayToList` (`arrayOfListCode`, `arrayToListCode`).

**Bounds.** `PrimOut` is the shape of each result: at most `G` new cells (`K` times the cost in
`primCode_spec`), and at most `C * primB M` steps, for `C` the primitive's cost and `M` the sum
of `B` and the final heap's length in symbols, with
`primB M = (2 M + 10) (fcE M M + allocBound (M² + 3 M + 2) M + 100 M + 100)`. A unit of cost
pays for a few lookups, the allocation of a cell of at most `(M + 1) (M + 2)` symbols, and scans
over at most `2 M` numbers of at most `M` bits (the at most `F ≤ M` fields of a cell, and the at
most `tySize ≤ K ≤ B ≤ M` cells of a default value). The code looks cells up before it
allocates any, so the step bounds are fixed in advance (`PrimOut.of_sat`); only `arrayGet`
chooses its bound after the scan (`PrimOut.seq`).

**Registers.** The code of every primitive starts and ends with empty registers
(`primCode_spec`). Inside it, `openTop` leaves a tag in register `1`, and the tests of the
loops leave their result for the loop's condition: `mkTest` and `rangeTest` a bit in register
`0`; `getTest` and `updTest` the top of `work` in register `0` and a bit in register `1`.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost Function

variable {P : Type} {prog : Program Stk Sym Rg P}

/-! ### The bound and the shape of the results -/

/-- The step bound of the primitives' code per unit of cost, for heaps, pointers and numbers of
at most `M` symbols: up to `2 M + 10` lookups, allocations of cells of at most `(M + 1) (M + 2)`
symbols, and linear scans. -/
def primB (M : ℕ) : ℕ :=
  (2 * M + 10) * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100)

/-- The code `x` replaces the arguments' pointers, above `w` on `work`, by a pointer to a
representation of `v`, appending at most `G` cells, within `C * primB M` steps (`M` is `B` plus
the final heap's length in symbols). -/
def PrimOut (prog : Program Stk Sym Rg P) (x : Code Stk Sym Rg P) (c : Cfg Stk Sym Rg)
    (h : List Cell) (w : List Sym) (t : Ty) (v : t.denote) (B F G C : ℕ) : Prop :=
  ∃ c' n h' l, Exec prog x c c' n ∧ HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
    c'.regs = Regs.empty ∧ Rep (h ++ h') t v (ofBits l) ∧ l.length ≤ B + (h ++ h').length ∧
    c'.stk .work = bits l ++ .nd :: w ∧ Fr [.heap, .cnt, .work] c c' ∧ h'.length ≤ G ∧
    n ≤ C * primB (B + (encHeap (h ++ h')).length)

theorem PrimOut.of_sat {x : Code Stk Sym Rg P} {c : Cfg Stk Sym Rg} {h : List Cell}
    {w : List Sym} {t : Ty} {v : t.denote} {B F G C T : ℕ}
    (hs : Sat prog x c T fun c' => ∃ h' l, HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
      c'.regs = Regs.empty ∧ Rep (h ++ h') t v (ofBits l) ∧ l.length ≤ B + (h ++ h').length ∧
      c'.stk .work = bits l ++ .nd :: w ∧ Fr [.heap, .cnt, .work] c c' ∧ h'.length ≤ G ∧
      T ≤ C * primB (B + (encHeap (h ++ h')).length)) : PrimOut prog x c h w t v B F G C := by
  obtain ⟨c', n, e, hn, h', l, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
  exact ⟨c', n, h', l, e, h1, h2, h3, h4, h5, h6, h7, h8, hn.trans h9⟩

/-- The sizes at the start are at most the final `M`. -/
theorem sizes_le (B : ℕ) (h h' : List Cell) :
    B + h.length ≤ B + (encHeap (h ++ h')).length ∧
      (encHeap h).length ≤ B + (encHeap (h ++ h')).length ∧
      (h ++ h').length ≤ (encHeap (h ++ h')).length :=
  ⟨by have := length_le_encHeap_append h h'; omega,
    by have := length_encHeap_mono h h'; omega, length_le_encHeap _⟩

theorem primB_ge (M : ℕ) :
    4 * fcE M M + 3 * allocBound (2 * M + 2) M + 100 * (M * M) + 1000 * M + 1000 ≤ primB M := by
  have hA := allocBound_mono (a := 2 * M + 2) (b := M * M + 3 * M + 2) (m := M) (n := M)
    (by nlinarith) le_rfl
  have e : primB M = 2 * (M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100)) +
      10 * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) := by
    unfold primB; ring
  have : 100 * (M * M) ≤ M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) := by
    nlinarith
  omega

/-- The bound per unit of cost covers `M` lookups and allocations. -/
theorem primB_ge' (M : ℕ) :
    M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) +
      M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) +
      10 * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) ≤ primB M := by
  unfold primB; nlinarith

theorem le_mul_primB {C X M : ℕ} (hC : 1 ≤ C) (hX : X ≤ primB M) : X ≤ C * primB M :=
  hX.trans (Nat.le_mul_of_pos_left _ hC)

/-! ### One cell from the arguments -/

theorem out_allocArgs (tg : Tag) {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {ls : List (List Bool)} {w : List Sym} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc ls ++ w)
    (hF : ls.length ≤ F) (h2 : ls.length ≤ 2) (hls : ∀ l ∈ ls, l.length ≤ B + h.length)
    {t : Ty} {v : t.denote}
    (hrep : ∀ l, CellAt (h ++ [⟨l, tg, ls⟩]) (ofBits l) tg ls →
      Rep (h ++ [⟨l, tg, ls⟩]) t v (ofBits l)) {G C : ℕ} (hG : 1 ≤ G) (hC : 1 ≤ C) :
    PrimOut prog (allocArgs tg ls.length) c h w t v B F G C := by
  refine PrimOut.of_sat ((allocArgs_sat tg hH hB h1B hv hw hF hls).mono le_rfl
    fun c' ⟨hr, l, hH', hB', hc', hl', hw', hf'⟩ => ⟨[⟨l, tg, ls⟩], l, hH', hB', hr, hrep l hc',
      by simp; omega, hw', hf', by simpa using hG, ?_⟩)
  obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, tg, ls⟩]
  obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, tg, ls⟩])).length := ⟨_, rfl⟩
  rw [← hM] at s1 s2 ⊢
  have hLf := length_encFields_le ls hls
  have hm₁ : ls.length * (B + h.length + 1) ≤ 2 * (B + h.length + 1) :=
    Nat.mul_le_mul_right _ h2
  have hm₂ : ls.length * (12 * (B + h.length) + 20) ≤ 2 * (12 * (B + h.length) + 20) :=
    Nat.mul_le_mul_right _ h2
  have hA := allocBound_mono (a := (encFields ls).length) (b := 2 * M + 2) (m := h.length)
    (n := M) (by omega) (by omega)
  refine le_mul_primB hC ((primB_ge M).trans' ?_)
  omega

/-- A natural literal: one cell with the bits of `k`. -/
def natLitCode (k : ℕ) : Code Stk Sym Rg P :=
  .seq (.act (.push .work (.mk 2))) (.seq (pushNum (toBits k) .work) (alloc .nat))

theorem out_natLit (k : ℕ) {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    (hH : HeapAt h c) (hB : HeapBnd B F h) (h1F : 1 ≤ F) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = w) (hk : (toBits k).length + 1 ≤ B) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) : PrimOut prog (natLitCode k) c h w .nat k B F G C := by
  unfold natLitCode
  refine PrimOut.of_sat (T := 2 * (toBits k).length + allocBound (encFields [toBits k]).length
    h.length + 5) (Sat.act_seq (by omega) ?_)
  have hH₁ : HeapAt h (Act.run (.push .work (.mk 2)) c) :=
    hH.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  refine Sat.seq_le (pushNum_sat (prog := prog) Stk.work (Act.run (.push .work (.mk 2)) c)
    (toBits k)) (by omega) fun c₂ ⟨hr₂, hw₂, hj₂⟩ => ?_
  have hH₂ : HeapAt h c₂ := hH₁.fr (fr1 hj₂) (by decide) (by decide) (by decide)
  have hw₂' : c₂.stk .work = encFields [toBits k] ++ .mk 2 :: w := by
    rw [hw₂]; simp [Act.run, hw, encFields]
  refine (allocB_sat .nat hH₂ hB (by omega) (by rw [hr₂]; exact hv) hw₂' (by simpa using h1F)
    (by simp; omega)).mono (by omega) fun c' ⟨hr', l, hH', hB', hc', hl', hw', hf'⟩ =>
      ⟨[⟨l, .nat, [toBits k]⟩], l, hH', hB', hr', by simpa [ofBits_toBits] using Rep.nat hc',
        by simp; omega, hw', ?_, by simpa using hG, ?_⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hf' j (by simp [hj.1, hj.2.1, hj.2.2]), hj₂ j hj.2.2]
    simp [Act.run, update_of_ne hj.2.2]
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .nat, [toBits k]⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .nat, [toBits k]⟩])).length := ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hA := allocBound_mono (a := (encFields [toBits k]).length) (b := 2 * M + 2)
      (m := h.length) (n := M) (by simp [encFields]; omega) (by omega)
    refine le_mul_primB hC ((primB_ge M).trans' ?_)
    omega

/-! ### Projections and Booleans -/

/-- The first field of the pair whose pointer is on `work`. -/
def fstCode : Code Stk Sym Rg P :=
  .seq openTop (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .t1 .t0) (.seq (dropNum .work)
    (.seq closeCell (moveNum2 .t1 .work .t0)))))

/-- The second field of the pair whose pointer is on `work`. -/
def sndCode : Code Stk Sym Rg P :=
  .seq openTop (.seq (.act (.set 1 none)) (.seq (dropNum .work) (.seq (moveNum2 .work .t1 .t0)
    (.seq closeCell (moveNum2 .t1 .work .t0)))))

/-- The result is an existing pointer `l`: no new cell. -/
theorem out_old {x : Code Stk Sym Rg P} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {w : List Sym} {t : Ty} {v : t.denote} {T G C : ℕ} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hC : 1 ≤ C) (hT : ∀ M, B + h.length ≤ M → (encHeap h).length ≤ M → T ≤ primB M)
    (hs : Sat prog x c T fun c' => c'.regs = Regs.empty ∧ ∃ l, Rep h t v (ofBits l) ∧
      l.length ≤ B + h.length ∧ c'.stk .work = bits l ++ .nd :: w ∧
      Fr [.work, .t0, .t1, .t2, .t3, .ptr] c c' ∧ c'.stk .t0 = c.stk .t0 ∧
      c'.stk .t1 = c.stk .t1 ∧ c'.stk .t2 = c.stk .t2 ∧ c'.stk .t3 = c.stk .t3 ∧
      c'.stk .ptr = c.stk .ptr) :
    PrimOut prog x c h w t v B F G C :=
  PrimOut.of_sat (hs.mono le_rfl fun c' ⟨hr, l, hR, hl, hw, hf, e0, e1, e2, e3, ep⟩ => by
    have hf' : Fr [.heap, .cnt, .work] c c' :=
      ((((((hf.mono (T := [.ptr, .t3, .t2, .t1, .t0, .heap, .cnt, .work]) (by decide)).restore
        ep).restore e3).restore e2).restore e1).restore e0)
    obtain ⟨s1, s2, -⟩ := sizes_le B h []
    refine ⟨[], l, by simpa using hH.fr hf (by decide) (by decide) (by decide),
      by simpa using hB, hr, by simpa using hR, by simpa using hl, hw, hf', by simp,
      le_mul_primB hC (hT _ s1 s2)⟩)

theorem out_fst {a b : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {x : (Ty.prod a b).denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h (.prod a b) x (ofBits lx)) (hlx : lx.length ≤ B + h.length) {G C : ℕ}
    (hC : 1 ≤ C) : PrimOut prog fstCode c h w a x.1 B F G C := by
  obtain ⟨l₁, l₂, hc, r₁, r₂⟩ := hr.pair_inv
  have hl₁ := hB.field_lt hc l₁ (by simp)
  have hl₂ := hB.field_lt hc l₂ (by simp)
  refine out_old (T := fcE (encHeap h).length (B + h.length) + 60 * (B + h.length) + 100) hH hB
    hC (fun M h1 h2 => (primB_ge M).trans' (by have := fcE_mono h2 h1; omega)) ?_
  unfold fstCode
  refine Sat.seq_le (openTop_sat (w := w) hH hv (by simpa [envEnc] using hw) hc hlx) (by omega)
    fun c₁ ⟨hr₁, hw₁, hf₁⟩ => Sat.act_seq (by omega) ?_
  have hv₂ : (Act.run (.set 1 none) c₁).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₁]
  have hw₂ : (Act.run (.set 1 none) c₁).stk .work =
      bits l₁ ++ .nd :: (bits l₂ ++ .nd :: .mk 0 :: w) := by
    simp [Act.run, hw₁, encFields]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv₂ hw₂) (by omega)
    fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => ?_
  refine Sat.seq_le (dropNum_sat hr₃ hw₃) (by omega) fun c₄ ⟨hr₄, hw₄, hj₄⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₄, empty_eq_rv]) hw₄) (by omega)
    fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
  have ht₅ : c₅.stk .t1 = bits l₁ ++ .nd :: c.stk .t1 := by
    rw [hj₅ .t1 (by decide), hj₄ .t1 (by decide), ht₃]
    simp only [Act.run]
    rw [hf₁ .t1 (by decide)]
  refine (moveNum2_sat (by decide) (by decide) (by decide) (by rw [hr₅, empty_eq_rv]) ht₅).mono
    (by omega) fun c' ⟨hr', ht', hw', hj'⟩ => ⟨hr', l₁, r₁, by omega, by rw [hw', hw₅], ?_,
      ?_, ht', ?_, ?_, ?_⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hj' j hj.2.2.1 hj.1, hj₅ j hj.1, hj₄ j hj.1, hj₃ j hj.1 hj.2.2.1]
    exact hf₁ j (by simp [hj.1])
  · rw [hj' .t0 (by decide) (by decide), hj₅ .t0 (by decide), hj₄ .t0 (by decide),
      hj₃ .t0 (by decide) (by decide)]
    exact hf₁ .t0 (by decide)
  · rw [hj' .t2 (by decide) (by decide), hj₅ .t2 (by decide), hj₄ .t2 (by decide),
      hj₃ .t2 (by decide) (by decide)]
    exact hf₁ .t2 (by decide)
  · rw [hj' .t3 (by decide) (by decide), hj₅ .t3 (by decide), hj₄ .t3 (by decide),
      hj₃ .t3 (by decide) (by decide)]
    exact hf₁ .t3 (by decide)
  · rw [hj' .ptr (by decide) (by decide), hj₅ .ptr (by decide), hj₄ .ptr (by decide),
      hj₃ .ptr (by decide) (by decide)]
    exact hf₁ .ptr (by decide)

theorem out_snd {a b : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {x : (Ty.prod a b).denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h (.prod a b) x (ofBits lx)) (hlx : lx.length ≤ B + h.length) {G C : ℕ}
    (hC : 1 ≤ C) : PrimOut prog sndCode c h w b x.2 B F G C := by
  obtain ⟨l₁, l₂, hc, r₁, r₂⟩ := hr.pair_inv
  have hl₁ := hB.field_lt hc l₁ (by simp)
  have hl₂ := hB.field_lt hc l₂ (by simp)
  refine out_old (T := fcE (encHeap h).length (B + h.length) + 60 * (B + h.length) + 100) hH hB
    hC (fun M h1 h2 => (primB_ge M).trans' (by have := fcE_mono h2 h1; omega)) ?_
  unfold sndCode
  refine Sat.seq_le (openTop_sat (w := w) hH hv (by simpa [envEnc] using hw) hc hlx) (by omega)
    fun c₁ ⟨hr₁, hw₁, hf₁⟩ => Sat.act_seq (by omega) ?_
  have hv₂ : (Act.run (.set 1 none) c₁).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₁]
  have hw₂ : (Act.run (.set 1 none) c₁).stk .work =
      bits l₁ ++ .nd :: (bits l₂ ++ .nd :: .mk 0 :: w) := by
    simp [Act.run, hw₁, encFields]
  refine Sat.seq_le (dropNum_sat hv₂ hw₂) (by omega) fun c₃ ⟨hr₃, hw₃, hj₃⟩ => ?_
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₃ hw₃) (by omega)
    fun c₄ ⟨hr₄, hw₄, ht₄, hj₄⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₄, empty_eq_rv]) hw₄) (by omega)
    fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
  have ht₅ : c₅.stk .t1 = bits l₂ ++ .nd :: c.stk .t1 := by
    rw [hj₅ .t1 (by decide), ht₄, hj₃ .t1 (by decide)]
    simp only [Act.run]
    rw [hf₁ .t1 (by decide)]
  refine (moveNum2_sat (by decide) (by decide) (by decide) (by rw [hr₅, empty_eq_rv]) ht₅).mono
    (by omega) fun c' ⟨hr', ht', hw', hj'⟩ => ⟨hr', l₂, r₂, by omega, by rw [hw', hw₅], ?_,
      ?_, ht', ?_, ?_, ?_⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hj' j hj.2.2.1 hj.1, hj₅ j hj.1, hj₄ j hj.1 hj.2.2.1, hj₃ j hj.1]
    exact hf₁ j (by simp [hj.1])
  · rw [hj' .t0 (by decide) (by decide), hj₅ .t0 (by decide), hj₄ .t0 (by decide) (by decide),
      hj₃ .t0 (by decide)]
    exact hf₁ .t0 (by decide)
  · rw [hj' .t2 (by decide) (by decide), hj₅ .t2 (by decide), hj₄ .t2 (by decide) (by decide),
      hj₃ .t2 (by decide)]
    exact hf₁ .t2 (by decide)
  · rw [hj' .t3 (by decide) (by decide), hj₅ .t3 (by decide), hj₄ .t3 (by decide) (by decide),
      hj₃ .t3 (by decide)]
    exact hf₁ .t3 (by decide)
  · rw [hj' .ptr (by decide) (by decide), hj₅ .ptr (by decide), hj₄ .ptr (by decide) (by decide),
      hj₃ .ptr (by decide)]
    exact hf₁ .ptr (by decide)

/-- Negation: fetch the Boolean's cell, then one cell with the other tag. -/
def notCode : Code Stk Sym Rg P :=
  .seq openTop (.seq closeCell (.ite (.is 1 (some (.tag .tt)))
    (.seq (.act (.set 1 none)) (allocArgs .ff 0)) (.seq (.act (.set 1 none)) (allocArgs .tt 0))))

theorem out_not {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x : Bool}
    {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h .bool x (ofBits lx)) (hlx : lx.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) : PrimOut prog notCode c h w .bool (!x) B F G C := by
  have hc := hr.bool_inv
  unfold notCode
  refine PrimOut.of_sat (T := fcE (encHeap h).length (B + h.length) + 12 * (B + h.length) +
    allocBound 0 h.length + 40) (Sat.seq_le (openTop_sat (w := w) hH hv
      (by simpa [envEnc] using hw) hc hlx) (by omega) fun c₁ ⟨hr₁, hw₁, hf₁⟩ => ?_)
  refine Sat.seq_le (closeCell_sat (w := w) hr₁ (by simpa [encFields] using hw₁)) (by omega)
    fun c₂ ⟨hr₂, hw₂, hj₂⟩ => ?_
  have hH₂ : HeapAt h c₂ := hH.fr ((hf₁.trans (fr1 hj₂)).mono (T := [.work]) (by simp))
    (by decide) (by decide) (by decide)
  have key : ∀ (tg : Tag) (v : Bool), (∀ l, CellAt (h ++ [⟨l, tg, []⟩]) (ofBits l) tg [] →
      Rep (h ++ [⟨l, tg, []⟩]) .bool v (ofBits l)) → ∀ c₃ : Cfg Stk Sym Rg,
      c₃.regs = Regs.empty → c₃.stk = c₂.stk →
      Sat prog (allocArgs tg 0) c₃ (allocBound 0 h.length + 9) fun c' =>
        ∃ h' l, HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧ c'.regs = Regs.empty ∧
        Rep (h ++ h') .bool v (ofBits l) ∧ l.length ≤ B + (h ++ h').length ∧
        c'.stk .work = bits l ++ .nd :: w ∧ Fr [.heap, .cnt, .work] c c' ∧ h'.length ≤ G ∧
        fcE (encHeap h).length (B + h.length) + 12 * (B + h.length) + allocBound 0 h.length +
          40 ≤ C * primB (B + (encHeap (h ++ h')).length) := by
    intro tg v hrep c₃ hv₃ hs₃
    have hH₃ : HeapAt h c₃ := hH₂.frame (by rw [hs₃]) (by rw [hs₃]) (by rw [hs₃])
    have := allocArgs_sat (prog := prog) tg (ls := []) (w := w) hH₃ hB h1B hv₃ (by simp [hs₃, hw₂])
      (by simp) (by simp)
    refine this.mono (by simp [encFields]) fun c' ⟨hr', l, hH', hB', hc', hl', hw', hf'⟩ =>
      ⟨[⟨l, tg, []⟩], l, hH', hB', hr', hrep l hc', by simp; omega, hw', ?_, by simpa using hG,
        ?_⟩
    · intro j hj
      rw [hf' j hj, show c₃.stk j = c₂.stk j by rw [hs₃]]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      rw [hj₂ j hj.2.2]
      exact hf₁ j (by simp [hj.2.2])
    · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, tg, []⟩]
      obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, tg, []⟩])).length := ⟨_, rfl⟩
      rw [← hM] at s1 s2 ⊢
      have hA := allocBound_mono (a := 0) (b := 2 * M + 2) (m := h.length) (n := M) (by omega)
        (by omega)
      have hf := fcE_mono s2 s1
      exact le_mul_primB hC ((primB_ge M).trans' (by omega))
  cases x
  · refine Sat.ite_false_le (by simp [Cond.eval, hr₂]) (by omega) (Sat.act_seq (by omega) ?_)
    refine (key .tt true (fun l hc' => Rep.bool true hc') (Act.run (.set 1 none) c₂) ?_
      rfl).mono (by omega)
      fun c' h => h
    rw [empty_eq_rv]; simp [Act.run, hr₂]
  · refine Sat.ite_true_le (by simp [Cond.eval, hr₂]) (by omega) (Sat.act_seq (by omega) ?_)
    refine (key .ff false (fun l hc' => Rep.bool false hc') (Act.run (.set 1 none) c₂) ?_
      rfl).mono (by omega)
      fun c' h => h
    rw [empty_eq_rv]; simp [Act.run, hr₂]

/-- Drop the number below the top of `work`. -/
def dropSnd : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .t1 .t0) (.seq (dropNum .work) (moveNum2 .t1 .work .t0))

theorem dropSnd_sat {c : Cfg Stk Sym Rg} {l₁ l₂ : List Bool} {w : List Sym}
    (hv : c.regs = Regs.empty) (hw : c.stk .work = bits l₁ ++ .nd :: bits l₂ ++ .nd :: w) :
    Sat prog dropSnd c (26 * l₁.length + 2 * l₂.length + 47) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = bits l₁ ++ .nd :: w ∧ Fr [.work] c c' := by
  unfold dropSnd
  refine Sat.seq_le (moveNum2_sat (l := l₁) (rest := bits l₂ ++ .nd :: w) (by decide) (by decide)
    (by decide) hv (by simpa using hw)) (by omega) fun c₁ ⟨hr₁, hw₁, ht₁, hj₁⟩ => ?_
  refine Sat.seq_le (dropNum_sat hr₁ hw₁) (by omega) fun c₂ ⟨hr₂, hw₂, hj₂⟩ => ?_
  have ht₂ : c₂.stk .t1 = bits l₁ ++ .nd :: c.stk .t1 := by rw [hj₂ .t1 (by decide), ht₁]
  refine (moveNum2_sat (by decide) (by decide) (by decide) hr₂ ht₂).mono (by omega)
    fun c' ⟨hr', ht', hw', hj'⟩ => ⟨hr', by rw [hw', hw₂], fun j hj => ?_⟩
  simp only [List.mem_singleton] at hj
  by_cases hj1 : j = .t1
  · subst hj1; exact ht'
  rw [hj' j hj1 hj, hj₂ j hj, hj₁ j hj hj1]

/-- Branch on the Boolean whose pointer is on top of `work` (the pointer stays). -/
def boolSel (x y : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (copyNum .work .ptr .t0) (.seq fetchCell (.seq closeCell (.ite (.is 1 (some (.tag .tt)))
    (.seq (.act (.set 1 none)) x) (.seq (.act (.set 1 none)) y))))

/-- Conjunction: the first argument if the second is true, else the second. -/
def andCode : Code Stk Sym Rg P := boolSel (dropNum .work) dropSnd

/-- Disjunction: the second argument if it is true, else the first. -/
def orCode : Code Stk Sym Rg P := boolSel dropSnd (dropNum .work)

theorem boolSel_sat {x y : Code Stk Sym Rg P} {B : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {lb lc : List Bool} {w : List Sym} {b : Bool} (hH : HeapAt h c)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = bits lc ++ .nd :: bits lb ++ .nd :: w)
    (hr : Rep h .bool b (ofBits lc)) (hlc : lc.length ≤ B + h.length) {T : ℕ}
    {Q : Cfg Stk Sym Rg → Prop}
    (hx : b = true → ∀ c₁ : Cfg Stk Sym Rg, c₁.regs = Regs.empty → c₁.stk = c.stk →
      Sat prog x c₁ T Q)
    (hy : b = false → ∀ c₁ : Cfg Stk Sym Rg, c₁.regs = Regs.empty → c₁.stk = c.stk →
      Sat prog y c₁ T Q) :
    Sat prog (boolSel x y) c (fcE (encHeap h).length (B + h.length) + 14 * (B + h.length) + T +
      30) Q := by
  have hc := hr.bool_inv
  unfold boolSel
  refine Sat.seq_le (copyNum_sat (l := lc) (rest := bits lb ++ .nd :: w) (by decide) (by decide)
    (by decide) hv (by simpa using hw)) (by omega) fun c₁ ⟨hr₁, hp₁, hj₁⟩ => ?_
  have hH₁ : HeapAt h c₁ := hH.fr (fr1 hj₁) (by decide) (by decide) (by decide)
  refine Sat.seq_le (fetchCellE_sat hH₁.wf hH₁.heap hH₁.scan hr₁ hc hlc hp₁) (by omega)
    fun c₂ ⟨hr₂, hw₂, hp₂, hj₂⟩ => ?_
  refine Sat.seq_le (closeCell_sat (w := c₁.stk .work) hr₂ (by simpa [encFields] using hw₂))
    (by omega) fun c₃ ⟨hr₃, hw₃, hj₃⟩ => ?_
  have hs₃ : (Act.run (.set 1 none) c₃).stk = c.stk := by
    funext j
    simp only [Act.run]
    by_cases hjw : j = .work
    · subst hjw; rw [hw₃, hj₁ .work (by decide)]
    by_cases hjp : j = .ptr
    · subst hjp; rw [hj₃ .ptr (by decide), hp₂]
    rw [hj₃ j hjw, hj₂ j hjw hjp, hj₁ j hjp]
  have hv₃ : (Act.run (.set 1 none) c₃).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₃]
  cases b
  · exact Sat.ite_false_le (by simp [Cond.eval, hr₃]) (by omega)
      (Sat.act_seq (by omega) ((hy rfl _ hv₃ hs₃).mono (by omega) fun _ h => h))
  · exact Sat.ite_true_le (by simp [Cond.eval, hr₃]) (by omega)
      (Sat.act_seq (by omega) ((hx rfl _ hv₃ hs₃).mono (by omega) fun _ h => h))

/-- An existing pointer as the result, with only `work` changed. -/
theorem out_old' {x : Code Stk Sym Rg P} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {w : List Sym} {t : Ty} {v : t.denote} {T G C : ℕ} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hC : 1 ≤ C) (hT : ∀ M, B + h.length ≤ M → (encHeap h).length ≤ M → T ≤ primB M)
    (hs : Sat prog x c T fun c' => c'.regs = Regs.empty ∧ ∃ l, Rep h t v (ofBits l) ∧
      l.length ≤ B + h.length ∧ c'.stk .work = bits l ++ .nd :: w ∧ Fr [.work] c c') :
    PrimOut prog x c h w t v B F G C :=
  out_old hH hB hC hT (hs.mono le_rfl fun _ ⟨hr, l, hR, hl, hw, hf⟩ =>
    ⟨hr, l, hR, hl, hw, hf.mono (by simp), hf _ (by decide), hf _ (by decide),
      hf _ (by decide), hf _ (by decide), hf _ (by decide)⟩)

theorem out_and {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {b d : Bool}
    {lb ld : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [lb, ld] ++ w) (rb : Rep h .bool b (ofBits lb))
    (rd : Rep h .bool d (ofBits ld)) (hlb : lb.length ≤ B + h.length)
    (hld : ld.length ≤ B + h.length) {G C : ℕ} (hC : 1 ≤ C) :
    PrimOut prog andCode c h w .bool (b && d) B F G C := by
  have hw' : c.stk .work = bits ld ++ .nd :: bits lb ++ .nd :: w := by simpa [envEnc] using hw
  refine out_old' (T := fcE (encHeap h).length (B + h.length) + 14 * (B + h.length) +
    (28 * (B + h.length) + 47) + 30) hH hB hC
    (fun M h1 h2 => (primB_ge M).trans' (by have := fcE_mono h2 h1; omega)) ?_
  refine boolSel_sat hH hv hw' rd hld ?_ ?_
  · intro hd c₁ hv₁ hs₁
    subst hd
    refine (dropNum_sat (l := ld) (rest := bits lb ++ .nd :: w) hv₁
      (by rw [hs₁, hw']; simp)).mono (by omega)
      fun c' ⟨hr', hw₁, hj'⟩ => ⟨hr', lb, by simpa using rb, hlb, hw₁, fun j hj => ?_⟩
    rw [hj' j (by simpa using hj), hs₁]
  · intro hd c₁ hv₁ hs₁
    subst hd
    refine (dropSnd_sat hv₁ (by rw [hs₁, hw'])).mono (by omega)
      fun c' ⟨hr', hw₁, hf'⟩ => ⟨hr', ld, by simpa using rd, hld, hw₁, fun j hj => ?_⟩
    rw [hf' j hj, hs₁]

theorem out_or {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {b d : Bool}
    {lb ld : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [lb, ld] ++ w) (rb : Rep h .bool b (ofBits lb))
    (rd : Rep h .bool d (ofBits ld)) (hlb : lb.length ≤ B + h.length)
    (hld : ld.length ≤ B + h.length) {G C : ℕ} (hC : 1 ≤ C) :
    PrimOut prog orCode c h w .bool (b || d) B F G C := by
  have hw' : c.stk .work = bits ld ++ .nd :: bits lb ++ .nd :: w := by simpa [envEnc] using hw
  refine out_old' (T := fcE (encHeap h).length (B + h.length) + 14 * (B + h.length) +
    (28 * (B + h.length) + 47) + 30) hH hB hC
    (fun M h1 h2 => (primB_ge M).trans' (by have := fcE_mono h2 h1; omega)) ?_
  refine boolSel_sat hH hv hw' rd hld ?_ ?_
  · intro hd c₁ hv₁ hs₁
    subst hd
    refine (dropSnd_sat hv₁ (by rw [hs₁, hw'])).mono (by omega)
      fun c' ⟨hr', hw₁, hf'⟩ => ⟨hr', ld, by simpa using rd, hld, hw₁, fun j hj => ?_⟩
    rw [hf' j hj, hs₁]
  · intro hd c₁ hv₁ hs₁
    subst hd
    refine (dropNum_sat (l := ld) (rest := bits lb ++ .nd :: w) hv₁
      (by rw [hs₁, hw']; simp)).mono (by omega)
      fun c' ⟨hr', hw₁, hj'⟩ => ⟨hr', lb, by simpa using rb, hlb, hw₁, fun j hj => ?_⟩
    rw [hj' j (by simpa using hj), hs₁]

/-! ### Arithmetic -/

/-- Fetch the two naturals (the second onto `t1`, the first onto `t2`). -/
theorem natTo2_sat {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [lx, ly] ++ w) (rx : Rep h .nat x (ofBits lx))
    (ry : Rep h .nat y (ofBits ly)) (hlx : lx.length ≤ B + h.length)
    (hly : ly.length ≤ B + h.length) {Y : Code Stk Sym Rg P} {T : ℕ} {Q : Cfg Stk Sym Rg → Prop}
    (hY : ∀ (c₂ : Cfg Stk Sym Rg) (nx ny : List Bool), ofBits nx = x → ofBits ny = y →
      nx.length < B + h.length → ny.length < B + h.length → c₂.regs = Regs.empty →
      c₂.stk .work = w → c₂.stk .t2 = bits nx ++ .nd :: c.stk .t2 →
      c₂.stk .t1 = bits ny ++ .nd :: c.stk .t1 → Fr [.work, .t1, .t2] c c₂ → Sat prog Y c₂ T Q) :
    Sat prog (.seq (natTo .t1) (.seq (natTo .t2) Y)) c
      (2 * (fcE (encHeap h).length (B + h.length) + 24 * (B + h.length) + 50) + T + 2) Q := by
  have hw' : c.stk .work = bits ly ++ .nd :: (bits lx ++ .nd :: w) := by simpa [envEnc] using hw
  refine Sat.seq_le (natTo_sat (by decide) (by decide) hH hB hv hw' ry hly le_rfl) (by omega)
    fun c₁ ⟨hr₁, hw₁, hf₁, ny, hny, hnyB, ht₁⟩ => ?_
  have hH₁ : HeapAt h c₁ := hH.fr hf₁ (by decide) (by decide) (by decide)
  refine Sat.seq_le (natTo_sat (by decide) (by decide) hH₁ hB hr₁ hw₁ rx hlx le_rfl) (by omega)
    fun c₂ ⟨hr₂, hw₂, hf₂, nx, hnx, hnxB, ht₂⟩ => (hY c₂ nx ny hnx hny hnxB hnyB hr₂ hw₂ ?_ ?_
      ((hf₁.trans hf₂).mono (by decide))).mono (by omega) fun _ h => h
  · rw [ht₂, hf₁ .t2 (by decide)]
  · rw [hf₂ .t1 (by decide), ht₁]

/-- Addition or subtraction: the bits of the two naturals, the operation onto `work`, one
cell. -/
def arithCode (op : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (natTo .t1) (.seq (natTo .t2) (.seq (.act (.push .work (.mk 2))) (.seq op (alloc .nat))))

theorem out_arith {op : Code Stk Sym Rg P} {g : List Bool → List Bool → List Bool}
    {f : ℕ → ℕ → ℕ}
    (hop : ∀ (c₁ : Cfg Stk Sym Rg) (xs ys : List Bool) (ra rb : List Sym),
      c₁.regs = Regs.empty → c₁.stk .t2 = bits xs ++ .nd :: ra →
      c₁.stk .t1 = bits ys ++ .nd :: rb →
      Sat prog op c₁ (23 * max xs.length ys.length + 37) fun c' => c'.regs = Regs.empty ∧
        c'.stk .t2 = ra ∧ c'.stk .t1 = rb ∧ c'.stk .work = bits (g xs ys) ++ .nd :: c₁.stk .work ∧
        ∀ j, j ≠ .t2 → j ≠ .t1 → j ≠ .work → c'.stk j = c₁.stk j)
    (hg : ∀ xs ys, ofBits (g xs ys) = f (ofBits xs) (ofBits ys) ∧
      (g xs ys).length ≤ max xs.length ys.length + 1)
    {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B) (h1F : 1 ≤ F)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx, ly] ++ w)
    (rx : Rep h .nat x (ofBits lx)) (ry : Rep h .nat y (ofBits ly))
    (hlx : lx.length ≤ B + h.length) (hly : ly.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) : PrimOut prog (arithCode op) c h w .nat (f x y) B F G C := by
  unfold arithCode
  refine PrimOut.of_sat (natTo2_sat hH hB hv hw rx ry hlx hly
    (T := 23 * (B + h.length) + allocBound (B + h.length + 1) h.length + 45)
    fun c₂ nx ny hnx hny hnxB hnyB hr₂ hw₂ ht₂ ht₁ hf₂ => ?_)
  refine Sat.act_seq (by omega) ?_
  have hH₂ : HeapAt h (Act.run (.push .work (.mk 2)) c₂) :=
    (hH.fr hf₂ (by decide) (by decide) (by decide)).frame (by simp [Act.run])
      (by simp [Act.run]) (by simp [Act.run])
  obtain ⟨hgv, hgl⟩ := hg nx ny
  refine Sat.seq_le (hop _ nx ny (c.stk .t2) (c.stk .t1) hr₂ (by simpa [Act.run] using ht₂)
    (by simpa [Act.run] using ht₁)) (by omega) fun c₃ ⟨hr₃, ht₃, ht₃', hw₃, hj₃⟩ => ?_
  have hH₃ : HeapAt h c₃ := hH₂.fr (fr3 hj₃) (by decide) (by decide) (by decide)
  have hw₃' : c₃.stk .work = encFields [g nx ny] ++ .mk 2 :: w := by
    rw [hw₃]; simp [Act.run, hw₂, encFields]
  have hA := allocBound_mono (a := (encFields [g nx ny]).length) (b := B + h.length + 1)
    (m := h.length) (n := h.length) (by simp [encFields]; omega) le_rfl
  refine (allocB_sat .nat hH₃ hB h1B hr₃ hw₃' (by simpa using h1F)
    (by simp; omega)).mono (by omega) fun c' ⟨hr', l, hH', hB', hc', hl', hw', hf'⟩ =>
      ⟨[⟨l, .nat, [g nx ny]⟩], l, hH', hB', hr', by simpa [hgv, hnx, hny] using Rep.nat hc',
        by simp; omega, hw', ?_, by simpa using hG, ?_⟩
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hf' j (by simp [hj.1, hj.2.1, hj.2.2])]
    by_cases h2 : j = .t2
    · subst h2; rw [ht₃]
    by_cases h1 : j = .t1
    · subst h1; rw [ht₃']
    rw [hj₃ j h2 h1 hj.2.2]
    simp only [Act.run]
    rw [update_of_ne hj.2.2]
    exact hf₂ j (by simp [hj.2.2, h1, h2])
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .nat, [g nx ny]⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .nat, [g nx ny]⟩])).length := ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hA' := allocBound_mono (a := B + h.length + 1) (b := 2 * M + 2) (m := h.length) (n := M)
      (by omega) (by omega)
    have hf := fcE_mono s2 s1
    exact le_mul_primB hC ((primB_ge M).trans' (by omega))

theorem out_add {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B) (h1F : 1 ≤ F)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx, ly] ++ w)
    (rx : Rep h .nat x (ofBits lx)) (ry : Rep h .nat y (ofBits ly))
    (hlx : lx.length ≤ B + h.length) (hly : ly.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) :
    PrimOut prog (arithCode (addNum .t2 .t1 .work .t0)) c h w .nat (x + y) B F G C :=
  out_arith (g := addBits) (fun _ _ _ _ _ hv ha hb => addNum_sat (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv ha hb)
    (fun xs ys => ⟨ofBits_addBits xs ys, (length_addBits xs ys).le⟩) hH hB h1B h1F hv hw rx ry
    hlx hly hG hC

theorem out_sub {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B) (h1F : 1 ≤ F)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx, ly] ++ w)
    (rx : Rep h .nat x (ofBits lx)) (ry : Rep h .nat y (ofBits ly))
    (hlx : lx.length ≤ B + h.length) (hly : ly.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) :
    PrimOut prog (arithCode (subNum .t2 .t1 .work .t0)) c h w .nat (x - y) B F G C :=
  out_arith (g := subBits) (fun _ _ _ _ _ hv ha hb => subNum_sat (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hv ha hb)
    (fun xs ys => ⟨ofBits_subBits xs ys, (length_subBits_le xs ys).trans (Nat.le_succ _)⟩) hH hB
    h1B h1F hv hw rx ry hlx hly hG hC

/-- A cell without fields at the end of a primitive's code, after work on the stacks that
changed only `work`. -/
theorem finish0 {B F : ℕ} {h : List Cell} {c c₃ : Cfg Stk Sym Rg} {w : List Sym} (tg : Tag)
    {t : Ty} {v : t.denote}
    (hrep : ∀ l, CellAt (h ++ [⟨l, tg, []⟩]) (ofBits l) tg [] →
      Rep (h ++ [⟨l, tg, []⟩]) t v (ofBits l))
    (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B) (hv : c₃.regs = Regs.empty)
    (hw : c₃.stk .work = w) (hf : Fr [.work] c c₃) {T₀ G C : ℕ} (hG : 1 ≤ G) (hC : 1 ≤ C)
    (hT : ∀ M, B + h.length ≤ M → (encHeap h).length ≤ M → T₀ ≤ 4 * fcE M M + 1000 * M) :
    Sat prog (allocArgs tg 0) c₃ (allocBound 0 h.length + 9) fun c' =>
      ∃ h' l, HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧ c'.regs = Regs.empty ∧
        Rep (h ++ h') t v (ofBits l) ∧ l.length ≤ B + (h ++ h').length ∧
        c'.stk .work = bits l ++ .nd :: w ∧ Fr [.heap, .cnt, .work] c c' ∧ h'.length ≤ G ∧
        T₀ + allocBound 0 h.length + 9 ≤ C * primB (B + (encHeap (h ++ h')).length) := by
  have hH₃ : HeapAt h c₃ := hH.fr hf (by decide) (by decide) (by decide)
  refine (allocArgs_sat (prog := prog) tg (ls := []) (w := w) hH₃ hB h1B hv (by simp [hw])
    (by simp) (by simp)).mono (by simp [encFields])
    fun c' ⟨hr', l, hH', hB', hc', hl', hw', hf'⟩ =>
      ⟨[⟨l, tg, []⟩], l, hH', hB', hr', hrep l hc', by simp; omega, hw',
        (hf.trans hf').mono (by simp), by simpa using hG, ?_⟩
  obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, tg, []⟩]
  obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, tg, []⟩])).length := ⟨_, rfl⟩
  rw [← hM] at s1 s2 ⊢
  have hA := allocBound_mono (a := 0) (b := 2 * M + 2) (m := h.length) (n := M) (by omega)
    (by omega)
  have := hT M s1 s2
  exact le_mul_primB hC ((primB_ge M).trans' (by omega))

/-- Comparison: the bits of the two naturals, the comparison bit, one Boolean cell. -/
def cmpCode (op : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (natTo .t1) (.seq (natTo .t2) (.seq op (.seq (.act (.pop .t3 0))
    (.ite (.is 0 (some (.bit true))) (.seq (.act (.set 0 none)) (allocArgs .tt 0))
      (.seq (.act (.set 0 none)) (allocArgs .ff 0))))))

theorem out_cmp {op : Code Stk Sym Rg P} {g : List Bool → List Bool → Bool} {f : ℕ → ℕ → Bool}
    (hop : ∀ (c₁ : Cfg Stk Sym Rg) (xs ys : List Bool) (ra rb : List Sym),
      c₁.regs = Regs.empty → c₁.stk .t2 = bits xs ++ .nd :: ra →
      c₁.stk .t1 = bits ys ++ .nd :: rb →
      Sat prog op c₁ (19 * max xs.length ys.length + 34) fun c' => c'.regs = Regs.empty ∧
        c'.stk .t2 = ra ∧ c'.stk .t1 = rb ∧ c'.stk .t3 = .bit (g xs ys) :: c₁.stk .t3 ∧
        ∀ j, j ≠ .t2 → j ≠ .t1 → j ≠ .t3 → c'.stk j = c₁.stk j)
    (hg : ∀ xs ys, g xs ys = f (ofBits xs) (ofBits ys))
    {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx, ly] ++ w)
    (rx : Rep h .nat x (ofBits lx)) (ry : Rep h .nat y (ofBits ly))
    (hlx : lx.length ≤ B + h.length) (hly : ly.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) : PrimOut prog (cmpCode op) c h w .bool (f x y) B F G C := by
  unfold cmpCode
  refine PrimOut.of_sat (natTo2_sat hH hB hv hw rx ry hlx hly
    (T := 19 * (B + h.length) + 40 + allocBound 0 h.length + 9)
    fun c₂ nx ny hnx hny hnxB hnyB hr₂ hw₂ ht₂ ht₁ hf₂ => ?_)
  refine Sat.seq_le (hop c₂ nx ny (c.stk .t2) (c.stk .t1) hr₂ ht₂ ht₁) (by omega)
    fun c₃ ⟨hr₃, ht₃, ht₃', ht₃'', hj₃⟩ => Sat.act_seq (by omega) ?_
  have hr₄ : (Act.run (.pop .t3 0) c₃).regs = rv (some (.bit (f x y))) none none none := by
    rw [empty_eq_rv] at hr₃; simp [Act.run, hr₃, ht₃'', hg, hnx, hny]
  have hv₅ : (Act.run (.set 0 none) (Act.run (.pop .t3 0) c₃)).regs = Regs.empty := by
    have e : (Act.run (.set 0 none) (Act.run (.pop .t3 0) c₃)).regs =
        update (Act.run (.pop .t3 0) c₃).regs 0 none := rfl
    rw [e, hr₄, empty_eq_rv, update_rv_zero]
  have hf₅ : Fr [.work] c (Act.run (.set 0 none) (Act.run (.pop .t3 0) c₃)) := by
    intro j hj
    simp only [List.mem_singleton] at hj
    simp only [Act.run]
    by_cases h3 : j = .t3
    · subst h3
      rw [update_self, ht₃'']
      simp only [List.tail_cons]
      exact hf₂ .t3 (by decide)
    rw [update_of_ne h3]
    by_cases h2 : j = .t2
    · subst h2; rw [ht₃]
    by_cases h1 : j = .t1
    · subst h1; rw [ht₃']
    rw [hj₃ j h2 h1 h3]
    exact hf₂ j (by simp [hj, h1, h2])
  have hw₅ : (Act.run (.set 0 none) (Act.run (.pop .t3 0) c₃)).stk .work = w := by
    simp only [Act.run]
    rw [update_of_ne (by decide), hj₃ .work (by decide) (by decide) (by decide), hw₂]
  have hT : ∀ M, B + h.length ≤ M → (encHeap h).length ≤ M →
      2 * (fcE (encHeap h).length (B + h.length) + 24 * (B + h.length) + 50) +
        19 * (B + h.length) + 42 ≤ 4 * fcE M M + 1000 * M :=
    fun M h1 h2 => by have := fcE_mono h2 h1; omega
  cases hfx : f x y
  · refine Sat.ite_false_le (by simp [Cond.eval, hr₄, hfx]) (by omega)
      (Sat.act_seq (by omega) ?_)
    exact ((finish0 .ff (fun l hc => by simpa using Rep.bool false hc) hH hB h1B hv₅ hw₅ hf₅
      hG hC hT).mono (by omega) fun c' ⟨h', l, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ =>
        ⟨h', l, a1, a2, a3, a4, a5, a6, a7, a8, by omega⟩)
  · refine Sat.ite_true_le (by simp [Cond.eval, hr₄, hfx]) (by omega)
      (Sat.act_seq (by omega) ?_)
    exact ((finish0 .tt (fun l hc => by simpa using Rep.bool true hc) hH hB h1B hv₅ hw₅ hf₅
      hG hC hT).mono (by omega) fun c' ⟨h', l, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ =>
        ⟨h', l, a1, a2, a3, a4, a5, a6, a7, a8, by omega⟩)

theorem out_natEq {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx, ly] ++ w)
    (rx : Rep h .nat x (ofBits lx)) (ry : Rep h .nat y (ofBits ly))
    (hlx : lx.length ≤ B + h.length) (hly : ly.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) :
    PrimOut prog (cmpCode (eqNum .t2 .t1 .t3 .t0)) c h w .bool (x == y) B F G C :=
  out_cmp (g := fun xs ys => decide (ofBits xs = ofBits ys)) (f := fun x y => x == y)
    (fun _ _ _ _ _ hv ha hb => eqNum_sat (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hv ha hb)
    (fun xs ys => by by_cases e : ofBits xs = ofBits ys <;> simp [e]) hH hB h1B hv hw rx ry hlx
    hly hG hC

theorem out_natLt {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {x y : ℕ}
    {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (h1B : 1 ≤ B)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx, ly] ++ w)
    (rx : Rep h .nat x (ofBits lx)) (ry : Rep h .nat y (ofBits ly))
    (hlx : lx.length ≤ B + h.length) (hly : ly.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G)
    (hC : 1 ≤ C) :
    PrimOut prog (cmpCode (ltNum .t2 .t1 .t3 .t0)) c h w .bool (decide (x < y)) B F G C :=
  out_cmp (g := fun xs ys => decide (ofBits xs < ofBits ys)) (f := fun x y => decide (x < y))
    (fun _ _ _ _ _ hv ha hb => (ltNum_sat (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hv ha hb).mono (by omega) fun _ h => h)
    (fun _ _ => rfl) hH hB h1B hv hw rx ry hlx hly hG hC

/-! ### Lists -/

theorem le_succ_mul {k a b c : ℕ} : (k + 1) * a + k * b + c ≤ (k + 1) * (a + b + c) := by
  have e : (k + 1) * (a + b + c) = (k + 1) * a + k * b + b + (k + 1) * c := by ring
  have : c ≤ (k + 1) * c := Nat.le_mul_of_pos_left c (by omega)
  omega

/-- The length of a list: walk it, count the pointers, one cell. -/
def lengthCode : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .ptr .t0) (.seq (.act (.push .t4 (.mk 3))) (.seq (walkList .t4)
    (.seq (countAll 3 .t4) (.seq (.act (.pop .t4 0)) (.seq (.act (.set 0 none))
      (.seq (.act (.push .work (.mk 2))) (.seq (moveNum2 .t2 .work .t0) (alloc .nat))))))))

theorem out_length {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {xs : List a.denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (hFB : F + 1 ≤ B)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h (.list a) xs (ofBits lx)) (hlx : lx.length ≤ B + h.length)
    (hk : xs.length + 1 ≤ F) {G : ℕ} (hG : 1 ≤ G) :
    PrimOut prog lengthCode c h w .nat xs.length B F G (xs.length + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlx
  have hw' : c.stk .work = bits lx ++ .nd :: w := by simpa [envEnc] using hw
  unfold lengthCode
  refine PrimOut.of_sat (T := (xs.length + 1) * (fcE (encHeap h).length E + 24 * E + 50) +
    xs.length * (2 * E + 35 * xs.length + 150) +
    (12 * E + 12 * xs.length + allocBound (xs.length + 2) h.length + 100))
    (Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw') (by omega)
      fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => Sat.act_seq (by omega) ?_)
  have F1 : Fr [.work, .ptr] c c₁ := fr2 hj₁
  have F2 := fr_push .t4 (.mk 3) c₁
  have hH₁ : HeapAt h (Act.run (.push .t4 (.mk 3)) c₁) :=
    hH.fr (F1.trans F2) (by decide) (by decide) (by decide)
  refine Sat.seq_le (walkList_sat (E := E) (q := lx) (rp := c.stk .ptr) (by decide) hH₁ hB hr₁
    (by simpa [Act.run] using hp₁) hr (by omega) (by omega)) (by omega)
    fun c₂ ⟨hr₂, hp₂, F3, psr, hR, hpB, ht₂⟩ => ?_
  have hlen : psr.length = xs.length := by rw [← hR.length_eq, List.length_reverse]
  have ht₂' : c₂.stk .t4 = encNums psr ++ .mk 3 :: c.stk .t4 := by
    rw [ht₂]; simp [Act.run, hj₁ .t4 (by decide) (by decide)]
  have hca := countAll_sat (prog := prog) (E := E) (by decide) hr₂ ht₂'
    (fun l hl => by have := hpB l hl; omega)
  rw [hlen] at hca
  refine Sat.seq_le hca (by omega) fun c₃ ⟨hr₃, ht₃, ht₃', F4⟩ => ?_
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
  have hcnt := length_cntBits_le xs.length
  have ht₃'' : (Act.run (.push .work (.mk 2)) (Act.run (.set 0 none)
      (Act.run (.pop .t4 0) c₃))).stk .t2 = bits (cntBits xs.length) ++ .nd :: c.stk .t2 := by
    simp only [Act.run]
    rw [update_of_ne (by decide), update_of_ne (by decide), ht₃', F3 .t2 (by decide)]
    simp [Act.run, hj₁ .t2 (by decide) (by decide)]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) (by
    simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero, update_rv_zero]) ht₃'') (by omega)
    fun c₄ ⟨hr₄, ht₄, hw₄, hj₄⟩ => ?_
  have F5 : Fr [.t4, .work, .t2, .work] c₃ c₄ :=
    (((fr_pop .t4 0 c₃).trans (fr_set 0 none _)).trans (fr_push .work (.mk 2) _)).trans
      (fr2 hj₄)
  have F14 : Fr [.work, .ptr, .t4, .ptr, .t4, .t4, .t2, .t4, .work, .t2, .work] c c₄ :=
    (((F1.trans F2).trans F3).trans F4).trans F5
  have hH₄ : HeapAt h c₄ := hH.fr F14 (by decide) (by decide) (by decide)
  have hw₄' : c₄.stk .work = encFields [cntBits xs.length] ++ .mk 2 :: w := by
    rw [hw₄]
    simp only [Act.run, update_self, encFields]
    rw [update_of_ne (by decide), F4 .work (by decide), F3 .work (by decide)]
    simp [Act.run, hw₁]
  have hA₀ := allocBound_mono (a := (encFields [cntBits xs.length]).length)
    (b := xs.length + 2) (m := h.length) (n := h.length) (by simp [encFields]; omega) le_rfl
  refine (allocB_sat .nat hH₄ hB (by omega) hr₄ hw₄' (by simp; omega)
    (by simp; omega)).mono (by omega) fun c' ⟨hr', l, hH', hB', hc', hl', hw', F6⟩ =>
      ⟨[⟨l, .nat, [cntBits xs.length]⟩], l, hH', hB', hr',
        by simpa [ofBits_cntBits] using Rep.nat hc', by simp; omega, hw', ?_,
        by simpa using hG, ?_⟩
  · have F : Fr [.ptr, .t4, .t2, .heap, .cnt, .work] c c' := (F14.trans F6).mono (by decide)
    have e₁ : c'.stk .ptr = c.stk .ptr := by
      rw [F6 .ptr (by decide), F5 .ptr (by decide), F4 .ptr (by decide), hp₂]
    have e₂ : c'.stk .t4 = c.stk .t4 := by
      rw [F6 .t4 (by decide), hj₄ .t4 (by decide) (by decide)]
      simp [Act.run, ht₃]
    have e₃ : c'.stk .t2 = c.stk .t2 := by rw [F6 .t2 (by decide), ht₄]
    exact ((F.restore e₁).restore e₂).restore e₃
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .nat, [cntBits xs.length]⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .nat, [cntBits xs.length]⟩])).length :=
      ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hA := allocBound_mono (a := xs.length + 2) (b := 2 * M + 2) (m := h.length) (n := M)
      (by omega) (by omega)
    have hf := fcE_mono s2 (by omega : E ≤ M)
    refine le_succ_mul.trans (Nat.mul_le_mul_left _ ((primB_ge M).trans' ?_))
    have : xs.length * xs.length ≤ M * M := Nat.mul_le_mul (by omega) (by omega)
    omega

theorem le_succ_mul2 {k a b b' c : ℕ} :
    (k + 1) * a + k * b + k * b' + c ≤ (k + 1) * (a + b + b' + c) := by
  have e : (k + 1) * (a + b + b' + c) = (k + 1) * a + k * b + k * b' + b + b' + (k + 1) * c := by
    ring
  have : c ≤ (k + 1) * c := Nat.le_mul_of_pos_left c (by omega)
  omega

/-- Reverse a list: walk it, reverse the pointers onto `lst`, cons them onto a new `nil`. -/
def reverseCode : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .ptr .t0) (.seq (.act (.push .t4 (.mk 3))) (.seq (walkList .t4)
    (.seq (.act (.push .lst (.mk 3))) (.seq (moveAll 3 .t4 .lst) (.seq (.act (.pop .t4 0))
      (.seq (.act (.set 0 none)) (.seq (allocArgs .nil 0) (buildListB .lst))))))))

theorem out_reverse {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {xs : List a.denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (h2F : 2 ≤ F) (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h (.list a) xs (ofBits lx)) (hlx : lx.length ≤ B + h.length) {G : ℕ}
    (hG : xs.length + 1 ≤ G) :
    PrimOut prog reverseCode c h w (.list a) xs.reverse B F G (xs.length + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlx
  obtain ⟨U, hU⟩ : ∃ U, U = B + h.length + 1 + xs.length := ⟨_, rfl⟩
  have hw' : c.stk .work = bits lx ++ .nd :: w := by simpa [envEnc] using hw
  unfold reverseCode
  refine PrimOut.of_sat (T := (xs.length + 1) * (fcE (encHeap h).length E + 24 * E + 50) +
    xs.length * (12 * E + 24) + xs.length * (36 * U + allocBound (2 * U + 2) U + 72) +
    (12 * E + allocBound 0 h.length + 100))
    (Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw') (by omega)
      fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => Sat.act_seq (by omega) ?_)
  have F1 : Fr [.work, .ptr] c c₁ := fr2 hj₁
  have F2 := fr_push .t4 (.mk 3) c₁
  have hH₁ : HeapAt h (Act.run (.push .t4 (.mk 3)) c₁) :=
    hH.fr (F1.trans F2) (by decide) (by decide) (by decide)
  refine Sat.seq_le (walkList_sat (E := E) (q := lx) (rp := c.stk .ptr) (by decide) hH₁ hB hr₁
    (by simpa [Act.run] using hp₁) hr (by omega) (by omega)) (by omega)
    fun c₂ ⟨hr₂, hp₂, F3, psr, hR, hpB, ht₂⟩ => Sat.act_seq (by omega) ?_
  have hlen : psr.length = xs.length := by rw [← hR.length_eq, List.length_reverse]
  have ht₂' : (Act.run (.push .lst (.mk 3)) c₂).stk .t4 =
      encNums psr ++ .mk 3 :: c.stk .t4 := by
    rw [show (Act.run (.push .lst (.mk 3)) c₂).stk .t4 = c₂.stk .t4 by simp [Act.run], ht₂]
    simp [Act.run, hj₁ .t4 (by decide) (by decide)]
  have hma := moveAll_sat (prog := prog) (i := 3) (b := .lst) (E := E)
    (c := Act.run (.push .lst (.mk 3)) c₂) (by decide) (by decide) (by decide) hr₂ ht₂'
    (fun l hl => by have := hpB l hl; omega)
  rw [hlen] at hma
  refine Sat.seq_le hma (by omega) fun c₃ ⟨hr₃, ht₃, hl₃, F4⟩ =>
    Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have hv₄ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero, update_rv_zero]
  have F5 : Fr [.work, .ptr, .t4, .ptr, .t4, .lst, .t4, .lst, .t4] c
      (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)) :=
    (((((F1.trans F2).trans F3).trans (fr_push .lst (.mk 3) c₂)).trans F4).trans
      (fr_pop .t4 0 c₃)).trans (fr_set 0 none _)
  have hH₄ := hH.fr F5 (by decide) (by decide) (by decide)
  have hw₄ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)).stk .work = w := by
    have e : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)).stk .work = c₃.stk .work := by
      simp [Act.run]
    rw [e, F4 .work (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), F3 .work (by decide)]
    simp [Act.run, hw₁]
  refine Sat.seq_le ((allocArgs_sat (prog := prog) .nil (ls := []) (w := w) hH₄ hB h1B hv₄
    (by simp [hw₄]) (by simp) (by simp)).mono (t' := allocBound 0 h.length + 9)
    (by simp [encFields]) fun _ h => h) (by omega)
    fun c₄ ⟨hr₄, lnil, hH₅, hB₅, hc₅, hl₅, hw₅, F6⟩ => ?_
  have hR' : RepList (h ++ [⟨lnil, .nil, []⟩]) a xs psr.reverse := by
    have := List.forall₂_reverse_iff.2 hR
    simp only [List.reverse_reverse] at this
    exact RepList.mono this
  have hl₄ : c₄.stk .lst = encNums psr.reverse ++ .mk 3 :: c.stk .lst := by
    rw [F6 .lst (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), hl₃]
    simp [Act.run, F3 .lst (by decide), hj₁ .lst (by decide) (by decide)]
  have hbl := buildListB_sat (prog := prog) (s := .lst) (by decide) h1B h2F hH₅ hB₅ hr₄ hl₄ hw₅
    hR' (Rep.nil hc₅) (fun p hp => by
      have := hpB p (List.mem_reverse.1 hp); simp; omega) (by simp; omega)
  have hU' : B + (h ++ [Cell.mk lnil .nil []]).length + psr.reverse.length = U := by
    simp [hlen]; omega
  rw [hU'] at hbl
  refine (hbl.mono (by rw [List.length_reverse, hlen]; omega) fun c' ⟨hr', hl', h'', q', hH', hB',
    hlh, hq', hrq, hw', F7⟩ => ⟨[⟨lnil, .nil, []⟩] ++ h'', q', by simpa using hH',
      by simpa using hB', hr', by simpa using hrq, by simpa using hq', hw', ?_, ?_, ?_⟩)
  · have F : Fr [.ptr, .t4, .lst, .heap, .cnt, .work] c c' :=
      ((F5.trans F6).trans F7).mono (by decide)
    have e₁ : c'.stk .ptr = c.stk .ptr := by
      rw [F7 .ptr (by decide), F6 .ptr (by decide)]
      simp only [Act.run]
      rw [update_of_ne (by decide), F4 .ptr (by decide)]
      simp only [Act.run]
      exact hp₂
    have e₂ : c'.stk .t4 = c.stk .t4 := by
      rw [F7 .t4 (by decide), F6 .t4 (by decide)]
      simp [Act.run, ht₃]
    exact ((F.restore e₁).restore e₂).restore hl'
  · simp [hlh, hlen]; omega
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h ([⟨lnil, .nil, []⟩] ++ h'')
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ ([⟨lnil, .nil, []⟩] ++ h''))).length :=
      ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hUM : U ≤ M := by
      simp only [List.length_append, List.length_singleton, hlh, List.length_reverse,
        hlen] at s3
      omega
    have hA := allocBound_mono (a := 2 * U + 2) (b := 2 * M + 2) (m := U) (n := M) (by omega)
      hUM
    have hA0 := allocBound_mono (a := 0) (b := 2 * M + 2) (m := h.length) (n := M) (by omega)
      (by omega)
    have hf := fcE_mono s2 (by omega : E ≤ M)
    refine le_succ_mul2.trans (Nat.mul_le_mul_left _ ((primB_ge M).trans' ?_))
    omega

/-- Append: walk the first list, then cons its elements onto the second. -/
def appendCode : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .lst .t0) (.seq (moveNum2 .work .ptr .t0) (.seq (.act (.push .t4 (.mk 3)))
    (.seq (walkList .t4) (.seq (moveNum2 .lst .work .t0) (buildListB .t4)))))

theorem out_append {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {xs ys : List a.denote} {lx ly : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (h2F : 2 ≤ F) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [lx, ly] ++ w) (rx : Rep h (.list a) xs (ofBits lx))
    (ry : Rep h (.list a) ys (ofBits ly)) (hlx : lx.length ≤ B + h.length)
    (hly : ly.length ≤ B + h.length) {G : ℕ} (hG : xs.length ≤ G) :
    PrimOut prog appendCode c h w (.list a) (xs ++ ys) B F G (xs.length + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlx hly
  obtain ⟨U, hU⟩ : ∃ U, U = B + h.length + xs.length := ⟨_, rfl⟩
  have hw' : c.stk .work = bits ly ++ .nd :: (bits lx ++ .nd :: w) := by
    simpa [envEnc] using hw
  unfold appendCode
  refine PrimOut.of_sat (T := (xs.length + 1) * (fcE (encHeap h).length E + 24 * E + 50) +
    xs.length * (36 * U + allocBound (2 * U + 2) U + 72) + (36 * E + 100))
    (Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw') (by omega)
      fun c₁ ⟨hr₁, hw₁, hl₁, hj₁⟩ => ?_)
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₁ hw₁) (by omega)
    fun c₂ ⟨hr₂, hw₂, hp₂, hj₂⟩ => Sat.act_seq (by omega) ?_
  have F1 : Fr [.work, .lst, .work, .ptr, .t4] c (Act.run (.push .t4 (.mk 3)) c₂) :=
    ((fr2 hj₁).trans (fr2 hj₂)).trans (fr_push .t4 (.mk 3) c₂)
  have hH₁ : HeapAt h (Act.run (.push .t4 (.mk 3)) c₂) :=
    hH.fr F1 (by decide) (by decide) (by decide)
  refine Sat.seq_le (walkList_sat (E := E) (q := lx) (rp := c.stk .ptr) (by decide) hH₁ hB hr₂
    (by simp [Act.run, hp₂, hj₁ .ptr (by decide) (by decide)]) rx (by omega) (by omega))
    (by omega) fun c₃ ⟨hr₃, hp₃, F3, psr, hR, hpB, ht₃⟩ => ?_
  have hlen : psr.length = xs.length := by rw [← hR.length_eq, List.length_reverse]
  have hl₃ : c₃.stk .lst = bits ly ++ .nd :: c.stk .lst := by
    rw [F3 .lst (by decide)]
    simp [Act.run, hj₂ .lst (by decide) (by decide), hl₁]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₃ hl₃) (by omega)
    fun c₄ ⟨hr₄, hl₄, hw₄, hj₄⟩ => ?_
  have F4 := (F1.trans F3).trans (fr2 hj₄)
  have hH₄ : HeapAt h c₄ := hH.fr F4 (by decide) (by decide) (by decide)
  have hw₄' : c₄.stk .work = bits ly ++ .nd :: w := by
    rw [hw₄, F3 .work (by decide)]
    simp [Act.run, hw₂]
  have ht₄ : c₄.stk .t4 = encNums psr ++ .mk 3 :: c.stk .t4 := by
    rw [hj₄ .t4 (by decide) (by decide), ht₃]
    simp [Act.run, hj₂ .t4 (by decide) (by decide), hj₁ .t4 (by decide) (by decide)]
  have hbl := buildListB_sat (prog := prog) (s := .t4) (by decide) h1B h2F hH₄ hB hr₄ ht₄ hw₄'
    hR ry (fun p hp => by have := hpB p hp; omega) (by omega)
  rw [show B + h.length + psr.length = U by omega] at hbl
  refine (hbl.mono (by rw [hlen]; omega) fun c' ⟨hr', ht', h'', q', hH', hB', hlh, hq', hrq, hw',
    F5⟩ => ⟨h'', q', hH', hB', hr', by simpa using hrq, hq', hw', ?_, by omega, ?_⟩)
  · have F : Fr [.ptr, .lst, .t4, .heap, .cnt, .work] c c' := (F4.trans F5).mono (by decide)
    have e₁ : c'.stk .ptr = c.stk .ptr := by
      rw [F5 .ptr (by decide), hj₄ .ptr (by decide) (by decide), hp₃]
    have e₂ : c'.stk .lst = c.stk .lst := by rw [F5 .lst (by decide), hl₄]
    exact ((F.restore e₁).restore e₂).restore ht'
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h h''
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ h'')).length := ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hUM : U ≤ M := by
      simp only [List.length_append, hlh, hlen] at s3
      omega
    have hA := allocBound_mono (a := 2 * U + 2) (b := 2 * M + 2) (m := U) (n := M) (by omega)
      hUM
    have hf := fcE_mono s2 (by omega : E ≤ M)
    refine le_succ_mul.trans (Nat.mul_le_mul_left _ ((primB_ge M).trans' ?_))
    omega

/-- An array from a list: walk it, move the pointers onto `work` (in order), one cell. -/
def arrayOfListCode : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .ptr .t0) (.seq (.act (.push .t4 (.mk 3))) (.seq (walkList .t4)
    (.seq (.act (.push .work (.mk 2))) (.seq (moveAll 3 .t4 .work) (.seq (.act (.pop .t4 0))
      (.seq (.act (.set 0 none)) (alloc .arr)))))))

theorem RepList.rep_arr {h : List Cell} {a : Ty} {xs : List a.denote} {ps : List (List Bool)}
    (hR : RepList h a xs ps) {p : ℕ} (hc : CellAt h p .arr ps) :
    Rep h (.array a) xs.toArray p :=
  .arr hc (by simpa using hR.length_eq.symm) fun i hi hv => by
    have := hR.get (by simpa using hv) hi
    simpa using this

theorem out_arrayOfList {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {xs : List a.denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h (.list a) xs (ofBits lx)) (hlx : lx.length ≤ B + h.length)
    (hk : xs.length + 1 ≤ F) (hFB : F ≤ B) {G : ℕ} (hG : 1 ≤ G) :
    PrimOut prog arrayOfListCode c h w (.array a) xs.toArray B F G (xs.length + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlx
  have hw' : c.stk .work = bits lx ++ .nd :: w := by simpa [envEnc] using hw
  unfold arrayOfListCode
  refine PrimOut.of_sat (T := (xs.length + 1) * (fcE (encHeap h).length E + 24 * E + 50) +
    xs.length * (12 * E + 24) + (12 * E + allocBound (xs.length * (E + 1)) h.length + 100))
    (Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw') (by omega)
      fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => Sat.act_seq (by omega) ?_)
  have F1 : Fr [.work, .ptr, .t4] c (Act.run (.push .t4 (.mk 3)) c₁) :=
    (fr2 hj₁).trans (fr_push .t4 (.mk 3) c₁)
  have hH₁ : HeapAt h (Act.run (.push .t4 (.mk 3)) c₁) :=
    hH.fr F1 (by decide) (by decide) (by decide)
  refine Sat.seq_le (walkList_sat (E := E) (q := lx) (rp := c.stk .ptr) (by decide) hH₁ hB hr₁
    (by simpa [Act.run] using hp₁) hr (by omega) (by omega)) (by omega)
    fun c₂ ⟨hr₂, hp₂, F2, psr, hR, hpB, ht₂⟩ => Sat.act_seq (by omega) ?_
  have hlen : psr.length = xs.length := by rw [← hR.length_eq, List.length_reverse]
  have ht₂' : (Act.run (.push .work (.mk 2)) c₂).stk .t4 =
      encNums psr ++ .mk 3 :: c.stk .t4 := by
    rw [show (Act.run (.push .work (.mk 2)) c₂).stk .t4 = c₂.stk .t4 by simp [Act.run], ht₂]
    simp [Act.run, hj₁ .t4 (by decide) (by decide)]
  have hma := moveAll_sat (prog := prog) (i := 3) (b := .work) (E := E)
    (c := Act.run (.push .work (.mk 2)) c₂) (by decide) (by decide) (by decide) hr₂ ht₂'
    (fun l hl => by have := hpB l hl; omega)
  rw [hlen] at hma
  refine Sat.seq_le hma (by omega) fun c₃ ⟨hr₃, ht₃, hw₃, F3⟩ =>
    Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have hv₄ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero, update_rv_zero]
  have F4 : Fr [.work, .ptr, .t4, .ptr, .t4, .work, .t4, .work, .t4] c
      (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)) :=
    ((((F1.trans F2).trans (fr_push .work (.mk 2) c₂)).trans F3).trans (fr_pop .t4 0 c₃)).trans
      (fr_set 0 none _)
  have hH₄ := hH.fr F4 (by decide) (by decide) (by decide)
  have hw₄ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₃)).stk .work =
      encFields psr.reverse ++ .mk 2 :: w := by
    simp only [Act.run]
    rw [update_of_ne (by decide), hw₃, encFields_eq_encNums]
    simp only [Act.run, update_self]
    rw [F2 .work (by decide)]
    simp [Act.run, hw₁]
  have hLf := length_encFields_le (U := E) psr.reverse fun p hp => by
    have := hpB p (List.mem_reverse.1 hp); omega
  rw [List.length_reverse, hlen] at hLf
  have hA₀ := allocBound_mono (a := (encFields psr.reverse).length) (b := xs.length * (E + 1))
    (m := h.length) (n := h.length) hLf le_rfl
  refine (allocB_sat .arr hH₄ hB h1B hv₄ hw₄ (by simp; omega) (fun f hf => by
    have := hpB f (List.mem_reverse.1 hf); omega)).mono (by omega)
    fun c' ⟨hr', l, hH', hB', hc', hl', hw', F5⟩ => ⟨[⟨l, .arr, psr.reverse⟩], l, hH', hB', hr',
      ?_, by simp; omega, hw', ?_, by simpa using hG, ?_⟩
  · have hR' : RepList h a xs psr.reverse := by
      have := List.forall₂_reverse_iff.2 hR
      simp only [List.reverse_reverse] at this
      exact this
    exact (RepList.mono hR').rep_arr hc'
  · have F : Fr [.ptr, .t4, .heap, .cnt, .work] c c' := (F4.trans F5).mono (by decide)
    have e₁ : c'.stk .ptr = c.stk .ptr := by
      rw [F5 .ptr (by decide)]
      simp only [Act.run]
      rw [update_of_ne (by decide), F3 .ptr (by decide)]
      simp only [Act.run]
      rw [update_of_ne (by decide)]
      exact hp₂
    have e₂ : c'.stk .t4 = c.stk .t4 := by
      rw [F5 .t4 (by decide)]
      simp [Act.run, ht₃]
    exact (F.restore e₁).restore e₂
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .arr, psr.reverse⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .arr, psr.reverse⟩])).length := ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hkM : xs.length ≤ M := by omega
    have hEM : E ≤ M := by omega
    have hm : xs.length * (E + 1) ≤ M * M + 3 * M + 2 := by nlinarith
    have hA := allocBound_mono (a := xs.length * (E + 1)) (b := M * M + 3 * M + 2)
      (m := h.length) (n := M) hm (by omega)
    have hf := fcE_mono s2 hEM
    refine le_succ_mul.trans (Nat.mul_le_mul_left _ ((primB_ge' M).trans' ?_))
    have : 0 ≤ M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) := Nat.zero_le _
    omega

/-- The elements of an array's cell, as a `RepList`. -/
theorem Rep.arr_list {h : List Cell} {a : Ty} {v : Array a.denote} {p : ℕ}
    (r : Rep h (.array a) v p) : ∃ fs, CellAt h p .arr fs ∧ RepList h a v.toList fs := by
  obtain ⟨fs, hc, hl, hr⟩ := r.arr_inv
  refine ⟨fs, hc, List.forall₂_iff_get.2 ⟨by simp [hl], fun i h₁ h₂ => ?_⟩⟩
  have := hr i h₂ (by simpa using h₁)
  simpa using this

/-- A list from an array: the fields of its cell, reversed onto `t4`, consed onto a new
`nil`. -/
def arrayToListCode : Code Stk Sym Rg P :=
  .seq openTop (.seq (.act (.set 1 none)) (.seq (.act (.push .t4 (.mk 3)))
    (.seq (moveAll 0 .work .t4) (.seq closeCell (.seq (allocArgs .nil 0) (buildListB .t4))))))

theorem out_arrayToList {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {v : Array a.denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (h2F : 2 ≤ F) (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lx] ++ w)
    (hr : Rep h (.array a) v (ofBits lx)) (hlx : lx.length ≤ B + h.length) {G : ℕ}
    (hG : v.size + 1 ≤ G) :
    PrimOut prog arrayToListCode c h w (.list a) v.toList B F G (v.size + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlx
  obtain ⟨U, hU⟩ : ∃ U, U = B + h.length + 1 + v.size := ⟨_, rfl⟩
  obtain ⟨fs, hc, hR⟩ := hr.arr_list
  have hlen : fs.length = v.size := by rw [← hR.length_eq, Array.length_toList]
  have hfB := hB.field_lt hc
  have hw' : c.stk .work = bits lx ++ .nd :: w := by simpa [envEnc] using hw
  have hk1 : fcE (encHeap h).length E + 12 * E + 20 ≤
      (v.size + 1) * (fcE (encHeap h).length E + 12 * E + 20) := Nat.le_mul_of_pos_left _ (by omega)
  unfold arrayToListCode
  refine PrimOut.of_sat (T := (v.size + 1) * (fcE (encHeap h).length E + 12 * E + 20) +
    v.size * (12 * E + 24) + v.size * (36 * U + allocBound (2 * U + 2) U + 72) +
    (allocBound 0 h.length + 100))
    (Sat.seq_le (openTop_sat (w := w) hH hv hw' hc hlx) (by omega)
      fun c₁ ⟨hr₁, hw₁, F1⟩ => Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
  have hma := moveAll_sat (prog := prog) (i := 0) (a := .work) (b := .t4) (E := E)
    (c := Act.run (.push .t4 (.mk 3)) (Act.run (.set 1 none) c₁)) (ns := fs) (rest := w)
    (by decide) (by decide) (by decide)
    (by simp only [Act.run]; rw [hr₁, empty_eq_rv, update_rv_one])
    (by simp [Act.run, hw₁, encFields_eq_encNums]) (fun l hl => by have := hfB l hl; omega)
  rw [hlen] at hma
  refine Sat.seq_le hma (by omega) fun c₂ ⟨hr₂, hw₂, ht₂, F2⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₂, empty_eq_rv]) hw₂) (by omega)
    fun c₃ ⟨hr₃, hw₃, hj₃⟩ => ?_
  have F3 : Fr [.work, .t4, .work, .t4, .work] c c₃ :=
    (((F1.trans (fr_set 1 none c₁)).trans (fr_push .t4 (.mk 3) _)).trans F2).trans (fr1 hj₃)
  have hH₃ := hH.fr F3 (by decide) (by decide) (by decide)
  refine Sat.seq_le ((allocArgs_sat (prog := prog) .nil (ls := []) (w := w) hH₃ hB h1B
    (by rw [hr₃, empty_eq_rv]) (by simp [hw₃]) (by simp) (by simp)).mono
    (t' := allocBound 0 h.length + 9) (by simp [encFields]) fun _ h => h) (by omega)
    fun c₄ ⟨hr₄, lnil, hH₄, hB₄, hc₄, hl₄, hw₄, F4⟩ => ?_
  have hR' : RepList (h ++ [⟨lnil, .nil, []⟩]) a v.toList.reverse fs.reverse := by
    have := List.forall₂_reverse_iff.2 hR
    exact RepList.mono this
  have ht₄ : c₄.stk .t4 = encNums fs.reverse ++ .mk 3 :: c.stk .t4 := by
    rw [F4 .t4 (by decide), hj₃ .t4 (by decide), ht₂]
    simp [Act.run, F1 .t4 (by decide)]
  have hbl := buildListB_sat (prog := prog) (s := .t4) (by decide) h1B h2F hH₄ hB₄ hr₄ ht₄ hw₄
    hR' (Rep.nil hc₄) (fun p hp => by
      have := hfB p (List.mem_reverse.1 hp); simp; omega) (by simp; omega)
  have hU' : B + (h ++ [Cell.mk lnil .nil []]).length + fs.reverse.length = U := by
    simp [hlen]; omega
  rw [hU'] at hbl
  refine (hbl.mono (by rw [List.length_reverse, hlen]; omega) fun c' ⟨hr', ht', h'', q', hH',
    hB', hlh, hq', hrq, hw', F5⟩ => ⟨[⟨lnil, .nil, []⟩] ++ h'', q', by simpa using hH',
      by simpa using hB', hr', by simpa using hrq, by simpa using hq', hw', ?_, ?_, ?_⟩)
  · have F : Fr [.t4, .heap, .cnt, .work] c c' := ((F3.trans F4).trans F5).mono (by decide)
    exact F.restore ht'
  · simp [hlh, hlen]; omega
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h ([⟨lnil, .nil, []⟩] ++ h'')
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ ([⟨lnil, .nil, []⟩] ++ h''))).length :=
      ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hUM : U ≤ M := by
      simp only [List.length_append, List.length_singleton, hlh, List.length_reverse,
        hlen] at s3
      omega
    have hA := allocBound_mono (a := 2 * U + 2) (b := 2 * M + 2) (m := U) (n := M) (by omega)
      hUM
    have hA0 := allocBound_mono (a := 0) (b := 2 * M + 2) (m := h.length) (n := M) (by omega)
      (by omega)
    have hf := fcE_mono s2 (by omega : E ≤ M)
    refine le_succ_mul2.trans (Nat.mul_le_mul_left _ ((primB_ge M).trans' ?_))
    omega

/-- The size of an array: count the fields of its cell, one cell. -/
def arraySizeCode : Code Stk Sym Rg P :=
  .seq openTop (.seq (.act (.set 1 none)) (.seq (countAll 0 .work) (.seq closeCell
    (.seq (.act (.push .work (.mk 2))) (.seq (moveNum2 .t2 .work .t0) (alloc .nat))))))

theorem out_arraySize {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {v : Array a.denote} {lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hFB : F + 1 ≤ B) (h1F : 1 ≤ F) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [lx] ++ w) (hr : Rep h (.array a) v (ofBits lx))
    (hlx : lx.length ≤ B + h.length) {G C : ℕ} (hG : 1 ≤ G) (hC : 1 ≤ C) :
    PrimOut prog arraySizeCode c h w .nat v.size B F G C := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlx
  obtain ⟨fs, hc, hR⟩ := hr.arr_list
  have hlen : fs.length = v.size := by rw [← hR.length_eq, Array.length_toList]
  have hfB := hB.field_lt hc
  have hkF : fs.length ≤ F := by
    obtain ⟨hp, -, hf⟩ := hc
    rw [← hf]; exact (hB _ hp).2.1
  have hw' : c.stk .work = bits lx ++ .nd :: w := by simpa [envEnc] using hw
  unfold arraySizeCode
  refine PrimOut.of_sat (T := fcE (encHeap h).length E + 12 * E +
    v.size * (2 * E + 35 * v.size + 150) + 12 * v.size + allocBound (v.size + 2) h.length + 100)
    (Sat.seq_le (openTop_sat (w := w) hH hv hw' hc hlx) (by omega)
      fun c₁ ⟨hr₁, hw₁, F1⟩ => Sat.act_seq (by omega) ?_)
  have hca := countAll_sat (prog := prog) (i := 0) (a := .work) (E := E)
    (c := Act.run (.set 1 none) c₁) (ns := fs) (rest := w) (by decide)
    (by simp only [Act.run]; rw [hr₁, empty_eq_rv, update_rv_one])
    (by simp [Act.run, hw₁, encFields_eq_encNums]) (fun l hl => by have := hfB l hl; omega)
  rw [hlen] at hca
  refine Sat.seq_le hca (by omega) fun c₂ ⟨hr₂, hw₂, ht₂, F2⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₂, empty_eq_rv]) hw₂) (by omega)
    fun c₃ ⟨hr₃, hw₃, hj₃⟩ => Sat.act_seq (by omega) ?_
  have hcnt := length_cntBits_le v.size
  have ht₃ : (Act.run (.push .work (.mk 2)) c₃).stk .t2 =
      bits (cntBits v.size) ++ .nd :: c.stk .t2 := by
    simp only [Act.run]
    rw [update_of_ne (by decide), hj₃ .t2 (by decide), ht₂]
    simp [Act.run, F1 .t2 (by decide)]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide)
    (by simp only [Act.run]; rw [hr₃, empty_eq_rv]) ht₃) (by omega)
    fun c₄ ⟨hr₄, ht₄, hw₄, hj₄⟩ => ?_
  have F4 : Fr [.work, .work, .t2, .work, .work, .t2, .work] c c₄ :=
    ((((F1.trans (fr_set 1 none c₁)).trans F2).trans (fr1 hj₃)).trans
      (fr_push .work (.mk 2) c₃)).trans (fr2 hj₄)
  have hH₄ := hH.fr F4 (by decide) (by decide) (by decide)
  have hw₄' : c₄.stk .work = encFields [cntBits v.size] ++ .mk 2 :: w := by
    rw [hw₄]; simp [Act.run, hw₃, encFields]
  have hA₀ := allocBound_mono (a := (encFields [cntBits v.size]).length)
    (b := v.size + 2) (m := h.length) (n := h.length) (by simp [encFields]; omega) le_rfl
  refine (allocB_sat .nat hH₄ hB (by omega) hr₄ hw₄' (by simp; omega)
    (by simp; omega)).mono (by omega) fun c' ⟨hr', l, hH', hB', hc', hl', hw', F5⟩ =>
      ⟨[⟨l, .nat, [cntBits v.size]⟩], l, hH', hB', hr',
        by simpa [ofBits_cntBits] using Rep.nat hc', by simp; omega, hw', ?_,
        by simpa using hG, ?_⟩
  · have F : Fr [.t2, .heap, .cnt, .work] c c' := (F4.trans F5).mono (by decide)
    exact F.restore (by rw [F5 .t2 (by decide), ht₄])
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .nat, [cntBits v.size]⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .nat, [cntBits v.size]⟩])).length :=
      ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hkM : v.size ≤ M := by omega
    have hEM : E ≤ M := by omega
    have hA := allocBound_mono (a := v.size + 2) (b := M * M + 3 * M + 2) (m := h.length) (n := M)
      (by nlinarith) (by omega)
    have hA3 : 300 ≤ allocBound (M * M + 3 * M + 2) M := by unfold allocBound; omega
    have hf := fcE_mono s2 hEM
    have hm : v.size * (2 * E + 35 * v.size + 150) ≤
        M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) :=
      Nat.mul_le_mul hkM (by omega)
    exact le_mul_primB hC ((primB_ge' M).trans' (by omega))

/-! ### Loops over counters -/

theorem le_succ_mul0 {k b c : ℕ} : k * b + c ≤ (k + 1) * (b + c) := by
  have e : (k + 1) * (b + c) = k * b + b + (k + 1) * c := by ring
  have : c ≤ (k + 1) * c := Nat.le_mul_of_pos_left c (by omega)
  omega

/-- The test of `arrayMk`: the bit `n = 0` for the counter `n` on `t2`, into register `0`. -/
def mkTest : Code Stk Sym Rg P :=
  .seq (copyNum .t2 .t3 .t0) (.seq (pushNum [] .lst) (.seq (eqNum .t3 .lst .ptr .t0)
    (.act (.pop .ptr 0))))

theorem mkTest_sat {c : Cfg Stk Sym Rg} {nb : List Bool} {r : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (ht : c.stk .t2 = bits nb ++ .nd :: r) (hE : nb.length ≤ E) :
    Sat prog mkTest c (33 * E + 70) fun c' =>
      c'.regs = rv (some (.bit (decide (ofBits nb = 0)))) none none none ∧ c'.stk = c.stk := by
  unfold mkTest
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hv ht) (by omega)
    fun c₁ ⟨hr₁, ht₁, hj₁⟩ => ?_
  refine Sat.seq_le ((pushNum_sat (prog := prog) Stk.lst c₁ []).mono (t' := 1) (by simp)
    fun _ h => h) (by omega) fun c₂ ⟨hr₂, hl₂, hj₂⟩ => ?_
  have ht₂ : c₂.stk .t3 = bits nb ++ .nd :: c.stk .t3 := by rw [hj₂ .t3 (by decide), ht₁]
  refine Sat.seq_le ((eqNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hr₂, hr₁]) ht₂ hl₂).mono (t' := 19 * nb.length + 34) (by simp)
    fun _ h => h) (by omega) fun c₃ ⟨hr₃, ht₃, hl₃, hp₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_⟩
  · rw [empty_eq_rv] at hr₃
    simp only [Act.run, hr₃, hp₃, update_rv_zero, List.head?_cons]
    rfl
  · funext j
    simp only [Act.run]
    by_cases hjp : j = .ptr
    · subst hjp; rw [update_self, hp₃]; simp [hj₂ .ptr (by decide), hj₁ .ptr (by decide)]
    rw [update_of_ne hjp]
    by_cases h3 : j = .t3
    · subst h3; rw [ht₃]
    by_cases hl : j = .lst
    · subst hl; rw [hl₃, hj₁ .lst (by decide)]
    rw [hj₃ j h3 hl hjp, hj₂ j hl, hj₁ j h3]

/-- An array of `k` copies of a value: push copies of its pointer while counting down. -/
def arrayMkCode : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .t1 .t0) (.seq (natTo .t2) (.seq (.act (.push .work (.mk 2)))
    (.seq mkTest (.seq (.loop (.is 0 (some (.bit false)))
        (.seq (.act (.set 0 none)) (.seq (copyNum .t1 .work .t0)
          (.seq (decNum .t2 .t3 .lst .t0) (.seq (moveNum2 .lst .t2 .t0) mkTest)))))
      (.seq (.act (.set 0 none)) (.seq (dropNum .t2) (.seq (dropNum .t1) (alloc .arr))))))))

theorem out_arrayMk {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {k : ℕ} {x : a.denote} {lk lx : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (h1B : 1 ≤ B) (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lk, lx] ++ w)
    (rk : Rep h .nat k (ofBits lk)) (rx : Rep h a x (ofBits lx))
    (hlk : lk.length ≤ B + h.length) (hlx : lx.length ≤ B + h.length) (hk : k + 1 ≤ F)
    (hFB : F ≤ B) {G : ℕ} (hG : 1 ≤ G) :
    PrimOut prog arrayMkCode c h w (.array a) (Array.replicate k x) B F G (k + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlk hlx
  have hw' : c.stk .work = bits lx ++ .nd :: (bits lk ++ .nd :: w) := by simpa [envEnc] using hw
  unfold arrayMkCode
  refine PrimOut.of_sat (T := k * (82 * E + 201) + (fcE (encHeap h).length E + 100 * E +
    allocBound (k * (E + 1)) h.length + 300))
    (Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw') (by omega)
      fun c₁ ⟨hr₁, hw₁, ht₁, hj₁⟩ => ?_)
  have hH₁ : HeapAt h c₁ := hH.fr (fr2 hj₁) (by decide) (by decide) (by decide)
  refine Sat.seq_le (natTo_sat (by decide) (by decide) hH₁ hB hr₁ hw₁ rk hlk (by omega))
    (by omega) fun c₂ ⟨hr₂, hw₂, F2, nk, hnk, hnkB, ht₂⟩ => Sat.act_seq (by omega) ?_
  have F2' : Fr [.work, .t1, .work, .t2, .work] c (Act.run (.push .work (.mk 2)) c₂) :=
    ((fr2 hj₁).trans F2).trans (fr_push .work (.mk 2) c₂)
  have hE1 : 1 ≤ E := by omega
  have hloop := Sat.loop (prog := prog) (b := .is 0 (some (.bit false)))
    (x := .seq (.act (.set 0 none)) (.seq (copyNum .t1 .work .t0)
      (.seq (decNum .t2 .t3 .lst .t0) (.seq (moveNum2 .lst .t2 .t0) mkTest))))
    (t := 82 * E + 200)
    (I := fun m c₃ => ∃ nb, ofBits nb = m ∧ nb.length ≤ E ∧ m ≤ k ∧
      c₃.stk .t2 = bits nb ++ .nd :: c.stk .t2 ∧ c₃.stk .t1 = bits lx ++ .nd :: c.stk .t1 ∧
      c₃.stk .work = encNums (List.replicate (k - m) lx) ++ .mk 2 :: w ∧
      c₃.regs = rv (some (.bit (decide (m = 0)))) none none none ∧ Fr [.work, .t1, .t2] c c₃)
    (Q := fun c₃ => ∃ nb, nb.length ≤ E ∧
      c₃.stk .t2 = bits nb ++ .nd :: c.stk .t2 ∧ c₃.stk .t1 = bits lx ++ .nd :: c.stk .t1 ∧
      c₃.stk .work = encNums (List.replicate k lx) ++ .mk 2 :: w ∧
      c₃.regs = rv (some (.bit true)) none none none ∧ Fr [.work, .t1, .t2] c c₃)
    (fun m c₃ ⟨nb, hnb, hnbE, hmk, ht₃, ht₃', hw₃, hr₃, F3⟩ => by
      refine ⟨by simp [Cond.eval, hr₃], Sat.act_seq (by omega) ?_⟩
      have hv₄ : (Act.run (.set 0 none) c₃).regs = Regs.empty := by
        simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero]
      refine Sat.seq_le (copyNum_sat (l := lx) (rest := c.stk .t1) (by decide) (by decide)
        (by decide) hv₄ (by simpa [Act.run] using ht₃')) (by omega) fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
      refine Sat.seq_le (decNum_sat (xs := nb) (ra := c.stk .t2) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) hr₅
        (by rw [hj₅ .t2 (by decide)]; simpa [Act.run] using ht₃)) (by omega)
        fun c₆ ⟨hr₆, ht₆, hl₆, hj₆⟩ => ?_
      have hsub := length_subBits_le nb [true]
      simp only [List.length_singleton] at hsub
      refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₆ hl₆) (by omega)
        fun c₇ ⟨hr₇, hl₇, ht₇, hj₇⟩ => ?_
      refine (mkTest_sat (E := E) hr₇ ht₇ (by omega)).mono (by omega)
        fun c₈ ⟨hr₈, hs₈⟩ => ⟨subBits nb [true], ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ofBits_subBits, hnb]; simp
      · rw [hs₈, ht₇, ht₆]
      · rw [hs₈, hj₇ .t1 (by decide) (by decide), hj₆ .t1 (by decide) (by decide),
          hj₅ .t1 (by decide)]
        simpa [Act.run] using ht₃'
      · rw [hs₈, hj₇ .work (by decide) (by decide), hj₆ .work (by decide) (by decide), hw₅]
        have e : k - m = (k - (m + 1)) + 1 := by omega
        rw [e, List.replicate_succ]
        simp [Act.run, hw₃]
      · rw [hr₈, ofBits_subBits, hnb]; simp
      · intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
        rw [hs₈]
        by_cases hl : j = .lst
        · subst hl
          rw [hl₇, hj₅ .lst (by decide)]
          exact F3 .lst (by decide)
        rw [hj₇ j hl hj.2.2, hj₆ j hj.2.2 hl, hj₅ j hj.1]
        exact F3 j (by simp [hj.1, hj.2.1, hj.2.2]))
    (fun c₃ ⟨nb, _, hnbE, _, ht₃, ht₃', hw₃, hr₃, F3⟩ =>
      ⟨by simp [Cond.eval, hr₃], nb, hnbE, ht₃, ht₃', by simpa using hw₃, by rw [hr₃]; simp,
        F3⟩)
  refine Sat.seq_le (mkTest_sat (E := E) (nb := nk) (r := c.stk .t2)
    (by simpa [Act.run] using hr₂)
    (by rw [show (Act.run (.push .work (.mk 2)) c₂).stk .t2 = c₂.stk .t2 by simp [Act.run],
      ht₂, hj₁ .t2 (by decide) (by decide)]) (by omega)) (by omega)
    fun c₃ ⟨hr₃, hs₃⟩ => ?_
  have I0 : ∃ nb, ofBits nb = k ∧ nb.length ≤ E ∧ k ≤ k ∧
      c₃.stk .t2 = bits nb ++ .nd :: c.stk .t2 ∧ c₃.stk .t1 = bits lx ++ .nd :: c.stk .t1 ∧
      c₃.stk .work = encNums (List.replicate (k - k) lx) ++ .mk 2 :: w ∧
      c₃.regs = rv (some (.bit (decide (k = 0)))) none none none ∧ Fr [.work, .t1, .t2] c c₃ := by
    refine ⟨nk, hnk, by omega, le_rfl, ?_, ?_, ?_, by rw [hr₃, hnk], ?_⟩
    · rw [hs₃]; simp [Act.run, ht₂, hj₁ .t2 (by decide) (by decide)]
    · rw [hs₃]; simp [Act.run, F2 .t1 (by decide), ht₁]
    · rw [hs₃]; simp [Act.run, hw₂]
    · intro j hj
      rw [hs₃]
      exact (F2'.mono (T := [.work, .t1, .t2]) (by decide)) j hj
  have e : k * (82 * E + 200 + 1) = k * (82 * E + 201) := by ring
  refine Sat.seq_le (hloop k c₃ I0) (by omega) fun c₄ ⟨nb, hnbE, ht₄, ht₄', hw₄, hr₄, F4⟩ =>
    Sat.act_seq (by omega) ?_
  have hv₅ : (Act.run (.set 0 none) c₄).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₄, empty_eq_rv, update_rv_zero]
  refine Sat.seq_le (dropNum_sat (l := nb) (rest := c.stk .t2) hv₅
    (by simpa [Act.run] using ht₄)) (by omega) fun c₅ ⟨hr₅, ht₅, hj₅⟩ => ?_
  refine Sat.seq_le (dropNum_sat (l := lx) (rest := c.stk .t1) hr₅
    (by rw [hj₅ .t1 (by decide)]; simpa [Act.run] using ht₄')) (by omega)
    fun c₆ ⟨hr₆, ht₆, hj₆⟩ => ?_
  have F6 : Fr [.work, .t1, .t2] c c₆ := fun j hj => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [hj₆ j hj.2.1, hj₅ j hj.2.2]
    exact F4 j (by simp [hj.1, hj.2.1, hj.2.2])
  have hH₆ := hH.fr F6 (by decide) (by decide) (by decide)
  have hw₆ : c₆.stk .work = encFields (List.replicate k lx) ++ .mk 2 :: w := by
    rw [hj₆ .work (by decide), hj₅ .work (by decide), encFields_eq_encNums]
    simpa [Act.run] using hw₄
  have hLf := length_encFields_le (U := E) (List.replicate k lx) fun p hp => by
    rw [List.eq_of_mem_replicate hp]; exact hlx
  rw [List.length_replicate] at hLf
  have hA₀ := allocBound_mono (a := (encFields (List.replicate k lx)).length) (b := k * (E + 1))
    (m := h.length) (n := h.length) hLf le_rfl
  refine (allocB_sat .arr hH₆ hB h1B hr₆ hw₆ (by simp; omega) (fun f hf => by
    rw [List.eq_of_mem_replicate hf]; omega)).mono (by omega)
    fun c' ⟨hr', l, hH', hB', hc', hl', hw', F7⟩ => ⟨[⟨l, .arr, List.replicate k lx⟩], l, hH',
      hB', hr', ?_, by simp; omega, hw', ?_, by simpa using hG, ?_⟩
  · refine .arr hc' (by simp) fun i hi hv => ?_
    simp only [List.getElem_replicate, Array.getElem_replicate]
    exact rx.mono
  · have F : Fr [.t1, .t2, .heap, .cnt, .work] c c' := (F6.trans F7).mono (by decide)
    exact (F.restore (by rw [F7 .t1 (by decide), ht₆])).restore
      (by rw [F7 .t2 (by decide), hj₆ .t2 (by decide), ht₅])
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .arr, List.replicate k lx⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .arr, List.replicate k lx⟩])).length :=
      ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hkM : k ≤ M := by omega
    have hEM : E ≤ M := by omega
    have hm : k * (E + 1) ≤ M * M + 3 * M + 2 := by nlinarith
    have hA := allocBound_mono (a := k * (E + 1)) (b := M * M + 3 * M + 2)
      (m := h.length) (n := M) hm (by omega)
    have hf := fcE_mono s2 hEM
    refine le_succ_mul0.trans (Nat.mul_le_mul_left _ ((primB_ge' M).trans' ?_))
    omega

theorem le_succ_mul1 {k b b' c : ℕ} : k * b + k * b' + c ≤ (k + 1) * (b + b' + c) := by
  have e : (k + 1) * (b + b' + c) = k * b + k * b' + b + b' + (k + 1) * c := by ring
  have : c ≤ (k + 1) * c := Nat.le_mul_of_pos_left c (by omega)
  omega

/-- The test of `range`: the bit `j < k` for the counter `j` on `t1` and the bound `k` on `t2`,
into register `0`. -/
def rangeTest : Code Stk Sym Rg P :=
  .seq (copyNum .t1 .t3 .t0) (.seq (copyNum .t2 .lst .t0) (.seq (ltNum .t3 .lst .ptr .t0)
    (.act (.pop .ptr 0))))

theorem rangeTest_sat {c : Cfg Stk Sym Rg} {xs ys : List Bool} {r₁ r₂ : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (h₁ : c.stk .t1 = bits xs ++ .nd :: r₁)
    (h₂ : c.stk .t2 = bits ys ++ .nd :: r₂) (hx : xs.length ≤ E) (hy : ys.length ≤ E) :
    Sat prog rangeTest c (47 * E + 80) fun c' =>
      c'.regs = rv (some (.bit (decide (ofBits xs < ofBits ys)))) none none none ∧
        c'.stk = c.stk := by
  unfold rangeTest
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hv h₁) (by omega)
    fun c₁ ⟨hr₁, ht₁, hj₁⟩ => ?_
  refine Sat.seq_le (copyNum_sat (l := ys) (rest := r₂) (by decide) (by decide) (by decide) hr₁
    (by rw [hj₁ .t2 (by decide)]; exact h₂)) (by omega) fun c₂ ⟨hr₂, hl₂, hj₂⟩ => ?_
  have ht₂ : c₂.stk .t3 = bits xs ++ .nd :: c.stk .t3 := by rw [hj₂ .t3 (by decide), ht₁]
  refine Sat.seq_le ((ltNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hr₂ ht₂ hl₂).mono (t' := 19 * E + 33) (by omega) fun _ h => h) (by omega)
    fun c₃ ⟨hr₃, ht₃, hl₃, hp₃, hj₃⟩ => Sat.act_le (by omega) ⟨?_, ?_⟩
  · rw [empty_eq_rv] at hr₃
    simp only [Act.run, hr₃, hp₃, update_rv_zero, List.head?_cons]
  · funext j
    simp only [Act.run]
    by_cases hjp : j = .ptr
    · subst hjp; rw [update_self, hp₃]; simp [hj₂ .ptr (by decide), hj₁ .ptr (by decide)]
    rw [update_of_ne hjp]
    by_cases h3 : j = .t3
    · subst h3; rw [ht₃]
    by_cases hl : j = .lst
    · subst hl; rw [hl₃, hj₁ .lst (by decide)]
    rw [hj₃ j h3 hl hjp, hj₂ j hl, hj₁ j h3]

theorem range_rev_succ (j : ℕ) : (List.range (j + 1)).reverse = j :: (List.range j).reverse := by
  simp [List.range_succ]

/-- The invariant of the loop of `range` with `m` iterations left. -/
def RangeInv (B F : ℕ) (h : List Cell) (c : Cfg Stk Sym Rg) (w : List Sym) (k : ℕ)
    (nk : List Bool) (m : ℕ) (c₃ : Cfg Stk Sym Rg) : Prop :=
  ∃ j h₁ psr, j + m = k ∧ HeapAt (h ++ h₁) c₃ ∧ HeapBnd B F (h ++ h₁) ∧
    h₁.length = j ∧ RepList (h ++ h₁) .nat (List.range j).reverse psr ∧
    (∀ p ∈ psr, p.length ≤ B + (h ++ h₁).length) ∧
    c₃.stk .t1 = bits (cntBits j) ++ .nd :: c.stk .t1 ∧
    c₃.stk .t2 = bits nk ++ .nd :: c.stk .t2 ∧ c₃.stk .t4 = encNums psr ++ .mk 3 :: c.stk .t4 ∧
    c₃.stk .work = w ∧ c₃.regs = rv (some (.bit (decide (j < k)))) none none none ∧
    Fr [.work, .t1, .t2, .t4, .heap, .cnt] c c₃

/-- The body of the loop of `range`. -/
def rangeBody : Code Stk Sym Rg P :=
  .seq (.act (.set 0 none)) (.seq (.act (.push .work (.mk 2)))
    (.seq (copyNum .t1 .work .t0) (.seq (alloc .nat) (.seq (moveNum2 .work .t4 .t0)
      (.seq (incNum .t1 .t3 .lst .t0) (.seq (moveNum2 .lst .t1 .t0) rangeTest))))))

/-- The numbers below `k`: count up to `k`, allocating a natural for each count, then cons
their pointers onto a new `nil`. -/
def rangeCode : Code Stk Sym Rg P :=
  .seq (natTo .t2) (.seq (.act (.push .t4 (.mk 3))) (.seq (pushNum [] .t1) (.seq rangeTest
    (.seq (.loop (.is 0 (some (.bit true))) rangeBody)
      (.seq (.act (.set 0 none)) (.seq (dropNum .t1) (.seq (dropNum .t2) (.seq (allocArgs .nil 0)
        (buildListB .t4)))))))))

theorem range_step {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {k : ℕ}
    {nk : List Bool} (hnk : ofBits nk = k) (hnkB : nk.length < B + h.length) (hFB : F + 1 ≤ B)
    (hk : k + 1 ≤ F) {E' : ℕ} (hE' : E' = B + h.length + k + 1) (m : ℕ) (c₃ : Cfg Stk Sym Rg)
    (hI : RangeInv B F h c w k nk (m + 1) c₃) :
    Cond.eval (.is 0 (some (.bit true))) c₃.regs = true ∧
      Sat prog rangeBody c₃ (110 * E' + allocBound E' E' + 250) (RangeInv B F h c w k nk m) := by
  obtain ⟨j, h₁, psr, hjm, hH₃, hB₃, hl₃, hR₃, hp₃, ht₃, ht₃', ht₃'', hw₃, hr₃, F3⟩ := hI
  have hjk : j < k := by omega
  have hcj := length_cntBits_le j
  refine ⟨by simp [Cond.eval, hr₃, hjk], ?_⟩
  unfold rangeBody
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have hv₄ : (Act.run (.push .work (.mk 2)) (Act.run (.set 0 none) c₃)).regs =
      Regs.empty := by
    simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero]
  refine Sat.seq_le (copyNum_sat (l := cntBits j) (rest := c.stk .t1) (by decide)
    (by decide) (by decide) hv₄ (by simpa [Act.run] using ht₃)) (by omega)
    fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
  have hw₅' : c₅.stk .work = encFields [cntBits j] ++ .mk 2 :: w := by
    rw [hw₅]; simp [Act.run, hw₃, encFields]
  have hH₅ : HeapAt (h ++ h₁) c₅ := hH₃.frame (by rw [hj₅ .heap (by decide)]; rfl)
    (by rw [hj₅ .scan (by decide)]; rfl) (by rw [hj₅ .cnt (by decide)]; rfl)
  have hlen : (h ++ h₁).length = h.length + j := by simp [hl₃]
  have hA := allocBound_mono (a := (encFields [cntBits j]).length) (b := E')
    (m := (h ++ h₁).length) (n := E') (by simp [encFields]; omega) (by omega)
  refine Sat.seq_le (allocB_sat .nat hH₅ hB₃ (by omega) hr₅ hw₅' (by simp; omega)
    (by simp; omega)) (by omega) fun c₆ ⟨hr₆, l, hH₆, hB₆, hc₆, hl₆, hw₆, F6⟩ => ?_
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₆ hw₆) (by omega)
    fun c₇ ⟨hr₇, hw₇, ht₇, hj₇⟩ => ?_
  have ht₇' : c₇.stk .t1 = bits (cntBits j) ++ .nd :: c.stk .t1 := by
    rw [hj₇ .t1 (by decide) (by decide), F6 .t1 (by decide), hj₅ .t1 (by decide)]
    simpa [Act.run] using ht₃
  refine Sat.seq_le (incNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hr₇ ht₇') (by omega) fun c₈ ⟨hr₈, ht₈, hl₈, hj₈⟩ => ?_
  have hla := length_addBits (cntBits j) [true]
  simp only [List.length_singleton] at hla
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₈ hl₈) (by omega)
    fun c₉ ⟨hr₉, hl₉, ht₉, hj₉⟩ => ?_
  have ht₉' : c₉.stk .t1 = bits (cntBits (j + 1)) ++ .nd :: c.stk .t1 := by
    rw [ht₉, ht₈]; rfl
  have ht₉'' : c₉.stk .t2 = bits nk ++ .nd :: c.stk .t2 := by
    rw [hj₉ .t2 (by decide) (by decide), hj₈ .t2 (by decide) (by decide),
      hj₇ .t2 (by decide) (by decide), F6 .t2 (by decide), hj₅ .t2 (by decide)]
    simpa [Act.run] using ht₃'
  have hc1 := length_cntBits_le (j + 1)
  refine (rangeTest_sat (E := E') hr₉ ht₉' ht₉'' (by omega) (by omega)).mono (by omega)
    fun c' ⟨hr', hs'⟩ => ?_
  have e₉ : ∀ i, i ≠ .t1 → i ≠ .lst → i ≠ .work → i ≠ .t4 → c'.stk i = c₆.stk i := by
    intro i h1 hl hw h4
    rw [hs', hj₉ i hl h1, hj₈ i h1 hl, hj₇ i hw h4]
  have hH' : HeapAt (h ++ (h₁ ++ [⟨l, .nat, [cntBits j]⟩])) c' := by
    rw [← List.append_assoc]
    exact hH₆.frame (e₉ _ (by decide) (by decide) (by decide) (by decide))
      (e₉ _ (by decide) (by decide) (by decide) (by decide))
      (e₉ _ (by decide) (by decide) (by decide) (by decide))
  have hR' : RepList (h ++ (h₁ ++ [⟨l, .nat, [cntBits j]⟩])) .nat (List.range (j + 1)).reverse
      (l :: psr) := by
    rw [range_rev_succ, ← List.append_assoc]
    refine List.Forall₂.cons ?_ (RepList.mono hR₃)
    simpa [ofBits_cntBits] using Rep.nat hc₆
  have hp' : ∀ p ∈ l :: psr, p.length ≤ B + (h ++ (h₁ ++ [Cell.mk l .nat [cntBits j]])).length := by
    intro p hp
    rw [← List.append_assoc, List.length_append, hlen, List.length_singleton]
    rcases List.mem_cons.1 hp with rfl | hp
    · omega
    · have := hp₃ p hp; omega
  have ht' : c'.stk .t4 = encNums (l :: psr) ++ .mk 3 :: c.stk .t4 := by
    rw [hs', hj₉ .t4 (by decide) (by decide), hj₈ .t4 (by decide) (by decide), ht₇,
      F6 .t4 (by decide), hj₅ .t4 (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), ht₃'', encNums_cons]
    simp
  have hw' : c'.stk .work = w := by
    rw [hs', hj₉ .work (by decide) (by decide), hj₈ .work (by decide) (by decide), hw₇]
  have hF' : Fr [.work, .t1, .t2, .t4, .heap, .cnt] c c' := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    obtain ⟨hiw, hi1, hi2, hi4, hih, hic⟩ := hi
    by_cases hl : i = .lst
    · subst hl
      rw [hs', hl₉, hj₇ .lst (by decide) (by decide), F6 .lst (by decide), hj₅ .lst (by decide)]
      simp only [Act.run]
      rw [update_of_ne (by decide)]
      exact F3 .lst (by decide)
    rw [e₉ i hi1 hl hiw hi4, F6 i (by simp [hiw, hih, hic]), hj₅ i hiw]
    simp only [Act.run]
    rw [update_of_ne hiw]
    exact F3 i (by simp [hiw, hi1, hi2, hi4, hih, hic])
  refine ⟨j + 1, h₁ ++ [⟨l, .nat, [cntBits j]⟩], l :: psr, by omega, hH',
    by rw [← List.append_assoc]; exact hB₆, by simp [hl₃], hR', hp', by rw [hs', ht₉'],
    by rw [hs', ht₉''], ht', hw', ?_, hF'⟩
  rw [hr', ofBits_cntBits, hnk]

theorem out_range {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym} {k : ℕ}
    {lk : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h) (hFB : F + 1 ≤ B) (h2F : 2 ≤ F)
    (hv : c.regs = Regs.empty) (hw : c.stk .work = envEnc [lk] ++ w)
    (rk : Rep h .nat k (ofBits lk)) (hlk : lk.length ≤ B + h.length) (hk : k + 1 ≤ F) {G : ℕ}
    (hG : 2 * k + 1 ≤ G) :
    PrimOut prog rangeCode c h w (.list .nat) (List.range k) B F G (k + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hlk
  obtain ⟨E', hE'⟩ : ∃ E', E' = B + h.length + k + 1 := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = B + h.length + 2 * k + 1 := ⟨_, rfl⟩
  have hw' : c.stk .work = bits lk ++ .nd :: w := by simpa [envEnc] using hw
  have e : k * (110 * E' + allocBound E' E' + 250 + 1) =
      k * (110 * E' + allocBound E' E' + 251) := by ring
  unfold rangeCode
  refine PrimOut.of_sat (T := k * (110 * E' + allocBound E' E' + 251) +
    k * (36 * U + allocBound (2 * U + 2) U + 72) + (fcE (encHeap h).length E + 26 * E +
      47 * E' + 2 * k + allocBound 0 (h.length + k) + 300))
    (Sat.seq_le (natTo_sat (by decide) (by decide) hH hB hv hw' rk hlk (by omega)) (by omega)
      fun c₁ ⟨hr₁, hw₁, F1, nk, hnk, hnkB, ht₁⟩ => Sat.act_seq (by omega) ?_)
  refine Sat.seq_le ((pushNum_sat (prog := prog) Stk.t1 (Act.run (.push .t4 (.mk 3)) c₁)
    []).mono (t' := 1) (by simp) fun _ h => h) (by omega) fun c₂ ⟨hr₂, ht₂, hj₂⟩ => ?_
  have ht₂' : c₂.stk .t2 = bits nk ++ .nd :: c.stk .t2 := by
    rw [hj₂ .t2 (by decide)]; simpa [Act.run] using ht₁
  refine Sat.seq_le (rangeTest_sat (E := E') (by rw [hr₂]; exact hr₁) ht₂ ht₂' (by simp)
    (by omega)) (by omega) fun c₃ ⟨hr₃, hs₃⟩ => ?_
  have I0 : RangeInv B F h c w k nk k c₃ := by
    refine ⟨0, [], [], by omega, ?_, by simpa using hB, rfl, List.Forall₂.nil, by simp, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    · rw [List.append_nil]
      exact hH.frame (by rw [hs₃, hj₂ .heap (by decide)]; simp [Act.run, F1 .heap (by decide)])
        (by rw [hs₃, hj₂ .scan (by decide)]; simp [Act.run, F1 .scan (by decide)])
        (by rw [hs₃, hj₂ .cnt (by decide)]; simp [Act.run, F1 .cnt (by decide)])
    · rw [hs₃, ht₂]; simp [Act.run, F1 .t1 (by decide), cntBits]
    · rw [hs₃, ht₂']
    · rw [hs₃, hj₂ .t4 (by decide)]; simp [Act.run, F1 .t4 (by decide)]
    · rw [hs₃, hj₂ .work (by decide)]; simp [Act.run, hw₁]
    · rw [hr₃, hnk]; rfl
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [hs₃, hj₂ i hi.2.1]
      simp only [Act.run]
      rw [update_of_ne hi.2.2.2.1]
      exact F1 i (by simp [hi.1, hi.2.2.1])
  have hloop := Sat.loop (prog := prog) (b := .is 0 (some (.bit true))) (x := rangeBody)
    (t := 110 * E' + allocBound E' E' + 250) (I := RangeInv B F h c w k nk)
    (Q := RangeInv B F h c w k nk 0)
    (fun m c₄ hI => range_step hnk hnkB hFB hk hE' m c₄ hI)
    (fun c₄ hI => by
      have hI' := hI
      obtain ⟨j, -, -, hjm, -, -, -, -, -, -, -, -, -, hr₄, -⟩ := hI'
      exact ⟨by simp [Cond.eval, hr₄, show j = k by omega], hI⟩)
  refine Sat.seq_le (hloop k c₃ I0) (by omega) fun c₄ hI₄ => Sat.act_seq (by omega) ?_
  obtain ⟨j, h₁, psr, hjm, hH₄, hB₄, hl₄, hR₄, hp₄, ht₄, ht₄', ht₄'', hw₄, hr₄, F4⟩ := hI₄
  obtain rfl : j = k := by omega
  have hck := length_cntBits_le j
  have hv₅ : (Act.run (.set 0 none) c₄).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₄, empty_eq_rv, update_rv_zero]
  refine Sat.seq_le (dropNum_sat (l := cntBits j) (rest := c.stk .t1) hv₅
    (by simpa [Act.run] using ht₄)) (by omega) fun c₅ ⟨hr₅, ht₅, hj₅⟩ => ?_
  refine Sat.seq_le (dropNum_sat (l := nk) (rest := c.stk .t2) hr₅
    (by rw [hj₅ .t2 (by decide)]; simpa [Act.run] using ht₄')) (by omega)
    fun c₆ ⟨hr₆, ht₆, hj₆⟩ => ?_
  have F6 : Fr [.work, .t1, .t2, .t4, .heap, .cnt] c c₆ := fun i hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hj₆ i hi.2.2.1, hj₅ i hi.2.1]
    exact F4 i (by simp [hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, hi.2.2.2.2.1, hi.2.2.2.2.2])
  have hH₆ : HeapAt (h ++ h₁) c₆ :=
    hH₄.fr (S := [.t1, .t2]) (fun i hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [hj₆ i hi.2, hj₅ i hi.1]; rfl) (by decide) (by decide) (by decide)
  have hlen : (h ++ h₁).length = h.length + j := by simp [hl₄]
  refine Sat.seq_le ((allocArgs_sat (prog := prog) .nil (ls := []) (w := w) hH₆ hB₄
    (by omega) hr₆ (by simp [hj₆ .work (by decide), hj₅ .work (by decide), Act.run, hw₄])
    (by simp) (by simp)).mono (t' := allocBound 0 (h.length + j) + 9)
    (by simp [encFields, hlen]) fun _ h => h) (by omega)
    fun c₇ ⟨hr₇, lnil, hH₇, hB₇, hc₇, hl₇, hw₇, F7⟩ => ?_
  have ht₇ : c₇.stk .t4 = encNums psr ++ .mk 3 :: c.stk .t4 := by
    rw [F7 .t4 (by decide), hj₆ .t4 (by decide), hj₅ .t4 (by decide)]
    simpa [Act.run] using ht₄''
  have hbl := buildListB_sat (prog := prog) (s := .t4) (by decide) (by omega) h2F hH₇ hB₇ hr₇
    ht₇ hw₇ (RepList.mono hR₄) (Rep.nil hc₇) (fun p hp => by
      have := hp₄ p hp; simp at this ⊢; omega) (by simp at hl₇ ⊢; omega)
  have hpl : psr.length = j := by rw [← hR₄.length_eq]; simp
  have hU' : B + (h ++ h₁ ++ [Cell.mk lnil .nil []]).length + psr.length = U := by
    simp [hl₄, hpl]; omega
  rw [hU', hpl] at hbl
  refine (hbl.mono (by omega) fun c' ⟨hr', ht', h'', q', hH', hB', hlh, hq', hrq, hw', F8⟩ =>
    ⟨h₁ ++ [⟨lnil, .nil, []⟩] ++ h'', q', by simpa using hH', by simpa using hB', hr',
      by simpa using hrq, by simpa using hq', hw', ?_, ?_, ?_⟩)
  · have F : Fr [.t1, .t2, .t4, .heap, .cnt, .work] c c' :=
      ((F6.trans F7).trans F8).mono (by decide)
    have e₁ : c'.stk .t1 = c.stk .t1 := by rw [F8 .t1 (by decide), F7 .t1 (by decide), hj₆ .t1
      (by decide), ht₅]
    have e₂ : c'.stk .t2 = c.stk .t2 := by rw [F8 .t2 (by decide), F7 .t2 (by decide), ht₆]
    exact ((F.restore e₁).restore e₂).restore ht'
  · simp [hl₄, hlh]; omega
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h (h₁ ++ [⟨lnil, .nil, []⟩] ++ h'')
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ (h₁ ++ [⟨lnil, .nil, []⟩] ++ h''))).length :=
      ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hUM : U ≤ M := by
      simp only [List.length_append, List.length_singleton, hlh, hl₄] at s3
      omega
    have hMM := Nat.zero_le (M * M)
    have hA1 := allocBound_mono (a := E') (b := M * M + 3 * M + 2) (m := E') (n := M)
      (by omega) (by omega)
    have hA2 := allocBound_mono (a := 2 * U + 2) (b := M * M + 3 * M + 2) (m := U) (n := M)
      (by omega) hUM
    have hA3 := allocBound_mono (a := 0) (b := M * M + 3 * M + 2) (m := h.length + j) (n := M)
      (by omega) (by omega)
    have hf := fcE_mono s2 (by omega : E ≤ M)
    refine le_succ_mul1.trans (Nat.mul_le_mul_left _ ((primB_ge' M).trans'
      (le_trans ?_ (Nat.le_add_left _ _))))
    clear * - hA1 hA2 hA3 hf hUM hE hE' hU s1
    omega

/-! ### Array reads -/

/-- Sequencing where the second part's step bound depends on how the first part ended. -/
theorem PrimOut.seq {x y : Code Stk Sym Rg P} {c : Cfg Stk Sym Rg} {h : List Cell}
    {w : List Sym} {t : Ty} {v : t.denote} {B F G C T₁ : ℕ} {Q₁ : Cfg Stk Sym Rg → Prop}
    (h₁ : Sat prog x c T₁ Q₁)
    (h₂ : ∀ c₁, Q₁ c₁ → ∃ T₂, Sat prog y c₁ T₂ fun c' => ∃ h' l, HeapAt (h ++ h') c' ∧
      HeapBnd B F (h ++ h') ∧ c'.regs = Regs.empty ∧ Rep (h ++ h') t v (ofBits l) ∧
      l.length ≤ B + (h ++ h').length ∧ c'.stk .work = bits l ++ .nd :: w ∧
      Fr [.heap, .cnt, .work] c c' ∧ h'.length ≤ G ∧
      T₁ + T₂ + 1 ≤ C * primB (B + (encHeap (h ++ h')).length)) :
    PrimOut prog (.seq x y) c h w t v B F G C := by
  obtain ⟨c₁, n₁, e₁, hn₁, q₁⟩ := h₁
  obtain ⟨T₂, c', n₂, e₂, hn₂, h', l, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h₂ c₁ q₁
  exact ⟨c', _, h', l, .seq e₁ e₂, a1, a2, a3, a4, a5, a6, a7, a8, by omega⟩

/-- Cells for the default value of a type. -/
def allocDefault : Ty → Code Stk Sym Rg P
  | .unit => allocArgs .unit 0
  | .bool => allocArgs .ff 0
  | .nat => natLitCode 0
  | .prod a b => .seq (allocDefault a) (.seq (allocDefault b) (allocArgs .pair 2))
  | .list _ => allocArgs .nil 0
  | .array _ => allocArgs .arr 0
  | .option _ => allocArgs .none 0

theorem one_le_tySize (t : Ty) : 1 ≤ tySize t := by cases t <;> simp [tySize]

/-- The default value's cells: `tySize t` of them. -/
theorem allocDefault_sat {B F : ℕ} (h1B : 1 ≤ B) (h2F : 2 ≤ F) :
    ∀ (t : Ty) (h : List Cell) (c : Cfg Stk Sym Rg) (V : ℕ), HeapAt h c → HeapBnd B F h →
      c.regs = Regs.empty → B + h.length + tySize t ≤ V →
      Sat prog (allocDefault t) c (tySize t * (allocBound (2 * V + 2) V + 100 * V + 200))
        fun c' => c'.regs = Regs.empty ∧ ∃ h' l, HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
          h'.length = tySize t ∧ Rep (h ++ h') t t.default (ofBits l) ∧
          l.length ≤ h.length + h'.length ∧ c'.stk .work = bits l ++ .nd :: c.stk .work ∧
          Fr [.heap, .cnt, .work] c c'
  | .prod a b, h, c, V, hH, hB, hv, hV => by
    have ha := one_le_tySize a
    have hb := one_le_tySize b
    simp only [tySize] at hV
    have e : tySize (.prod a b) * (allocBound (2 * V + 2) V + 100 * V + 200) =
        tySize a * (allocBound (2 * V + 2) V + 100 * V + 200) +
        tySize b * (allocBound (2 * V + 2) V + 100 * V + 200) +
        (allocBound (2 * V + 2) V + 100 * V + 200) := by simp only [tySize]; ring
    rw [e]
    refine Sat.seq_le (allocDefault_sat h1B h2F a h c V hH hB hv (by omega)) (by omega)
      fun c₁ ⟨hr₁, h₁, la, hH₁, hB₁, hl₁, ra, hla, hw₁, F1⟩ => ?_
    refine Sat.seq_le (allocDefault_sat h1B h2F b (h ++ h₁) c₁ V hH₁ hB₁ hr₁ (by simp; omega))
      (by omega) fun c₂ ⟨hr₂, h₂, lb, hH₂, hB₂, hl₂, rb, hlb, hw₂, F2⟩ => ?_
    have hw₂' : c₂.stk .work = envEnc [la, lb] ++ c.stk .work := by
      rw [hw₂, hw₁]; simp [envEnc]
    have hls : ∀ l ∈ [la, lb], l.length ≤ B + (h ++ h₁ ++ h₂).length := by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      simp only [List.length_append] at hla hlb ⊢
      rcases hl with rfl | rfl <;> omega
    have hlsV : ∀ l ∈ [la, lb], l.length ≤ V := by
      intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      simp only [List.length_append] at hla hlb
      rcases hl with rfl | rfl <;> omega
    have hLf := length_encFields_le [la, lb] hlsV
    simp only [List.length_cons, List.length_nil] at hLf
    have hlenV : B + (h ++ h₁ ++ h₂).length ≤ V := by simp [hl₁, hl₂]; omega
    have hA := allocBound_mono (a := (encFields [la, lb]).length) (b := 2 * V + 2)
      (m := (h ++ h₁ ++ h₂).length) (n := V) (by omega) (by omega)
    have hb3 : 3 * ([la, lb].length * (12 * (B + (h ++ h₁ ++ h₂).length) + 20)) ≤
        72 * V + 120 := by
      simp only [List.length_cons, List.length_nil]; omega
    refine (allocArgs_sat (prog := prog) .pair (ls := [la, lb]) hH₂ hB₂ h1B hr₂ hw₂'
      (by simpa using h2F) hls).mono (by omega)
      fun c' ⟨hr', l, hH', hB', hc', hl', hw', F3⟩ => ⟨hr', h₁ ++ h₂ ++ [⟨l, .pair, [la, lb]⟩], l,
        by simpa using hH', by simpa using hB', by simp [hl₁, hl₂, tySize]; omega, ?_,
        by simp at hl' ⊢; omega, hw', ((F1.trans F2).trans F3).mono (by decide)⟩
    have r := Rep.pair (x := a.default) (y := b.default) hc'
      ((ra.mono (h' := h₂)).mono (h' := [⟨l, .pair, [la, lb]⟩]))
      (rb.mono (h' := [⟨l, .pair, [la, lb]⟩]))
    simpa [Ty.default, List.append_assoc] using r
  | .nat, h, c, V, hH, hB, hv, hV => by
    simp only [tySize] at hV ⊢
    simp only [allocDefault, natLitCode]
    refine Sat.act_seq (by omega) ?_
    have hH₁ : HeapAt h (Act.run (.push .work (.mk 2)) c) :=
      hH.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
    refine Sat.seq_le ((pushNum_sat (prog := prog) Stk.work (Act.run (.push .work (.mk 2)) c)
      (toBits 0)).mono (t' := 1) (by simp [toBits]) fun _ h => h) (by omega)
      fun c₂ ⟨hr₂, hw₂, hj₂⟩ => ?_
    have hH₂ : HeapAt h c₂ := hH₁.fr (fr1 hj₂) (by decide) (by decide) (by decide)
    have hw₂' : c₂.stk .work = encFields [[]] ++ .mk 2 :: c.stk .work := by
      rw [hw₂]; simp [Act.run, encFields, toBits]
    have hA := allocBound_mono (a := (encFields [[]]).length) (b := 2 * V + 2)
      (m := h.length) (n := V) (by simp [encFields]) (by omega)
    refine (allocB_sat .nat hH₂ hB h1B (by rw [hr₂]; exact hv) hw₂' (by simp; omega)
      (by simp)).mono (by omega) fun c' ⟨hr', l, hH', hB', hc', hl', hw', F'⟩ =>
        ⟨hr', [⟨l, .nat, [[]]⟩], l, hH', hB', rfl, by simpa [Ty.default] using Rep.nat hc',
          by simp; omega, hw', ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    rw [F' j (by simp [hj.1, hj.2.1, hj.2.2]), hj₂ j hj.2.2]
    simp [Act.run, update_of_ne hj.2.2]
  | .unit, h, c, V, hH, hB, hv, hV => alloc0_default .unit hH hB hv hV rfl (fun l hc => .unit hc)
  | .bool, h, c, V, hH, hB, hv, hV => alloc0_default .ff hH hB hv hV rfl
      (fun l hc => by simpa [Ty.default] using Rep.bool false hc)
  | .list a, h, c, V, hH, hB, hv, hV => alloc0_default .nil hH hB hv hV rfl (fun l hc => .nil hc)
  | .array a, h, c, V, hH, hB, hv, hV => alloc0_default .arr hH hB hv hV rfl
      (fun l hc => .arr hc (by simp [Ty.default]) fun i hi => by simp at hi)
  | .option a, h, c, V, hH, hB, hv, hV => alloc0_default .none hH hB hv hV rfl
      (fun l hc => .none hc)
where
  alloc0_default (tg : Tag) {t : Ty} {h : List Cell} {c : Cfg Stk Sym Rg} {V : ℕ}
      (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
      (hV : B + h.length + tySize t ≤ V) (ht : tySize t = 1)
      (hrep : ∀ l, CellAt (h ++ [⟨l, tg, []⟩]) (ofBits l) tg [] →
        Rep (h ++ [⟨l, tg, []⟩]) t t.default (ofBits l)) :
      Sat prog (allocArgs tg 0) c (tySize t * (allocBound (2 * V + 2) V + 100 * V + 200))
        fun c' => c'.regs = Regs.empty ∧ ∃ h' l, HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
          h'.length = tySize t ∧ Rep (h ++ h') t t.default (ofBits l) ∧
          l.length ≤ h.length + h'.length ∧ c'.stk .work = bits l ++ .nd :: c.stk .work ∧
          Fr [.heap, .cnt, .work] c c' := by
    have hA := allocBound_mono (a := 0) (b := 2 * V + 2) (m := h.length) (n := V) (by omega)
      (by omega)
    refine (allocArgs_sat (prog := prog) tg (ls := []) (w := c.stk .work) hH hB h1B hv
      (by simp) (by simp) (by simp)).mono (by simp [encFields, ht]; omega)
      fun c' ⟨hr', l, hH', hB', hc', hl', hw', F'⟩ =>
        ⟨hr', [⟨l, tg, []⟩], l, hH', hB', by simp [ht], hrep l hc', by simp; omega, hw', F'⟩

/-- The test of `arrayGet`: the top of `work` into register `0`, and the bit `i = 0` for the
index `i` on `t2` into register `1`. -/
def getTest : Code Stk Sym Rg P :=
  .seq (copyNum .t2 .t3 .t0) (.seq (pushNum [] .lst) (.seq (eqNum .t3 .lst .ptr .t0)
    (.seq (.act (.pop .ptr 1)) (.act (.peek .work 0)))))

theorem getTest_sat {c : Cfg Stk Sym Rg} {nb : List Bool} {r : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (ht : c.stk .t2 = bits nb ++ .nd :: r) (hE : nb.length ≤ E) :
    Sat prog getTest c (33 * E + 72) fun c' =>
      c'.regs = rv (c.stk .work).head? (some (.bit (decide (ofBits nb = 0)))) none none ∧
        c'.stk = c.stk := by
  unfold getTest
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hv ht) (by omega)
    fun c₁ ⟨hr₁, ht₁, hj₁⟩ => ?_
  refine Sat.seq_le ((pushNum_sat (prog := prog) Stk.lst c₁ []).mono (t' := 1) (by simp)
    fun _ h => h) (by omega) fun c₂ ⟨hr₂, hl₂, hj₂⟩ => ?_
  have ht₂ : c₂.stk .t3 = bits nb ++ .nd :: c.stk .t3 := by rw [hj₂ .t3 (by decide), ht₁]
  refine Sat.seq_le ((eqNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hr₂, hr₁]) ht₂ hl₂).mono (t' := 19 * nb.length + 34) (by simp)
    fun _ h => h) (by omega) fun c₃ ⟨hr₃, ht₃, hl₃, hp₃, hj₃⟩ =>
      Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_⟩)
  · have hs : c₃.stk .work = c.stk .work := by
      rw [hj₃ .work (by decide) (by decide) (by decide), hj₂ .work (by decide),
        hj₁ .work (by decide)]
    rw [empty_eq_rv] at hr₃
    simp only [Act.run, hr₃, hp₃, update_rv_one, update_rv_zero, List.head?_cons]
    rw [update_of_ne (by decide), hs]
    rfl
  · funext j
    simp only [Act.run]
    by_cases hjp : j = .ptr
    · subst hjp; rw [update_self, hp₃]; simp [hj₂ .ptr (by decide), hj₁ .ptr (by decide)]
    rw [update_of_ne hjp]
    by_cases h3 : j = .t3
    · subst h3; rw [ht₃]
    by_cases hl : j = .lst
    · subst hl; rw [hl₃, hj₁ .lst (by decide)]
    rw [hj₃ j h3 hl hjp, hj₂ j hl, hj₁ j h3]

/-- The body of the scan of `arrayGet`: drop a field, count the index down. -/
def getBody : Code Stk Sym Rg P :=
  .seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq (dropNum .work)
    (.seq (decNum .t2 .t3 .lst .t0) (.seq (moveNum2 .lst .t2 .t0) getTest))))

/-- The scan of `arrayGet`: the index onto `t2`, the array's fields onto `work`, then drop
fields while the index is positive and fields remain. -/
def getScan : Code Stk Sym Rg P :=
  .seq (natTo .t2) (.seq openTop (.seq (.act (.set 1 none)) (.seq getTest
    (.loop (.and (.not (.is 0 (some (.mk 0)))) (.is 1 (some (.bit false)))) getBody))))

/-- The end of `arrayGet`: past the fields, the default value; else the field on top. -/
def getFinish (a : Ty) : Code Stk Sym Rg P :=
  .ite (.is 0 (some (.mk 0)))
    (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq closeCell (.seq (dropNum .t2)
      (allocDefault a)))))
    (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .t1 .t0)
      (.seq (dropNum .t2) (.seq (countAll 0 .work) (.seq (dropNum .t2) (.seq closeCell
        (moveNum2 .t1 .work .t0))))))))

/-- An array read. -/
def arrayGetCode (a : Ty) : Code Stk Sym Rg P := .seq getScan (getFinish a)

/-- The state of the scan of `arrayGet` after `j` fields. -/
def GetInv (c : Cfg Stk Sym Rg) (w : List Sym) (fs : List (List Bool)) (I E j : ℕ)
    (c₃ : Cfg Stk Sym Rg) : Prop :=
  ∃ nb, ofBits nb = I - j ∧ nb.length ≤ E ∧ c₃.stk .t2 = bits nb ++ .nd :: c.stk .t2 ∧
    c₃.stk .work = encFields (fs.drop j) ++ .mk 0 :: w ∧
    c₃.regs = rv (c₃.stk .work).head? (some (.bit (decide (I - j = 0)))) none none ∧
    Fr [.work, .t2] c c₃

theorem get_step {c : Cfg Stk Sym Rg} {w : List Sym} {fs : List (List Bool)} {I E : ℕ}
    (hE1 : 1 ≤ E) (hfE : ∀ f ∈ fs, f.length ≤ E) (m : ℕ) (c₃ : Cfg Stk Sym Rg)
    (hI : ∃ j, j + (m + 1) = min I fs.length ∧ GetInv c w fs I E j c₃) :
    Cond.eval (.and (.not (.is 0 (some (.mk 0)))) (.is 1 (some (.bit false)))) c₃.regs = true ∧
      Sat prog getBody c₃ (70 * E + 200)
        (fun c₄ => ∃ j, j + m = min I fs.length ∧ GetInv c w fs I E j c₄) := by
  obtain ⟨j, hjm, nb, hnb, hnbE, ht₃, hw₃, hr₃, F3⟩ := hI
  have hjk : j < fs.length := by omega
  have hjI : j < I := by omega
  have hw₃' : c₃.stk .work = bits fs[j] ++ .nd :: (encFields (fs.drop (j + 1)) ++ .mk 0 :: w) := by
    rw [hw₃, List.drop_eq_getElem_cons hjk, encFields_cons]; simp
  have hfj := hfE _ (List.getElem_mem hjk)
  refine ⟨?_, ?_⟩
  · simp only [Cond.eval, hr₃, rv_zero, rv_one, hw₃']
    simp [head_bits_ne_mk, show I - j ≠ 0 by omega]
  unfold getBody
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have hv₄ : (Act.run (.set 1 none) (Act.run (.set 0 none) c₃)).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₃, update_rv_zero, update_rv_one, empty_eq_rv]
  refine Sat.seq_le (dropNum_sat (l := fs[j]) (rest := encFields (fs.drop (j + 1)) ++ .mk 0 :: w)
    hv₄ (by simpa [Act.run] using hw₃')) (by omega) fun c₅ ⟨hr₅, hw₅, hj₅⟩ => ?_
  refine Sat.seq_le (decNum_sat (xs := nb) (ra := c.stk .t2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hr₅
    (by rw [hj₅ .t2 (by decide)]; simpa [Act.run] using ht₃)) (by omega)
    fun c₆ ⟨hr₆, ht₆, hl₆, hj₆⟩ => ?_
  have hsub := length_subBits_le nb [true]
  simp only [List.length_singleton] at hsub
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₆ hl₆) (by omega)
    fun c₇ ⟨hr₇, hl₇, ht₇, hj₇⟩ => ?_
  refine (getTest_sat (E := E) hr₇ ht₇ (by omega)).mono (by omega)
    fun c₈ ⟨hr₈, hs₈⟩ => ⟨j + 1, by omega, subBits nb [true], ?_, by omega, ?_, ?_, ?_, ?_⟩
  · rw [ofBits_subBits, hnb]; simp; omega
  · rw [hs₈, ht₇, ht₆]
  · rw [hs₈, hj₇ .work (by decide) (by decide), hj₆ .work (by decide) (by decide), hw₅]
  · rw [hr₈, ofBits_subBits, hnb, hs₈]
    simp only [ofBits]
    congr 3
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hs₈]
    by_cases hl : i = .lst
    · subst hl
      rw [hl₇, hj₅ .lst (by decide)]
      exact F3 .lst (by decide)
    rw [hj₇ i hl hi.2, hj₆ i hi.2 hl, hj₅ i hi.1]
    exact F3 i (by simp [hi.1, hi.2])

theorem fcE_ge (M : ℕ) : 150 ≤ fcE M M := by unfold fcE lookupBound; omega

theorem allocBound_ge (a n : ℕ) : 300 ≤ allocBound a n := by unfold allocBound; omega

theorem out_arrayGet {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {arr : Array a.denote} {I : ℕ} {la li : List Bool} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hFB : F + 1 ≤ B) (h2F : 2 ≤ F) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [la, li] ++ w) (ra : Rep h (.array a) arr (ofBits la))
    (ri : Rep h .nat I (ofBits li)) (hla : la.length ≤ B + h.length)
    (hli : li.length ≤ B + h.length) (hty : tySize a ≤ B) {G : ℕ} (hG : tySize a ≤ G) :
    PrimOut prog (arrayGetCode a) c h w a (arr.getD I a.default) B F G 1 := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hla hli
  obtain ⟨fs, hc, hR⟩ := ra.arr_list
  have hlen : fs.length = arr.size := by rw [← hR.length_eq, Array.length_toList]
  have hfB := hB.field_lt hc
  have hfE : ∀ f ∈ fs, f.length ≤ E := fun f hf => by have := hfB f hf; omega
  have hkF : fs.length ≤ F := by
    obtain ⟨hp, -, hf⟩ := hc
    rw [← hf]; exact (hB _ hp).2.1
  have hw' : c.stk .work = bits li ++ .nd :: (bits la ++ .nd :: w) := by simpa [envEnc] using hw
  have e1 : min I fs.length * (70 * E + 200 + 1) ≤ fs.length * (70 * E + 201) :=
    Nat.mul_le_mul (Nat.min_le_right _ _) le_rfl
  refine PrimOut.seq (T₁ := 2 * fcE (encHeap h).length E + 69 * E + 160 +
    fs.length * (70 * E + 201)) (Q₁ := fun c₁ => ∃ j, j = min I fs.length ∧
      GetInv c w fs I E j c₁) ?_ ?_
  · unfold getScan
    refine Sat.seq_le (natTo_sat (by decide) (by decide) hH hB hv hw' ri hli (by omega))
      (by omega) fun c₁ ⟨hr₁, hw₁, F1, ni, hni, hniB, ht₁⟩ => ?_
    have hH₁ := hH.fr F1 (by decide) (by decide) (by decide)
    refine Sat.seq_le (openTop_sat (w := w) hH₁ hr₁ hw₁ hc hla) (by omega)
      fun c₂ ⟨hr₂, hw₂, F2⟩ => Sat.act_seq (by omega) ?_
    have hv₃ : (Act.run (.set 1 none) c₂).regs = Regs.empty := by
      simp only [Act.run]; rw [hr₂, update_rv_one, empty_eq_rv]
    have ht₃ : (Act.run (.set 1 none) c₂).stk .t2 = bits ni ++ .nd :: c.stk .t2 := by
      simp only [Act.run]; rw [F2 .t2 (by decide), ht₁]
    refine Sat.seq_le (getTest_sat (E := E) hv₃ ht₃ (by omega)) (by omega)
      fun c₃ ⟨hr₃, hs₃⟩ => ?_
    have hloop := Sat.loop (prog := prog)
      (b := .and (.not (.is 0 (some (.mk 0)))) (.is 1 (some (.bit false)))) (x := getBody)
      (t := 70 * E + 200)
      (I := fun m c₄ => ∃ j, j + m = min I fs.length ∧ GetInv c w fs I E j c₄)
      (Q := fun c₄ => ∃ j, j = min I fs.length ∧ GetInv c w fs I E j c₄)
      (fun m c₄ hI => get_step (by omega) hfE m c₄ hI)
      (fun c₄ ⟨j, hj, hG'⟩ => by
        refine ⟨?_, j, by omega, hG'⟩
        obtain ⟨nb, hnb, -, -, hw₄, hr₄, -⟩ := hG'
        by_cases hjk : j = fs.length
        · rw [hjk, List.drop_length] at hw₄
          simp [Cond.eval, hr₄, hw₄, encFields]
        · have : I - j = 0 := by omega
          simp [Cond.eval, hr₄, this])
    refine (hloop (min I fs.length) c₃ ⟨0, by omega, ni, by rw [hni]; simp, by omega, ?_, ?_,
      ?_, ?_⟩).mono (by omega) fun _ h => h
    · rw [hs₃, ht₃]
    · rw [hs₃]; simp [Act.run, hw₂]
    · rw [hr₃, hs₃, hni]; simp
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      rw [hs₃]
      simp only [Act.run]
      rw [F2 i (by simp [hi.1])]
      exact F1 i (by simp [hi.1, hi.2])
  · rintro c₁ ⟨j, hj, nb, hnb, hnbE, ht₁, hw₁, hr₁, F1⟩
    by_cases hIk : I < fs.length
    · -- in bounds: the field at `I`
      have hjI : j = I := by omega
      subst hjI
      have hw₁' : c₁.stk .work =
          bits fs[j] ++ .nd :: (encFields (fs.drop (j + 1)) ++ .mk 0 :: w) := by
        rw [hw₁, List.drop_eq_getElem_cons hIk, encFields_cons]; simp
      have hfj := hfE _ (List.getElem_mem hIk)
      refine ⟨fs.length * (2 * E + 35 * fs.length + 150) + 30 * E + 2 * fs.length + 100, ?_⟩
      refine Sat.ite_false_le (by simp [Cond.eval, hr₁, hw₁', head_bits_ne_mk]) (by omega)
        (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
      have hv₂ : (Act.run (.set 1 none) (Act.run (.set 0 none) c₁)).regs = Regs.empty := by
        simp only [Act.run]; rw [hr₁, update_rv_zero, update_rv_one, empty_eq_rv]
      refine Sat.seq_le (moveNum2_sat (l := fs[j]) (rest := encFields (fs.drop (j + 1)) ++
        .mk 0 :: w) (by decide) (by decide) (by decide) hv₂ (by simpa [Act.run] using hw₁'))
        (by omega) fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => ?_
      refine Sat.seq_le (dropNum_sat (l := nb) (rest := c.stk .t2) hr₃
        (by rw [hj₃ .t2 (by decide) (by decide)]; simpa [Act.run] using ht₁)) (by omega)
        fun c₄ ⟨hr₄, ht₄, hj₄⟩ => ?_
      have hca := countAll_sat (prog := prog) (i := 0) (a := .work) (E := E) (c := c₄)
        (ns := fs.drop (j + 1)) (rest := w) (by decide) hr₄
        (by rw [hj₄ .work (by decide), hw₃, encFields_eq_encNums])
        (fun l hl => hfE l (List.mem_of_mem_drop hl))
      have hr' : (fs.drop (j + 1)).length ≤ fs.length := by simp
      have hm : (fs.drop (j + 1)).length * (2 * E + 35 * (fs.drop (j + 1)).length + 150) ≤
          fs.length * (2 * E + 35 * fs.length + 150) := Nat.mul_le_mul hr' (by omega)
      refine Sat.seq_le hca (by omega) fun c₅ ⟨hr₅, hw₅, ht₅, F5⟩ => ?_
      have hcnt := length_cntBits_le (fs.drop (j + 1)).length
      refine Sat.seq_le (dropNum_sat (l := cntBits (fs.drop (j + 1)).length) (rest := c.stk .t2)
        hr₅ (by rw [ht₅, ht₄])) (by omega) fun c₆ ⟨hr₆, ht₆, hj₆⟩ => ?_
      refine Sat.seq_le (closeCell_sat (r := none) (w := w) (by rw [hr₆, empty_eq_rv])
        (by rw [hj₆ .work (by decide), hw₅])) (by omega) fun c₇ ⟨hr₇, hw₇, hj₇⟩ => ?_
      have ht₇ : c₇.stk .t1 = bits fs[j] ++ .nd :: c.stk .t1 := by
        rw [hj₇ .t1 (by decide), hj₆ .t1 (by decide), F5 .t1 (by decide), hj₄ .t1 (by decide),
          ht₃]
        simp only [Act.run]
        rw [F1 .t1 (by decide)]
      refine (moveNum2_sat (by decide) (by decide) (by decide) (by rw [hr₇, empty_eq_rv]) ht₇).mono
        (by omega) fun c' ⟨hr', ht', hw', hj'⟩ => ?_
      have hF' : Fr [.work] c c' := by
        intro i hi
        simp only [List.mem_singleton] at hi
        by_cases h1 : i = .t1
        · subst h1; exact ht'
        by_cases h2 : i = .t2
        · subst h2; rw [hj' .t2 (by decide) (by decide), hj₇ .t2 (by decide), ht₆]
        rw [hj' i h1 hi, hj₇ i hi, hj₆ i h2, F5 i (by simp [hi, h2]), hj₄ i h2, hj₃ i hi h1]
        simp only [Act.run]
        exact F1 i (by simp [hi, h2])
      have hrep : Rep (h ++ []) a (arr.getD j a.default) (ofBits fs[j]) := by
        have r := hR.get (by simpa [hlen] using hIk) hIk
        simp only [List.get_eq_getElem, Array.getElem_toList] at r
        rw [List.append_nil, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
        exact r
      refine ⟨[], fs[j], by simpa using hH.fr hF' (by decide) (by decide) (by decide),
        by simpa using hB, hr', hrep, by simp; omega, by rw [hw', hw₇], hF'.mono (by simp),
        by simp, ?_⟩
      obtain ⟨s1, s2, -⟩ := sizes_le B h []
      obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [])).length := ⟨_, rfl⟩
      rw [← hM] at s1 s2 ⊢
      have hkM : fs.length ≤ M := by omega
      have hEM : E ≤ M := by omega
      have hf := fcE_mono s2 hEM
      have hA := allocBound_ge (M * M + 3 * M + 2) M
      have hf150 := fcE_ge M
      have m1 : fs.length * (70 * E + 201) ≤
          M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) :=
        Nat.mul_le_mul hkM (by omega)
      have m2 : fs.length * (2 * E + 35 * fs.length + 150) ≤
          M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) :=
        Nat.mul_le_mul hkM (by omega)
      refine le_mul_primB le_rfl ((primB_ge' M).trans' ?_)
      clear * - hf hA hf150 m1 m2 hkM hEM
      omega
    · -- past the fields: the default value
      have hjk : j = fs.length := by omega
      subst hjk
      have hw₁' : c₁.stk .work = .mk 0 :: w := by
        rw [hw₁, List.drop_length]; simp [encFields]
      obtain ⟨V, hV⟩ : ∃ V, V = B + h.length + tySize a := ⟨_, rfl⟩
      refine ⟨2 * E + 30 + tySize a * (allocBound (2 * V + 2) V + 100 * V + 200), ?_⟩
      refine Sat.ite_true_le (by simp [Cond.eval, hr₁, hw₁']) (by omega)
        (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
      refine Sat.seq_le (closeCell_sat (r := none) (w := w) (by
        simp only [Act.run]; rw [hr₁, update_rv_zero, update_rv_one])
        (by simpa [Act.run] using hw₁')) (by omega) fun c₃ ⟨hr₃, hw₃, hj₃⟩ => ?_
      refine Sat.seq_le (dropNum_sat (l := nb) (rest := c.stk .t2) (by rw [hr₃, empty_eq_rv])
        (by rw [hj₃ .t2 (by decide)]; simpa [Act.run] using ht₁)) (by omega)
        fun c₄ ⟨hr₄, ht₄, hj₄⟩ => ?_
      have F4 : Fr [.work] c c₄ := by
        intro i hi
        simp only [List.mem_singleton] at hi
        by_cases h2 : i = .t2
        · subst h2; exact ht₄
        rw [hj₄ i h2, hj₃ i hi]
        simp only [Act.run]
        exact F1 i (by simp [hi, h2])
      have hH₄ := hH.fr F4 (by decide) (by decide) (by decide)
      refine (allocDefault_sat (by omega) h2F a h c₄ V hH₄ hB hr₄ (by omega)).mono (by omega)
        fun c' ⟨hr', h', l, hH', hB', hl', hrep, hll, hw', F'⟩ => ⟨h', l, hH', hB', hr', ?_,
          by simp; omega, by rw [hw', hj₄ .work (by decide), hw₃], (F4.trans F').mono (by simp),
          by omega, ?_⟩
      · have : arr.getD I a.default = a.default := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]; rfl
        rw [this]; exact hrep
      · obtain ⟨s1, s2, s3⟩ := sizes_le B h h'
        obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ h')).length := ⟨_, rfl⟩
        rw [← hM] at s1 s2 ⊢
        simp only [List.length_append, hl'] at s3
        have hkM : fs.length ≤ M := by omega
        have hEM : E ≤ M := by omega
        have hVM : V ≤ M := by omega
        have htM : tySize a ≤ M := by omega
        have hf := fcE_mono s2 hEM
        have hA := allocBound_ge (M * M + 3 * M + 2) M
        have hA2 := allocBound_mono (a := 2 * V + 2) (b := M * M + 3 * M + 2) (m := V) (n := M)
          (by have := Nat.zero_le (M * M); omega) hVM
        have hf150 := fcE_ge M
        have m1 : fs.length * (70 * E + 201) ≤
            M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) :=
          Nat.mul_le_mul hkM (by omega)
        have m2 : tySize a * (allocBound (2 * V + 2) V + 100 * V + 200) ≤
            M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) :=
          Nat.mul_le_mul htM (by omega)
        refine le_mul_primB le_rfl ((primB_ge' M).trans' ?_)
        clear * - hf hA hf150 m1 m2 hkM hEM
        omega

/-! ### Array writes -/

/-- The test of the scan of `arrayUpdate`: the top of `work` into register `0`, and the bit
`i = 0` for the index `i` on `t3` into register `1`. -/
def updTest : Code Stk Sym Rg P :=
  .seq (copyNum .t3 .t1 .t0) (.seq (pushNum [] .ptr) (.seq (eqNum .t1 .ptr .lst .t0)
    (.seq (.act (.pop .lst 1)) (.act (.peek .work 0)))))

theorem updTest_sat {c : Cfg Stk Sym Rg} {nb : List Bool} {r : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (ht : c.stk .t3 = bits nb ++ .nd :: r) (hE : nb.length ≤ E) :
    Sat prog updTest c (33 * E + 72) fun c' =>
      c'.regs = rv (c.stk .work).head? (some (.bit (decide (ofBits nb = 0)))) none none ∧
        c'.stk = c.stk := by
  unfold updTest
  refine Sat.seq_le (copyNum_sat (by decide) (by decide) (by decide) hv ht) (by omega)
    fun c₁ ⟨hr₁, ht₁, hj₁⟩ => ?_
  refine Sat.seq_le ((pushNum_sat (prog := prog) Stk.ptr c₁ []).mono (t' := 1) (by simp)
    fun _ h => h) (by omega) fun c₂ ⟨hr₂, hp₂, hj₂⟩ => ?_
  have ht₂ : c₂.stk .t1 = bits nb ++ .nd :: c.stk .t1 := by rw [hj₂ .t1 (by decide), ht₁]
  refine Sat.seq_le ((eqNum_sat (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [hr₂, hr₁]) ht₂ hp₂).mono (t' := 19 * nb.length + 34) (by simp)
    fun _ h => h) (by omega) fun c₃ ⟨hr₃, ht₃, hp₃, hl₃, hj₃⟩ =>
      Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_⟩)
  · have hs : c₃.stk .work = c.stk .work := by
      rw [hj₃ .work (by decide) (by decide) (by decide), hj₂ .work (by decide),
        hj₁ .work (by decide)]
    rw [empty_eq_rv] at hr₃
    simp only [Act.run, hr₃, hl₃, update_rv_one, update_rv_zero, List.head?_cons]
    rw [update_of_ne (by decide), hs]
    rfl
  · funext j
    simp only [Act.run]
    by_cases hjl : j = .lst
    · subst hjl; rw [update_self, hl₃]; simp [hj₂ .lst (by decide), hj₁ .lst (by decide)]
    rw [update_of_ne hjl]
    by_cases h1 : j = .t1
    · subst h1; rw [ht₃]
    by_cases hp : j = .ptr
    · subst hp; rw [hp₃, hj₁ .ptr (by decide)]
    rw [hj₃ j h1 hp hjl, hj₂ j hp, hj₁ j h1]

/-- The body of the scan of `arrayUpdate`: move a field onto `t4`, count the index down. -/
def updBody : Code Stk Sym Rg P :=
  .seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .t4 .t0)
    (.seq (decNum .t3 .t1 .ptr .t0) (.seq (moveNum2 .ptr .t3 .t0) updTest))))

/-- The state of the scan of `arrayUpdate` after `j` fields. -/
def UpdInv (c : Cfg Stk Sym Rg) (w : List Sym) (fs : List (List Bool)) (I E j : ℕ)
    (r₃ : List Sym) (c₃ : Cfg Stk Sym Rg) : Prop :=
  ∃ nb, ofBits nb = I - j ∧ nb.length ≤ E ∧ c₃.stk .t3 = bits nb ++ .nd :: r₃ ∧
    c₃.stk .work = encFields (fs.drop j) ++ .mk 2 :: w ∧
    c₃.stk .t4 = encNums (fs.take j).reverse ++ .mk 3 :: c.stk .t4 ∧
    c₃.regs = rv (c₃.stk .work).head? (some (.bit (decide (I - j = 0)))) none none ∧
    Fr [.work, .t3, .t4] c c₃

theorem upd_step {c : Cfg Stk Sym Rg} {w : List Sym} {fs : List (List Bool)} {I E : ℕ}
    {r₃ : List Sym} (hE1 : 1 ≤ E) (hfE : ∀ f ∈ fs, f.length ≤ E) (m : ℕ) (c₃ : Cfg Stk Sym Rg)
    (hI : ∃ j, j + (m + 1) = min I fs.length ∧ UpdInv c w fs I E j r₃ c₃) :
    Cond.eval (.and (.not (.is 0 (some (.mk 2)))) (.is 1 (some (.bit false)))) c₃.regs = true ∧
      Sat prog updBody c₃ (80 * E + 200)
        (fun c₄ => ∃ j, j + m = min I fs.length ∧ UpdInv c w fs I E j r₃ c₄) := by
  obtain ⟨j, hjm, nb, hnb, hnbE, ht₃, hw₃, h4₃, hr₃, F3⟩ := hI
  have hjk : j < fs.length := by omega
  have hjI : j < I := by omega
  have hw₃' : c₃.stk .work = bits fs[j] ++ .nd :: (encFields (fs.drop (j + 1)) ++ .mk 2 :: w) := by
    rw [hw₃, List.drop_eq_getElem_cons hjk, encFields_cons]; simp
  have hfj := hfE _ (List.getElem_mem hjk)
  refine ⟨?_, ?_⟩
  · simp only [Cond.eval, hr₃, rv_zero, rv_one, hw₃']
    simp [head_bits_ne_mk, show I - j ≠ 0 by omega]
  unfold updBody
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have hv₄ : (Act.run (.set 1 none) (Act.run (.set 0 none) c₃)).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₃, update_rv_zero, update_rv_one, empty_eq_rv]
  refine Sat.seq_le (moveNum2_sat (l := fs[j]) (rest := encFields (fs.drop (j + 1)) ++ .mk 2 :: w)
    (by decide) (by decide) (by decide) hv₄ (by simpa [Act.run] using hw₃')) (by omega)
    fun c₅ ⟨hr₅, hw₅, h4₅, hj₅⟩ => ?_
  refine Sat.seq_le (decNum_sat (xs := nb) (ra := r₃) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hr₅
    (by rw [hj₅ .t3 (by decide) (by decide)]; simpa [Act.run] using ht₃)) (by omega)
    fun c₆ ⟨hr₆, ht₆, hp₆, hj₆⟩ => ?_
  have hsub := length_subBits_le nb [true]
  simp only [List.length_singleton] at hsub
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₆ hp₆) (by omega)
    fun c₇ ⟨hr₇, hp₇, ht₇, hj₇⟩ => ?_
  refine (updTest_sat (E := E) hr₇ ht₇ (by omega)).mono (by omega)
    fun c₈ ⟨hr₈, hs₈⟩ => ⟨j + 1, by omega, subBits nb [true], ?_, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ofBits_subBits, hnb]; simp; omega
  · rw [hs₈, ht₇, ht₆]
  · rw [hs₈, hj₇ .work (by decide) (by decide), hj₆ .work (by decide) (by decide), hw₅]
  · rw [hs₈, hj₇ .t4 (by decide) (by decide), hj₆ .t4 (by decide) (by decide), h4₅]
    simp only [Act.run]
    have e : (fs.take (j + 1)).reverse = fs[j] :: (fs.take j).reverse := by
      rw [List.take_succ_eq_append_getElem hjk]; simp
    rw [h4₃, e, encNums_cons]
    simp
  · rw [hr₈, ofBits_subBits, hnb, hs₈]
    simp only [ofBits]
    congr 3
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hs₈]
    by_cases hp : i = .ptr
    · subst hp
      rw [hp₇, hj₅ .ptr (by decide) (by decide)]
      exact F3 .ptr (by decide)
    by_cases h1 : i = .t1
    · subst h1
      rw [hj₇ .t1 (by decide) (by decide), hj₆ .t1 (by decide) (by decide),
        hj₅ .t1 (by decide) (by decide)]
      exact F3 .t1 (by decide)
    rw [hj₇ i hp hi.2.1, hj₆ i hi.2.1 hp, hj₅ i hi.1 hi.2.2]
    exact F3 i (by simp [hi.1, hi.2.1, hi.2.2])

/-- The end of `setAt`: move the fields back from `t4`, drop the marker and the index. -/
def setTail : Code Stk Sym Rg P :=
  .seq (moveAll 3 .t4 .work) (.seq (.act (.pop .t4 0)) (.seq (.act (.set 0 none)) (dropNum .t3)))

theorem setTail_sat {c₀ c : Cfg Stk Sym Rg} {ps : List (List Bool)} {nb : List Bool}
    {r₃ : List Sym} {E : ℕ} (hv : c.regs = Regs.empty)
    (h4 : c.stk .t4 = encNums ps.reverse ++ .mk 3 :: c₀.stk .t4)
    (h3 : c.stk .t3 = bits nb ++ .nd :: r₃) (hps : ∀ p ∈ ps, p.length ≤ E)
    (hnb : nb.length ≤ E) :
    Sat prog setTail c (ps.length * (12 * E + 24) + 2 * E + 20) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = encNums ps ++ c.stk .work ∧
        c'.stk .t4 = c₀.stk .t4 ∧ c'.stk .t3 = r₃ ∧ Fr [.work, .t4, .t3] c c' := by
  unfold setTail
  have hma := moveAll_sat (prog := prog) (i := 3) (a := .t4) (b := .work) (E := E) (by decide)
    (by decide) (by decide) hv h4 (fun p hp => hps p (List.mem_reverse.1 hp))
  rw [List.length_reverse, List.reverse_reverse] at hma
  refine Sat.seq_le hma (by omega) fun c₁ ⟨hr₁, h4₁, hw₁, F1⟩ =>
    Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  refine (dropNum_sat (l := nb) (rest := r₃) (by simp only [Act.run]; rw [hr₁, empty_eq_rv,
    update_rv_zero, update_rv_zero]) (by
      simp only [Act.run]; rw [update_of_ne (by decide), F1 .t3 (by decide), h3])).mono
    (by omega) fun c' ⟨hr', h3', hj'⟩ => ⟨hr', ?_, ?_, h3', ?_⟩
  · rw [hj' .work (by decide)]; simpa [Act.run] using hw₁
  · rw [hj' .t4 (by decide)]; simp [Act.run, h4₁]
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hj' i hi.2.2]
    simp only [Act.run]
    rw [update_of_ne hi.2.1, F1 i (by simp [hi.1, hi.2.1])]

/-- Write the pointer on `t2` into the field, at the index on `t3`, of the fields above `mk 2`
on `work` (no change past the fields). -/
def setAt : Code Stk Sym Rg P :=
  .seq (.act (.push .t4 (.mk 3))) (.seq updTest
    (.seq (.loop (.and (.not (.is 0 (some (.mk 2)))) (.is 1 (some (.bit false)))) updBody)
      (.seq (.ite (.is 0 (some (.mk 2)))
          (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (dropNum .t2)))
          (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq (dropNum .work)
            (moveNum2 .t2 .work .t0)))))
        setTail)))

theorem setAt_sat {c : Cfg Stk Sym Rg} {fs : List (List Bool)} {w : List Sym}
    {ni lv : List Bool} {r₂ r₃ : List Sym} {E : ℕ} (hE1 : 1 ≤ E) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = encFields fs ++ .mk 2 :: w) (h₂ : c.stk .t2 = bits lv ++ .nd :: r₂)
    (h₃ : c.stk .t3 = bits ni ++ .nd :: r₃) (hfE : ∀ f ∈ fs, f.length ≤ E)
    (hlv : lv.length ≤ E) (hni : ni.length ≤ E) :
    Sat prog setAt c (fs.length * (92 * E + 225) + 60 * E + 200) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = encFields (fs.set (ofBits ni) lv) ++ .mk 2 :: w ∧
        c'.stk .t2 = r₂ ∧ c'.stk .t3 = r₃ ∧ Fr [.work, .t2, .t3] c c' := by
  obtain ⟨I, hI⟩ : ∃ I, I = ofBits ni := ⟨_, rfl⟩
  rw [← hI]
  have e1 : min I fs.length * (80 * E + 200 + 1) ≤ fs.length * (80 * E + 201) :=
    Nat.mul_le_mul (Nat.min_le_right _ _) le_rfl
  have e2 : fs.length * (80 * E + 201) + fs.length * (12 * E + 24) =
      fs.length * (92 * E + 225) := by ring
  unfold setAt
  refine Sat.act_seq (by omega) ?_
  refine Sat.seq_le (updTest_sat (E := E) (r := r₃) hv (by simpa [Act.run] using h₃) hni)
    (by omega) fun c₁ ⟨hr₁, hs₁⟩ => ?_
  have hloop := Sat.loop (prog := prog)
    (b := .and (.not (.is 0 (some (.mk 2)))) (.is 1 (some (.bit false)))) (x := updBody)
    (t := 80 * E + 200)
    (I := fun m c₄ => ∃ j, j + m = min I fs.length ∧ UpdInv c w fs I E j r₃ c₄)
    (Q := fun c₄ => ∃ j, j = min I fs.length ∧ UpdInv c w fs I E j r₃ c₄)
    (fun m c₄ hI' => upd_step hE1 hfE m c₄ hI')
    (fun c₄ ⟨j, hj, hU⟩ => by
      refine ⟨?_, j, by omega, hU⟩
      obtain ⟨nb, hnb, -, -, hw₄, -, hr₄, -⟩ := hU
      by_cases hjk : j = fs.length
      · rw [hjk, List.drop_length] at hw₄
        simp [Cond.eval, hr₄, hw₄, encFields]
      · have : I - j = 0 := by omega
        simp [Cond.eval, hr₄, this])
  refine Sat.seq_le (hloop (min I fs.length) c₁ ⟨0, by omega, ni, by rw [hI]; simp, hni, ?_, ?_,
    ?_, ?_, ?_⟩) (by omega) fun c₂ ⟨j, hj, nb, hnb, hnbE, ht₂, hw₂, h4₂, hr₂, F2⟩ => ?_
  · rw [hs₁]; simpa [Act.run] using h₃
  · rw [hs₁]; simpa [Act.run] using hw
  · rw [hs₁]; simp [Act.run]
  · rw [hr₁, hs₁, hI]; simp
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [hs₁]
    simp [Act.run, update_of_ne hi.2.2]
  have hnbE' : nb.length ≤ E := hnbE
  have hps : ∀ p ∈ fs.take j, p.length ≤ E := fun p hp => hfE p (List.mem_of_mem_take hp)
  have hpl : (fs.take j).length ≤ fs.length := by simp
  have hm : (fs.take j).length * (12 * E + 24) ≤ fs.length * (12 * E + 24) :=
    Nat.mul_le_mul hpl le_rfl
  have F2' : Fr [.work, .t3, .t4] c c₂ := F2
  by_cases hIk : I < fs.length
  · -- the field at `I` is replaced
    have hjI : j = I := by omega
    subst hjI
    have hw₂' : c₂.stk .work =
        bits fs[j] ++ .nd :: (encFields (fs.drop (j + 1)) ++ .mk 2 :: w) := by
      rw [hw₂, List.drop_eq_getElem_cons hIk, encFields_cons]; simp
    have hfj := hfE _ (List.getElem_mem hIk)
    have hbr : Sat prog (.ite (.is 0 (some (.mk 2)))
        (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (dropNum .t2)))
        (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq (dropNum .work)
          (moveNum2 .t2 .work .t0))))) c₂ (14 * E + 40) fun c' => c'.regs = Regs.empty ∧
        c'.stk .work = bits lv ++ .nd :: (encFields (fs.drop (j + 1)) ++ .mk 2 :: w) ∧
        c'.stk .t2 = r₂ ∧ c'.stk .t4 = c₂.stk .t4 ∧ c'.stk .t3 = c₂.stk .t3 ∧
        Fr [.work, .t2] c₂ c' := by
      refine Sat.ite_false_le (by simp [Cond.eval, hr₂, hw₂', head_bits_ne_mk]) (by omega)
        (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
      have hv₃ : (Act.run (.set 1 none) (Act.run (.set 0 none) c₂)).regs = Regs.empty := by
        simp only [Act.run]; rw [hr₂, update_rv_zero, update_rv_one, empty_eq_rv]
      refine Sat.seq_le (dropNum_sat (l := fs[j]) (rest := encFields (fs.drop (j + 1)) ++
        .mk 2 :: w) hv₃ (by simpa [Act.run] using hw₂')) (by omega)
        fun c₄ ⟨hr₄, hw₄, hj₄⟩ => ?_
      have h2₄ : c₄.stk .t2 = bits lv ++ .nd :: r₂ := by
        rw [hj₄ .t2 (by decide)]
        simp only [Act.run]
        rw [F2 .t2 (by decide), h₂]
      refine (moveNum2_sat (by decide) (by decide) (by decide) hr₄ h2₄).mono (by omega)
        fun c' ⟨hr', h2', hw', hj'⟩ => ⟨hr', by rw [hw', hw₄], h2', ?_, ?_, ?_⟩
      · rw [hj' .t4 (by decide) (by decide), hj₄ .t4 (by decide)]; rfl
      · rw [hj' .t3 (by decide) (by decide), hj₄ .t3 (by decide)]; rfl
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        rw [hj' i hi.2 hi.1, hj₄ i hi.1]; rfl
    refine Sat.seq_le hbr (by omega) fun c₃ ⟨hr₃, hw₃, ht₃, h4₃, h3₃, F3⟩ => ?_
    refine (setTail_sat (c₀ := c) (E := E) hr₃ (by rw [h4₃, h4₂]) (by rw [h3₃, ht₂]) hps
      hnbE').mono (by omega) fun c' ⟨hr', hw', h4', h3', F4⟩ => ⟨hr', ?_, ?_, h3', ?_⟩
    · rw [hw', hw₃, List.set_eq_take_append_cons_drop]
      simp [hIk, encFields_eq_encNums, encNums_append]
    · rw [F4 .t2 (by decide), ht₃]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      by_cases h4 : i = .t4
      · subst h4; exact h4'
      rw [F4 i (by simp [hi.1, h4, hi.2.2]), F3 i (by simp [hi.1, hi.2.1])]
      exact F2 i (by simp [hi.1, hi.2.2, h4])
  · -- past the fields: no change
    have hjk : j = fs.length := by omega
    subst hjk
    have hw₂' : c₂.stk .work = .mk 2 :: w := by
      rw [hw₂, List.drop_length]; simp [encFields]
    have hbr : Sat prog (.ite (.is 0 (some (.mk 2)))
        (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (dropNum .t2)))
        (.seq (.act (.set 0 none)) (.seq (.act (.set 1 none)) (.seq (dropNum .work)
          (moveNum2 .t2 .work .t0))))) c₂ (14 * E + 40) fun c' => c'.regs = Regs.empty ∧
        c'.stk .work = .mk 2 :: w ∧ c'.stk .t2 = r₂ ∧ c'.stk .t4 = c₂.stk .t4 ∧
        c'.stk .t3 = c₂.stk .t3 ∧ Fr [.work, .t2] c₂ c' := by
      refine Sat.ite_true_le (by simp [Cond.eval, hr₂, hw₂']) (by omega)
        (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
      have hv₃ : (Act.run (.set 1 none) (Act.run (.set 0 none) c₂)).regs = Regs.empty := by
        simp only [Act.run]; rw [hr₂, update_rv_zero, update_rv_one, empty_eq_rv]
      refine (dropNum_sat (l := lv) (rest := r₂) hv₃ (by
        simp only [Act.run]; rw [F2 .t2 (by decide), h₂])).mono (by omega)
        fun c' ⟨hr', h2', hj'⟩ => ⟨hr', ?_, h2', ?_, ?_, ?_⟩
      · rw [hj' .work (by decide)]; simpa [Act.run] using hw₂'
      · rw [hj' .t4 (by decide)]; rfl
      · rw [hj' .t3 (by decide)]; rfl
      · intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
        rw [hj' i hi.2]; rfl
    refine Sat.seq_le hbr (by omega) fun c₃ ⟨hr₃, hw₃, ht₃, h4₃, h3₃, F3⟩ => ?_
    refine (setTail_sat (c₀ := c) (E := E) hr₃ (by rw [h4₃, h4₂]) (by rw [h3₃, ht₂]) hps
      hnbE').mono (by omega) fun c' ⟨hr', hw', h4', h3', F4⟩ => ⟨hr', ?_, ?_, h3', ?_⟩
    · rw [hw', hw₃, List.set_eq_of_length_le (by omega), List.take_length,
        encFields_eq_encNums]
    · rw [F4 .t2 (by decide), ht₃]
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      by_cases h4 : i = .t4
      · subst h4; exact h4'
      rw [F4 i (by simp [hi.1, h4, hi.2.2]), F3 i (by simp [hi.1, hi.2.1])]
      exact F2 i (by simp [hi.1, hi.2.2, h4])

theorem RepList.set {h : List Cell} {a : Ty} {x : a.denote} {lv : List Bool}
    (rx : Rep h a x (ofBits lv)) :
    ∀ {xs : List a.denote} {fs : List (List Bool)}, RepList h a xs fs → ∀ i : ℕ,
      RepList h a (xs.set i x) (fs.set i lv)
  | [], [], .nil, _ => List.Forall₂.nil
  | _ :: _, _ :: _, .cons _ hr, 0 => List.Forall₂.cons (R := fun x p => Rep h a x (ofBits p)) rx hr
  | _ :: _, _ :: _, .cons r hr, i + 1 =>
    List.Forall₂.cons (R := fun x p => Rep h a x (ofBits p)) r (RepList.set rx hr i)

/-- Apply the write whose pair's pointer is on top of `lst` to the fields above `mk 2` on
`work`: fetch the pair, then the index, then `setAt`. -/
def applyW : Code Stk Sym Rg P :=
  .seq (moveNum2 .lst .ptr .t0) (.seq fetchCell (.seq (.act (.set 1 none))
    (.seq (moveNum2 .work .t1 .t0) (.seq (moveNum2 .work .t2 .t0) (.seq closeCell
      (.seq (moveNum2 .t1 .ptr .t0) (.seq fetchCell (.seq (.act (.set 1 none))
        (.seq (moveNum2 .work .t3 .t0) (.seq closeCell setAt))))))))))

theorem applyW_sat {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    {fs : List (List Bool)} {w : List Sym} {p : List Bool} {rl : List Sym} {i : ℕ}
    {x : a.denote} {E : ℕ} (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty)
    (hl : c.stk .lst = bits p ++ .nd :: rl) (hr : Rep h (.prod .nat a) (i, x) (ofBits p))
    (hp : p.length ≤ E) (hE : B + h.length ≤ E) (hE1 : 1 ≤ E)
    (hw : c.stk .work = encFields fs ++ .mk 2 :: w) (hfE : ∀ f ∈ fs, f.length ≤ E) :
    Sat prog applyW c (2 * fcE (encHeap h).length E + fs.length * (92 * E + 225) + 120 * E +
      330) fun c' => c'.regs = Regs.empty ∧ c'.stk .lst = rl ∧ ∃ lv, Rep h a x (ofBits lv) ∧
        lv.length < B + h.length ∧ c'.stk .work = encFields (fs.set i lv) ++ .mk 2 :: w ∧
        Fr [.work, .lst] c c' := by
  obtain ⟨l₁, l₂, hc, r₁, r₂⟩ := hr.pair_inv
  obtain ⟨ni, hci, hni⟩ := r₁.nat_inv
  have hl₁ := hB.field_lt hc l₁ (by simp)
  have hl₂ := hB.field_lt hc l₂ (by simp)
  have hni' := hB.field_lt hci ni (by simp)
  unfold applyW
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hl) (by omega)
    fun c₁ ⟨hr₁, hl₁', hp₁, hj₁⟩ => ?_
  have F1 : Fr [.lst, .ptr] c c₁ := fr2 hj₁
  have hH₁ := hH.fr F1 (by decide) (by decide) (by decide)
  refine Sat.seq_le (fetchCellE_sat (E := E) hH₁.wf hH₁.heap hH₁.scan hr₁ hc hp hp₁) (by omega)
    fun c₂ ⟨hr₂, hw₂, hp₂, hj₂⟩ => Sat.act_seq (by omega) ?_
  have hv₃ : (Act.run (.set 1 none) c₂).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₂, update_rv_one, empty_eq_rv]
  refine Sat.seq_le (moveNum2_sat (l := l₁) (rest := bits l₂ ++ .nd :: .mk 0 :: c₁.stk .work)
    (by decide) (by decide) (by decide) hv₃ (by simp [Act.run, hw₂, encFields])) (by omega)
    fun c₄ ⟨hr₄, hw₄, ht₄, hj₄⟩ => ?_
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₄ hw₄) (by omega)
    fun c₅ ⟨hr₅, hw₅, ht₅, hj₅⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₅, empty_eq_rv]) hw₅) (by omega)
    fun c₆ ⟨hr₆, hw₆, hj₆⟩ => ?_
  have ht₆ : c₆.stk .t1 = bits l₁ ++ .nd :: c.stk .t1 := by
    rw [hj₆ .t1 (by decide), hj₅ .t1 (by decide) (by decide), ht₄]
    simp only [Act.run]
    rw [hj₂ .t1 (by decide) (by decide), F1 .t1 (by decide)]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide)
    (by rw [hr₆, empty_eq_rv]) ht₆) (by omega) fun c₇ ⟨hr₇, ht₇, hp₇, hj₇⟩ => ?_
  have hp₇' : c₇.stk .ptr = bits l₁ ++ .nd :: c.stk .ptr := by
    rw [hp₇, hj₆ .ptr (by decide), hj₅ .ptr (by decide) (by decide),
      hj₄ .ptr (by decide) (by decide)]
    simp only [Act.run]
    rw [hp₂]
  have F7 : Fr [.lst, .ptr, .work, .ptr, .work, .t1, .work, .t2, .work, .t1, .ptr] c c₇ :=
    ((((((F1.trans (fr2 hj₂)).trans (fr_set 1 none c₂)).trans (fr2 hj₄)).trans
      (fr2 hj₅)).trans (fr1 hj₆)).trans (fr2 hj₇))
  have hH₇ := hH.fr F7 (by decide) (by decide) (by decide)
  have hw₇ : c₇.stk .work = encFields fs ++ .mk 2 :: w := by
    rw [hj₇ .work (by decide) (by decide), hw₆, hj₁ .work (by decide) (by decide), hw]
  refine Sat.seq_le (fetchCellE_sat (E := E) hH₇.wf hH₇.heap hH₇.scan hr₇ hci (by omega) hp₇')
    (by omega) fun c₈ ⟨hr₈, hw₈, hp₈, hj₈⟩ => Sat.act_seq (by omega) ?_
  have hv₉ : (Act.run (.set 1 none) c₈).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₈, update_rv_one, empty_eq_rv]
  refine Sat.seq_le (moveNum2_sat (l := ni) (rest := .mk 0 :: c₇.stk .work) (by decide)
    (by decide) (by decide) hv₉ (by simp [Act.run, hw₈, encFields])) (by omega)
    fun c₁₀ ⟨hr₁₀, hw₁₀, ht₁₀, hj₁₀⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₁₀, empty_eq_rv]) hw₁₀) (by omega)
    fun c₁₁ ⟨hr₁₁, hw₁₁, hj₁₁⟩ => ?_
  have F11 : Fr [.work, .ptr, .work, .t3, .work] c₇ c₁₁ :=
    (((fr2 hj₈).trans (fr_set 1 none c₈)).trans (fr2 hj₁₀)).trans (fr1 hj₁₁)
  have ht2 : c₁₁.stk .t2 = bits l₂ ++ .nd :: c.stk .t2 := by
    rw [F11 .t2 (by decide), hj₇ .t2 (by decide) (by decide), hj₆ .t2 (by decide), ht₅,
      hj₄ .t2 (by decide) (by decide)]
    simp only [Act.run]
    rw [hj₂ .t2 (by decide) (by decide), F1 .t2 (by decide)]
  have ht3 : c₁₁.stk .t3 = bits ni ++ .nd :: c.stk .t3 := by
    rw [hj₁₁ .t3 (by decide), ht₁₀]
    simp only [Act.run]
    rw [hj₈ .t3 (by decide) (by decide), F7 .t3 (by decide)]
  have hw11 : c₁₁.stk .work = encFields fs ++ .mk 2 :: w := by rw [hw₁₁, hw₇]
  refine (setAt_sat (E := E) hE1 (by rw [hr₁₁, empty_eq_rv]) hw11 ht2 ht3 hfE (by omega)
    (by omega)).mono (by omega)
    fun c' ⟨hr', hw', h2', h3', F12⟩ => ⟨hr', ?_, l₂, r₂, hl₂, by rw [hw', hni], ?_⟩
  · rw [F12 .lst (by decide), F11 .lst (by decide), hj₇ .lst (by decide) (by decide),
      hj₆ .lst (by decide), hj₅ .lst (by decide) (by decide), hj₄ .lst (by decide) (by decide)]
    simp only [Act.run]
    rw [hj₂ .lst (by decide) (by decide), hl₁']
  · have F : Fr [.ptr, .t1, .t2, .t3, .work, .lst] c c' :=
      ((F7.trans F11).trans F12).mono (by decide)
    have e₁ : c'.stk .ptr = c.stk .ptr := by
      rw [F12 .ptr (by decide), hj₁₁ .ptr (by decide), hj₁₀ .ptr (by decide) (by decide)]
      simp only [Act.run]
      rw [hp₈]
    have e₂ : c'.stk .t1 = c.stk .t1 := by rw [F12 .t1 (by decide), F11 .t1 (by decide), ht₇]
    exact (((F.restore e₁).restore e₂).restore h2').restore h3'

/-- Put the marker `mk 2` instead of `mk 0` below the fields on `work`. -/
def reMark : Code Stk Sym Rg P :=
  .seq (.act (.push .t4 (.mk 3))) (.seq (moveAll 0 .work .t4) (.seq closeCell
    (.seq (.act (.push .work (.mk 2))) (.seq (moveAll 3 .t4 .work) (.seq (.act (.pop .t4 0))
      (.act (.set 0 none)))))))

theorem reMark_sat {c : Cfg Stk Sym Rg} {fs : List (List Bool)} {w : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (hw : c.stk .work = encFields fs ++ .mk 0 :: w)
    (hfE : ∀ f ∈ fs, f.length ≤ E) :
    Sat prog reMark c (fs.length * (24 * E + 48) + 30) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = encFields fs ++ .mk 2 :: w ∧ Fr [.work] c c' := by
  have e : fs.length * (24 * E + 48) = fs.length * (12 * E + 24) + fs.length * (12 * E + 24) := by
    ring
  unfold reMark
  refine Sat.act_seq (by omega) ?_
  have hma := moveAll_sat (prog := prog) (i := 0) (a := .work) (b := .t4) (E := E)
    (c := Act.run (.push .t4 (.mk 3)) c) (ns := fs) (rest := w) (by decide) (by decide)
    (by decide) hv (by simpa [Act.run, encFields_eq_encNums] using hw) hfE
  refine Sat.seq_le hma (by omega) fun c₁ ⟨hr₁, hw₁, ht₁, F1⟩ => ?_
  refine Sat.seq_le (closeCell_sat (r := none) (by rw [hr₁, empty_eq_rv]) hw₁) (by omega)
    fun c₂ ⟨hr₂, hw₂, hj₂⟩ => Sat.act_seq (by omega) ?_
  have hma2 := moveAll_sat (prog := prog) (i := 3) (a := .t4) (b := .work) (E := E)
    (c := Act.run (.push .work (.mk 2)) c₂) (ns := fs.reverse) (rest := c.stk .t4) (by decide)
    (by decide) (by decide) (by simp only [Act.run]; rw [hr₂, empty_eq_rv])
    (by simp [Act.run, hj₂ .t4 (by decide), ht₁])
    (fun f hf => hfE f (List.mem_reverse.1 hf))
  rw [List.length_reverse, List.reverse_reverse] at hma2
  refine Sat.seq_le hma2 (by omega) fun c₃ ⟨hr₃, ht₃, hw₃, F3⟩ =>
    Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_, ?_⟩)
  · simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero, update_rv_zero]
  · simp only [Act.run]
    rw [update_of_ne (by decide), hw₃, encFields_eq_encNums]
    simp [Act.run, hw₂]
  · intro i hi
    simp only [List.mem_singleton] at hi
    simp only [Act.run]
    by_cases h4 : i = .t4
    · subst h4; rw [update_self, ht₃]; rfl
    rw [update_of_ne h4, F3 i (by simp [h4, hi])]
    simp only [Act.run]
    rw [update_of_ne hi, hj₂ i hi, F1 i (by simp [h4, hi])]
    simp [Act.run, update_of_ne h4]

/-- Apply the writes whose pairs' pointers are on `lst` (the first on top) above `mk 3`. -/
def writesLoop : Code Stk Sym Rg P :=
  .seq (.act (.peek .lst 0)) (.seq (.loop (.not (.is 0 (some (.mk 3))))
      (.seq (.act (.set 0 none)) (.seq applyW (.act (.peek .lst 0)))))
    (.seq (.act (.pop .lst 0)) (.act (.set 0 none))))

theorem applyWrites_snoc {a : Ty} (arr : Array a.denote) (ws : List (ℕ × a.denote))
    (wr : ℕ × a.denote) :
    Prim.applyWrites arr (ws ++ [wr]) = (Prim.applyWrites arr ws).setIfInBounds wr.1 wr.2 := by
  simp [Prim.applyWrites, List.foldl_append]

theorem writesLoop_sat {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c)
    (hB : HeapBnd B F h) {E : ℕ} (hE : B + h.length ≤ E) (hE1 : 1 ≤ E)
    (hv : c.regs = Regs.empty) {ws : List (ℕ × a.denote)} {prs : List (List Bool)}
    {rl : List Sym} (hR : RepList h (.prod .nat a) ws prs) (hpB : ∀ p ∈ prs, p.length ≤ E)
    (hl : c.stk .lst = encNums prs ++ .mk 3 :: rl) {cur : Array a.denote}
    {fs : List (List Bool)} {w : List Sym} (hcur : RepList h a cur.toList fs)
    (hfB : ∀ f ∈ fs, f.length < B + h.length) (hw : c.stk .work = encFields fs ++ .mk 2 :: w) :
    Sat prog writesLoop c (prs.length * (2 * fcE (encHeap h).length E +
      fs.length * (92 * E + 225) + 120 * E + 335) + 8) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .lst = rl ∧ ∃ fs',
        RepList h a (Prim.applyWrites cur ws).toList fs' ∧
        fs'.length = fs.length ∧ (∀ f ∈ fs', f.length < B + h.length) ∧
        c'.stk .work = encFields fs' ++ .mk 2 :: w ∧ Fr [.work, .lst] c c' := by
  have hloop := Sat.loop_list (prog := prog) (b := .not (.is 0 (some (.mk 3))))
    (x := .seq (.act (.set 0 none)) (.seq applyW (.act (.peek .lst 0))))
    (f := fun _ => 2 * fcE (encHeap h).length E + fs.length * (92 * E + 225) + 120 * E + 334)
    (I := fun rs c₁ => ∃ dws rws fsc, dws ++ rws = ws ∧ RepList h (.prod .nat a) rws rs ∧
      (∀ q ∈ rs, q.length ≤ E) ∧
      RepList h a (Prim.applyWrites cur dws).toList fsc ∧ fsc.length = fs.length ∧
      (∀ f ∈ fsc, f.length < B + h.length) ∧ c₁.stk .lst = encNums rs ++ .mk 3 :: rl ∧
      c₁.stk .work = encFields fsc ++ .mk 2 :: w ∧ c₁.regs = rv (c₁.stk .lst).head? none none none ∧
      Fr [.work, .lst] c c₁)
    (Q := fun c₁ => ∃ fsc, RepList h a (Prim.applyWrites cur ws).toList fsc ∧
      fsc.length = fs.length ∧ (∀ f ∈ fsc, f.length < B + h.length) ∧
      c₁.stk .lst = .mk 3 :: rl ∧ c₁.stk .work = encFields fsc ++ .mk 2 :: w ∧
      c₁.regs = rv (some (.mk 3)) none none none ∧ Fr [.work, .lst] c c₁)
    (fun p rs c₁ ⟨dws, rws, fsc, hd, hR₁, hq₁, hc₁, hlen₁, hfB₁, hl₁, hw₁, hr₁, F1⟩ => by
      obtain ⟨⟨i, x⟩, rws', hwr, hR₁', rfl⟩ := List.forall₂_cons_right_iff.1 hR₁
      have hpE : p.length ≤ E := hq₁ p (by simp)
      have hl₁' : c₁.stk .lst = bits p ++ .nd :: (encNums rs ++ .mk 3 :: rl) := by
        rw [hl₁]; simp
      refine ⟨by simp [Cond.eval, hr₁, hl₁', head_bits_ne_mk], Sat.act_seq (by omega) ?_⟩
      have hH₁ := hH.fr F1 (by decide) (by decide) (by decide)
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        simp only [Act.run]; rw [hr₁, update_rv_zero, empty_eq_rv]
      have hap := applyW_sat (prog := prog) (E := E) (p := p) (rl := encNums rs ++ .mk 3 :: rl)
        (w := w) (fs := fsc) (hH₁.frame (c' := Act.run (.set 0 none) c₁) rfl rfl rfl) hB hv₂
        (by simpa [Act.run] using hl₁') hwr hpE hE
        hE1 (by simpa [Act.run] using hw₁) (fun f hf => by have := hfB₁ f hf; omega)
      rw [hlen₁] at hap
      refine Sat.seq_le hap (by omega) fun c₃ ⟨hr₃, hl₃, lv, rx, hlv, hw₃, F3⟩ =>
        Sat.act_le (by omega)
          ⟨dws ++ [(i, x)], rws', fsc.set i lv, by rw [← hd]; simp, hR₁',
            fun q hq => hq₁ q (by simp [hq]), ?_, by simp [hlen₁], ?_, by simpa [Act.run] using hl₃,
            by simpa [Act.run] using hw₃, ?_, ?_⟩
      · rw [applyWrites_snoc, Array.toList_setIfInBounds]
        exact RepList.set rx hc₁ i
      · intro f hf
        rcases List.mem_or_eq_of_mem_set hf with hf | rfl
        · exact hfB₁ f hf
        · exact hlv
      · simp only [Act.run]; rw [hr₃, empty_eq_rv, update_rv_zero]
      · intro j hj
        simp only [Act.run]
        rw [F3 j hj]
        exact F1 j hj)
    (fun c₁ ⟨dws, rws, fsc, hd, hR₁, _, hc₁, hlen₁, hfB₁, hl₁, hw₁, hr₁, F1⟩ => by
      obtain rfl := List.forall₂_nil_right_iff.1 hR₁
      simp only [List.append_nil] at hd
      subst hd
      simp only [encNums_nil, List.nil_append] at hl₁
      exact ⟨by simp [Cond.eval, hr₁, hl₁], fsc, hc₁, hlen₁, hfB₁, hl₁, hw₁,
        by rw [hr₁, hl₁]; rfl, F1⟩)
  have hS : (prs.map fun _ => 2 * fcE (encHeap h).length E + fs.length * (92 * E + 225) +
      120 * E + 334 + 1).sum = prs.length * (2 * fcE (encHeap h).length E +
        fs.length * (92 * E + 225) + 120 * E + 335) := sum_map_const _ _
  unfold writesLoop
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop prs _ ⟨[], ws, fs, by simp, hR, hpB,
    by simpa [Prim.applyWrites] using hcur, rfl, hfB, by simpa [Act.run] using hl,
    by simpa [Act.run] using hw,
    by simp [Act.run, hv, empty_eq_rv], fun j _ => rfl⟩) (by omega)
    fun c₂ ⟨fsc, hc₂, hlen₂, hfB₂, hl₂, hw₂, hr₂, F2⟩ =>
      Sat.act_seq (by omega) (Sat.act_le (by omega) ⟨?_, ?_, fsc, hc₂, hlen₂, hfB₂, ?_, ?_⟩))
  · simp only [Act.run]; rw [hr₂, empty_eq_rv, update_rv_zero, update_rv_zero]
  · simp [Act.run, hl₂]
  · simp [Act.run, hw₂]
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [Act.run]
    rw [update_of_ne hj.2]
    exact F2 j (by simp [hj.1, hj.2])

theorem le_comb {n k W₁ W₂ W₃ W₄ W₅ P : ℕ} (h1 : W₁ + W₂ + W₅ ≤ P) (h2 : W₃ ≤ P)
    (h3 : W₂ + W₄ ≤ P) : n * W₁ + (n + 1) * W₂ + n * W₅ + k * W₃ + W₄ ≤ (k + n + 1) * P := by
  have a1 : n * (W₁ + W₂ + W₅) ≤ n * P := Nat.mul_le_mul_left _ h1
  have a2 : k * W₃ ≤ k * P := Nat.mul_le_mul_left _ h2
  have e1 : n * (W₁ + W₂ + W₅) = n * W₁ + n * W₂ + n * W₅ := by ring
  have e2 : (n + 1) * W₂ = n * W₂ + W₂ := by ring
  have e3 : (k + n + 1) * P = k * P + n * P + P := by ring
  omega

/-- The step bound of `arrayUpdate`, against `primB`. -/
theorem upd_bound {n k E N₀ n₀ M : ℕ} (hk : k ≤ M) (hE : E ≤ M) (hN : N₀ ≤ M) (hn : n₀ ≤ M) :
    n * (2 * fcE N₀ E + k * (92 * E + 225) + 120 * E + 336) + (n + 1) * (fcE N₀ E + 24 * E + 50) +
      n * (12 * E + 24) + k * (24 * E + 48) + (fcE N₀ E + 60 * E + allocBound (k * (E + 1)) n₀ +
        200) ≤ (k + n + 1) * primB M := by
  have hf := fcE_mono hN hE
  have hA := allocBound_ge (M * M + 3 * M + 2) M
  have hf150 := fcE_ge M
  have hm : k * (E + 1) ≤ M * M + 3 * M + 2 := by nlinarith
  have hA' := allocBound_mono (a := k * (E + 1)) (b := M * M + 3 * M + 2) (m := n₀) (n := M) hm hn
  have m1 : k * (92 * E + 225) ≤
      M * (fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100) :=
    Nat.mul_le_mul hk (by omega)
  have hP := primB_ge' M
  refine le_comb ?_ ?_ ?_ <;> omega

/-- Array writes: the fields of the array's cell (above `mk 2`), the writes applied in order,
then one cell. -/
def arrayUpdateCode : Code Stk Sym Rg P :=
  .seq (moveNum2 .work .lst .t0) (.seq openTop (.seq (.act (.set 1 none)) (.seq reMark
    (.seq (moveNum2 .lst .ptr .t0) (.seq (.act (.push .t4 (.mk 3))) (.seq (walkList .t4)
      (.seq (.act (.push .lst (.mk 3))) (.seq (moveAll 3 .t4 .lst) (.seq (.act (.pop .t4 0))
        (.seq (.act (.set 0 none)) (.seq writesLoop (alloc .arr))))))))))))

theorem out_arrayUpdate {a : Ty} {B F : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg} {w : List Sym}
    {arr : Array a.denote} {ws : List (ℕ × a.denote)} {la lw : List Bool} (hH : HeapAt h c)
    (hB : HeapBnd B F h) (h1B : 1 ≤ B) (hFB : F ≤ B) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = envEnc [la, lw] ++ w) (ra : Rep h (.array a) arr (ofBits la))
    (rws : Rep h (.list (.prod .nat a)) ws (ofBits lw)) (hla : la.length ≤ B + h.length)
    (hlw : lw.length ≤ B + h.length) {G : ℕ} (hG : 1 ≤ G) :
    PrimOut prog arrayUpdateCode c h w (.array a) (Prim.applyWrites arr ws) B F G
      (arr.size + ws.length + 1) := by
  obtain ⟨E, hE⟩ : ∃ E, E = B + h.length := ⟨_, rfl⟩
  rw [← hE] at hla hlw
  obtain ⟨fs, hc, hR⟩ := ra.arr_list
  have hlen : fs.length = arr.size := by rw [← hR.length_eq, Array.length_toList]
  rw [← hlen]
  have hfB := hB.field_lt hc
  have hfE : ∀ f ∈ fs, f.length ≤ E := fun f hf => by have := hfB f hf; omega
  have hkF : fs.length ≤ F := by
    obtain ⟨hp, -, hf⟩ := hc
    rw [← hf]; exact (hB _ hp).2.1
  have hw' : c.stk .work = bits lw ++ .nd :: (bits la ++ .nd :: w) := by simpa [envEnc] using hw
  unfold arrayUpdateCode
  refine PrimOut.of_sat (T := ws.length * (2 * fcE (encHeap h).length E +
    fs.length * (92 * E + 225) + 120 * E + 336) + (ws.length + 1) *
    (fcE (encHeap h).length E + 24 * E + 50) + ws.length * (12 * E + 24) +
    fs.length * (24 * E + 48) + (fcE (encHeap h).length E + 60 * E +
      allocBound (fs.length * (E + 1)) h.length + 200))
    (Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hv hw') (by omega)
      fun c₁ ⟨hr₁, hw₁, hl₁, hj₁⟩ => ?_)
  have F1 : Fr [.work, .lst] c c₁ := fr2 hj₁
  have hH₁ := hH.fr F1 (by decide) (by decide) (by decide)
  have hW1 : fcE (encHeap h).length E + 24 * E + 50 ≤
      (ws.length + 1) * (fcE (encHeap h).length E + 24 * E + 50) :=
    Nat.le_mul_of_pos_left _ (by omega)
  refine Sat.seq_le (openTop_sat (w := w) hH₁ hr₁ hw₁ hc hla) (by omega)
    fun c₂ ⟨hr₂, hw₂, F2⟩ => Sat.act_seq (by omega) ?_
  refine Sat.seq_le (reMark_sat (E := E) (w := w) (by simp only [Act.run]; rw [hr₂, update_rv_one,
    empty_eq_rv]) (by simpa [Act.run] using hw₂) hfE) (by omega)
    fun c₃ ⟨hr₃, hw₃, F3⟩ => ?_
  have hl₃ : c₃.stk .lst = bits lw ++ .nd :: c.stk .lst := by
    rw [F3 .lst (by decide)]
    simp only [Act.run]
    rw [F2 .lst (by decide), hl₁]
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₃ hl₃) (by omega)
    fun c₄ ⟨hr₄, hl₄, hp₄, hj₄⟩ => Sat.act_seq (by omega) ?_
  have F4 : Fr [.work, .lst, .work, .work, .lst, .ptr, .t4] c (Act.run (.push .t4 (.mk 3)) c₄) :=
    ((((F1.trans F2).trans (fr_set 1 none c₂ |>.trans F3)).trans (fr2 hj₄)).trans
      (fr_push .t4 (.mk 3) c₄)).mono (by decide)
  have hH₄ := hH.fr F4 (by decide) (by decide) (by decide)
  refine Sat.seq_le (walkList_sat (E := E) (q := lw) (rp := c.stk .ptr) (by decide) hH₄ hB hr₄
    (by simp only [Act.run]; rw [update_of_ne (by decide), hp₄, F3 .ptr (by decide)]
        simp only [Act.run]; rw [F2 .ptr (by decide), F1 .ptr (by decide)])
    rws (by omega) (by omega)) (by omega)
    fun c₅ ⟨hr₅, hp₅, F5, psr, hRw, hpB, ht₅⟩ => Sat.act_seq (by omega) ?_
  have hlen' : psr.length = ws.length := by rw [← hRw.length_eq, List.length_reverse]
  have ht₅' : (Act.run (.push .lst (.mk 3)) c₅).stk .t4 = encNums psr ++ .mk 3 :: c.stk .t4 := by
    simp only [Act.run]
    rw [update_of_ne (by decide), ht₅]
    simp only [Act.run, update_self]
    rw [hj₄ .t4 (by decide) (by decide), F3 .t4 (by decide)]
    simp only [Act.run]
    rw [F2 .t4 (by decide), F1 .t4 (by decide)]
  have hma := moveAll_sat (prog := prog) (i := 3) (a := .t4) (b := .lst) (E := E)
    (c := Act.run (.push .lst (.mk 3)) c₅) (by decide) (by decide) (by decide) hr₅ ht₅'
    (fun l hl => by have := hpB l hl; omega)
  rw [hlen'] at hma
  refine Sat.seq_le hma (by omega) fun c₆ ⟨hr₆, ht₆, hl₆, F6⟩ =>
    Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_)
  have F7 : Fr [.work, .lst, .work, .work, .lst, .ptr, .t4, .ptr, .t4, .lst, .t4, .lst, .t4] c
      (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₆)) :=
    ((((F4.trans F5).trans (fr_push .lst (.mk 3) c₅)).trans F6).trans (fr_pop .t4 0 c₆)).trans
      (fr_set 0 none _)
  have hH₇ := hH.fr F7 (by decide) (by decide) (by decide)
  have hv₇ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₆)).regs = Regs.empty := by
    simp only [Act.run]; rw [hr₆, empty_eq_rv, update_rv_zero, update_rv_zero]
  have hl₇ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₆)).stk .lst =
      encNums psr.reverse ++ .mk 3 :: c.stk .lst := by
    simp only [Act.run]
    rw [update_of_ne (by decide), hl₆]
    simp only [Act.run, update_self]
    rw [F5 .lst (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), hl₄]
  have hw₇ : (Act.run (.set 0 none) (Act.run (.pop .t4 0) c₆)).stk .work =
      encFields fs ++ .mk 2 :: w := by
    simp only [Act.run]
    rw [update_of_ne (by decide), F6 .work (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), F5 .work (by decide)]
    simp only [Act.run]
    rw [update_of_ne (by decide), hj₄ .work (by decide) (by decide), hw₃]
  have hRw' : RepList h (.prod .nat a) ws psr.reverse := by
    have := List.forall₂_reverse_iff.2 hRw
    simp only [List.reverse_reverse] at this
    exact this
  have hwl := writesLoop_sat (prog := prog) (E := E) hH₇ hB (by omega) (by omega) hv₇ hRw'
    (fun p hp => by have := hpB p (List.mem_reverse.1 hp); omega) hl₇ hR hfB hw₇
  rw [List.length_reverse, hlen'] at hwl
  have hm : ws.length * (2 * fcE (encHeap h).length E + fs.length * (92 * E + 225) + 120 * E +
      335) ≤ ws.length * (2 * fcE (encHeap h).length E + fs.length * (92 * E + 225) + 120 * E +
      336) := Nat.mul_le_mul_left _ (by omega)
  refine Sat.seq_le hwl (by omega) fun c₈ ⟨hr₈, hl₈, fs', hR', hlen₈, hfB', hw₈, F8⟩ => ?_
  have hH₈ := hH₇.fr F8 (by decide) (by decide) (by decide)
  have hLf := length_encFields_le (U := E) fs' fun f hf => by have := hfB' f hf; omega
  rw [hlen₈] at hLf
  have hA₀ := allocBound_mono (a := (encFields fs').length) (b := fs.length * (E + 1))
    (m := h.length) (n := h.length) hLf le_rfl
  refine (allocB_sat .arr hH₈ hB h1B hr₈ hw₈ (by omega) (fun f hf => by
    have := hfB' f hf; omega)).mono (by omega)
    fun c' ⟨hr', l, hH', hB', hc', hl', hw', F9⟩ => ⟨[⟨l, .arr, fs'⟩], l, hH', hB', hr',
      ?_, by simp; omega, hw', ?_, by simpa using hG, ?_⟩
  · have r := (RepList.mono hR').rep_arr hc'
    simpa using r
  · have F : Fr [.ptr, .t4, .lst, .heap, .cnt, .work] c c' :=
      (((F7.trans F8).trans F9)).mono (by decide)
    have e₁ : c'.stk .ptr = c.stk .ptr := by
      rw [F9 .ptr (by decide), F8 .ptr (by decide)]
      simp only [Act.run]
      rw [update_of_ne (by decide), F6 .ptr (by decide)]
      simp only [Act.run]
      rw [update_of_ne (by decide), hp₅]
    have e₂ : c'.stk .t4 = c.stk .t4 := by
      rw [F9 .t4 (by decide), F8 .t4 (by decide)]
      simp [Act.run, ht₆]
    have e₃ : c'.stk .lst = c.stk .lst := by rw [F9 .lst (by decide), hl₈]
    exact ((F.restore e₁).restore e₂).restore e₃
  · obtain ⟨s1, s2, s3⟩ := sizes_le B h [⟨l, .arr, fs'⟩]
    obtain ⟨M, hM⟩ : ∃ M, M = B + (encHeap (h ++ [⟨l, .arr, fs'⟩])).length := ⟨_, rfl⟩
    rw [← hM] at s1 s2 ⊢
    have hb := upd_bound (n := ws.length) (k := fs.length) (E := E) (N₀ := (encHeap h).length)
      (n₀ := h.length) (M := M) (by omega) (by omega) (by omega) (by omega)
    exact hb

/-! ### The primitives' code and its specification -/

/-- **Code for every primitive.** -/
def primCode : {args : List Ty} → {t : Ty} → Prim args t → Code Stk Sym Rg P
  | _, _, .unit => allocArgs .unit 0
  | _, _, .natLit k => natLitCode k
  | _, _, .boolLit b => allocArgs (if b then .tt else .ff) 0
  | _, _, .add => arithCode (addNum .t2 .t1 .work .t0)
  | _, _, .sub => arithCode (subNum .t2 .t1 .work .t0)
  | _, _, .natEq => cmpCode (eqNum .t2 .t1 .t3 .t0)
  | _, _, .natLt => cmpCode (ltNum .t2 .t1 .t3 .t0)
  | _, _, .not => notCode
  | _, _, .and => andCode
  | _, _, .or => orCode
  | _, _, .pair => allocArgs .pair 2
  | _, _, .fst => fstCode
  | _, _, .snd => sndCode
  | _, _, .none => allocArgs .none 0
  | _, _, .some => allocArgs .some 1
  | _, _, .nil => allocArgs .nil 0
  | _, _, .cons => allocArgs .cons 2
  | _, _, .append => appendCode
  | _, _, .reverse => reverseCode
  | _, _, .length => lengthCode
  | _, _, .range => rangeCode
  | _, _, .arrayMk => arrayMkCode
  | _, _, .arraySize => arraySizeCode
  | _, a, .arrayGet => arrayGetCode a
  | _, _, .arrayUpdate => arrayUpdateCode
  | _, _, .arrayOfList => arrayOfListCode
  | _, _, .arrayToList => arrayToListCode

theorem PrimOut.spec {x : Code Stk Sym Rg P} {c : Cfg Stk Sym Rg} {h : List Cell}
    {w : List Sym} {t : Ty} {v : t.denote} {B F K C : ℕ} {Q : ℕ → ℕ}
    (ho : PrimOut prog x c h w t v B F (K * C) C) (hQ : ∀ N, primB (B + N) ≤ Q N) :
    ∃ c' n h' l, Exec prog x c c' n ∧ HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
      c'.regs = Regs.empty ∧ Rep (h ++ h') t v (ofBits l) ∧
      l.length ≤ B + (h ++ h').length ∧ c'.stk .work = bits l ++ .nd :: w ∧
      (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c.stk j) ∧
      h'.length ≤ K * C ∧ n ≤ C * Q (encHeap (h ++ h')).length := by
  obtain ⟨c', n, h', l, e, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ho
  exact ⟨c', n, h', l, e, a1, a2, a3, a4, a5, a6, fun j h1 h2 h3 => a7 j (by simp [h1, h2, h3]),
    a8, a9.trans (Nat.mul_le_mul_left _ (hQ _))⟩

theorem Args.eq_nil {var : Ty → Type} (xs : Args var []) : xs = .nil := by cases xs; rfl

theorem Args.eq_one {var : Ty → Type} {a : Ty} (xs : Args var [a]) : ∃ x, xs = .cons x .nil := by
  cases xs with
  | cons x xs => cases xs; exact ⟨x, rfl⟩

theorem Args.eq_two {var : Ty → Type} {a b : Ty} (xs : Args var [a, b]) :
    ∃ x y, xs = .cons x (.cons y .nil) := by
  cases xs with
  | cons x xs => cases xs with
    | cons y xs => cases xs; exact ⟨x, y, rfl⟩

theorem ArgsRep.nil_inv {h : List Cell} {ls : List (List Bool)} (hR : ArgsRep h .nil ls) :
    ls = [] := by cases hR; rfl

theorem ArgsRep.one_inv {h : List Cell} {a : Ty} {x : a.denote} {ls : List (List Bool)}
    (hR : ArgsRep h (.cons x .nil) ls) : ∃ l, ls = [l] ∧ Rep h a x (ofBits l) := by
  cases hR with
  | cons r hR => cases hR; exact ⟨_, rfl, r⟩

theorem ArgsRep.two_inv {h : List Cell} {a b : Ty} {x : a.denote} {y : b.denote}
    {ls : List (List Bool)} (hR : ArgsRep h (.cons x (.cons y .nil)) ls) :
    ∃ l₁ l₂, ls = [l₁, l₂] ∧ Rep h a x (ofBits l₁) ∧ Rep h b y (ofBits l₂) := by
  cases hR with
  | cons r₁ hR => cases hR with
    | cons r₂ hR => cases hR; exact ⟨_, _, rfl, r₁, r₂⟩

/-- **The specification of the primitives' code** (`PLAN-17.md` §9): `primCode` meets
`PrimSpec` for every program, when counts of at most `F` elements fit the field bound
(`F + 1 ≤ B`), cells may have two fields (`2 ≤ F`), and `Q` is at least `primB` at `B` plus
the heap's length. -/
theorem primCode_spec (prog : Program Stk Sym Rg P) {B F K : ℕ} {Q : ℕ → ℕ} (hFB : F + 1 ≤ B)
    (h2F : 2 ≤ F) (hQ : ∀ N, primB (B + N) ≤ Q N) : PrimSpec prog primCode B F K Q := by
  intro args t p xs h c ls w hpw hKB hcost hH hB hv hR hls hw
  have h2K : 2 ≤ K := (two_le_pw p).trans hpw
  have h1B : 1 ≤ B := by omega
  have h1F : 1 ≤ F := by omega
  cases p with
  | unit =>
    obtain rfl := Args.eq_nil xs; obtain rfl := hR.nil_inv
    exact (out_allocArgs (prog := prog) .unit hH hB h1B hv hw (by simp) (by simp) (by simp)
      (fun l hc => .unit hc) (by omega) (le_refl _)).spec hQ
  | natLit k =>
    obtain rfl := Args.eq_nil xs; obtain rfl := hR.nil_inv
    have : (toBits k).length + 2 ≤ K := hpw
    exact (out_natLit (prog := prog) k hH hB h1F hv (by simpa [envEnc] using hw) (by omega)
      (by omega) (le_refl _)).spec hQ
  | boolLit b =>
    obtain rfl := Args.eq_nil xs; obtain rfl := hR.nil_inv
    exact (out_allocArgs (prog := prog) (if b then .tt else .ff) hH hB h1B hv hw (by simp)
      (by simp) (by simp) (fun l hc => .bool b hc) (by omega)
      (le_refl _)).spec hQ
  | add =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_add (prog := prog) hH hB h1B h1F hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      (by omega) (le_refl _)).spec hQ
  | sub =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_sub (prog := prog) hH hB h1B h1F hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      (by omega) (le_refl _)).spec hQ
  | natEq =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_natEq (prog := prog) hH hB h1B hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      (by omega) (le_refl _)).spec hQ
  | natLt =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_natLt (prog := prog) hH hB h1B hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      (by omega) (le_refl _)).spec hQ
  | not =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_not (prog := prog) hH hB h1B hv hw r (hls _ (by simp))
      (by omega) (le_refl _)).spec hQ
  | and =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_and (prog := prog) hH hB hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      (le_refl _)).spec hQ
  | or =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_or (prog := prog) hH hB hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      (le_refl _)).spec hQ
  | pair =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_allocArgs (prog := prog) .pair hH hB h1B hv hw (by simp; omega) (by simp) hls
      (fun l hc => .pair hc r₁.mono r₂.mono) (by omega) (le_refl _)).spec hQ
  | fst =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_fst (prog := prog) hH hB hv hw r (hls _ (by simp)) (le_refl _)).spec hQ
  | snd =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_snd (prog := prog) hH hB hv hw r (hls _ (by simp)) (le_refl _)).spec hQ
  | none =>
    obtain rfl := Args.eq_nil xs; obtain rfl := hR.nil_inv
    exact (out_allocArgs (prog := prog) .none hH hB h1B hv hw (by simp) (by simp) (by simp)
      (fun l hc => .none hc) (by omega) (le_refl _)).spec hQ
  | some =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_allocArgs (prog := prog) .some hH hB h1B hv hw (by simp; omega) (by simp) hls
      (fun l' hc => .some hc r.mono) (by omega) (le_refl _)).spec hQ
  | nil =>
    obtain rfl := Args.eq_nil xs; obtain rfl := hR.nil_inv
    exact (out_allocArgs (prog := prog) .nil hH hB h1B hv hw (by simp) (by simp) (by simp)
      (fun l hc => .nil hc) (by omega) (le_refl _)).spec hQ
  | cons =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_allocArgs (prog := prog) .cons hH hB h1B hv hw (by simp; omega) (by simp) hls
      (fun l hc => .cons hc r₁.mono r₂.mono) (by omega) (le_refl _)).spec hQ
  | append =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_append (prog := prog) hH hB h1B h2F hv hw r₁ r₂ (hls _ (by simp))
      (hls _ (by simp)) (by nlinarith)).spec hQ
  | reverse =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_reverse (prog := prog) hH hB h1B h2F hv hw r (hls _ (by simp))
      (by nlinarith)).spec hQ
  | length =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_length (prog := prog) hH hB hFB hv hw r (hls _ (by simp)) hcost
      (by nlinarith)).spec hQ
  | range =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_range (prog := prog) hH hB hFB h2F hv hw r (hls _ (by simp)) hcost
      (by nlinarith)).spec hQ
  | arrayMk =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_arrayMk (prog := prog) hH hB h1B hv hw r₁ r₂ (hls _ (by simp)) (hls _ (by simp))
      hcost (by omega) (by nlinarith)).spec hQ
  | arraySize =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_arraySize (prog := prog) hH hB hFB h1F hv hw r (hls _ (by simp))
      (by omega) (le_refl _)).spec hQ
  | arrayGet =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    have : tySize _ + 2 ≤ K := hpw
    exact (out_arrayGet (prog := prog) hH hB hFB h2F hv hw r₁ r₂ (hls _ (by simp))
      (hls _ (by simp)) (by omega) (by omega)).spec hQ
  | arrayUpdate =>
    obtain ⟨x, y, rfl⟩ := Args.eq_two xs; obtain ⟨l₁, l₂, rfl, r₁, r₂⟩ := hR.two_inv
    exact (out_arrayUpdate (prog := prog) hH hB h1B (by omega) hv hw r₁ r₂ (hls _ (by simp))
      (hls _ (by simp)) (by nlinarith)).spec hQ
  | arrayOfList =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_arrayOfList (prog := prog) hH hB h1B hv hw r (hls _ (by simp)) hcost (by omega)
      (by nlinarith)).spec hQ
  | arrayToList =>
    obtain ⟨x, rfl⟩ := Args.eq_one xs; obtain ⟨l, rfl, r⟩ := hR.one_inv
    exact (out_arrayToList (prog := prog) hH hB h1B h2F hv hw r (hls _ (by simp))
      (by nlinarith)).spec hQ

theorem primB_mono {M M' : ℕ} (h : M ≤ M') : primB M ≤ primB M' := by
  unfold primB
  have h₁ := fcE_mono h h
  have h₂ := allocBound_mono (a := M * M + 3 * M + 2) (b := M' * M' + 3 * M' + 2)
    (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul h h) (Nat.mul_le_mul_left 3 h)) 2) h
  exact Nat.mul_le_mul (by omega) (by omega)

theorem ctrlB_mono {D M M' : ℕ} (h : M ≤ M') : ctrlB D M ≤ ctrlB D M' := by
  unfold ctrlB
  have := fetchB_mono (le_refl D) h
  have := fcE_mono h h
  omega

end GraphIso.TM
