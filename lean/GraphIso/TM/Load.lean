module

public import GraphIso.TM.Ser
public import GraphIso.TM.Alloc
public import Mathlib.Data.List.Forall2
public import Mathlib.Tactic.DefEqTransformations

/-!
# Loading the input

Stage 17d (`PLAN-17.md` §7). `load t` reads `ser t v` from the input stack `inp` and builds
cells representing `v` on the heap, leaving a pointer on `work`.

* **`LoadSpec a ld`**: assume `HeapAt h c`, empty registers, `ser a x ++ rest` on `inp`, and
  `h.length + cellsB a x ≤ U`. Then `ld` runs within `ldB a x U` steps to a configuration with
  empty registers, `rest` on `inp`, cells `h'` appended to the heap (`HeapAt (h ++ h')`, at most
  `cellsB a x` of them), and a pointer `l` pushed onto `work` with `l.length ≤ U` and
  `Rep (h ++ h') a x (ofBits l)`. The stacks other than `heap`, `cnt`, `inp` and `work` are
  unchanged.
* **`load_sat t`**: `load t` meets `LoadSpec t` for every type `t`. A pair loads its components
  and allocates a pair cell; an option reads its tag; a list loads its elements (`readElems`),
  allocates the `nil` cell and then the `cons` cells from the end of the list (`buildList`); an
  array loads its elements (serialized in reverse order) and allocates one cell with their
  pointers.
* **Bounds**, with `L = (ser t v).length`: `cellsB_le`, `cellsB t v ≤ wt t * (L + 1)`; and
  `ldB_le`, `ldB t v U ≤ wt t * (L + 1) * PL U` for `L ≤ U`, where
  `PL U = allocBound ((U + 1) * (U + 2)) U + 30 * U + 100` is a polynomial of degree 4.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost Function

variable {P : Type} {prog : Program Stk Sym Rg P}

/-- The pointers `ps` represent the values `xs`. -/
def RepList (h : List Cell) (a : Ty) (xs : List a.denote) (ps : List (List Bool)) : Prop :=
  List.Forall₂ (fun x p => Rep h a x (ofBits p)) xs ps

theorem RepList.mono {h h' : List Cell} {a : Ty} {xs : List a.denote} {ps : List (List Bool)}
    (hr : RepList h a xs ps) : RepList (h ++ h') a xs ps :=
  hr.imp fun _ _ r => r.mono

/-- Close a step-budget side condition. -/
local macro "budget" : tactic =>
  `(tactic| first | omega | (simp only [List.length_reverse] at *; omega))

/-! ### The code -/

/-- Read elements, each after the tag `cons`, with `ld` until the tag `nil`, which is dropped;
`ld` pushes the pointer of each element onto `work`. -/
def readElems (ld : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (.act (.peek .inp 0))
    (.seq (.loop (.is 0 (some (.tag .cons)))
        (.seq (.act (.set 0 none)) (.seq (.act (.pop .inp 0)) (.seq (.act (.set 0 none))
          (.seq ld (.act (.peek .inp 0)))))))
      (.seq (.act (.set 0 none)) (.seq (.act (.pop .inp 0)) (.act (.set 0 none)))))

/-- From `q :: p_k :: … :: p₁ :: mk 3` on `work`, the cons cells of `p₁ … p_k` onto the list
`q`; the marker is dropped and the pointer of the list is left on `work`. -/
def buildList : Code Stk Sym Rg P :=
  .seq (moveBits .work .t1) (.seq (.act (.peek .work 0))
    (.seq (.loop (.not (.is 0 (some (.mk 3))))
        (.seq (.act (.set 0 none)) (.seq (moveBits .work .t2) (.seq (.act (.push .work (.mk 2)))
          (.seq (moveBits .t1 .work) (.seq (moveBits .t2 .work) (.seq (alloc .cons)
            (.seq (moveBits .work .t1) (.act (.peek .work 0))))))))))
      (.seq (.act (.set 0 none)) (.seq (.act (.pop .work 0)) (.seq (.act (.set 0 none))
        (moveBits .t1 .work))))))

/-- Allocate a cell without fields. -/
def alloc0 (t : Tag) : Code Stk Sym Rg P := .seq (.act (.push .work (.mk 2))) (alloc t)

/-- Load a serialized value of type `t` from `inp` into the heap; push its pointer onto
`work`. -/
def load : Ty → Code Stk Sym Rg P
  | .unit => alloc0 .unit
  | .bool => .seq (.act (.pop .inp 0))
      (.ite (.is 0 (some (.tag .tt))) (.seq (.act (.set 0 none)) (alloc0 .tt))
        (.seq (.act (.set 0 none)) (alloc0 .ff)))
  | .nat => .seq (.act (.push .work (.mk 2)))
      (.seq (moveBits .inp .t1) (.seq (moveBits .t1 .work) (alloc .nat)))
  | .prod a b => .seq (load a) (.seq (load b)
      (.seq (moveBits .work .t1) (.seq (moveBits .work .t2) (.seq (.act (.push .work (.mk 2)))
        (.seq (moveBits .t1 .work) (.seq (moveBits .t2 .work) (alloc .pair)))))))
  | .option a => .seq (.act (.pop .inp 0))
      (.ite (.is 0 (some (.tag .none))) (.seq (.act (.set 0 none)) (alloc0 .none))
        (.seq (.act (.set 0 none)) (.seq (load a) (.seq (moveBits .work .t1)
          (.seq (.act (.push .work (.mk 2))) (.seq (moveBits .t1 .work) (alloc .some)))))))
  | .list a => .seq (.act (.push .work (.mk 3))) (.seq (readElems (load a))
      (.seq (alloc0 .nil) buildList))
  | .array a => .seq (.act (.push .work (.mk 2))) (.seq (readElems (load a)) (alloc .arr))

/-! ### Bounds -/

/-- The number of cells that loading `v` allocates, at most. -/
def cellsB : (t : Ty) → t.denote → ℕ
  | .unit, _ => 1
  | .bool, _ => 1
  | .nat, _ => 1
  | .prod a b, v => cellsB a v.1 + cellsB b v.2 + 1
  | .option _, none => 1
  | .option a, some x => cellsB a x + 1
  | .list a, xs => (xs.map fun x => cellsB a x + 1).sum + 1
  | .array a, v => (v.toList.map fun x => cellsB a x).sum + 1

/-- The step bound of `load`, for addresses and counters of length at most `U`. -/
def ldB : (t : Ty) → t.denote → ℕ → ℕ
  | .unit, _, U => allocBound 0 U + 2
  | .bool, _, U => allocBound 0 U + 7
  | .nat, n, U => 12 * (toBits n).length + 22 + allocBound ((toBits n).length + 1) U
  | .prod a b, v, U => ldB a v.1 U + ldB b v.2 U + 4 * (6 * U + 9) + allocBound (2 * U + 2) U + 10
  | .option _, none, U => allocBound 0 U + 7
  | .option a, some x, U => ldB a x U + 2 * (6 * U + 9) + allocBound (U + 1) U + 10
  | .list a, xs, U => (xs.map fun x => ldB a x U + 8 + 1).sum + 9 + allocBound 0 U +
      2 * (6 * U + 9) +
      xs.length * (4 * (6 * U + 9) + allocBound (2 * U + 2) U + 11) + 20
  | .array a, v, U => (v.toList.reverse.map fun x => ldB a x U + 8 + 1).sum + 9 +
      allocBound (v.size * (U + 1)) U + 4

/-! ### Reading elements -/

theorem HeapAt.frame {h : List Cell} {c c' : Cfg Stk Sym Rg} (hH : HeapAt h c)
    (hh : c'.stk .heap = c.stk .heap) (hs : c'.stk .scan = c.stk .scan)
    (hc : c'.stk .cnt = c.stk .cnt) : HeapAt h c' :=
  ⟨hH.wf, hh.trans hH.heap, hs.trans hH.scan, by rw [hc]; exact hH.cnt⟩

/-- The specification of a loader `ld` for the type `a`: from a heap `h` with room for the
cells of `x` below `U`, it reads `ser a x` and leaves a pointer `l` (of length at most `U`) to a
representation of `x` on `work`. -/
def LoadSpec (a : Ty) (ld : Code Stk Sym Rg P) : Prop :=
  ∀ (prog : Program Stk Sym Rg P) (x : a.denote) (h : List Cell) (c : Cfg Stk Sym Rg)
    (rest : List Sym) (U : ℕ), HeapAt h c → c.regs = Regs.empty →
    c.stk .inp = ser a x ++ rest → h.length + cellsB a x ≤ U →
    Sat prog ld c (ldB a x U) fun c' => c'.regs = Regs.empty ∧
      ∃ h' l, HeapAt (h ++ h') c' ∧ h'.length ≤ cellsB a x ∧ l.length ≤ U ∧
        Rep (h ++ h') a x (ofBits l) ∧ c'.stk .inp = rest ∧
        c'.stk .work = bits l ++ .nd :: c.stk .work ∧
        ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .inp → j ≠ .work → c'.stk j = c.stk j

theorem readElems_sat {a : Ty} {ld : Code Stk Sym Rg P} (hld : LoadSpec a ld)
    (xs : List a.denote) {h : List Cell} {c : Cfg Stk Sym Rg} {rest : List Sym} {U : ℕ}
    (hH : HeapAt h c) (hv : c.regs = Regs.empty)
    (hi : c.stk .inp = serElems a xs ++ .tag .nil :: rest)
    (hU : h.length + (xs.map (cellsB a)).sum ≤ U) :
    Sat prog (readElems ld) c ((xs.map fun x => ldB a x U + 8 + 1).sum + 9) fun c' =>
      c'.regs = Regs.empty ∧
      ∃ h' ps, HeapAt (h ++ h') c' ∧ h'.length ≤ (xs.map (cellsB a)).sum ∧
        (∀ p ∈ ps, p.length ≤ U) ∧ RepList (h ++ h') a xs ps ∧ c'.stk .inp = rest ∧
        c'.stk .work = encFields ps.reverse ++ c.stk .work ∧
        ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .inp → j ≠ .work → c'.stk j = c.stk j := by
  have hloop := Sat.loop_list (prog := prog) (b := .is 0 (some (.tag .cons)))
    (x := .seq (.act (.set 0 none)) (.seq (.act (.pop .inp 0)) (.seq (.act (.set 0 none))
      (.seq ld (.act (.peek .inp 0))))))
    (f := fun x => ldB a x U + 8)
    (I := fun rs c₁ => ∃ done ps h₁, done ++ rs = xs ∧ HeapAt (h ++ h₁) c₁ ∧
      h₁.length ≤ (done.map (cellsB a)).sum ∧ (∀ p ∈ ps, p.length ≤ U) ∧
      RepList (h ++ h₁) a done ps ∧ c₁.stk .inp = serElems a rs ++ .tag .nil :: rest ∧
      c₁.regs = rv (c₁.stk .inp).head? none none none ∧
      c₁.stk .work = encFields ps.reverse ++ c.stk .work ∧
      ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .inp → j ≠ .work → c₁.stk j = c.stk j)
    (Q := fun c₁ => ∃ ps h₁, HeapAt (h ++ h₁) c₁ ∧ h₁.length ≤ (xs.map (cellsB a)).sum ∧
      (∀ p ∈ ps, p.length ≤ U) ∧ RepList (h ++ h₁) a xs ps ∧
      c₁.stk .inp = .tag .nil :: rest ∧ c₁.regs = rv (some (.tag .nil)) none none none ∧
      c₁.stk .work = encFields ps.reverse ++ c.stk .work ∧
      ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .inp → j ≠ .work → c₁.stk j = c.stk j)
    (fun x rs c₁ ⟨done, ps, h₁, hd, hH₁, hl₁, hps, hR, hi₁, hr₁, hw₁, hj₁⟩ => by
      rw [serElems_cons] at hi₁
      refine ⟨by simp [Cond.eval, hr₁, hi₁], ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
      set c₂ := Act.run (.set 0 none) (Act.run (.pop .inp 0) (Act.run (.set 0 none) c₁))
        with hc₂
      have hv₂ : c₂.regs = Regs.empty := by
        rw [empty_eq_rv]; simp [hc₂, Act.run, hr₁, hi₁]
      have hi₂ : c₂.stk .inp = ser a x ++ (serElems a rs ++ .tag .nil :: rest) := by
        simp [hc₂, Act.run, hi₁]
      have hH₂ : HeapAt (h ++ h₁) c₂ := hH₁.frame (by simp [hc₂, Act.run])
        (by simp [hc₂, Act.run]) (by simp [hc₂, Act.run])
      have hsum : (xs.map (cellsB a)).sum =
          (done.map (cellsB a)).sum + cellsB a x + (rs.map (cellsB a)).sum := by
        rw [← hd]; simp [List.sum_append]; omega
      have hU₂ : (h ++ h₁).length + cellsB a x ≤ U := by
        rw [List.length_append]; omega
      refine Sat.seq_le (hld prog x (h ++ h₁) c₂ _ U hH₂ hv₂ hi₂ hU₂) (by omega)
        fun c₃ ⟨hr₃, h₂, l, hH₃, hl₃, hlU, hR₃, hi₃, hw₃, hj₃⟩ =>
          Sat.act_le (by omega) ⟨done ++ [x], ps ++ [l], h₁ ++ h₂, by simp [← hd], ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_⟩
      · rw [← List.append_assoc]
        exact hH₃.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
      · simp only [List.length_append, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil]
        omega
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact hps p hp
        · rw [List.mem_singleton.1 hp]; exact hlU
      · rw [← List.append_assoc]
        exact List.rel_append hR.mono (.cons hR₃ .nil)
      · simp [Act.run, hi₃]
      · rw [empty_eq_rv] at hr₃
        simp [Act.run, hr₃]
      · simp only [Act.run]
        rw [hw₃, hc₂]
        simp [Act.run, hw₁, encFields]
      · intro j hjh hjc hji hjw
        simp only [Act.run]
        rw [hj₃ j hjh hjc hji hjw, hc₂]
        simp [Act.run, update_of_ne hji, hj₁ j hjh hjc hji hjw])
    (fun c₁ ⟨done, ps, h₁, hd, hH₁, hl₁, hps, hR, hi₁, hr₁, hw₁, hj₁⟩ => by
      simp only [List.append_nil] at hd
      subst hd
      simp only [serElems, List.map_nil, List.flatten_nil, List.nil_append] at hi₁
      exact ⟨by simp [Cond.eval, hr₁, hi₁], ps, h₁, hH₁, hl₁, hps, hR, hi₁,
        by simp [hr₁, hi₁], hw₁, hj₁⟩)
  unfold readElems
  refine Sat.act_seq (by omega) (Sat.seq_le (hloop xs _ ⟨[], [], [], by simp, ?_, by simp,
    by simp, List.Forall₂.nil, ?_, ?_, ?_, ?_⟩) (by omega)
      fun c₁ ⟨ps, h₁, hH₁, hl₁, hps, hR, hi₁, hr₁, hw₁, hj₁⟩ => Sat.act_seq (by omega)
        (Sat.act_seq (by omega) (Sat.act_le (by omega)
          ⟨?_, h₁, ps, ?_, hl₁, hps, hR, ?_, ?_, ?_⟩)))
  · rw [List.append_nil]
    exact hH.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  · simp [Act.run, hi]
  · rw [empty_eq_rv] at hv
    simp [Act.run, hv]
  · simp [Act.run, encFields]
  · intro j _ _ _ _; simp [Act.run]
  · rw [empty_eq_rv]; simp [Act.run, hr₁, hi₁]
  · exact hH₁.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  · simp [Act.run, hi₁]
  · simp [Act.run, hw₁]
  · intro j hjh hjc hji hjw
    simp [Act.run, update_of_ne hji, hj₁ j hjh hjc hji hjw]

/-! ### Loading each type -/

theorem allocBound_mono {a b m n : ℕ} (hab : a ≤ b) (hmn : m ≤ n) :
    allocBound a m ≤ allocBound b n := by
  unfold allocBound
  have := Nat.mul_le_mul hab (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hab) 14)
  omega

theorem cellAt_new {h : List Cell} {l : List Bool} {t : Tag} {fs : List (List Bool)}
    (hl : ofBits l = h.length) : CellAt (h ++ [⟨l, t, fs⟩]) (ofBits l) t fs :=
  ⟨by simp [hl], by simp [hl], by simp [hl]⟩

/-- Allocation of a cell without fields, as a loader of one value. -/
theorem alloc0_sat {t : Tag} {h : List Cell} {c : Cfg Stk Sym Rg} {U : ℕ} (hH : HeapAt h c)
    (hv : c.regs = Regs.empty) (hU : h.length + 1 ≤ U) :
    Sat prog (alloc0 t) c (allocBound 0 U + 2) fun c' => c'.regs = Regs.empty ∧
      ∃ l, HeapAt (h ++ [⟨l, t, []⟩]) c' ∧ ofBits l = h.length ∧ l.length ≤ U ∧
        c'.stk .work = bits l ++ .nd :: c.stk .work ∧
        ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c.stk j := by
  unfold alloc0
  refine Sat.act_seq (by omega) ?_
  have hH₁ : HeapAt h (Act.run (.push .work (.mk 2)) c) :=
    hH.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  have hw₁ : (Act.run (.push .work (.mk 2)) c).stk .work = encFields [] ++ .mk 2 :: c.stk .work :=
    by simp [Act.run, encFields]
  have hb := allocBound_mono (a := (encFields []).length) (b := 0) (by simp [encFields])
    (by omega : h.length ≤ U)
  refine (alloc_sat t hH₁ hv hw₁).mono (by omega)
    fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
      ⟨hr, l, hH', hl, by omega, hw', fun j hjh hjc hjw => ?_⟩
  rw [hj' j hjh hjc hjw]
  simp [Act.run, update_of_ne hjw]

theorem load_unit : LoadSpec (P := P) .unit (load .unit) := by
  intro prog x h c rest U hH hv hi hU
  have hU' : h.length + 1 ≤ U := hU
  simp only [ldB]
  refine (alloc0_sat hH hv hU').mono le_rfl fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
    ⟨hr, _, l, hH', by simp [cellsB], hlU, .unit (cellAt_new hl), ?_, hw', ?_⟩
  · rw [hj' .inp (by decide) (by decide) (by decide), hi]; rfl
  · intro j hjh hjc _ hjw; exact hj' j hjh hjc hjw

theorem load_bool : LoadSpec (P := P) .bool (load .bool) := by
  intro prog b h c rest U hH hv hi hU
  simp only [ldB]
  have hU' : h.length + 1 ≤ U := hU
  have hi' : c.stk .inp = .tag (if b then .tt else .ff) :: rest := hi
  unfold load
  refine Sat.act_seq (by budget) ?_
  set c₁ := Act.run (.pop .inp 0) c with hc₁
  have hH₁ : HeapAt h c₁ := hH.frame (by simp [hc₁, Act.run]) (by simp [hc₁, Act.run])
    (by simp [hc₁, Act.run])
  have hr₁ : c₁.regs = rv (some (.tag (if b then .tt else .ff))) none none none := by
    rw [empty_eq_rv] at hv; simp [hc₁, Act.run, hv, hi']
  have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₁]
  have hH₂ : HeapAt h (Act.run (.set 0 none) c₁) :=
    hH₁.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  cases b with
  | true =>
    refine Sat.ite_true_le (by simp [Cond.eval, hr₁]) (by budget)
      (Sat.act_seq (by omega) ((alloc0_sat hH₂ hv₂ hU').mono (by omega)
        fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
          ⟨hr, _, l, hH', by simp [cellsB], hlU, .bool true (cellAt_new hl), ?_, ?_, ?_⟩))
    · rw [hj' .inp (by decide) (by decide) (by decide)]; simp [Act.run, hc₁, hi']
    · rw [hw']; simp [Act.run, hc₁]
    · intro j hjh hjc hji hjw
      rw [hj' j hjh hjc hjw]; simp [Act.run, hc₁, update_of_ne hji]
  | false =>
    refine Sat.ite_false_le (by simp [Cond.eval, hr₁]) (by budget)
      (Sat.act_seq (by omega) ((alloc0_sat hH₂ hv₂ hU').mono (by omega)
        fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
          ⟨hr, _, l, hH', by simp [cellsB], hlU, .bool false (cellAt_new hl), ?_, ?_, ?_⟩))
    · rw [hj' .inp (by decide) (by decide) (by decide)]; simp [Act.run, hc₁, hi']
    · rw [hw']; simp [Act.run, hc₁]
    · intro j hjh hjc hji hjw
      rw [hj' j hjh hjc hjw]; simp [Act.run, hc₁, update_of_ne hji]

theorem load_nat : LoadSpec (P := P) .nat (load .nat) := by
  intro prog n h c rest U hH hv hi hU
  simp only [ldB]
  have hU' : h.length + 1 ≤ U := hU
  have hi' : c.stk .inp = bits (toBits n) ++ .nd :: rest := by rw [hi]; simp [ser]
  unfold load
  refine Sat.act_seq (by budget) ?_
  set c₁ := Act.run (.push .work (.mk 2)) c with hc₁
  have hi₁ : c₁.stk .inp = bits (toBits n) ++ .nd :: rest := by simp [hc₁, Act.run, hi']
  refine Sat.seq_le (moveBits_sat (by decide) hv hi₁) (by budget)
    fun c₂ ⟨hr₂, hi₂, ht₂, hj₂⟩ => ?_
  refine Sat.seq_le (moveBits_sat (by decide) hr₂ ht₂) (by budget)
    fun c₃ ⟨hr₃, ht₃, hw₃, hj₃⟩ => ?_
  have e : ∀ j, j ≠ .inp → j ≠ .t1 → j ≠ .work → c₃.stk j = c.stk j := by
    intro j h1 h2 h3
    rw [hj₃ j h2 h3, hj₂ j h1 h2]
    simp [hc₁, Act.run, update_of_ne h3]
  have hH₃ : HeapAt h c₃ := hH.frame (e .heap (by decide) (by decide) (by decide))
    (e .scan (by decide) (by decide) (by decide)) (e .cnt (by decide) (by decide) (by decide))
  have hw₃' : c₃.stk .work = encFields [toBits n] ++ .mk 2 :: c.stk .work := by
    rw [hw₃, hj₂ .work (by decide) (by decide)]; simp [hc₁, Act.run, encFields]
  have hb := allocBound_mono (a := (encFields [toBits n]).length) (b := (toBits n).length + 1)
    (by simp [encFields]) (by omega : h.length ≤ U)
  refine (alloc_sat .nat hH₃ hr₃ hw₃').mono (by budget)
    fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ => ⟨hr, _, l, hH', by simp [cellsB], by omega, ?_, ?_,
      hw', ?_⟩
  · have r := Rep.nat (h := h ++ [⟨l, .nat, [toBits n]⟩]) (cellAt_new hl)
    rwa [ofBits_toBits] at r
  · rw [hj' .inp (by decide) (by decide) (by decide), hj₃ .inp (by decide) (by decide), hi₂]
  · intro j hjh hjc hji hjw
    rw [hj' j hjh hjc hjw]
    by_cases hj1 : j = .t1
    · subst hj1; rw [ht₃]; simp [hc₁, Act.run]
    exact e j hji hj1 hjw

theorem load_prod {a b : Ty} (ha : LoadSpec (P := P) a (load a))
    (hb : LoadSpec (P := P) b (load b)) : LoadSpec (P := P) (.prod a b) (load (.prod a b)) := by
  intro prog v h c rest U hH hv hi hU
  simp only [ldB]
  have hU' : h.length + (cellsB a v.1 + cellsB b v.2 + 1) ≤ U := hU
  have hi₀ : c.stk .inp = ser a v.1 ++ (ser b v.2 ++ rest) := by rw [hi]; simp [ser]
  unfold load
  refine Sat.seq_le (ha prog v.1 h c _ U hH hv hi₀ (by omega)) (by budget)
    fun c₁ ⟨hr₁, h₁, la, hH₁, hl₁, hla, hRa, hi₁, hw₁, hj₁⟩ => ?_
  refine Sat.seq_le (hb prog v.2 (h ++ h₁) c₁ _ U hH₁ hr₁ hi₁ (by simp; omega))
    (by budget) fun c₂ ⟨hr₂, h₂, lb, hH₂, hl₂, hlb, hRb, hi₂, hw₂, hj₂⟩ => ?_
  refine Sat.seq_le (moveBits_sat (by decide) hr₂ hw₂) (by budget)
    fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => ?_
  rw [hw₁] at hw₃
  refine Sat.seq_le (moveBits_sat (by decide) hr₃ hw₃) (by budget)
    fun c₄ ⟨hr₄, hw₄, ht₄, hj₄⟩ => ?_
  refine Sat.act_seq (by budget) ?_
  set c₅ := Act.run (.push .work (.mk 2)) c₄ with hc₅
  have ht₅ : c₅.stk .t1 = bits lb.reverse ++ .nd :: c₂.stk .t1 := by
    simp [hc₅, Act.run, hj₄ .t1 (by decide) (by decide), ht₃]
  refine Sat.seq_le (moveBits_sat (by decide) hr₄ ht₅) (by budget)
    fun c₆ ⟨hr₆, ht₆, hw₆, hj₆⟩ => ?_
  have ht₆' : c₆.stk .t2 = bits la.reverse ++ .nd :: c₃.stk .t2 := by
    rw [hj₆ .t2 (by decide) (by decide)]; simp [hc₅, Act.run, ht₄]
  refine Sat.seq_le (moveBits_sat (by decide) hr₆ ht₆') (by budget)
    fun c₇ ⟨hr₇, ht₇, hw₇, hj₇⟩ => ?_
  have e : ∀ j, j ≠ .work → j ≠ .t1 → j ≠ .t2 → c₇.stk j = c₂.stk j := by
    intro j h1 h2 h3
    rw [hj₇ j h3 h1, hj₆ j h2 h1]
    simp only [hc₅, Act.run]
    rw [update_of_ne h1, hj₄ j h1 h3, hj₃ j h1 h2]
  have hH₇ : HeapAt (h ++ h₁ ++ h₂) c₇ := hH₂.frame (e .heap (by decide) (by decide) (by decide))
    (e .scan (by decide) (by decide) (by decide)) (e .cnt (by decide) (by decide) (by decide))
  have hw₇' : c₇.stk .work = encFields [la, lb] ++ .mk 2 :: c.stk .work := by
    rw [hw₇, hw₆]
    simp [hc₅, Act.run, hw₄, encFields]
  have hcells : (h ++ h₁ ++ h₂).length + 1 ≤ U := by simp only [List.length_append]; omega
  have hbnd := allocBound_mono (a := (encFields [la, lb]).length) (b := 2 * U + 2)
    (by simp [encFields]; omega) (by omega : (h ++ h₁ ++ h₂).length ≤ U)
  refine (alloc_sat .pair hH₇ hr₇ hw₇').mono (by budget)
    fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
      ⟨hr, h₁ ++ h₂ ++ [⟨l, .pair, [la, lb]⟩], l, by simpa [List.append_assoc] using hH',
        by simp [cellsB]; omega, by omega, ?_, ?_, hw', ?_⟩
  · have r := Rep.pair (cellAt_new hl) ((hRa.mono (h' := h₂)).mono (h' := [⟨l, .pair, [la, lb]⟩]))
      (hRb.mono (h' := [⟨l, .pair, [la, lb]⟩]))
    simpa [List.append_assoc] using r
  · rw [hj' .inp (by decide) (by decide) (by decide), e .inp (by decide) (by decide) (by decide),
      hi₂]
  · intro j hjh hjc hji hjw
    rw [hj' j hjh hjc hjw]
    by_cases hj2 : j = .t2
    · subst hj2
      rw [ht₇, hj₃ .t2 (by decide) (by decide), hj₂ .t2 hjh hjc hji hjw, hj₁ .t2 hjh hjc hji hjw]
    by_cases hj1 : j = .t1
    · subst hj1
      rw [hj₇ .t1 (by decide) (by decide), ht₆, hj₂ .t1 hjh hjc hji hjw,
        hj₁ .t1 hjh hjc hji hjw]
    rw [e j hjw hj1 hj2, hj₂ j hjh hjc hji hjw, hj₁ j hjh hjc hji hjw]

theorem load_option {a : Ty} (ha : LoadSpec (P := P) a (load a)) :
    LoadSpec (P := P) (.option a) (load (.option a)) := by
  intro prog v h c rest U hH hv hi hU
  unfold load
  have hH₁ : HeapAt h (Act.run (.pop .inp 0) c) :=
    hH.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  have hH₂ : HeapAt h (Act.run (.set 0 none) (Act.run (.pop .inp 0) c)) :=
    hH₁.frame (by simp [Act.run]) (by simp [Act.run]) (by simp [Act.run])
  cases v with
  | none =>
    simp only [ldB]
    refine Sat.act_seq (by budget) ?_
    set c₁ := Act.run (.pop .inp 0) c with hc₁
    have hi' : c.stk .inp = .tag .none :: rest := hi
    have hr₁ : c₁.regs = rv (some (.tag .none)) none none none := by
      rw [empty_eq_rv] at hv; simp [hc₁, Act.run, hv, hi']
    have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
      rw [empty_eq_rv]; simp [Act.run, hr₁]
    have hU' : h.length + 1 ≤ U := hU
    refine Sat.ite_true_le (by simp [Cond.eval, hr₁]) (by budget)
      (Sat.act_seq (by budget) ((alloc0_sat hH₂ hv₂ hU').mono (by budget)
        fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
          ⟨hr, _, l, hH', by simp [cellsB], hlU, .none (cellAt_new hl), ?_, ?_, ?_⟩))
    · rw [hj' .inp (by decide) (by decide) (by decide)]; simp [Act.run, hc₁, hi']
    · rw [hw']; simp [Act.run, hc₁]
    · intro j hjh hjc hji hjw
      rw [hj' j hjh hjc hjw]; simp [Act.run, hc₁, update_of_ne hji]
  | some x =>
    simp only [ldB]
    refine Sat.act_seq (by budget) ?_
    set c₁ := Act.run (.pop .inp 0) c with hc₁
    have hi' : c.stk .inp = .tag .some :: (ser a x ++ rest) := by rw [hi]; simp [ser]
    have hr₁ : c₁.regs = rv (some (.tag .some)) none none none := by
      rw [empty_eq_rv] at hv; simp [hc₁, Act.run, hv, hi']
    have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
      rw [empty_eq_rv]; simp [Act.run, hr₁]
    have hi₂ : (Act.run (.set 0 none) c₁).stk .inp = ser a x ++ rest := by
      simp [Act.run, hc₁, hi']
    have hU' : h.length + (cellsB a x + 1) ≤ U := hU
    refine Sat.ite_false_le (by simp [Cond.eval, hr₁]) (by budget)
      (Sat.act_seq (by budget) ?_)
    refine Sat.seq_le (ha prog x h _ rest U hH₂ hv₂ hi₂ (by omega)) (by budget)
      fun c₃ ⟨hr₃, h₁, lx, hH₃, hl₃, hlx, hRx, hi₃, hw₃, hj₃⟩ => ?_
    refine Sat.seq_le (moveBits_sat (by decide) hr₃ hw₃) (by budget)
      fun c₄ ⟨hr₄, hw₄, ht₄, hj₄⟩ => ?_
    refine Sat.act_seq (by budget) ?_
    set c₅ := Act.run (.push .work (.mk 2)) c₄ with hc₅
    have ht₅ : c₅.stk .t1 = bits lx.reverse ++ .nd :: c₃.stk .t1 := by
      simp [hc₅, Act.run, ht₄]
    refine Sat.seq_le (moveBits_sat (by decide) hr₄ ht₅) (by budget)
      fun c₆ ⟨hr₆, ht₆, hw₆, hj₆⟩ => ?_
    have e : ∀ j, j ≠ .work → j ≠ .t1 → c₆.stk j = c₃.stk j := by
      intro j h1 h2
      rw [hj₆ j h2 h1]
      simp only [hc₅, Act.run]
      rw [update_of_ne h1, hj₄ j h1 h2]
    have hH₆ : HeapAt (h ++ h₁) c₆ := hH₃.frame (e .heap (by decide) (by decide))
      (e .scan (by decide) (by decide)) (e .cnt (by decide) (by decide))
    have hw₆' : c₆.stk .work = encFields [lx] ++ .mk 2 :: c.stk .work := by
      rw [hw₆]
      simp [hc₅, Act.run, hw₄, hc₁, encFields]
    have hcells : (h ++ h₁).length + 1 ≤ U := by simp only [List.length_append]; omega
    have hbnd := allocBound_mono (a := (encFields [lx]).length) (b := U + 1)
      (by simp [encFields]; omega) (by omega : (h ++ h₁).length ≤ U)
    refine (alloc_sat .some hH₆ hr₆ hw₆').mono (by budget)
      fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
        ⟨hr, h₁ ++ [⟨l, .some, [lx]⟩], l, by simpa [List.append_assoc] using hH',
          by simp [cellsB]; omega, by omega, ?_, ?_, hw', ?_⟩
    · have r := Rep.some (cellAt_new hl) (hRx.mono (h' := [⟨l, .some, [lx]⟩]))
      simpa [List.append_assoc] using r
    · rw [hj' .inp (by decide) (by decide) (by decide), e .inp (by decide) (by decide), hi₃]
    · intro j hjh hjc hji hjw
      rw [hj' j hjh hjc hjw]
      by_cases hj1 : j = .t1
      · subst hj1
        rw [ht₆, hj₃ .t1 hjh hjc hji hjw]
        simp [Act.run, hc₁]
      rw [e j hjw hj1, hj₃ j hjh hjc hji hjw]
      simp [Act.run, hc₁, update_of_ne hji]

/-! ### Lists and arrays -/

theorem sum_map_const {α : Type} (l : List α) (k : ℕ) : (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons _ l ih => simp [Nat.succ_mul]; omega

/-- The step bound of `buildList` for `k` cells. -/
def blB (U k : ℕ) : ℕ :=
  2 * (6 * U + 9) + k * (4 * (6 * U + 9) + allocBound (2 * U + 2) U + 11) + 11

theorem buildList_sat {a : Ty} (rs : List (a.denote × List Bool)) {bs : List a.denote}
    {q : List Bool} {h : List Cell} {c : Cfg Stk Sym Rg} {w₀ : List Sym} {U : ℕ}
    (hH : HeapAt h c) (hv : c.regs = Regs.empty)
    (hw : c.stk .work = bits q ++ .nd :: (encFields (rs.map Prod.snd) ++ .mk 3 :: w₀))
    (hq : Rep h (.list a) bs (ofBits q)) (hR : ∀ pr ∈ rs, Rep h a pr.1 (ofBits pr.2))
    (hqU : q.length ≤ U) (hpU : ∀ pr ∈ rs, pr.2.length ≤ U) (hU : h.length + rs.length ≤ U) :
    Sat prog buildList c (blB U rs.length) fun c' => c'.regs = Regs.empty ∧
      ∃ h' q', HeapAt (h ++ h') c' ∧ h'.length ≤ rs.length ∧ q'.length ≤ U ∧
        Rep (h ++ h') (.list a) (rs.reverse.map Prod.fst ++ bs) (ofBits q') ∧
        c'.stk .work = bits q' ++ .nd :: w₀ ∧
        ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c.stk j := by
  obtain ⟨F, hF⟩ : ∃ F, F = 4 * (6 * U + 9) + allocBound (2 * U + 2) U + 10 := ⟨_, rfl⟩
  have hloop := Sat.loop_list (prog := prog) (b := .not (.is 0 (some (.mk 3))))
    (x := .seq (.act (.set 0 none)) (.seq (moveBits .work .t2) (.seq (.act (.push .work (.mk 2)))
      (.seq (moveBits .t1 .work) (.seq (moveBits .t2 .work) (.seq (alloc .cons)
        (.seq (moveBits .work .t1) (.act (.peek .work 0)))))))))
    (f := fun _ => F)
    (I := fun rs' c₁ => ∃ done q₁ h₁, done ++ rs' = rs ∧ HeapAt (h ++ h₁) c₁ ∧
      h₁.length ≤ done.length ∧ q₁.length ≤ U ∧
      Rep (h ++ h₁) (.list a) (done.reverse.map Prod.fst ++ bs) (ofBits q₁) ∧
      c₁.stk .t1 = bits q₁.reverse ++ .nd :: c.stk .t1 ∧
      c₁.stk .work = encFields (rs'.map Prod.snd) ++ .mk 3 :: w₀ ∧
      c₁.regs = rv (c₁.stk .work).head? none none none ∧
      ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → j ≠ .t1 → c₁.stk j = c.stk j)
    (Q := fun c₁ => ∃ q₁ h₁, HeapAt (h ++ h₁) c₁ ∧ h₁.length ≤ rs.length ∧ q₁.length ≤ U ∧
      Rep (h ++ h₁) (.list a) (rs.reverse.map Prod.fst ++ bs) (ofBits q₁) ∧
      c₁.stk .t1 = bits q₁.reverse ++ .nd :: c.stk .t1 ∧ c₁.stk .work = .mk 3 :: w₀ ∧
      c₁.regs = rv (some (.mk 3)) none none none ∧
      ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → j ≠ .t1 → c₁.stk j = c.stk j)
    (fun pr rs' c₁ ⟨done, q₁, h₁, hd, hH₁, hl₁, hq₁, hR₁, ht₁, hw₁, hr₁, hj₁⟩ => by
      obtain ⟨x, p⟩ := pr
      have hmem : (x, p) ∈ rs := by rw [← hd]; simp
      have hpU : p.length ≤ U := hpU _ hmem
      have hw₁' :
          c₁.stk .work = bits p ++ .nd :: (encFields (rs'.map Prod.snd) ++ .mk 3 :: w₀) := by
        rw [hw₁]; simp [encFields]
      have hhead : (c₁.stk .work).head? ≠ some (.mk 3) := by
        rw [hw₁']; cases p <;> simp [bits]
      refine ⟨by simp [Cond.eval, hr₁, hhead], ?_⟩
      refine Sat.act_seq (by budget) ?_
      have hv₂ : (Act.run (.set 0 none) c₁).regs = Regs.empty := by
        rw [empty_eq_rv]; simp [Act.run, hr₁]
      refine Sat.seq_le (moveBits_sat (by decide) hv₂ hw₁') (by budget)
        fun c₃ ⟨hr₃, hw₃, ht₃, hj₃⟩ => ?_
      refine Sat.act_seq (by budget) ?_
      set c₄ := Act.run (.push .work (.mk 2)) c₃ with hc₄
      have ht₄ : c₄.stk .t1 = bits q₁.reverse ++ .nd :: c.stk .t1 := by
        simp [hc₄, Act.run, hj₃ .t1 (by decide) (by decide), ht₁]
      refine Sat.seq_le (moveBits_sat (by decide) hr₃ ht₄) (by budget)
        fun c₅ ⟨hr₅, ht₅, hw₅, hj₅⟩ => ?_
      have ht₅' : c₅.stk .t2 = bits p.reverse ++ .nd :: (Act.run (.set 0 none) c₁).stk .t2 := by
        rw [hj₅ .t2 (by decide) (by decide)]; simp [hc₄, Act.run, ht₃]
      refine Sat.seq_le (moveBits_sat (by decide) hr₅ ht₅') (by budget)
        fun c₆ ⟨hr₆, ht₆, hw₆, hj₆⟩ => ?_
      have e : ∀ j, j ≠ .work → j ≠ .t1 → j ≠ .t2 → c₆.stk j = c₁.stk j := by
        intro j h1 h2 h3
        rw [hj₆ j h3 h1, hj₅ j h2 h1]
        simp only [hc₄, Act.run]
        rw [update_of_ne h1, hj₃ j h1 h3]
        simp [Act.run]
      have hH₆ : HeapAt (h ++ h₁) c₆ := hH₁.frame (e .heap (by decide) (by decide) (by decide))
        (e .scan (by decide) (by decide) (by decide)) (e .cnt (by decide) (by decide) (by decide))
      have hw₆' : c₆.stk .work = encFields [p, q₁] ++ .mk 2 ::
          (encFields (rs'.map Prod.snd) ++ .mk 3 :: w₀) := by
        rw [hw₆, hw₅]
        simp [hc₄, Act.run, hw₃, encFields]
      have hcells : (h ++ h₁).length + 1 ≤ U := by
        have := congrArg List.length hd
        simp only [List.length_append, List.length_cons] at this ⊢
        omega
      have hbnd := allocBound_mono (a := (encFields [p, q₁]).length) (b := 2 * U + 2)
        (by simp [encFields]; omega) (by omega : (h ++ h₁).length ≤ U)
      refine Sat.seq_le (alloc_sat .cons hH₆ hr₆ hw₆') (by budget)
        fun c₇ ⟨hr₇, l, hH₇, hl, hlU, hw₇, hj₇⟩ => ?_
      refine Sat.seq_le (moveBits_sat (by decide) hr₇ hw₇) (by budget)
        fun c₈ ⟨hr₈, hw₈, ht₈, hj₈⟩ => Sat.act_le (by budget)
          ⟨done ++ [(x, p)], l, h₁ ++ [⟨l, .cons, [p, q₁]⟩], by simp [← hd], ?_, ?_, by omega,
            ?_, ?_, ?_, ?_, ?_⟩
      · rw [← List.append_assoc]
        exact hH₇.frame (by simp [Act.run, hj₈ .heap (by decide) (by decide)])
          (by simp [Act.run, hj₈ .scan (by decide) (by decide)])
          (by simp [Act.run, hj₈ .cnt (by decide) (by decide)])
      · simp; omega
      · have hx : Rep (h ++ h₁) a x (ofBits p) := (hR _ hmem).mono
        have r := Rep.cons (cellAt_new hl) (hx.mono (h' := [⟨l, .cons, [p, q₁]⟩]))
          (hR₁.mono (h' := [⟨l, .cons, [p, q₁]⟩]))
        simpa [List.append_assoc] using r
      · simp only [Act.run]
        rw [ht₈, hj₇ .t1 (by decide) (by decide) (by decide), hj₆ .t1 (by decide) (by decide), ht₅]
      · simp only [Act.run]
        rw [hw₈]
      · rw [empty_eq_rv] at hr₈
        simp [Act.run, hr₈, update_rv_zero]
      · intro j hjh hjc hjw hj1
        simp only [Act.run]
        by_cases hj2 : j = .t2
        · subst hj2
          rw [hj₈ .t2 (by decide) (by decide), hj₇ .t2 (by decide) (by decide) (by decide), ht₆]
          simp only [Act.run]
          exact hj₁ .t2 hjh hjc hjw hj1
        rw [hj₈ j hjw hj1, hj₇ j hjh hjc hjw, e j hjw hj1 hj2, hj₁ j hjh hjc hjw hj1])
    (fun c₁ ⟨done, q₁, h₁, hd, hH₁, hl₁, hq₁, hR₁, ht₁, hw₁, hr₁, hj₁⟩ => by
      simp only [List.append_nil] at hd
      subst hd
      simp only [List.map_nil, encFields, List.nil_append] at hw₁
      exact ⟨by simp [Cond.eval, hr₁, hw₁], q₁, h₁, hH₁, hl₁, hq₁, hR₁, ht₁, hw₁,
        by simp [hr₁, hw₁], hj₁⟩)
  have hk : (rs.map fun _ => F + 1).sum =
      rs.length * (4 * (6 * U + 9) + allocBound (2 * U + 2) U + 11) := by
    rw [sum_map_const, hF]
  unfold buildList blB
  refine Sat.seq_le (moveBits_sat (by decide) hv hw) (by budget) fun c₁ ⟨hr₁, hw₁, ht₁, hj₁⟩ => ?_
  refine Sat.act_seq (by budget) ?_
  refine Sat.seq_le (hloop rs _ ⟨[], q, [], by simp, ?_, by simp, hqU, ?_, ?_, ?_, ?_, ?_⟩)
    (by budget) fun c₂ ⟨q₁, h₁, hH₂, hl₂, hq₂, hR₂, ht₂, hw₂, hr₂, hj₂⟩ => ?_
  · rw [List.append_nil]
    exact hH.frame (by simp [Act.run, hj₁ .heap (by decide) (by decide)])
      (by simp [Act.run, hj₁ .scan (by decide) (by decide)])
      (by simp [Act.run, hj₁ .cnt (by decide) (by decide)])
  · simpa using hq
  · simp [Act.run, ht₁]
  · simp [Act.run, hw₁]
  · rw [empty_eq_rv] at hr₁
    simp [Act.run, hr₁, update_rv_zero]
  · intro j _ _ hjw hj1
    simp [Act.run, hj₁ j hjw hj1]
  refine Sat.act_seq (by budget) (Sat.act_seq (by budget) (Sat.act_seq (by budget) ?_))
  set c₃ := Act.run (.set 0 none) (Act.run (.pop .work 0) (Act.run (.set 0 none) c₂)) with hc₃
  have hv₃ : c₃.regs = Regs.empty := by
    rw [empty_eq_rv]; simp [hc₃, Act.run, hr₂, hw₂]
  have ht₃ : c₃.stk .t1 = bits q₁.reverse ++ .nd :: c.stk .t1 := by simp [hc₃, Act.run, ht₂]
  refine (moveBits_sat (by decide) hv₃ ht₃).mono (by budget)
    fun c' ⟨hr', ht', hw', hj'⟩ => ⟨hr', h₁, q₁, ?_, hl₂, hq₂, hR₂, ?_, ?_⟩
  · exact hH₂.frame (by rw [hj' .heap (by decide) (by decide)]; simp [hc₃, Act.run])
      (by rw [hj' .scan (by decide) (by decide)]; simp [hc₃, Act.run])
      (by rw [hj' .cnt (by decide) (by decide)]; simp [hc₃, Act.run])
  · rw [hw']
    simp [hc₃, Act.run, hw₂]
  · intro j hjh hjc hjw
    by_cases hj1 : j = .t1
    · subst hj1; exact ht'
    rw [hj' j hj1 hjw]
    simp [hc₃, Act.run, update_of_ne hjw, hj₂ j hjh hjc hjw hj1]

theorem length_encFields_le {U : ℕ} :
    ∀ ps : List (List Bool), (∀ p ∈ ps, p.length ≤ U) → (encFields ps).length ≤ ps.length * (U + 1)
  | [], _ => by simp [encFields]
  | p :: ps, hps => by
    have h₁ := hps p (by simp)
    have h₂ := length_encFields_le ps fun q hq => hps q (by simp [hq])
    rw [length_encFields_cons, List.length_cons, Nat.succ_mul]
    omega

theorem load_list {a : Ty} (ha : LoadSpec (P := P) a (load a)) :
    LoadSpec (P := P) (.list a) (load (.list a)) := by
  intro prog xs h c rest U hH hv hi hU
  simp only [ldB]
  have hsum : (xs.map fun x => cellsB a x + 1).sum = (xs.map (cellsB a)).sum + xs.length := by
    clear hi hU
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  have hU' : h.length + ((xs.map (cellsB a)).sum + xs.length + 1) ≤ U := by
    have : h.length + ((xs.map fun x => cellsB a x + 1).sum + 1) ≤ U := hU
    omega
  unfold load
  refine Sat.act_seq (by budget) ?_
  set c₁ := Act.run (.push .work (.mk 3)) c with hc₁
  have hH₁ : HeapAt h c₁ := hH.frame (by simp [hc₁, Act.run]) (by simp [hc₁, Act.run])
    (by simp [hc₁, Act.run])
  have hi₁ : c₁.stk .inp = serElems a xs ++ .tag .nil :: rest := by
    simp [hc₁, Act.run, hi, ser, serElems]
  refine Sat.seq_le (readElems_sat (U := U) ha xs hH₁ hv hi₁ (by omega)) (by budget)
    fun c₂ ⟨hr₂, h₁, ps, hH₂, hl₂, hps, hR, hi₂, hw₂, hj₂⟩ => ?_
  have hlen : xs.length = ps.length := hR.length_eq
  refine Sat.seq_le (alloc0_sat (t := .nil) (U := U) hH₂ hr₂
    (by simp only [List.length_append]; omega)) (by budget)
    fun c₃ ⟨hr₃, q, hH₃, hq, hqU, hw₃, hj₃⟩ => ?_
  set rs := (xs.zip ps).reverse with hrs
  have hrslen : rs.length = xs.length := by simp [hrs, hlen]
  have hrs₂ : rs.map Prod.snd = ps.reverse := by
    simp [hrs, List.map_reverse, List.map_snd_zip, hlen]
  have hrs₁ : rs.reverse.map Prod.fst = xs := by simp [hrs, List.map_fst_zip, hlen]
  have hw₃' : c₃.stk .work =
      bits q ++ .nd :: (encFields (rs.map Prod.snd) ++ .mk 3 :: c.stk .work) := by
    rw [hw₃, hw₂, hrs₂]; simp [hc₁, Act.run]
  have hRq : Rep (h ++ h₁ ++ [⟨q, .nil, []⟩]) (.list a) [] (ofBits q) := .nil (cellAt_new hq)
  have hRrs : ∀ pr ∈ rs, Rep (h ++ h₁ ++ [⟨q, .nil, []⟩]) a pr.1 (ofBits pr.2) := by
    intro pr hpr
    rw [hrs, List.mem_reverse] at hpr
    exact (List.forall₂_zip hR hpr).mono
  have hpsU : ∀ pr ∈ rs, pr.2.length ≤ U := by
    intro pr hpr
    rw [hrs, List.mem_reverse] at hpr
    exact hps _ (List.of_mem_zip hpr).2
  have hlU : (h ++ h₁ ++ [(⟨q, .nil, []⟩ : Cell)]).length + rs.length ≤ U := by
    simp only [List.length_append, List.length_singleton]; omega
  refine (buildList_sat rs hH₃ hr₃ hw₃' hRq hRrs hqU hpsU hlU).mono
    (by simp only [blB]; rw [hrslen]; omega)
    fun c' ⟨hr, h₂, q', hH', hl', hq'U, hRq', hw', hj'⟩ =>
      ⟨hr, h₁ ++ [⟨q, .nil, []⟩] ++ h₂, q', by simpa [List.append_assoc] using hH',
        by simp only [cellsB, List.length_append, List.length_singleton]; omega, hq'U, ?_, ?_, ?_,
        ?_⟩
  · rw [hrs₁, List.append_nil] at hRq'
    simpa [List.append_assoc] using hRq'
  · rw [hj' .inp (by decide) (by decide) (by decide), hj₃ .inp (by decide) (by decide)
      (by decide), hi₂]
  · rw [hw']
  · intro j hjh hjc hji hjw
    rw [hj' j hjh hjc hjw, hj₃ j hjh hjc hjw, hj₂ j hjh hjc hji hjw]
    simp [hc₁, Act.run, update_of_ne hjw]

theorem load_array {a : Ty} (ha : LoadSpec (P := P) a (load a)) :
    LoadSpec (P := P) (.array a) (load (.array a)) := by
  intro prog v h c rest U hH hv hi hU
  simp only [ldB]
  have hU' : h.length + ((v.toList.map (cellsB a)).sum + 1) ≤ U := hU
  have hsr : (v.toList.reverse.map (cellsB a)).sum = (v.toList.map (cellsB a)).sum := by
    simp [List.map_reverse, List.sum_reverse]
  have hsc : (v.toList.map fun x => cellsB a x).sum = (v.toList.reverse.map (cellsB a)).sum := by
    simp [List.map_reverse, List.sum_reverse]
  unfold load
  refine Sat.act_seq (by budget) ?_
  set c₁ := Act.run (.push .work (.mk 2)) c with hc₁
  have hH₁ : HeapAt h c₁ := hH.frame (by simp [hc₁, Act.run]) (by simp [hc₁, Act.run])
    (by simp [hc₁, Act.run])
  have hi₁ : c₁.stk .inp = serElems a v.toList.reverse ++ .tag .nil :: rest := by
    simp [hc₁, Act.run, hi, ser, serElems]
  refine Sat.seq_le (readElems_sat (U := U) ha v.toList.reverse hH₁ hv hi₁ (by rw [hsr]; omega))
    (by budget) fun c₂ ⟨hr₂, h₁, ps, hH₂, hl₂, hps, hR, hi₂, hw₂, hj₂⟩ => ?_
  have hlen : v.toList.reverse.length = ps.length := hR.length_eq
  have hw₂' : c₂.stk .work = encFields ps.reverse ++ .mk 2 :: c.stk .work := by
    rw [hw₂]; simp [hc₁, Act.run]
  have hLf : (encFields ps.reverse).length ≤ v.size * (U + 1) := by
    have := length_encFields_le ps.reverse fun p hp => hps p (List.mem_reverse.1 hp)
    simp only [List.length_reverse] at this hlen
    simpa [← hlen] using this
  have hbnd := allocBound_mono hLf (by simp only [List.length_append]; omega :
    (h ++ h₁).length ≤ U)
  refine (alloc_sat .arr hH₂ hr₂ hw₂').mono (by budget)
    fun c' ⟨hr, l, hH', hl, hlU, hw', hj'⟩ =>
      ⟨hr, h₁ ++ [⟨l, .arr, ps.reverse⟩], l, by simpa [List.append_assoc] using hH',
        by simp only [cellsB, List.length_append, List.length_singleton]; rw [hsc]; omega,
        by simp only [List.length_append] at hlU; omega, ?_, ?_, ?_, ?_⟩
  · have hR' : RepList (h ++ h₁) a v.toList ps.reverse := by
      have := List.rel_reverse hR
      simpa [RepList] using this
    obtain ⟨hl₁, hl₂⟩ := List.forall₂_iff_get.1 hR'
    have r : Rep (h ++ h₁ ++ [⟨l, .arr, ps.reverse⟩]) (.array a) v (ofBits l) :=
      .arr (cellAt_new hl) (by rw [← hl₁]; simp) fun i hi hv' => by
        have := (hl₂ i (by simpa using hv') hi).mono (h' := [⟨l, .arr, ps.reverse⟩])
        simpa using this
    simpa [List.append_assoc] using r
  · rw [hj' .inp (by decide) (by decide) (by decide), hi₂]
  · rw [hw']
  · intro j hjh hjc hji hjw
    rw [hj' j hjh hjc hjw, hj₂ j hjh hjc hji hjw]
    simp [hc₁, Act.run, update_of_ne hjw]

/-- **Loading**: `load t` meets its specification for every type. -/
theorem load_sat : ∀ t : Ty, LoadSpec (P := P) t (load t)
  | .unit => load_unit
  | .bool => load_bool
  | .nat => load_nat
  | .prod a b => load_prod (load_sat a) (load_sat b)
  | .option a => load_option (load_sat a)
  | .list a => load_list (load_sat a)
  | .array a => load_array (load_sat a)

/-! ### Polynomial bounds -/

theorem sum_le_wt {α : Type} (f g : α → ℕ) (w : ℕ) (xs : List α) (h : ∀ x ∈ xs, f x ≤ w * g x) :
    (xs.map f).sum ≤ w * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    have h₁ := h x (by simp)
    have h₂ := ih fun y hy => h y (by simp [hy])
    omega

/-- **The number of cells** of a loaded value is at most `wt t * (L + 1)`. -/
theorem cellsB_le : ∀ (t : Ty) (v : t.denote), cellsB t v ≤ wt t * ((ser t v).length + 1)
  | .unit, _ => by simp [cellsB, wt, ser]
  | .bool, _ => by simp [cellsB, wt, ser]
  | .nat, _ => by simp [cellsB, wt, ser]
  | .prod a b, v => by
    have h₁ := cellsB_le a v.1
    have h₂ := cellsB_le b v.2
    simp only [cellsB, wt, ser, List.length_append]
    nlinarith
  | .option a, none => by
    have := one_le_wt a
    simp only [cellsB, wt, ser, List.length_singleton]
    nlinarith
  | .option a, some x => by
    have h₁ := cellsB_le a x
    simp only [cellsB, wt, ser, List.length_cons]
    nlinarith
  | .list a, xs => by
    have h₁ := sum_le_wt (fun x => cellsB a x + 1) (fun x => (ser a x).length + 1) (wt a + 1) xs
      fun x _ => by have := cellsB_le a x; nlinarith
    simp only [cellsB, wt, ser_list, List.length_append, length_serElems, List.length_singleton]
    nlinarith
  | .array a, v => by
    have h₁ := sum_le_wt (cellsB a) (fun x => (ser a x).length + 1) (wt a) v.toList.reverse
      fun x _ => cellsB_le a x
    have e₁ : (v.toList.reverse.map (cellsB a)).sum = (v.toList.map (cellsB a)).sum := by
      simp [List.map_reverse, List.sum_reverse]
    simp only [cellsB, wt, ser_array, List.length_append, length_serElems, List.length_singleton]
    nlinarith

/-- A bound on the steps of loading one constructor, for addresses of length at most `U`. -/
def PL (U : ℕ) : ℕ := allocBound ((U + 1) * (U + 2)) U + 30 * U + 100

theorem PL_ge (U : ℕ) : 30 * U + 100 ≤ PL U := by unfold PL; omega

theorem length_le_sum_succ {α : Type} (g : α → ℕ) (xs : List α) :
    xs.length ≤ (xs.map fun x => g x + 1).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

theorem le_wtP {x w L P : ℕ} (hx : x ≤ P) (hw : 1 ≤ w) : x ≤ w * (L + 1) * P := by
  have : 1 ≤ w * (L + 1) := Nat.mul_le_mul hw (Nat.succ_le_succ (Nat.zero_le L))
  calc x ≤ 1 * P := by omega
    _ ≤ w * (L + 1) * P := Nat.mul_le_mul_right P this

theorem le_mul_of_parts {x X Z P : ℕ} (hx : x ≤ X * P) (hk : X ≤ Z) : x ≤ Z * P :=
  hx.trans (Nat.mul_le_mul_right P hk)

theorem wtP_add {x y o X Y Z P : ℕ} (hx : x ≤ X * P) (hy : y ≤ Y * P) (ho : o ≤ P)
    (hk : X + Y + 1 ≤ Z) : x + y + o ≤ Z * P := by
  have := Nat.mul_le_mul_right P hk
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at this
  omega

theorem wtP_add1 {x o X Z P : ℕ} (hx : x ≤ X * P) (ho : o ≤ P) (hk : X + 1 ≤ Z) :
    x + o ≤ Z * P := by
  have := Nat.mul_le_mul_right P hk
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem sum_wtP {α : Type} (ld g : α → ℕ) (w P : ℕ) (xs : List α)
    (h : ∀ x ∈ xs, ld x + 9 ≤ (w * g x + 1) * P) :
    (xs.map fun x => ld x + 8 + 1).sum ≤ (w * (xs.map g).sum + xs.length) * P := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h₁ := h x (by simp)
    have h₂ := ih fun y hy => h y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.add_mul,
      Nat.one_mul] at h₁ h₂ ⊢
    omega

/-- **The steps of loading** are at most `wt t * (L + 1) * PL U` for `L ≤ U`. -/
theorem ldB_le : ∀ (t : Ty) (v : t.denote) (U : ℕ), (ser t v).length ≤ U →
    ldB t v U ≤ wt t * ((ser t v).length + 1) * PL U
  | .unit, _, U, _ => by
    have := allocBound_mono (a := 0) (b := (U + 1) * (U + 2)) (Nat.zero_le _) (le_refl U)
    simp only [ldB]
    exact le_wtP (by unfold PL; omega) (one_le_wt _)
  | .bool, _, U, _ => by
    have := allocBound_mono (a := 0) (b := (U + 1) * (U + 2)) (Nat.zero_le _) (le_refl U)
    simp only [ldB]
    exact le_wtP (by unfold PL; omega) (one_le_wt _)
  | .nat, n, U, hL => by
    have hl : (toBits n).length + 1 ≤ U + 1 := by simp [ser] at hL; omega
    have := allocBound_mono (a := (toBits n).length + 1) (b := (U + 1) * (U + 2)) (by nlinarith)
      (le_refl U)
    simp only [ldB]
    exact le_wtP (by unfold PL; omega) (one_le_wt _)
  | .prod a b, v, U, hL => by
    simp only [ser, List.length_append] at hL
    have h₁ := ldB_le a v.1 U (by omega)
    have h₂ := ldB_le b v.2 U (by omega)
    have := allocBound_mono (a := 2 * U + 2) (b := (U + 1) * (U + 2)) (by nlinarith) (le_refl U)
    have hP : 4 * (6 * U + 9) + allocBound (2 * U + 2) U + 10 ≤ PL U := by unfold PL; omega
    have hk : wt a * ((ser a v.1).length + 1) + wt b * ((ser b v.2).length + 1) + 1 ≤
        (wt a + wt b + 1) * ((ser a v.1).length + (ser b v.2).length + 1) := by
      nlinarith [Nat.zero_le (wt a * (ser b v.2).length), Nat.zero_le (wt b * (ser a v.1).length)]
    have := wtP_add h₁ h₂ hP hk
    simp only [ldB, wt, ser, List.length_append]
    omega
  | .option a, none, U, _ => by
    have := allocBound_mono (a := 0) (b := (U + 1) * (U + 2)) (Nat.zero_le _) (le_refl U)
    simp only [ldB]
    exact le_wtP (by unfold PL; omega) (one_le_wt _)
  | .option a, some x, U, hL => by
    simp only [ser, List.length_cons] at hL
    have h₁ := ldB_le a x U (by omega)
    have := allocBound_mono (a := U + 1) (b := (U + 1) * (U + 2)) (by nlinarith) (le_refl U)
    have hP : 2 * (6 * U + 9) + allocBound (U + 1) U + 10 ≤ PL U := by unfold PL; omega
    have hk : wt a * ((ser a x).length + 1) + 1 ≤ (wt a + 1) * ((ser a x).length + 1 + 1) := by
      nlinarith
    have := wtP_add1 h₁ hP hk
    simp only [ldB, wt, ser, List.length_cons]
    omega
  | .list a, xs, U, hL => by
    rw [ser_list, List.length_append, length_serElems, List.length_singleton] at hL
    obtain ⟨S, hS⟩ : ∃ S, S = (xs.map fun x => (ser a x).length + 1).sum := ⟨_, rfl⟩
    rw [← hS] at hL
    have hk : xs.length ≤ S := by rw [hS]; exact length_le_sum_succ _ xs
    have h9 : 9 ≤ PL U := by unfold PL; omega
    have hel : ∀ x ∈ xs, ldB a x U + 9 ≤ (wt a * ((ser a x).length + 1) + 1) * PL U :=
      fun x hx => by
        have hx' : (ser a x).length + 1 ≤ S := by
          rw [hS]; exact le_sum_of_mem_nat (List.mem_map.2 ⟨x, hx, rfl⟩)
        have h₁ := ldB_le a x U (by omega)
        rw [Nat.add_mul, Nat.one_mul]; omega
    have hsum := sum_wtP (fun x => ldB a x U) (fun x => (ser a x).length + 1) (wt a) (PL U) xs hel
    beta_reduce at hsum
    rw [← hS] at hsum
    have h₂ := allocBound_mono (a := 0) (b := (U + 1) * (U + 2)) (Nat.zero_le _) (le_refl U)
    have h₃ := allocBound_mono (a := 2 * U + 2) (b := (U + 1) * (U + 2)) (by nlinarith)
      (le_refl U)
    have hC : 4 * (6 * U + 9) + allocBound (2 * U + 2) U + 11 ≤ PL U := by unfold PL; omega
    have hlen := Nat.mul_le_mul_left xs.length hC
    have hrest : 9 + allocBound 0 U + 2 * (6 * U + 9) + 20 ≤ PL U := by unfold PL; omega
    have hk₂ : wt a * S + xs.length + xs.length + 1 ≤ (wt a + 2) * (S + 1 + 1) := by nlinarith
    have e : (wt a * S + xs.length + xs.length + 1) * PL U =
        (wt a * S + xs.length) * PL U + xs.length * PL U + PL U := by ring
    simp only [ldB, wt, ser_list, List.length_append, length_serElems, List.length_singleton]
    rw [← hS]
    refine le_mul_of_parts (X := wt a * S + xs.length + xs.length + 1) ?_ hk₂
    rw [e]; omega
  | .array a, v, U, hL => by
    rw [ser_array, List.length_append, length_serElems, List.length_singleton] at hL
    obtain ⟨S, hS⟩ : ∃ S, S = (v.toList.reverse.map fun x => (ser a x).length + 1).sum :=
      ⟨_, rfl⟩
    rw [← hS] at hL
    have hk : v.toList.reverse.length ≤ S := by rw [hS]; exact length_le_sum_succ _ _
    have hsz : v.size ≤ S := by
      have := hk; simp only [List.length_reverse, Array.length_toList] at this; exact this
    have h9 : 9 ≤ PL U := by unfold PL; omega
    have hel : ∀ x ∈ v.toList.reverse,
        ldB a x U + 9 ≤ (wt a * ((ser a x).length + 1) + 1) * PL U := fun x hx => by
      have hx' : (ser a x).length + 1 ≤ S := by
        rw [hS]; exact le_sum_of_mem_nat (List.mem_map.2 ⟨x, hx, rfl⟩)
      have h₁ := ldB_le a x U (by omega)
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hsum := sum_wtP (fun x => ldB a x U) (fun x => (ser a x).length + 1) (wt a) (PL U)
      v.toList.reverse hel
    beta_reduce at hsum
    rw [← hS] at hsum
    have h₂ := allocBound_mono (a := v.size * (U + 1)) (b := (U + 1) * (U + 2))
      (Nat.mul_le_mul (by omega) (by omega)) (le_refl U)
    have hrest : 9 + allocBound (v.size * (U + 1)) U + 4 ≤ PL U := by unfold PL; omega
    have hk₂ : wt a * S + v.toList.reverse.length + 1 ≤ (wt a + 2) * (S + 1 + 1) := by nlinarith
    have e : (wt a * S + v.toList.reverse.length + 1) * PL U =
        (wt a * S + v.toList.reverse.length) * PL U + PL U := by ring
    simp only [ldB, wt, ser_array, List.length_append, length_serElems, List.length_singleton]
    rw [← hS]
    refine le_mul_of_parts (X := wt a * S + v.toList.reverse.length + 1) ?_ hk₂
    rw [e]; omega

end GraphIso.TM
