module

public import GraphIso.TM.Num

/-!
# Arithmetic on stacks

Stage 17b (`PLAN-17.md` §5). Serial arithmetic on the numbers of `GraphIso.TM.Num`: every
operation runs the bit processor `zipNum f`, which steps through two numbers together, as
`zipL f` does on their bit lists (`zipNum_sat`). With `M = max |xs| |ys|` for numbers `xs`,
`ys` on `a`, `b` (both are consumed; the stacks `o`, `t` must differ from them and from each
other):

* `addNum a b o t` pushes `addBits xs ys`, of value `ofBits xs + ofBits ys` and length `M + 1`,
  onto `o` (`addNum_sat`, `23 M + 37` steps);
* `subNum a b o t` pushes `subBits xs ys`, of value `ofBits xs - ofBits ys` (truncated) and
  length at most `M` (`subNum_sat`, `23 M + 37` steps);
* `ltNum a b o t` pushes the bit `decide (ofBits xs < ofBits ys)` (`ltNum_sat`, `19 M + 33`
  steps);
* `eqNum a b o t` pushes the bit `decide (ofBits xs = ofBits ys)` (`eqNum_sat`, `19 M + 34`
  steps);
* `incNum a b o t` and `decNum a b o t` push `addBits xs [true]` and `subBits xs [true]`, of
  values `ofBits xs + 1` and `ofBits xs - 1`, onto `o`, using `b` and `t` as temporaries
  (`incNum_sat`, `decNum_sat`, `23 |xs| + 64` steps).

`zipNum f c₀ a b o` leaves the output bits on `o` most significant first, with the final carry on
top, so the sum is ready to be moved back (`moveBits`) and the borrow or comparator flag to be
popped.
-/

@[expose] public section

namespace GraphIso.TM

open Function

variable {K P : Type} [DecidableEq K] {prog : Program K Sym Rg P}

/-! ### The bit processor -/

/-- Read the next bit of the number on `a` into register `r`: pop it, or at the `nd` (which
stays) read `false`. -/
def readBit (a : K) (r : Fin Rg) : Code K Sym Rg P :=
  .ite (isBit r) (.act (.pop a r)) (.act (.set r (some (.bit false))))

theorem readBit_sat {a : K} {r : Fin Rg} {c : Cfg K Sym Rg} {l : List Bool} {rest : List Sym}
    (hr : c.regs r = (c.stk a).head?) (ha : c.stk a = bits l ++ .nd :: rest) :
    Sat prog (readBit a r) c 2 fun c' =>
      c' = ⟨update c.regs r (some (.bit (hd l))), update c.stk a (bits (tl l) ++ .nd :: rest)⟩ := by
  cases l with
  | nil =>
    refine Sat.ite_false (isBit_eval_nd (by simp [hr, ha])) (Sat.act_le le_rfl ?_)
    simp [Act.run]
    simpa using ha
  | cons x l =>
    refine Sat.ite_true (isBit_eval_bit x (by simp [hr, ha])) (Sat.act_le le_rfl ?_)
    simp [Act.run, ha]

/-- Branch on the bit in register `r`. -/
def bitCase (r : Fin Rg) (g : Bool → Code K Sym Rg P) : Code K Sym Rg P :=
  .ite (.is r (some (.bit true))) (g true) (g false)

theorem bitCase_sat {r : Fin Rg} {g : Bool → Code K Sym Rg P} {c : Cfg K Sym Rg} {v : Bool}
    {t : ℕ} {Q : Cfg K Sym Rg → Prop} (h : c.regs r = some (.bit v)) (h' : Sat prog (g v) c t Q) :
    Sat prog (bitCase r g) c (t + 1) Q := by
  cases v
  · exact Sat.ite_false (by simp [Cond.eval, h]) h'
  · exact Sat.ite_true (by simp [Cond.eval, h]) h'

/-- One step of the bit processor: from the bits in registers `0`, `1` and the carry in
register `2`, push the output bit of `f` onto `o` and set the carry. -/
def zipTable (f : Bool → Bool → Bool → Bool × Bool) (o : K) : Code K Sym Rg P :=
  bitCase 0 fun x => bitCase 1 fun y => bitCase 2 fun c =>
    .seq (.act (.push o (.bit (f x y c).1))) (.act (.set 2 (some (.bit (f x y c).2))))

theorem zipTable_sat (f : Bool → Bool → Bool → Bool × Bool) (o : K) {c : Cfg K Sym Rg}
    {x y z : Bool} (h₀ : c.regs 0 = some (.bit x)) (h₁ : c.regs 1 = some (.bit y))
    (h₂ : c.regs 2 = some (.bit z)) :
    Sat prog (zipTable f o) c 6 fun c' =>
      c' = ⟨update c.regs 2 (some (.bit (f x y z).2)),
        update c.stk o (.bit (f x y z).1 :: c.stk o)⟩ :=
  bitCase_sat h₀ (bitCase_sat h₁ (bitCase_sat h₂ (Sat.act_seq (by omega) (Sat.act_le le_rfl rfl))))

/-- The loop body of the bit processor. -/
def zipBody (f : Bool → Bool → Bool → Bool × Bool) (a b o : K) : Code K Sym Rg P :=
  .seq (readBit a 0)
    (.seq (readBit b 1) (.seq (zipTable f o) (.seq (.act (.peek a 0)) (.act (.peek b 1)))))

/-- The bit processor: run `f` through the numbers on `a` and `b` from the carry `c₀`,
consuming them, and push the output bits (most significant on top, with an `nd` under them) and
then the final carry onto `o`. -/
def zipNum (f : Bool → Bool → Bool → Bool × Bool) (c₀ : Bool) (a b o : K) : Code K Sym Rg P :=
  .seq (.act (.push o .nd))
    (.seq (.act (.set 2 (some (.bit c₀))))
      (.seq (.act (.peek a 0))
        (.seq (.act (.peek b 1))
          (.seq (.loop ((isBit 0).or (isBit 1)) (zipBody f a b o))
            (.seq (.act (.pop a 0))
              (.seq (.act (.pop b 1))
                (.seq (.act (.set 0 none))
                  (.seq (.act (.set 1 none))
                    (.seq (.act (.pushReg o 2)) (.act (.set 2 none)))))))))))

theorem isBit_eval_head {v : Regs Sym Rg} {r : Fin Rg} {l : List Bool} {rest : List Sym}
    (h : v r = (bits l ++ .nd :: rest).head?) : (isBit r).eval v = !l.isEmpty := by
  cases l with
  | nil => exact isBit_eval_nd (by simpa using h)
  | cons x l => exact isBit_eval_bit x (by simpa using h)

theorem zipNum_sat (f : Bool → Bool → Bool → Bool × Bool) (c₀ : Bool) {a b o : K} (hab : a ≠ b)
    (hao : a ≠ o) (hbo : b ≠ o) {c : Cfg K Sym Rg} {xs ys : List Bool} {ra rb : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra)
    (hb : c.stk b = bits ys ++ .nd :: rb) :
    Sat prog (zipNum f c₀ a b o) c (17 * max xs.length ys.length + 21) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧ c'.stk b = rb ∧
        c'.stk o = .bit (zipL f xs ys c₀).2 :: bits (zipL f xs ys c₀).1.reverse ++ .nd :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ o → c'.stk j = c.stk j := by
  rw [empty_eq_rv] at hv ⊢
  have hloop := Sat.loop (prog := prog) (b := (isBit 0).or (isBit 1)) (x := zipBody f a b o)
    (t := 16)
    (I := fun m c₁ => ∃ xs' ys' z out, max xs'.length ys'.length = m ∧
      zipL f xs ys c₀ = (out.reverse ++ (zipL f xs' ys' z).1, (zipL f xs' ys' z).2) ∧
      c₁.regs = rv (c₁.stk a).head? (c₁.stk b).head? (some (.bit z)) none ∧
      c₁.stk a = bits xs' ++ .nd :: ra ∧ c₁.stk b = bits ys' ++ .nd :: rb ∧
      c₁.stk o = bits out ++ .nd :: c.stk o ∧ ∀ j, j ≠ a → j ≠ b → j ≠ o → c₁.stk j = c.stk j)
    (Q := fun c₁ => c₁.regs = rv (some .nd) (some .nd) (some (.bit (zipL f xs ys c₀).2)) none ∧
      c₁.stk a = .nd :: ra ∧ c₁.stk b = .nd :: rb ∧
      c₁.stk o = bits (zipL f xs ys c₀).1.reverse ++ .nd :: c.stk o ∧
      ∀ j, j ≠ a → j ≠ b → j ≠ o → c₁.stk j = c.stk j)
    (fun m c₁ ⟨xs', ys', z, out, hm, hz, hr, ha₁, hb₁, ho₁, hj₁⟩ => by
      have hne : xs' ≠ [] ∨ ys' ≠ [] := by
        by_contra hc
        push Not at hc
        simp [hc.1, hc.2] at hm
      refine ⟨?_, ?_⟩
      · rw [Cond.or_eval, isBit_eval_head (l := xs') (rest := ra) (by simp [hr, ha₁]),
          isBit_eval_head (l := ys') (rest := rb) (by simp [hr, hb₁])]
        rcases hne with h | h <;> simp [h]
      unfold zipBody
      refine Sat.seq_le (readBit_sat (by simp [hr]) ha₁) (by omega) fun c₂ hc₂ => ?_
      subst hc₂
      refine Sat.seq_le (readBit_sat (l := ys') (rest := rb) (by simp [hr, update_of_ne hab.symm])
        (by simp [update_of_ne hab.symm, hb₁])) (by omega) fun c₃ hc₃ => ?_
      subst hc₃
      refine Sat.seq_le (zipTable_sat f o (x := hd xs') (y := hd ys') (z := z) (by simp [hr])
        (by simp) (by simp [hr])) (by omega) fun c₄ hc₄ => ?_
      subst hc₄
      refine Sat.act_seq (by omega) (Sat.act_le (by omega) ?_)
      refine ⟨tl xs', tl ys', (f (hd xs') (hd ys') z).2, (f (hd xs') (hd ys') z).1 :: out,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [tl, List.length_tail]; omega
      · rw [hz, zipL_step f xs' ys' z hne]; simp
      · simp [Act.run, hr]
      · simp [Act.run, update_of_ne hao, update_of_ne hab]
      · simp [Act.run, update_of_ne hbo]
      · simp [Act.run, ho₁, update_of_ne (Ne.symm hbo), update_of_ne (Ne.symm hao)]
      · intro j hja hjb hjo
        simp [Act.run, update_of_ne hja, update_of_ne hjb, update_of_ne hjo, hj₁ j hja hjb hjo])
    (fun c₁ ⟨xs', ys', z, out, hm, hz, hr, ha₁, hb₁, ho₁, hj₁⟩ => by
      obtain ⟨rfl, rfl⟩ : xs' = [] ∧ ys' = [] := by
        constructor <;> apply List.eq_nil_of_length_eq_zero <;> omega
      simp only [zipL_nil, List.append_nil] at hz
      rw [hz]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Cond.or_eval, isBit_eval_nd (by simp [hr, ha₁]), isBit_eval_nd (by simp [hr, hb₁])]
        rfl
      · simp [hr, ha₁, hb₁]
      · simpa using ha₁
      · simpa using hb₁
      · simpa using ho₁
      · exact hj₁)
  unfold zipNum
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega)
    (Sat.act_seq (by omega) ?_)))
  refine Sat.seq_le (hloop (max xs.length ys.length) _
    ⟨xs, ys, c₀, [], rfl, by simp, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
    fun c₃ ⟨hr₃, ha₃, hb₃, ho₃, hj₃⟩ => ?_
  · simp [Act.run, hv]
  · simp [Act.run, ha, update_of_ne hao]
  · simp [Act.run, hb, update_of_ne hbo]
  · simp [Act.run]
  · intro j hja hjb hjo; simp [Act.run, update_of_ne hjo]
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega)
    (Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_le (by omega) ?_)))))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Act.run, hr₃]
  · simp [Act.run, ha₃, update_of_ne hab, update_of_ne hao]
  · simp [Act.run, hb₃, update_of_ne hbo, update_of_ne (Ne.symm hab)]
  · simp [Act.run, ho₃, hr₃, update_of_ne (Ne.symm hbo), update_of_ne (Ne.symm hao)]
  · intro j hja hjb hjo
    simp [Act.run, update_of_ne hja, update_of_ne hjb, update_of_ne hjo, hj₃ j hja hjb hjo]

/-! ### Operations -/

/-- Add the numbers on `a` and `b` onto `o`, through `t`. -/
def addNum (a b o t : K) : Code K Sym Rg P := .seq (zipNum fullAdd false a b t) (moveBits t o)

theorem addNum_sat {a b o t : K} (hab : a ≠ b) (hao : a ≠ o) (hat : a ≠ t) (hbo : b ≠ o)
    (hbt : b ≠ t) (hot : o ≠ t) {c : Cfg K Sym Rg} {xs ys : List Bool} {ra rb : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra)
    (hb : c.stk b = bits ys ++ .nd :: rb) :
    Sat prog (addNum a b o t) c (23 * max xs.length ys.length + 37) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧ c'.stk b = rb ∧
        c'.stk o = bits (addBits xs ys) ++ .nd :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ o → c'.stk j = c.stk j := by
  refine Sat.seq_le (zipNum_sat fullAdd false hab hat hbt hv ha hb) (by omega)
    fun c₁ ⟨hr₁, ha₁, hb₁, ht₁, hj₁⟩ => ?_
  have ht₁' : c₁.stk t = bits (addBits xs ys).reverse ++ .nd :: c.stk t := by
    rw [ht₁]; simp [addBits]
  refine (moveBits_sat (Ne.symm hot) hr₁ ht₁').mono (by simp [length_addBits]; omega)
    fun c₂ ⟨hr₂, ht₂, ho₂, hj₂⟩ => ⟨hr₂, ?_, ?_, ?_, fun j hja hjb hjo => ?_⟩
  · rw [hj₂ a hat hao, ha₁]
  · rw [hj₂ b hbt hbo, hb₁]
  · rw [ho₂, hj₁ o (Ne.symm hao) (Ne.symm hbo) hot]; simp
  · by_cases hjt : j = t
    · subst hjt; exact ht₂
    rw [hj₂ j hjt hjo, hj₁ j hja hjb hjt]

/-- Subtract (truncated) the number on `b` from the one on `a`, onto `o`, through `t`. -/
def subNum (a b o t : K) : Code K Sym Rg P :=
  .seq (zipNum fullSub false a b t)
    (.seq (.act (.pop t 0))
      (.ite (.is 0 (some (.bit true)))
        (.seq (.act (.set 0 none)) (.seq (dropNum t) (.act (.push o .nd))))
        (.seq (.act (.set 0 none)) (moveBits t o))))

theorem subNum_sat {a b o t : K} (hab : a ≠ b) (hao : a ≠ o) (hat : a ≠ t) (hbo : b ≠ o)
    (hbt : b ≠ t) (hot : o ≠ t) {c : Cfg K Sym Rg} {xs ys : List Bool} {ra rb : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra)
    (hb : c.stk b = bits ys ++ .nd :: rb) :
    Sat prog (subNum a b o t) c (23 * max xs.length ys.length + 37) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧ c'.stk b = rb ∧
        c'.stk o = bits (subBits xs ys) ++ .nd :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ o → c'.stk j = c.stk j := by
  refine Sat.seq_le (zipNum_sat fullSub false hab hat hbt hv ha hb) (by omega)
    fun c₁ ⟨hr₁, ha₁, hb₁, ht₁, hj₁⟩ => ?_
  rw [empty_eq_rv] at hr₁
  refine Sat.act_seq (by omega) ?_
  have hlen := length_zipL fullSub xs ys false
  set out := (zipL fullSub xs ys false).1 with hout
  cases hw : (zipL fullSub xs ys false).2
  · have hsub : subBits xs ys = out := by simp [subBits, hw, hout]
    refine Sat.ite_false_le (by simp [Act.run, Cond.eval, hr₁, ht₁, hw]) (by omega)
      (Sat.act_seq (by omega) ?_)
    have hv₂ : (Act.run (.set 0 none) (Act.run (.pop t 0) c₁)).regs = Regs.empty := by
      simp [Act.run, hr₁, empty_eq_rv]
    have ht₂ : (Act.run (.set 0 none) (Act.run (.pop t 0) c₁)).stk t =
        bits out.reverse ++ .nd :: c.stk t := by
      simp [Act.run, ht₁]
    refine (moveBits_sat (Ne.symm hot) hv₂ ht₂).mono (by simp; omega)
      fun c₂ ⟨hr₂, ht₃, ho₂, hj₂⟩ => ⟨hr₂, ?_, ?_, ?_, fun j hja hjb hjo => ?_⟩
    · rw [hj₂ a hat hao]; simp [Act.run, update_of_ne hat, ha₁]
    · rw [hj₂ b hbt hbo]; simp [Act.run, update_of_ne hbt, hb₁]
    · rw [ho₂, hsub]; simp [Act.run, update_of_ne hot, hj₁ o (Ne.symm hao) (Ne.symm hbo) hot]
    · by_cases hjt : j = t
      · subst hjt; exact ht₃
      rw [hj₂ j hjt hjo]; simp [Act.run, update_of_ne hjt, hj₁ j hja hjb hjt]
  · have hsub : subBits xs ys = [] := by simp [subBits, hw]
    refine Sat.ite_true_le (by simp [Act.run, Cond.eval, hr₁, ht₁, hw]) (by omega)
      (Sat.act_seq (by omega) ?_)
    have hv₂ : (Act.run (.set 0 none) (Act.run (.pop t 0) c₁)).regs = Regs.empty := by
      simp [Act.run, hr₁, empty_eq_rv]
    have ht₂ : (Act.run (.set 0 none) (Act.run (.pop t 0) c₁)).stk t =
        bits out.reverse ++ .nd :: c.stk t := by
      simp [Act.run, ht₁]
    refine Sat.seq_le (dropNum_sat hv₂ ht₂) (by simp; omega)
      fun c₂ ⟨hr₂, ht₃, hj₂⟩ =>
        Sat.act_le (by simp; omega) ⟨hr₂, ?_, ?_, ?_, fun j hja hjb hjo => ?_⟩
    · simp [Act.run, update_of_ne hao, hj₂ a hat, update_of_ne hat, ha₁]
    · simp [Act.run, update_of_ne hbo, hj₂ b hbt, update_of_ne hbt, hb₁]
    · rw [hsub]
      simp [Act.run, hj₂ o hot, update_of_ne hot, hj₁ o (Ne.symm hao) (Ne.symm hbo) hot]
    · by_cases hjt : j = t
      · subst hjt; simp [Act.run, update_of_ne (Ne.symm hot), ht₃]
      simp [Act.run, update_of_ne hjo, hj₂ j hjt, update_of_ne hjt, hj₁ j hja hjb hjt]

/-- Push the bit `ofBits xs < ofBits ys` for the numbers on `a` and `b` onto `o`, through `t`. -/
def ltNum (a b o t : K) : Code K Sym Rg P :=
  .seq (zipNum fullSub false a b t)
    (.seq (.act (.pop t 0)) (.seq (.act (.pushReg o 0)) (.seq (.act (.set 0 none)) (dropNum t))))

theorem ltNum_sat {a b o t : K} (hab : a ≠ b) (hao : a ≠ o) (hat : a ≠ t) (hbo : b ≠ o)
    (hbt : b ≠ t) (hot : o ≠ t) {c : Cfg K Sym Rg} {xs ys : List Bool} {ra rb : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra)
    (hb : c.stk b = bits ys ++ .nd :: rb) :
    Sat prog (ltNum a b o t) c (19 * max xs.length ys.length + 33) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧ c'.stk b = rb ∧
        c'.stk o = .bit (decide (ofBits xs < ofBits ys)) :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ o → c'.stk j = c.stk j := by
  refine Sat.seq_le (zipNum_sat fullSub false hab hat hbt hv ha hb) (by omega)
    fun c₁ ⟨hr₁, ha₁, hb₁, ht₁, hj₁⟩ => ?_
  rw [empty_eq_rv] at hr₁
  refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega) ?_))
  have hlen := length_zipL fullSub xs ys false
  have hv₂ : (Act.run (.set 0 none) (Act.run (.pushReg o 0) (Act.run (.pop t 0) c₁))).regs =
      Regs.empty := by
    simp [Act.run, hr₁, empty_eq_rv]
  have ht₂ : (Act.run (.set 0 none) (Act.run (.pushReg o 0) (Act.run (.pop t 0) c₁))).stk t =
      bits (zipL fullSub xs ys false).1.reverse ++ .nd :: c.stk t := by
    simp [Act.run, ht₁, update_of_ne (Ne.symm hot)]
  refine (dropNum_sat hv₂ ht₂).mono (by simp; omega)
    fun c₂ ⟨hr₂, ht₃, hj₂⟩ => ⟨hr₂, ?_, ?_, ?_, fun j hja hjb hjo => ?_⟩
  · simp [Act.run, hj₂ a hat, update_of_ne hao, update_of_ne hat, ha₁]
  · simp [Act.run, hj₂ b hbt, update_of_ne hbo, update_of_ne hbt, hb₁]
  · simp [Act.run, hj₂ o hot, ht₁, hr₁, update_of_ne hot, zipL_sub_lt,
      hj₁ o (Ne.symm hao) (Ne.symm hbo) hot]
  · by_cases hjt : j = t
    · subst hjt; rw [ht₃]
    simp [Act.run, hj₂ j hjt, update_of_ne hjo, update_of_ne hjt, hj₁ j hja hjb hjt]

/-- Push the bit `ofBits xs = ofBits ys` for the numbers on `a` and `b` onto `o`, through `t`. -/
def eqNum (a b o t : K) : Code K Sym Rg P :=
  .seq (zipNum diffBit false a b t)
    (.seq (.act (.pop t 0))
      (.seq (.ite (.is 0 (some (.bit true))) (.act (.push o (.bit false)))
          (.act (.push o (.bit true))))
        (.seq (.act (.set 0 none)) (dropNum t))))

theorem eqNum_sat {a b o t : K} (hab : a ≠ b) (hao : a ≠ o) (hat : a ≠ t) (hbo : b ≠ o)
    (hbt : b ≠ t) (hot : o ≠ t) {c : Cfg K Sym Rg} {xs ys : List Bool} {ra rb : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra)
    (hb : c.stk b = bits ys ++ .nd :: rb) :
    Sat prog (eqNum a b o t) c (19 * max xs.length ys.length + 34) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧ c'.stk b = rb ∧
        c'.stk o = .bit (decide (ofBits xs = ofBits ys)) :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ b → j ≠ o → c'.stk j = c.stk j := by
  refine Sat.seq_le (zipNum_sat diffBit false hab hat hbt hv ha hb) (by omega)
    fun c₁ ⟨hr₁, ha₁, hb₁, ht₁, hj₁⟩ => ?_
  rw [empty_eq_rv] at hr₁
  refine Sat.act_seq (by omega) ?_
  have hlen := length_zipL diffBit xs ys false
  set c₂ := Act.run (.pop t 0) c₁ with hc₂
  have hr₂ : c₂.regs = rv (some (.bit (zipL diffBit xs ys false).2)) none none none := by
    simp [hc₂, Act.run, hr₁, ht₁]
  have ht₂ : c₂.stk t = bits (zipL diffBit xs ys false).1.reverse ++ .nd :: c.stk t := by
    simp [hc₂, Act.run, ht₁]
  have hite : Sat prog (.ite (.is 0 (some (.bit true))) (.act (.push o (.bit false)))
      (.act (.push o (.bit true)))) c₂ 2
      (· = ⟨c₂.regs, update c₂.stk o (.bit (decide (ofBits xs = ofBits ys)) :: c₂.stk o)⟩) := by
    cases hw : (zipL diffBit xs ys false).2
    · refine Sat.ite_false (by simp [Cond.eval, hr₂, hw]) (Sat.act_le le_rfl ?_)
      rw [zipL_diff_false] at hw
      simp at hw
      simp [Act.run, hw]
    · refine Sat.ite_true (by simp [Cond.eval, hr₂, hw]) (Sat.act_le le_rfl ?_)
      rw [zipL_diff_false] at hw
      simp at hw
      simp [Act.run, hw]
  refine Sat.seq_le hite (by omega) fun c₃ hc₃ => ?_
  subst hc₃
  refine Sat.act_seq (by omega) ?_
  have hv₃ : (Act.run (.set 0 none) ⟨c₂.regs, update c₂.stk o
      (.bit (decide (ofBits xs = ofBits ys)) :: c₂.stk o)⟩).regs = Regs.empty := by
    simp [Act.run, hr₂, empty_eq_rv]
  have ht₃ : (Act.run (.set 0 none) ⟨c₂.regs, update c₂.stk o
      (.bit (decide (ofBits xs = ofBits ys)) :: c₂.stk o)⟩).stk t =
      bits (zipL diffBit xs ys false).1.reverse ++ .nd :: c.stk t := by
    simp [Act.run, ht₂, update_of_ne (Ne.symm hot)]
  refine (dropNum_sat hv₃ ht₃).mono (by simp; omega)
    fun c₄ ⟨hr₄, ht₄, hj₄⟩ => ⟨hr₄, ?_, ?_, ?_, fun j hja hjb hjo => ?_⟩
  · simp [Act.run, hj₄ a hat, update_of_ne hao, hc₂, update_of_ne hat, ha₁]
  · simp [Act.run, hj₄ b hbt, update_of_ne hbo, hc₂, update_of_ne hbt, hb₁]
  · simp [Act.run, hj₄ o hot, hc₂, update_of_ne hot, hj₁ o (Ne.symm hao) (Ne.symm hbo) hot]
  · by_cases hjt : j = t
    · subst hjt; rw [ht₄]
    simp [Act.run, hj₄ j hjt, update_of_ne hjo, hc₂, update_of_ne hjt, hj₁ j hja hjb hjt]

/-- Add one to the number on `a`, onto `o`, through `b` and `t` (which end as they started). -/
def incNum (a b o t : K) : Code K Sym Rg P := .seq (pushNum [true] b) (addNum a b o t)

theorem incNum_sat {a b o t : K} (hab : a ≠ b) (hao : a ≠ o) (hat : a ≠ t) (hbo : b ≠ o)
    (hbt : b ≠ t) (hot : o ≠ t) {c : Cfg K Sym Rg} {xs : List Bool} {ra : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra) :
    Sat prog (incNum a b o t) c (23 * xs.length + 64) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧
        c'.stk o = bits (addBits xs [true]) ++ .nd :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ o → c'.stk j = c.stk j := by
  refine Sat.seq_le (pushNum_sat b c [true]) (by simp only [List.length_singleton]; omega)
    fun c₁ ⟨hr₁, hb₁, hj₁⟩ => ?_
  rw [hv] at hr₁
  refine (addNum_sat (xs := xs) hab hao hat hbo hbt hot hr₁ (by rw [hj₁ a hab]; exact ha) hb₁).mono
    (by simp; omega) fun c₂ ⟨hr₂, ha₂, hb₂, ho₂, hj₂⟩ => ⟨hr₂, ha₂, ?_, fun j hja hjo => ?_⟩
  · rw [ho₂, hj₁ o (Ne.symm hbo)]
  · by_cases hjb : j = b
    · subst hjb; exact hb₂
    rw [hj₂ j hja hjb hjo, hj₁ j hjb]

/-- Subtract one (truncated) from the number on `a`, onto `o`, through `b` and `t`. -/
def decNum (a b o t : K) : Code K Sym Rg P := .seq (pushNum [true] b) (subNum a b o t)

theorem decNum_sat {a b o t : K} (hab : a ≠ b) (hao : a ≠ o) (hat : a ≠ t) (hbo : b ≠ o)
    (hbt : b ≠ t) (hot : o ≠ t) {c : Cfg K Sym Rg} {xs : List Bool} {ra : List Sym}
    (hv : c.regs = Regs.empty) (ha : c.stk a = bits xs ++ .nd :: ra) :
    Sat prog (decNum a b o t) c (23 * xs.length + 64) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk a = ra ∧
        c'.stk o = bits (subBits xs [true]) ++ .nd :: c.stk o ∧
        ∀ j, j ≠ a → j ≠ o → c'.stk j = c.stk j := by
  refine Sat.seq_le (pushNum_sat b c [true]) (by simp only [List.length_singleton]; omega)
    fun c₁ ⟨hr₁, hb₁, hj₁⟩ => ?_
  rw [hv] at hr₁
  refine (subNum_sat (xs := xs) hab hao hat hbo hbt hot hr₁ (by rw [hj₁ a hab]; exact ha) hb₁).mono
    (by simp; omega) fun c₂ ⟨hr₂, ha₂, hb₂, ho₂, hj₂⟩ => ⟨hr₂, ha₂, ?_, fun j hja hjo => ?_⟩
  · rw [ho₂, hj₁ o (Ne.symm hbo)]
  · by_cases hjb : j = b
    · subst hjb; exact hb₂
    rw [hj₂ j hja hjb hjo, hj₁ j hjb]

end GraphIso.TM
