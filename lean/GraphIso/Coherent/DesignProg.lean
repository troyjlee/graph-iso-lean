module

public import GraphIso.Coherent.DesignArray
public import GraphIso.Coherent.WLProg

/-!
# The Design Lemma search as a program

Programs computing the search of `GraphIso/Coherent/DesignArray.lean` (`searchA`): for every
list `x` of fewer than `k` points, in a fixed order, the individualized vertex colouring
(`col1Prog`), the first point of a class of more than `t` points (`domProg`), and whether the
individualized 2-skeleton is a clique on that class (`pairColsProg`, `cliqueProg`); the first
`x` where the Design Lemma's conclusion holds is returned with its vertex colouring
(`RunsWithin.searchProg`). The cost is at most `searchCost k m`, independent of `t`.
-/

@[expose] public section

namespace GraphIso.Coherent

open Cost Programs Sims

variable {k m : ℕ}

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One term of the code of `(x, u, …, u)`. -/
def pad1StepProg (pw : var (.array (.array .nat))) (l : var .nat) (xA : var (.array .nat))
    (u acc i : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natLt i l) fun lt =>
  .bind (.ite lt (.op2 .arrayGet xA i) (.ret u)) fun d =>
  .bind (get2Prog pw i d) fun v => .op2 .add acc v

/-- The code of `(x, u, …, u)`. -/
def pad1Prog (pw : var (.array (.array .nat))) (rk : var (.list .nat)) (l : var .nat)
    (xA : var (.array .nat)) (u : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .foldList rk z fun acc i => pad1StepProg pw l xA u acc i

/-- One term of the code of `(x, u, v, …, v)`. -/
def pad2StepProg (pw : var (.array (.array .nat))) (l : var .nat) (xA : var (.array .nat))
    (u v acc i : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natLt i l) fun lt =>
  .bind (.ite lt (.op2 .arrayGet xA i)
    (.bind (.op2 .natEq i l) fun eq => .ite eq (.ret u) (.ret v))) fun d =>
  .bind (get2Prog pw i d) fun w => .op2 .add acc w

/-- The code of `(x, u, v, …, v)`. -/
def pad2Prog (pw : var (.array (.array .nat))) (rk : var (.list .nat)) (l : var .nat)
    (xA : var (.array .nat)) (u v : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .foldList rk z fun acc i => pad2StepProg pw l xA u v acc i

/-- The individualized vertex colouring. -/
def col1Prog (c : var (.array .nat)) (pw : var (.array (.array .nat))) (rk rm : var (.list .nat))
    (l : var .nat) (xA : var (.array .nat)) : Prog S rec var (.list .nat) :=
  mapList rm fun u => .bind (pad1Prog pw rk l xA u) fun code => .op2 .arrayGet c code

/-- The size of the class of `u`. -/
def cntProg (col : var (.list .nat)) (colA : var (.array .nat)) (u : var .nat) :
    Prog S rec var .nat :=
  .bind (.op2 .arrayGet colA u) fun cu =>
  .bind (filterProg col fun a => .op2 .natEq a cu) fun f => .op1 .length f

/-- One step of the search for a point of a class of more than `t` points. -/
def domStepProg (col : var (.list .nat)) (colA : var (.array .nat)) (t : var .nat)
    (st : var (.option .nat)) (u : var .nat) : Prog S rec var (.option .nat) :=
  .caseOption st
    (.bind (cntProg col colA u) fun n => .bind (.op2 .natLt t n) fun big =>
      .ite big (.op1 .some u) (.ret st))
    fun _ => .ret st

/-- The first point of a class of more than `t` points. -/
def domProg (col : var (.list .nat)) (colA : var (.array .nat)) (rm : var (.list .nat))
    (t : var .nat) : Prog S rec var (.option .nat) :=
  .bind (.op0 .none) fun nn => .foldList rm nn fun st u => domStepProg col colA t st u

/-- The class of `u₀`. -/
def classProg (colA : var (.array .nat)) (rm : var (.list .nat)) (u₀ : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet colA u₀) fun c₀ =>
  filterProg rm fun w => .bind (.op2 .arrayGet colA w) fun cw => .op2 .natEq cw c₀

/-- The colour of `(v, w)` in the individualized 2-skeleton, onto `acc` if `w ≠ v`. -/
def pairStepProg (c : var (.array .nat)) (pw : var (.array (.array .nat))) (rk : var (.list .nat))
    (l : var .nat) (xA : var (.array .nat)) (v : var .nat) (acc : var (.list .nat))
    (w : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op2 .natEq w v) fun eq =>
  .ite eq (.ret acc)
    (.bind (pad2Prog pw rk l xA v w) fun code => .bind (.op2 .arrayGet c code) fun a =>
      .op2 .cons a acc)

/-- The colours of the pairs of distinct points of `C`, from `v`, onto `acc`. -/
def pairRowProg (c : var (.array .nat)) (pw : var (.array (.array .nat))) (rk : var (.list .nat))
    (l : var .nat) (xA : var (.array .nat)) (C : var (.list .nat)) (acc : var (.list .nat))
    (v : var .nat) : Prog S rec var (.list .nat) :=
  .foldList C acc fun acc' w => pairStepProg c pw rk l xA v acc' w

/-- The colours of the pairs of distinct points of `C`. -/
def pairColsProg (c : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk : var (.list .nat)) (l : var .nat) (xA : var (.array .nat)) (C : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op0 .nil) fun nl =>
  .bind (.foldList C nl fun acc v => pairRowProg c pw rk l xA C acc v) fun r => .op1 .reverse r

/-- Whether all the colours are equal. -/
def cliqueProg (P : var (.list .nat)) : Prog S rec var .bool :=
  .bind (.op0 (.natLit 0)) fun z =>
  .bind (.caseList P (.ret z) fun h _ => .ret h) fun hd => allList P fun a => .op2 .natEq a hd

/-- **The test at a candidate**, with its vertex colouring. -/
def goodProg (c : var (.array .nat)) (pw : var (.array (.array .nat))) (rk rm : var (.list .nat))
    (k t : var .nat) (xd : var (.list .nat)) : Prog S rec var (.prod .bool (.array .nat)) :=
  .bind (.op1 .length xd) fun l => .bind (.op1 .arrayOfList xd) fun xA =>
  .bind (col1Prog c pw rk rm l xA) fun col => .bind (.op1 .arrayOfList col) fun colA =>
  .bind (domProg col colA rm t) fun dom =>
  .caseOption dom (.bind (.op0 (.boolLit true)) fun tt => .op2 .pair tt colA)
    fun u₀ => .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .add l two) fun l₂ =>
      .bind (.op2 .natLt k l₂) fun short => .bind (.op1 .not short) fun fits =>
      .bind (classProg colA rm u₀) fun C => .bind (pairColsProg c pw rk l xA C) fun P =>
      .bind (cliqueProg P) fun cl => .bind (.op1 .not cl) fun ncl =>
      .bind (.op2 .and fits ncl) fun g => .op2 .pair g colA

/-- One candidate of the search. -/
def searchStepProg (c : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk rm : var (.list .nat)) (k t : var .nat)
    (st : var (.option (.prod (.list .nat) (.array .nat))))
    (xd : var (.list .nat)) : Prog S rec var (.option (.prod (.list .nat) (.array .nat))) :=
  .caseOption st
    (.bind (goodProg c pw rk rm k t xd) fun g => .bind (.op1 .fst g) fun good =>
      .bind (.op1 .snd g) fun colA =>
      .ite good (.bind (.op2 .pair xd colA) fun r => .op1 .some r) (.ret st))
    fun _ => .ret st

/-- The candidates of length `l`. -/
def searchLenProg (c : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk rm : var (.list .nat)) (k m t : var .nat)
    (st : var (.option (.prod (.list .nat) (.array .nat)))) (l : var .nat) :
    Prog S rec var (.option (.prod (.list .nat) (.array .nat))) :=
  .bind (tupsProg l m) fun tups =>
  .foldList tups st fun st' xd => searchStepProg c pw rk rm k t st' xd

/-- **The Design Lemma search**: the first list of fewer than `k` points where the Design
Lemma's conclusion holds for the colouring `c`, with its vertex colouring. -/
def searchProg (c : var (.array .nat)) (k m t : var .nat) :
    Prog S rec var (.option (.prod (.list .nat) (.array .nat))) :=
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (pwTabProg m rk rm) fun pw => .bind (.op0 .none) fun nn =>
  .foldList rk nn fun st l => searchLenProg c pw rk rm k m t st l

end Prog

/-! ### Models of the folds and costs -/

/-- One step of the search. -/
def sstep (c : Array ℕ) (k m t : ℕ) (st : Option (List ℕ × Array ℕ)) (xd : List ℕ) :
    Option (List ℕ × Array ℕ) :=
  match st with
  | none => if goodA c (pwTab k m) k m t xd then
      some (xd, (col1A c (pwTab k m) k m xd.length xd.toArray).toArray) else none
  | some r => some r

theorem foldl_sstep_some (c : Array ℕ) (k m t : ℕ) (r : List ℕ × Array ℕ) :
    ∀ l : List (List ℕ), l.foldl (sstep c k m t) (some r) = some r
  | [] => rfl
  | _ :: l => foldl_sstep_some c k m t r l

theorem foldl_sstep_none (c : Array ℕ) (k m t : ℕ) :
    ∀ l : List (List ℕ), l.foldl (sstep c k m t) none =
      (l.find? (goodA c (pwTab k m) k m t)).map fun xd =>
        (xd, (col1A c (pwTab k m) k m xd.length xd.toArray).toArray)
  | [] => rfl
  | xd :: l => by
    by_cases h : goodA c (pwTab k m) k m t xd = true
    · simp [sstep, h, foldl_sstep_some]
    · simp only [List.foldl_cons, sstep, h, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
      exact foldl_sstep_none c k m t l

theorem foldl_domStep (col : List ℕ) (t : ℕ) :
    ∀ (l : List ℕ) (st : Option ℕ),
      l.foldl (fun st u => match st with
        | none => if t < cntA col u then some u else none
        | some v => some v) st =
        match st with
        | none => l.find? fun u => t < cntA col u
        | some v => some v
  | [], none => rfl
  | [], some _ => rfl
  | u :: l, none => by
    by_cases h : t < cntA col u
    · simp only [List.foldl_cons, h, ↓reduceIte, List.find?_cons, decide_true]
      exact foldl_domStep col t l (some u)
    · simp only [List.foldl_cons, h, ↓reduceIte, List.find?_cons, decide_false]
      exact foldl_domStep col t l none
  | u :: l, some v => foldl_domStep col t l (some v)

theorem pairCols_fold (c : Array ℕ) (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ)
    (C : List ℕ) :
    (C.foldl (fun acc v => C.foldl (fun acc' w =>
        if w = v then acc' else get c (codePad2 pw k l xA v w) :: acc') acc) []).reverse =
      pairCols c pw k l xA C := by
  have hin : ∀ (v : ℕ) (L : List ℕ) (r : List ℕ),
      L.foldl (fun acc' w => if w = v then acc' else get c (codePad2 pw k l xA v w) :: acc') r =
        ((L.filter (· ≠ v)).map fun w => get c (codePad2 pw k l xA v w)).reverse ++ r := by
    intro v L
    induction L with
    | nil => simp
    | cons w L ih =>
      intro r
      by_cases hw : w = v
      · simp [hw, ih]
      · simp [hw, ih]
  have hout : ∀ (L : List ℕ) (r : List ℕ),
      L.foldl (fun acc v => C.foldl (fun acc' w =>
        if w = v then acc' else get c (codePad2 pw k l xA v w) :: acc') acc) r =
        (L.flatMap fun v => (C.filter (· ≠ v)).map fun w =>
          get c (codePad2 pw k l xA v w)).reverse ++ r := by
    intro L
    induction L with
    | nil => simp
    | cons v L ih =>
      intro r
      rw [List.foldl_cons, hin, ih, List.flatMap_cons, List.reverse_append, List.append_assoc]
  rw [hout]
  simp [pairCols]

theorem length_pairCols_le (c : Array ℕ) (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ)
    (C : List ℕ) : (pairCols c pw k l xA C).length ≤ C.length * C.length := by
  unfold pairCols
  rw [List.length_flatMap]
  have : ∀ v ∈ C, ((C.filter (· ≠ v)).map fun w => get c (codePad2 pw k l xA v w)).length ≤
      C.length := fun v _ => by
    rw [List.length_map]
    exact List.length_filter_le _ _
  have h := List.sum_le_length_nsmul (C.map fun v => ((C.filter (· ≠ v)).map fun w =>
    get c (codePad2 pw k l xA v w)).length) C.length fun n hn => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hn
      exact this v hv
  simpa using h

/-- The cost of the test at one candidate. -/
def goodCost (k m : ℕ) : ℕ :=
  2 * k + 2 + (m * (7 * k + 5) + 2) + (m + 1) + (m * (6 * m + 9) + 1) + 5 + (6 * m + 3) +
    (m * (m * (8 * k + 6) + 1) + m * m + 2) + (3 * (m * m) + 3) + 3

/-- A bound on the cost of the digit lists of every length `l ≤ k`. -/
def tupsBound (k m : ℕ) : ℕ := m + k + 5 + k * (1 + extCost m (m ^ k + 2))

/-- **The cost of the search.** -/
def searchCost (k m : ℕ) : ℕ :=
  k + m + 3 + pwTabCost k m + k * (1 + tupsBound k m + (m ^ k + 1) * (goodCost k m + 7))

theorem tupsCost_le {l k m : ℕ} (hl : l ≤ k) : tupsCost l m ≤ tupsBound k m := by
  unfold tupsCost tupsBound
  have h1 := extCost_mono m (by have := pow_le_pow_add_one (m := m) hl; omega :
    m ^ l + 1 ≤ m ^ k + 2)
  have h2 := Nat.mul_le_mul hl (Nat.add_le_add_left h1 1)
  omega

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.pad1Prog (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ) (u : ℕ) :
    RunsWithin X body (Coherent.pad1Prog pw (List.range k) l xA u) (codePad1 pw k l xA u)
      (7 * k + 1) := by
  have hstep : ∀ acc i, RunsWithin X body (Coherent.pad1StepProg pw l xA u acc i)
      (acc + get2 pw i (if i < l then get xA i else u)) 6 := fun acc i => by
    by_cases h : i < l
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.ite_pos (show decide (i < l) = true by simpa using h)
          (RunsWithin.prim _ _))
        run_step (RunsWithin.get2Prog _ _ _)
        exact (RunsWithin.prim _ _).of_eq (by
          simp [Prim.eval, h, get, Array.getD_eq_getD_getElem?, Ty.default])
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.ite_neg (show decide (i < l) = false by simpa using h)
          (RunsWithin.ret _))
        run_step (RunsWithin.get2Prog _ _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, h])
      case hc => simp [Prim.cost]
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 6) (F := fun acc i => acc + get2 pw i (if i < l then get xA i else u))
    (f := fun acc i => Coherent.pad1StepProg pw l xA u acc i) (List.range k) 0
    fun acc i _ => hstep acc i
  rw [sum_map_const, List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.pad2Prog (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ) (u v : ℕ) :
    RunsWithin X body (Coherent.pad2Prog pw (List.range k) l xA u v) (codePad2 pw k l xA u v)
      (8 * k + 1) := by
  have hstep : ∀ acc i, RunsWithin X body (Coherent.pad2StepProg pw l xA u v acc i)
      (acc + get2 pw i (if i < l then get xA i else if i = l then u else v)) 7 := fun acc i => by
    by_cases h : i < l
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.ite_pos (show decide (i < l) = true by simpa using h)
          (RunsWithin.prim _ _))
        run_step (RunsWithin.get2Prog _ _ _)
        exact (RunsWithin.prim _ _).of_eq (by
          simp [Prim.eval, h, get, Array.getD_eq_getD_getElem?, Ty.default])
      case hc => simp [Prim.cost]
    · by_cases h' : i = l
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.ite_neg (show decide (i < l) = false by simpa using h)
            (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.ite_pos
              (show (i == l) = true by simpa using h') (RunsWithin.ret _))))
          run_step (RunsWithin.get2Prog _ _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, h'])
        case hc => simp [Prim.cost]
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.ite_neg (show decide (i < l) = false by simpa using h)
            (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.ite_neg
              (show (i == l) = false by simpa using h') (RunsWithin.ret _))))
          run_step (RunsWithin.get2Prog _ _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, h, h'])
        case hc => simp [Prim.cost]
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 7)
    (F := fun acc i => acc + get2 pw i (if i < l then get xA i else if i = l then u else v))
    (f := fun acc i => Coherent.pad2StepProg pw l xA u v acc i) (List.range k) 0
    fun acc i _ => hstep acc i
  rw [sum_map_const, List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.col1Prog (c : Array ℕ) (pw : Array (Array ℕ)) (k m l : ℕ) (xA : Array ℕ) :
    RunsWithin X body (Coherent.col1Prog c pw (List.range k) (List.range m) l xA)
      (col1A c pw k m l xA) (m * (7 * k + 5) + 2) := by
  have := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (c := 7 * k + 2) (xs := List.range m)
    (f := fun u => .bind (Coherent.pad1Prog pw (List.range k) l xA u) fun code =>
      .op2 .arrayGet c code) (F := fun u => get c (codePad1 pw k l xA u)) fun u _ =>
      RunsWithin.bind_le (RunsWithin.pad1Prog pw k l xA u) (RunsWithin.prim_le (by
        simp [Prim.eval, get, Array.getD_eq_getD_getElem?, Ty.default]) le_rfl)
        (by simp [Prim.cost])
  rw [List.length_range] at this
  exact this.mono (le_of_eq (by ring))

theorem RunsWithin.cntProg (col : List ℕ) (u : ℕ) :
    RunsWithin X body (Coherent.cntProg col col.toArray u) (cntA col u) (6 * col.length + 4) := by
  set cu := Prim.eval (Prim.arrayGet (a := .nat)) (.cons col.toArray (.cons u .nil)) with hcu
  have hcu' : cu = col.getD u 0 := by
    simp [hcu, Prim.eval, Ty.default, List.getD_eq_getElem?_getD]
  have hf := RunsWithin.filterProg (X := X) (body := body) (t := .nat) (xs := col) (c := 1)
    (p := fun a => .op2 .natEq a cu)
    (P := fun a => Prim.eval Prim.natEq (.cons a (.cons cu .nil)))
    fun a _ => RunsWithin.prim _ _
  have hlen := List.length_filter_le (fun a => Prim.eval Prim.natEq (.cons a (.cons cu .nil))) col
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hf
    refine (RunsWithin.prim _ _).of_eq ?_
    simp only [Prim.eval, cntA, ← hcu']
    exact congrArg List.length (List.filter_congr fun x _ => Bool.eq_iff_iff.2 (by simp))
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    omega

theorem RunsWithin.domProg (col : List ℕ) (t : ℕ) :
    RunsWithin X body (Coherent.domProg col col.toArray (List.range col.length) t) (domA col t)
      (col.length * (6 * col.length + 9) + 1) := by
  have hstep : ∀ (st : Option ℕ) (u : ℕ), RunsWithin X body
      (Coherent.domStepProg col col.toArray t st u)
      (match st with
        | none => if t < cntA col u then some u else none
        | some v => some v) (6 * col.length + 8) := by
    intro st u
    cases st with
    | some v =>
      apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOpt_eq_some (show (some v : Option ℕ) = some v from rfl) _
        exact RunsWithin.ret _
      case hc => omega
    | none =>
      by_cases h : t < cntA col u
      · apply RunsWithin.mono
        case h =>
          run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
          run_step (RunsWithin.cntProg col u)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (show decide (t < cntA col u) = true by simpa using h) _
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, h])
        case hc => simp [Prim.cost]; omega
      · apply RunsWithin.mono
        case h =>
          run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
          run_step (RunsWithin.cntProg col u)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show decide (t < cntA col u) = false by simpa using h) _
          exact (RunsWithin.ret _).of_eq (by simp [h])
        case hc => simp [Prim.cost]; omega
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .option .nat)
    (cf := fun _ => 6 * col.length + 8)
    (f := fun st u => Coherent.domStepProg col col.toArray t st u)
    (List.range col.length) none fun st u _ => hstep st u
  rw [sum_map_const, List.length_range, foldl_domStep] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp [Prim.cost]; nlinarith

theorem RunsWithin.classProg (col : List ℕ) (u₀ : ℕ) :
    RunsWithin X body (Coherent.classProg col.toArray (List.range col.length) u₀) (classA col u₀)
      (6 * col.length + 3) := by
  set c₀ := Prim.eval (Prim.arrayGet (a := .nat)) (.cons col.toArray (.cons u₀ .nil)) with hc₀
  have hget : ∀ w, Prim.eval (Prim.arrayGet (a := .nat)) (.cons col.toArray (.cons w .nil)) =
      col.getD w 0 := fun w => by
    simp [Prim.eval, Ty.default, List.getD_eq_getElem?_getD]
  have hf := RunsWithin.filterProg (X := X) (body := body) (t := .nat)
    (xs := List.range col.length) (c := 2)
    (p := fun w => .bind (.op2 .arrayGet col.toArray w) fun cw => .op2 .natEq cw c₀)
    (P := fun w => col.getD w 0 == col.getD u₀ 0)
    fun w _ => RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le (by
      rw [hget w, hc₀, hget u₀]
      rfl) le_rfl) (by simp [Prim.cost])
  rw [List.length_range] at hf
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    refine hf.of_eq ?_
    exact List.filter_congr fun x _ => Bool.eq_iff_iff.2 (by simp)
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.pairColsProg (c : Array ℕ) (pw : Array (Array ℕ)) (k l : ℕ) (xA : Array ℕ)
    (C : List ℕ) :
    RunsWithin X body (Coherent.pairColsProg c pw (List.range k) l xA C) (pairCols c pw k l xA C)
      (C.length * (C.length * (8 * k + 6) + 1) + C.length * C.length + 2) := by
  have hstep : ∀ v acc w, RunsWithin X body (Coherent.pairStepProg c pw (List.range k) l xA v acc w)
      (if w = v then acc else get c (codePad2 pw k l xA v w) :: acc) (8 * k + 5) := by
    intro v acc w
    by_cases h : w = v
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (w == v) = true by simpa using h) _
        exact (RunsWithin.ret _).of_eq (by simp [h])
      case hc => simp only [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (w == v) = false by simpa using h) _
        run_step (RunsWithin.pad2Prog _ _ _ _ _ _)
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by
          simp [Prim.eval, h, get, Array.getD_eq_getD_getElem?, Ty.default])
      case hc => simp only [Prim.cost]; omega
  have hrow : ∀ (acc : List ℕ) (v : ℕ),
      RunsWithin X body (Coherent.pairRowProg c pw (List.range k) l xA C acc v)
      (C.foldl (fun acc' w => if w = v then acc' else get c (codePad2 pw k l xA v w) :: acc') acc)
      (C.length * (8 * k + 6)) := by
    intro acc v
    have := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .list .nat)
      (cf := fun _ => 8 * k + 5)
      (F := fun acc' w => if w = v then acc' else get c (codePad2 pw k l xA v w) :: acc')
      (f := fun acc' w => Coherent.pairStepProg c pw (List.range k) l xA v acc' w) C acc
      fun acc' w _ => hstep v acc' w
    rw [sum_map_const] at this
    exact this
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (cf := fun _ => C.length * (8 * k + 6))
    (f := fun acc v => Coherent.pairRowProg c pw (List.range k) l xA C acc v) C []
    fun acc v _ => hrow acc v
  rw [sum_map_const] at hfold
  have hlen := length_pairCols_le c pw k l xA C
  rw [← pairCols_fold] at hlen
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact (RunsWithin.prim _ _).of_eq (by simp only [Prim.eval]; exact pairCols_fold _ _ _ _ _ _)
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    rw [List.length_reverse] at hlen
    generalize hG : C.length * (C.length * (8 * k + 6) + 1) = G
    refine Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left
      (Nat.add_le_add_right hlen 1) _) _) ?_
    omega

theorem RunsWithin.cliqueProg (P : List ℕ) :
    RunsWithin X body (Coherent.cliqueProg P) (P.all fun a => a = P.headD 0)
      (3 * P.length + 3) := by
  have hall := RunsWithin.allList_le (X := X) (body := body) (a' := .nat) (c := 1) (xs := P)
    (p := fun a => .op2 .natEq a (P.headD 0)) (P := fun a => a == P.headD 0)
    fun a _ => RunsWithin.prim _ _
  rcases P with _ | ⟨h, P⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.caseList_eq_nil rfl (RunsWithin.ret _))
      exact hall.of_eq (by simp)
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.caseList_eq_cons rfl (RunsWithin.ret _))
      refine hall.of_eq ?_
      simp only [List.headD_cons]
      exact congrArg (List.all (h :: P)) (funext fun a => Bool.eq_iff_iff.2 (by
        rw [beq_iff_eq]; exact decide_eq_true_iff.symm))
    case hc => simp [Prim.cost]; omega

theorem not_decide_lt (a b : ℕ) : (!decide (a < b)) = decide (b ≤ a) := by
  by_cases h : a < b
  · simp [h, Nat.not_le.2 h]
  · simp [h, Nat.not_lt.1 h]

theorem length_classA_le (col : List ℕ) (u : ℕ) : (classA col u).length ≤ col.length := by
  unfold classA
  exact (List.length_filter_le _ _).trans (by simp)

/-- **The test at one candidate.** -/
theorem RunsWithin.goodProg (c : Array ℕ) (k m t : ℕ) {xd : List ℕ} (hxd : xd.length ≤ k) :
    RunsWithin X body (Coherent.goodProg c (pwTab k m) (List.range k) (List.range m) k t xd)
      (goodA c (pwTab k m) k m t xd, (col1A c (pwTab k m) k m xd.length xd.toArray).toArray)
      (goodCost k m) := by
  set col := col1A c (pwTab k m) k m xd.length xd.toArray with hcol
  have hlen : col.length = m := length_col1A _ _ _ _ _ _
  have hdom := RunsWithin.domProg (X := X) (body := body) col t
  have hcls : ∀ u₀, RunsWithin X body (Coherent.classProg col.toArray (List.range m) u₀)
      (classA col u₀) (6 * m + 3) := fun u₀ => by
    have := RunsWithin.classProg (X := X) (body := body) col u₀
    rwa [hlen] at this
  rw [hlen] at hdom
  rcases hd : domA col t with _ | u₀
  · rw [hd] at hdom
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.col1Prog c (pwTab k m) k m xd.length xd.toArray)
      run_step (RunsWithin.prim _ _)
      run_step hdom
      run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
      run_step (RunsWithin.prim _ _)
      refine (RunsWithin.prim _ _).of_eq ?_
      simp [Prim.eval, goodA, ← hcol, hd]
    case hc =>
      simp only [Prim.cost, Args.head_cons, goodCost]
      nlinarith
  · rw [hd] at hdom
    set C := classA col u₀ with hC
    have hCm : C.length ≤ m := hlen ▸ length_classA_le col u₀
    set P := pairCols c (pwTab k m) k xd.length xd.toArray C with hP
    have hPm : P.length ≤ m * m :=
      (length_pairCols_le _ _ _ _ _ _).trans (Nat.mul_le_mul hCm hCm)
    have hpc := RunsWithin.pairColsProg (X := X) (body := body) c (pwTab k m) k xd.length
      xd.toArray C
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.col1Prog c (pwTab k m) k m xd.length xd.toArray)
      run_step (RunsWithin.prim _ _)
      run_step hdom
      run_with RunsWithin.caseOpt_eq_some (show (some u₀ : Option ℕ) = some u₀ from rfl) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (hcls u₀)
      run_step hpc
      run_step (RunsWithin.cliqueProg P)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      refine (RunsWithin.prim _ _).of_eq ?_
      simp [Prim.eval, goodA, ← hcol, hd, ← hC, ← hP, cliqueA, not_decide_lt]
    case hc =>
      simp only [Prim.cost, Args.head_cons, goodCost]
      have h1 := Nat.mul_le_mul_right (C.length * (8 * k + 6) + 1) hCm
      have h2 := Nat.mul_le_mul_left m
        (Nat.add_le_add_right (Nat.mul_le_mul_right (8 * k + 6) hCm) 1)
      have h3 := Nat.mul_le_mul hCm hCm
      nlinarith

theorem RunsWithin.searchStepProg (c : Array ℕ) (k m t : ℕ) (st : Option (List ℕ × Array ℕ))
    {xd : List ℕ} (hxd : xd.length ≤ k) :
    RunsWithin X body
      (Coherent.searchStepProg c (pwTab k m) (List.range k) (List.range m) k t st xd)
      (sstep c k m t st xd) (goodCost k m + 6) := by
  cases st with
  | some r =>
    apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseOpt_eq_some (show (some r : Option (List ℕ × Array ℕ)) = some r
        from rfl) _
      exact (RunsWithin.ret _).of_eq rfl
    case hc => omega
  | none =>
    have hg := RunsWithin.goodProg (X := X) (body := body) c k m t hxd
    by_cases h : goodA c (pwTab k m) k m t xd = true
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOpt_eq_none (show (none : Option (List ℕ × Array ℕ)) = none
          from rfl) _
        run_step hg
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show goodA c (pwTab k m) k m t xd = true from h) _
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, sstep, h])
      case hc => simp [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOpt_eq_none (show (none : Option (List ℕ × Array ℕ)) = none
          from rfl) _
        run_step hg
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show goodA c (pwTab k m) k m t xd = false by simpa using h) _
        exact (RunsWithin.ret _).of_eq (by simp [sstep, h])
      case hc => simp [Prim.cost]; omega

theorem RunsWithin.searchLenProg (c : Array ℕ) (k m t : ℕ) (st : Option (List ℕ × Array ℕ))
    {l : ℕ} (hl : l ≤ k) :
    RunsWithin X body
      (Coherent.searchLenProg c (pwTab k m) (List.range k) (List.range m) k m t st l)
      ((tupList l m).foldl (sstep c k m t) st)
      (tupsCost l m + m ^ l * (goodCost k m + 7)) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat)
    (b' := .option (.prod (.list .nat) (.array .nat))) (cf := fun _ => goodCost k m + 6)
    (F := sstep c k m t)
    (f := fun st' xd => Coherent.searchStepProg c (pwTab k m) (List.range k) (List.range m) k t
      st' xd) (tupList l m) st fun st' xd hxd => RunsWithin.searchStepProg c k m t st'
        (by rw [length_of_mem_tupList hxd]; exact hl)
  rw [sum_map_const, length_tupList, show goodCost k m + 6 + 1 = goodCost k m + 7 from rfl]
    at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.tupsProg l m)
    exact hfold
  case hc => omega

/-- **The Design Lemma search**, at cost at most `searchCost k m`. -/
theorem RunsWithin.searchProg (c : Array ℕ) (k m t : ℕ) :
    RunsWithin X body (Coherent.searchProg c k m t) (searchA c k m t) (searchCost k m) := by
  have hstep : ∀ (st : Option (List ℕ × Array ℕ)) (l : ℕ), l ∈ List.range k →
      RunsWithin X body
        (Coherent.searchLenProg c (pwTab k m) (List.range k) (List.range m) k m t st l)
        ((tupList l m).foldl (sstep c k m t) st)
        (tupsBound k m + (m ^ k + 1) * (goodCost k m + 7)) := by
    intro st l hl
    have hl' : l ≤ k := (List.mem_range.1 hl).le
    refine (RunsWithin.searchLenProg c k m t st hl').mono ?_
    have := tupsCost_le (m := m) hl'
    have := Nat.mul_le_mul_right (goodCost k m + 7) (pow_le_pow_add_one (m := m) hl')
    omega
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .option (.prod (.list .nat) (.array .nat)))
    (cf := fun _ => tupsBound k m + (m ^ k + 1) * (goodCost k m + 7))
    (F := fun st l => (tupList l m).foldl (sstep c k m t) st)
    (f := fun st l => Coherent.searchLenProg c (pwTab k m) (List.range k) (List.range m) k m t
      st l) (List.range k) none hstep
  rw [sum_map_const, List.length_range, ← List.foldl_flatMap, foldl_sstep_none] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.pwTabProg k m)
    run_step (RunsWithin.prim _ _)
    exact hfold.of_eq rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, searchCost]
    nlinarith

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_pad1Prog {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)} {l₁ u₁ : var₁ .nat} {l₂ u₂ : var₂ .nat}
    {xA₁ : var₁ (.array .nat)} {xA₂ : var₂ (.array .nat)}
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hxA : ⟨.array .nat, xA₁, xA₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pad1Prog pw₁ rk₁ l₁ xA₁ u₁)
      (pad1Prog pw₂ rk₂ l₂ xA₂ u₂) := by
  unfold pad1Prog pad1StepProg get2Prog
  prog_wf

theorem wf_pad2Prog {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)} {l₁ u₁ v₁ : var₁ .nat}
    {l₂ u₂ v₂ : var₂ .nat} {xA₁ : var₁ (.array .nat)} {xA₂ : var₂ (.array .nat)}
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hxA : ⟨.array .nat, xA₁, xA₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ)
    (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pad2Prog pw₁ rk₁ l₁ xA₁ u₁ v₁)
      (pad2Prog pw₂ rk₂ l₂ xA₂ u₂ v₂) := by
  unfold pad2Prog pad2StepProg get2Prog
  prog_wf

theorem wf_col1Prog {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)} {l₁ : var₁ .nat}
    {l₂ : var₂ .nat} {xA₁ : var₁ (.array .nat)} {xA₂ : var₂ (.array .nat)}
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hxA : ⟨.array .nat, xA₁, xA₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (col1Prog c₁ pw₁ rk₁ rm₁ l₁ xA₁)
      (col1Prog c₂ pw₂ rk₂ rm₂ l₂ xA₂) := by
  unfold col1Prog
  refine wf_mapList hrm fun Γ' hΓ u₁ u₂ hu => ?_
  have := hΓ hc
  exact .bind (wf_pad1Prog (hΓ hpw) (hΓ hrk) (hΓ hl) (hΓ hxA) hu) fun _ _ => by prog_wf

theorem wf_cntProg {col₁ : var₁ (.list .nat)} {col₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)} {u₁ : var₁ .nat} {u₂ : var₂ .nat}
    (hcol : ⟨.list .nat, col₁, col₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cntProg col₁ colA₁ u₁) (cntProg col₂ colA₂ u₂) := by
  unfold cntProg
  refine .bind (.prim _ (.cons hcolA (.cons hu .nil))) fun _ _ =>
    .bind (wf_filterProg (by simp [hcol]) fun Γ' hΓ a₁ a₂ ha => ?_) fun _ _ => by prog_wf
  have := hΓ List.mem_cons_self
  prog_wf

theorem wf_domProg {col₁ : var₁ (.list .nat)} {col₂ : var₂ (.list .nat)}
    {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)} {rm₁ : var₁ (.list .nat)}
    {rm₂ : var₂ (.list .nat)} {t₁ : var₁ .nat} {t₂ : var₂ .nat}
    (hcol : ⟨.list .nat, col₁, col₂⟩ ∈ Γ) (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (domProg col₁ colA₁ rm₁ t₁) (domProg col₂ colA₂ rm₂ t₂) := by
  unfold domProg domStepProg
  refine .bind (.prim _ .nil) fun _ _ => .foldList (by simp [hrm]) (by simp)
    fun st₁ st₂ u₁ u₂ => .caseOption (by simp) ?_ fun _ _ => .ret (by simp)
  exact .bind (wf_cntProg (by simp [hcol]) (by simp [hcolA]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [ht]) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) (.prim _ (.cons (by simp) .nil)) (.ret (by simp))

theorem wf_classProg {colA₁ : var₁ (.array .nat)} {colA₂ : var₂ (.array .nat)}
    {rm₁ : var₁ (.list .nat)} {rm₂ : var₂ (.list .nat)} {u₁ : var₁ .nat} {u₂ : var₂ .nat}
    (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ) (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (classProg colA₁ rm₁ u₁) (classProg colA₂ rm₂ u₂) := by
  unfold classProg
  refine .bind (.prim _ (.cons hcolA (.cons hu .nil))) fun _ _ =>
    wf_filterProg (by simp [hrm]) fun Γ' hΓ w₁ w₂ hw => ?_
  have := hΓ List.mem_cons_self
  have := hΓ (List.mem_cons_of_mem _ hcolA)
  prog_wf

theorem wf_pairColsProg {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)} {l₁ : var₁ .nat} {l₂ : var₂ .nat}
    {xA₁ : var₁ (.array .nat)} {xA₂ : var₂ (.array .nat)} {C₁ : var₁ (.list .nat)}
    {C₂ : var₂ (.list .nat)} (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hxA : ⟨.array .nat, xA₁, xA₂⟩ ∈ Γ)
    (hC : ⟨.list .nat, C₁, C₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pairColsProg c₁ pw₁ rk₁ l₁ xA₁ C₁)
      (pairColsProg c₂ pw₂ rk₂ l₂ xA₂ C₂) := by
  unfold pairColsProg pairRowProg pairStepProg
  refine .bind (.prim _ .nil) fun _ _ => .bind (.foldList (by simp [hC]) (by simp)
    fun acc₁ acc₂ v₁ v₂ => .foldList (by simp [hC]) (by simp) fun acc₁' acc₂' w₁ w₂ => ?_)
    fun _ _ => .prim _ (.cons (by simp) .nil)
  exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) (.ret (by simp)) (.bind (wf_pad2Prog (by simp [hpw]) (by simp [hrk])
      (by simp [hl]) (by simp [hxA]) (by simp) (by simp)) fun _ _ =>
      .bind (.prim _ (.cons (by simp [hc]) (.cons (by simp) .nil))) fun _ _ =>
      .prim _ (.cons (by simp) (.cons (by simp) .nil)))

theorem wf_cliqueProg {P₁ : var₁ (.list .nat)} {P₂ : var₂ (.list .nat)}
    (hP : ⟨.list .nat, P₁, P₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cliqueProg P₁) (cliqueProg P₂) := by
  unfold cliqueProg
  refine .bind (.prim _ .nil) fun _ _ => .bind (.caseList (by simp [hP]) (.ret (by simp))
    fun _ _ _ _ => .ret (by simp)) fun _ _ => wf_allList (by simp [hP]) fun Γ' hΓ a₁ a₂ ha => ?_
  have := hΓ List.mem_cons_self
  prog_wf

theorem wf_goodProg {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)} {k₁ t₁ : var₁ .nat}
    {k₂ t₂ : var₂ .nat} {xd₁ : var₁ (.list .nat)} {xd₂ : var₂ (.list .nat)}
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hxd : ⟨.list .nat, xd₁, xd₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (goodProg c₁ pw₁ rk₁ rm₁ k₁ t₁ xd₁)
      (goodProg c₂ pw₂ rk₂ rm₂ k₂ t₂ xd₂) := by
  unfold goodProg
  exact .bind (.prim _ (.cons hxd .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hxd]) .nil)) fun _ _ =>
    .bind (wf_col1Prog (by simp [hc]) (by simp [hpw]) (by simp [hrk]) (by simp [hrm]) (by simp)
      (by simp)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_domProg (by simp) (by simp) (by simp [hrm]) (by simp [ht])) fun _ _ =>
    .caseOption (by simp)
      (.bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil)))
      fun _ _ => .bind (.prim _ .nil) fun _ _ =>
        .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
        .bind (.prim _ (.cons (by simp [hk]) (.cons (by simp) .nil))) fun _ _ =>
        .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
        .bind (wf_classProg (by simp) (by simp [hrm]) (by simp)) fun _ _ =>
        .bind (wf_pairColsProg (by simp [hc]) (by simp [hpw]) (by simp [hrk]) (by simp)
          (by simp) (by simp)) fun _ _ =>
        .bind (wf_cliqueProg (by simp)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
        fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
        .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_searchProg {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {k₁ m₁ t₁ : var₁ .nat} {k₂ m₂ t₂ : var₂ .nat} (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (searchProg c₁ k₁ m₁ t₁) (searchProg c₂ k₂ m₂ t₂) := by
  unfold searchProg searchLenProg searchStepProg
  refine .bind (.prim _ (.cons hk .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hm]) .nil))
    fun _ _ => .bind (wf_pwTabProg (by simp [hm]) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .foldList (by simp) (by simp) fun st₁ st₂ l₁ l₂ =>
    .bind (wf_tupsProg (by simp) (by simp [hm])) fun _ _ =>
    .foldList (by simp) (by simp) fun st₁' st₂' xd₁ xd₂ =>
    .caseOption (by simp) ?_ fun _ _ => .ret (by simp)
  refine .bind (wf_goodProg (by simp [hc]) (by simp) (by simp) (by simp) (by simp [hk])
    (by simp [ht]) (by simp)) fun _ _ => ?_
  prog_wf

end Wf

end GraphIso.Coherent
