module

public import GraphIso.Main.M5CJData

/-!
# Coloured Johnson pairs in M5: the programs

Stage 14j-4b, items 2–3 (`PLAN-14.md` §14.5). Programs computing the colourings and the
coloured Johnson pairs of `M5CJData`, each with a `RunsWithin` spec at an explicit cost:

* `q2bProg` (`q2bD`) and `q3Prog` (`q3D`): one array, written in two passes;
* `cjOfProg` (`cjOfD`): the coloured datum of a Johnson leaf;
* Case 2b: `firstTupleProg` (`firstTupleD`) and `cjLeaves2bProg` (`cjLeaves2bD`, the shape of
  stage 14h's `allLeavesProg` with the tuple's colouring);
* Case 3: `c3ClsProg` (`c3ClsD`, the prefix of stage 14i's `outcomeProg` and the class),
  and `cjStructs3Prog` (`cjStructs3D`, the shape of `allStructsProg` with the good list's
  colouring).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Case2b GraphIso.Align

/-! ### Programs -/

section Progs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 2b's colouring** (`q2bD`): `1` on `Φ`, then `2 + i` at the `i`-th point of `S`. -/
def q2bProg (m : var .nat) (Φ Sl : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk m z) fun blank =>
  .bind (mapList Φ fun v => .bind (.op0 (.natLit 1)) fun one => .op2 .pair v one) fun w₁ =>
  .bind (.op1 .arrayOfList Sl) fun SA => .bind (.op1 .length Sl) fun l =>
  .bind (.op1 .range l) fun rl =>
  .bind (mapList rl fun i => .bind (.op2 .arrayGet SA i) fun v =>
      .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .add i two) fun c => .op2 .pair v c) fun w₂ =>
  .bind (.op2 .append w₁ w₂) fun ws =>
  .prim .arrayUpdate (.cons blank (.cons ws .nil))

/-- **Case 3's colouring** (`q3D`): `2` on `V`, then `1` on `C`. -/
def q3Prog (M : var .nat) (V C : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk M z) fun blank =>
  .bind (mapList V fun v => .bind (.op0 (.natLit 2)) fun two => .op2 .pair v two) fun w₁ =>
  .bind (mapList C fun v => .bind (.op0 (.natLit 1)) fun one => .op2 .pair v one) fun w₂ =>
  .bind (.op2 .append w₁ w₂) fun ws =>
  .prim .arrayUpdate (.cons blank (.cons ws .nil))

/-- **The coloured datum of a Johnson leaf** (`cjOfD`), empty for any other leaf. -/
def cjOfProg (q : var (.array .nat)) (o : var outTy) : Prog S rec var (.list cjTy) :=
  .bind (.op1 .fst o) fun tag => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .natEq tag two) fun isJ =>
  .ite isJ
    (.bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun jd => .bind (.op2 .pair jd q) fun e =>
      .bind (.op0 .nil) fun nil => .op2 .cons e nil)
    (.op0 .nil)

/-- **The first tuple** (`firstTupleD`). -/
def firstTupleProg (Φ : var (.list .nat)) (j : var .nat) : Prog S rec var (.list .nat) :=
  .bind (Case2b.tuplesProg Φ j) fun Ts => .caseList Ts (.op0 .nil) fun Sl _ => .ret Sl

end Progs

section ProgsD

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The coloured Johnson leaves of Case 2b** (`cjLeaves2bD`): every tuple `S` with its
colouring, every pair, every Johnson leaf. -/
def cjLeaves2bProg (N n : var .nat) (F : var (Ty.group D)) (Φ : var (.list .nat))
    (j : var .nat) : Prog (groupSig D) rec var (.list cjTy) :=
  .bind (Case2b.tuplesProg Φ j) fun Ts =>
  Align.joFlatMap Ts fun Sl =>
    .bind (.op2 .sub N n) fun m => .bind (q2bProg m Φ Sl) fun q =>
    .bind (phiSProg m Φ Sl) fun ΦS =>
    .bind (.op1 .length ΦS) fun m' => .bind (Case2b.pairsProg m') fun ps =>
    Align.joFlatMap ps fun ab => .bind (.op1 .fst ab) fun a => .bind (.op1 .snd ab) fun b =>
      .bind (choiceProg N n F Φ Sl a b) fun ls => Align.joFlatMap ls fun o => cjOfProg q o

end ProgsD

section ProgsD3

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **The dominant class at a good list** (`c3ClsD`): the prefix of stage 14i's `outcomeProg`
(the vertex colouring and its large class), then the class as base indices. -/
def c3ClsProg (VA W : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk rm : var (.list .nat)) (t : var .nat) (z : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .length z) fun l => .bind (.op1 .arrayOfList z) fun zA =>
  .bind (Coherent.col1Prog W pw rk rm l zA) fun col =>
  .bind (.op1 .arrayOfList col) fun colA =>
  .bind (Coherent.domProg col colA rm t) fun dom =>
  .caseOption dom (.op0 .nil) fun u₀ =>
    .bind (Coherent.classProg colA rm u₀) fun C => mapList C fun i => .op2 .arrayGet VA i

/-- **The coloured Johnson structures at a good list** (`cjOutcome3D`). -/
def cjOutcome3Prog (M : var .nat) (V : var (.list .nat)) (VA W : var (.array .nat))
    (pw : var (.array (.array .nat))) (rk rm : var (.list .nat)) (t : var .nat)
    (z : var (.list .nat)) : Prog S rec var (.list cjTy) :=
  .bind (c3ClsProg VA W pw rk rm t z) fun C => .bind (q3Prog M V C) fun q =>
  .bind (Case3.outcomeProg M V VA W pw rk rm t z) fun os =>
  Align.joFlatMap os fun o => cjOfProg q o

/-- **The coloured Johnson structures of Case 3** (`cjStructs3D`): the prefix of
`allStructsProg`, then every good list. -/
def cjStructs3Prog (M k : var .nat) (V : var (.list .nat)) (col : var (.array .nat)) :
    Prog S rec var (.list cjTy) :=
  .bind (.op1 .length V) fun m => .bind (.op1 .arrayOfList V) fun VA =>
  .bind (Case3.wlCProg k m col) fun W =>
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (Coherent.pwTabProg m rk rm) fun pw =>
  .bind (Case3.tOfProg m) fun t =>
  .bind (SoJProg.goodListProg W k m t) fun gl =>
  Align.joFlatMap gl fun z => cjOutcome3Prog M V VA W pw rk rm t z

end ProgsD3

/-! ### Specifications -/

section ProgSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of `q2bProg` for `|Φ| = p` and `|S| = s`. -/
def q2bCost (m p s : ℕ) : ℕ := 2 * m + 7 * p + 11 * s + 11

theorem RunsWithin.q2bProg (m : ℕ) (Φ Sl : List ℕ) :
    RunsWithin X body (Main.q2bProg m Φ Sl) (q2bD m Φ Sl) (q2bCost m Φ.length Sl.length) := by
  have h₁ := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .prod .nat .nat)
    (xs := Φ) (f := fun v => Prog.bind (Prog.op0 (.natLit 1)) fun one => Prog.op2 .pair v one)
    (F := fun v => (v, 1)) (c := 2) fun v _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])
  have h₂ := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .prod .nat .nat)
    (xs := List.range Sl.length)
    (f := fun i => Prog.bind (Prog.op2 .arrayGet Sl.toArray i) fun v =>
      Prog.bind (Prog.op0 (.natLit 2)) fun two => Prog.bind (Prog.op2 .add i two) fun c =>
        Prog.op2 .pair v c)
    (F := fun i => (Sl.getD i 0, i + 2)) (c := 4) fun i _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, Ty.default])
      case hc => simp [Prim.cost]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step h₁
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step h₂
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, Args.tail, List.length_map, List.length_append,
      Array.size_replicate, List.length_range, q2bCost]
    omega

/-- The cost of `q3Prog` for `|V| = p` and `|C| = s`. -/
def q3Cost (M p s : ℕ) : ℕ := 2 * M + 7 * p + 6 * s + 10

theorem RunsWithin.q3Prog (M : ℕ) (V C : List ℕ) :
    RunsWithin X body (Main.q3Prog M V C) (q3D M V C) (q3Cost M V.length C.length) := by
  have h₁ := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .prod .nat .nat)
    (xs := V) (f := fun v => Prog.bind (Prog.op0 (.natLit 2)) fun two => Prog.op2 .pair v two)
    (F := fun v => (v, 2)) (c := 2) fun v _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])
  have h₂ := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .prod .nat .nat)
    (xs := C) (f := fun v => Prog.bind (Prog.op0 (.natLit 1)) fun one => Prog.op2 .pair v one)
    (F := fun v => (v, 1)) (c := 2) fun v _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step h₁
    run_step h₂
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, Args.tail, List.length_map, List.length_append,
      Array.size_replicate, q3Cost]
    omega

theorem RunsWithin.cjOfProg (q : Array ℕ) (o : SoJTree.OutD) :
    RunsWithin X body (Main.cjOfProg q o) (cjOfD q o) 9 := by
  by_cases h : o.1 = 2
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, cjOfD, h])
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h]) _
      exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, cjOfD, h])
    case hc => simp [Prim.cost]

theorem RunsWithin.firstTupleProg (Φ : List ℕ) (j : ℕ) :
    RunsWithin X body (Main.firstTupleProg Φ j) (firstTupleD Φ j) (tuplesCost Φ.length j + 2) := by
  unfold firstTupleD
  rcases hT : tuplesD Φ j with _ | ⟨Sl, Ts⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tuplesProg Φ j)
      run_with Coherent.RunsWithin.caseList_eq_nil hT _
      exact RunsWithin.prim _ _
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tuplesProg Φ j)
      run_with Coherent.RunsWithin.caseList_eq_cons hT _
      exact RunsWithin.ret _
    case hc => simp

end ProgSpecs

section ProgSpecsD

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}

/-- The cost of one pair's coloured leaves: the choice within `Cc`, at most `Lc` leaves. -/
def cjPairCost (Cc Lc : ℕ) : ℕ := Cc + 2 + (Lc * (9 + 1 + 6) + 4)

/-- The cost of one tuple's coloured leaves in `cjLeaves2bProg`: `m = N - n`, `|Φ| = nΦ`,
`|S| = j`. -/
def cjTupleCost (m nΦ j Cc Lc : ℕ) : ℕ :=
  1 + q2bCost m nΦ j + (m * (3 * nΦ + 3 * j + 9) + m + 4) + (m + 1) + pairsCost m +
    (m * m * (cjPairCost Cc Lc + Lc + 6) + 4)

/-- The cost of `cjLeaves2bProg`. -/
def cjAllCost (m nΦ j Cc Lc : ℕ) : ℕ :=
  tuplesCost nΦ j + (nΦ ^ j * (cjTupleCost m nΦ j Cc Lc + m * m * Lc + 6) + 4)

/-- **The coloured Johnson leaves of Case 2b, as a program**, given a uniform bound `Cc` on the
cost of every choice and `Lc` on its number of leaves. -/
theorem RunsWithin.cjLeaves2bProg {N n : ℕ} {F : GroupData D.denote} {Φ : List ℕ}
    {j Cc Lc : ℕ}
    (hc : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      RunsWithin X body (Case2b.choiceProg N n F Φ Sl ab.1 ab.2)
        (choiceLeavesD X.O N n F Φ Sl ab.1 ab.2) Cc)
    (hL : ∀ Sl ∈ tuplesD Φ j, ∀ ab ∈ pairsD (phiSD (N - n) Φ Sl).length,
      (choiceLeavesD X.O N n F Φ Sl ab.1 ab.2).length ≤ Lc) :
    RunsWithin X body (Main.cjLeaves2bProg N n F Φ j) (cjLeaves2bD X.O N n F Φ j)
      (cjAllCost (N - n) Φ.length j Cc Lc) := by
  have hm' : ∀ Sl, (phiSD (N - n) Φ Sl).length ≤ N - n := fun Sl => length_phiSD_le _ _ _
  have hpair : ∀ Sl, (pairsD (phiSD (N - n) Φ Sl).length).length ≤ (N - n) * (N - n) :=
    fun Sl => (Case2b.length_pairsD_le _).trans (Nat.mul_le_mul (hm' Sl) (hm' Sl))
  have hcj : ∀ (q : Array ℕ) (l : List SoJTree.OutD), (l.flatMap (cjOfD q)).length ≤ l.length := by
    intro q l
    rw [List.length_flatMap]
    calc (l.map fun o => (cjOfD q o).length).sum ≤ (l.map fun _ => 1).sum :=
          List.sum_le_sum fun o _ => by unfold cjOfD; split_ifs <;> simp
      _ = l.length := by simp
  have htup := RunsWithin.tuplesProg (X := X) (body := body) Φ j
  apply RunsWithin.mono
  case h =>
    run_step htup
    refine Align.RunsWithin.joFlatMap (a' := .list .nat) (b' := cjTy)
      (F := cjChoice2bD X.O N n F Φ) (c := cjTupleCost (N - n) Φ.length j Cc Lc)
      (L := (N - n) * (N - n) * Lc) (fun Sl hSl => ?_) fun Sl hSl => ?_
    · have hSlen : Sl.length = j := mem_tuplesD_length hSl
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.q2bProg (N - n) Φ Sl)
        run_step (RunsWithin.phiSProg (N - n) Φ Sl)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.pairsProg _)
        refine Align.RunsWithin.joFlatMap (a' := .prod .nat .nat) (b' := cjTy)
          (F := fun ab => (choiceLeavesD X.O N n F Φ Sl ab.1 ab.2).flatMap
            (cjOfD (q2bD (N - n) Φ Sl)))
          (c := cjPairCost Cc Lc) (L := Lc) (fun ab hab => ?_)
          fun ab hab => (hcj _ _).trans (hL Sl hSl ab hab)
        have hfm := Align.RunsWithin.joFlatMap (X := X) (body := body) (a' := outTy) (b' := cjTy)
          (xs := choiceLeavesD X.O N n F Φ Sl ab.1 ab.2)
          (f := fun o => Main.cjOfProg (q2bD (N - n) Φ Sl) o) (F := cjOfD (q2bD (N - n) Φ Sl))
          (c := 9) (L := 1) (fun o _ => RunsWithin.cjOfProg _ o)
          (fun o _ => by unfold cjOfD; split_ifs <;> simp)
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step hc Sl hSl ab hab
          exact hfm
        case hc =>
          have := Nat.mul_le_mul_right (9 + 1 + 6) (hL Sl hSl ab hab)
          simp only [Prim.cost, cjPairCost]
          omega
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head, cjTupleCost]
        have h1 := pairsCost_mono (hm' Sl)
        have h2 := Nat.mul_le_mul_right (cjPairCost Cc Lc + Lc + 6) (hpair Sl)
        have h3 := hm' Sl
        rw [hSlen]
        omega
    · unfold cjChoice2bD
      rw [List.length_flatMap]
      calc ((pairsD (phiSD (N - n) Φ Sl).length).map fun ab =>
              ((choiceLeavesD X.O N n F Φ Sl ab.1 ab.2).flatMap
                (cjOfD (q2bD (N - n) Φ Sl))).length).sum ≤
            ((pairsD (phiSD (N - n) Φ Sl).length).map fun _ => Lc).sum :=
            List.sum_le_sum fun ab hab => (hcj _ _).trans (hL Sl hSl ab hab)
        _ = (pairsD (phiSD (N - n) Φ Sl).length).length * Lc := by
            rw [List.map_const', List.sum_replicate, smul_eq_mul]
        _ ≤ (N - n) * (N - n) * Lc := Nat.mul_le_mul_right _ (hpair Sl)
  case hc =>
    simp only [cjAllCost]
    have := Nat.mul_le_mul_right (cjTupleCost (N - n) Φ.length j Cc Lc + (N - n) * (N - n) * Lc +
      6) (length_tuplesD_le Φ j)
    omega

end ProgSpecsD

section ProgSpecs3

open GraphIso.Case3 GraphIso.Coherent

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of `c3ClsProg` on `m` points at a list of `L` points. -/
def c3ClsCost (k m L : ℕ) : ℕ := outPrefixCost k m L + (6 * m + 3) + (m * 4 + 2) + 1

theorem length_classA_le (col : List ℕ) (u : ℕ) : (classA col u).length ≤ col.length := by
  unfold classA
  exact (List.length_filter_le _ _).trans (by simp)

theorem length_c3ClsD_le (k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) :
    (c3ClsD k V W z).length ≤ V.length := by
  unfold c3ClsD
  split
  · simp
  · rw [length_classB]
    exact (length_classA_le _ _).trans (le_of_eq (length_col1D W z))

theorem RunsWithin.c3ClsProg (k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) :
    RunsWithin X body
      (Main.c3ClsProg V.toArray W (pwTab k V.length) (List.range k) (List.range V.length)
        (tOf V.length) z)
      (c3ClsD k V W z) (c3ClsCost k V.length z.length) := by
  set col := col1D k V.length W z with hcol
  have hlen : col.length = V.length := length_col1D W z
  have hdom := RunsWithin.domProg (X := X) (body := body) col (tOf V.length)
  rw [hlen] at hdom
  have hc1 := RunsWithin.col1Prog (X := X) (body := body) W (pwTab k V.length) k V.length
    z.length z.toArray
  unfold c3ClsD
  rw [← hcol]
  rcases hd : domA col (tOf V.length) with _ | u₀
  · rw [hd] at hdom
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hc1
      run_step (RunsWithin.prim _ _)
      run_step hdom
      run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Args.head_cons, c3ClsCost, outPrefixCost, length_col1A]
      omega
  · rw [hd] at hdom
    have hcl := RunsWithin.classProg (X := X) (body := body) col u₀
    rw [hlen] at hcl
    have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
      (xs := classA col u₀) (f := fun i => Prog.op2 .arrayGet V.toArray i)
      (F := fun i => V.getD i 0) (c := 1)
      fun i _ => (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, Ty.default])
    have hCl := length_classA_le col u₀
    rw [hlen] at hCl
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hc1
      run_step (RunsWithin.prim _ _)
      run_step hdom
      run_with RunsWithin.caseOpt_eq_some (show (some u₀ : Option ℕ) = some u₀ from rfl) _
      run_step hcl
      exact hmap
    case hc =>
      simp only [Prim.cost, Args.head_cons, c3ClsCost, outPrefixCost, length_col1A]
      have := Nat.mul_le_mul_right (1 + 3) hCl
      omega

/-- The cost of `cjOutcome3Prog` at a list of `L` points, the outcome within `Cz` and with at
most `Z + 1` structures. -/
def cjOut3Cost (M k m L Cz Z : ℕ) : ℕ :=
  c3ClsCost k m L + q3Cost M m m + Cz + ((Z + 1) * (9 + 1 + 6) + 4)

theorem RunsWithin.cjOutcome3Prog (M k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) :
    RunsWithin X body
      (Main.cjOutcome3Prog M V V.toArray W (pwTab k V.length) (List.range k)
        (List.range V.length) (tOf V.length) z)
      (cjOutcome3D M k V W z)
      (cjOut3Cost M k V.length z.length (outCostD M k V W z) (outSzD k V W z)) := by
  have hfm := Align.RunsWithin.joFlatMap (X := X) (body := body) (a' := outTy) (b' := cjTy)
    (xs := outcomeD M k V W z) (f := fun o => Main.cjOfProg (q3D M V (c3ClsD k V W z)) o)
    (F := cjOfD (q3D M V (c3ClsD k V W z))) (c := 9) (L := 1)
    (fun o _ => RunsWithin.cjOfProg _ o) (fun o _ => by unfold cjOfD; split_ifs <;> simp)
  have hos := length_outcomeD_le (k := k) M V W z
  have hC := length_c3ClsD_le k V W z
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.c3ClsProg k V W z)
    run_step (RunsWithin.q3Prog M V (c3ClsD k V W z))
    run_step (RunsWithin.outcomeProg M k V W z)
    exact hfm
  case hc =>
    have := Nat.mul_le_mul_right (9 + 1 + 6) hos
    simp only [cjOut3Cost, q3Cost]
    omega

theorem c3ClsCost_mono {k m L L' : ℕ} (h : L ≤ L') : c3ClsCost k m L ≤ c3ClsCost k m L' := by
  unfold c3ClsCost outPrefixCost
  omega

/-- The cost of `cjStructs3Prog`: the prefix, at most `k (m^k + 1)` good lists, each of
outcome cost at most `Cz` with at most `Z + 1` structures. -/
def cjStructs3Cost (M k m Cz Z : ℕ) : ℕ :=
  pipePrefixCost k m + (k * (m ^ k + 1) * (cjOut3Cost M k m k Cz Z + (Z + 1) + 6) + 4)

/-- **The coloured Johnson structures of Case 3, as a program**, for uniform bounds `Cz` on the
outcome's cost and `Z` on the `soj` size at each good list. -/
theorem RunsWithin.cjStructs3Prog (M k : ℕ) (V : List ℕ) (col : Array ℕ) {Cz Z : ℕ}
    (hC : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outCostD M k V (wlCD k V.length col) z ≤ Cz)
    (hZ : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outSzD k V (wlCD k V.length col) z ≤ Z) :
    RunsWithin X body (Main.cjStructs3Prog M k V col) (cjStructs3D M k V col)
      (cjStructs3Cost M k V.length Cz Z) := by
  have hcj : ∀ (q : Array ℕ) (l : List SoJTree.OutD), (l.flatMap (cjOfD q)).length ≤ l.length := by
    intro q l
    rw [List.length_flatMap]
    calc (l.map fun o => (cjOfD q o).length).sum ≤ (l.map fun _ => 1).sum :=
          List.sum_le_sum fun o _ => by unfold cjOfD; split_ifs <;> simp
      _ = l.length := by simp
  have hfm := Align.RunsWithin.joFlatMap (X := X) (body := body) (a' := .list .nat) (b' := cjTy)
    (xs := goodListsD k V.length (wlCD k V.length col))
    (f := fun z => Main.cjOutcome3Prog M V V.toArray (wlCD k V.length col) (pwTab k V.length)
      (List.range k) (List.range V.length) (tOf V.length) z)
    (F := cjOutcome3D M k V (wlCD k V.length col)) (c := cjOut3Cost M k V.length k Cz Z)
    (L := Z + 1)
    (fun z hz => (RunsWithin.cjOutcome3Prog M k V _ z).mono (by
      obtain ⟨x, hx, rfl, -⟩ := mem_goodListsD.1 hz
      have h1 := c3ClsCost_mono (k := k) (m := V.length)
        (show (x.map Fin.val).length ≤ k by rw [List.length_map]; omega)
      have h2 := hC _ hz
      have h3 := hZ _ hz
      unfold cjOut3Cost
      have := Nat.mul_le_mul_right (9 + 1 + 6) (Nat.add_le_add_right h3 1)
      omega))
    (fun z hz => (hcj _ _).trans ((length_outcomeD_le M V _ z).trans
      (Nat.add_le_add_right (hZ z hz) 1)))
  have hgl := length_goodListsD_le k V.length (wlCD k V.length col)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.wlCProg k _ col)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.pwTabProg k _)
    run_step (RunsWithin.tOfProg _)
    run_step (SoJProg.RunsWithin.goodListProg _ k _ _)
    exact hfm
  case hc =>
    have := Nat.mul_le_mul_right (cjOut3Cost M k V.length k Cz Z + (Z + 1) + 6) hgl
    simp only [Prim.cost, Prim.eval, Args.head_cons, cjStructs3Cost, pipePrefixCost]
    omega

end ProgSpecs3

end GraphIso.Main
