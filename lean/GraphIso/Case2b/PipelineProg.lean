module

public import GraphIso.Case2b.Pipeline
public import GraphIso.Align.JohnOps
public import GraphIso.Reductions.RestrictionProg
public import GraphIso.Coherent.WLProg
public import GraphIso.SoJProg.DLTest

/-!
# Case 2b on data: the programs of the leaves

Stage 14h, item 3 (`PLAN-14.md` §12), the programs without backend calls: the numbering of
`Φ ∖ S` (`phiSProg`), positions (`ptsProg`), halving (`halfProg`, for `t = (m' + 3) / 2`),
indices in a list (`idxProg`), moving index lists (`mapEProg`), the transposed orbital
colouring (`tcolProg`), transposition (`transProg`), trimming (`trimProg`), the extension to
the base (`extProg`), the leaves of a colouring (`leavesOfProg`: the components leaf, or the
trimmed leaves of `sojProg`, at a cost linear in the size `sojSz` of the `soj` tree it builds),
and the enumerations (`tuplesProg`, `pairsProg`). Each computes
its data model of `GraphIso/Case2b/Pipeline.lean` (`RunsWithin.*`), at an explicit polynomial
cost, and is well formed.
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.SplitJohnson GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Toolkit GraphIso.Sims

/-! ### Data models of the loops -/

/-- One step of halving: count pairs. -/
def halfStepD (st : ℕ × Bool) : ℕ × Bool := if st.2 then (st.1 + 1, false) else (st.1, true)

theorem foldl_halfStep (k : ℕ) :
    (List.range k).foldl (fun st _ => halfStepD st) (0, false) = (k / 2, decide (k % 2 = 1)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, halfStepD]
    by_cases h : k % 2 = 1
    · simp only [h, decide_true, ↓reduceIte]
      rw [show (k + 1) / 2 = k / 2 + 1 by omega, show (k + 1) % 2 = 0 by omega]
      rfl
    · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show (k + 1) / 2 = k / 2 by omega, show (k + 1) % 2 = 1 by omega]
      rfl

/-- One step of the index search for `v`: stop once found. -/
def idxStepD (v : ℕ) (st : ℕ × Bool) (x : ℕ) : ℕ × Bool :=
  if st.2 then st else if x == v then (st.1, true) else (st.1 + 1, false)

theorem foldl_idxStep_true (v : ℕ) (i : ℕ) :
    ∀ xs : List ℕ, xs.foldl (idxStepD v) (i, true) = (i, true)
  | [] => rfl
  | _ :: xs => by simp only [List.foldl_cons, idxStepD, ↓reduceIte, foldl_idxStep_true v i xs]

theorem foldl_idxStep (v : ℕ) : ∀ (xs : List ℕ) (i : ℕ),
    (xs.foldl (idxStepD v) (i, false)).1 = i + xs.idxOf v
  | [], i => by simp
  | x :: xs, i => by
    simp only [List.foldl_cons, idxStepD, Bool.false_eq_true, ↓reduceIte]
    by_cases h : x = v
    · subst h
      simp [foldl_idxStep_true, List.idxOf_cons_self]
    · have hb : (x == v) = false := by simp [h]
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      rw [foldl_idxStep v xs (i + 1), List.idxOf_cons_ne _ h]
      omega

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One halving step. -/
def halfBody (st : var (.prod .nat .bool)) : Prog S rec var (.prod .nat .bool) :=
  .bind (.op1 .fst st) fun q => .bind (.op1 .snd st) fun odd =>
  .ite odd
    (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add q one) fun q' =>
      .bind (.op0 (.boolLit false)) fun ff => .op2 .pair q' ff)
    (.bind (.op0 (.boolLit true)) fun tt => .op2 .pair q tt)

/-- `⌊k / 2⌋`. -/
def halfProg (k : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .range k) fun is => .bind (.op0 (.natLit 0)) fun z =>
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .pair z f) fun st₀ =>
  .bind (.foldList is st₀ fun st _ => halfBody st) fun st => .op1 .fst st

/-- One step of the index search. -/
def idxBody (v : var .nat) (st : var (.prod .nat .bool)) (x : var .nat) :
    Prog S rec var (.prod .nat .bool) :=
  .bind (.op1 .snd st) fun found =>
  .ite found (.ret st)
    (.bind (.op2 .natEq x v) fun e =>
      .ite e
        (.bind (.op1 .fst st) fun i => .bind (.op0 (.boolLit true)) fun tt => .op2 .pair i tt)
        (.bind (.op1 .fst st) fun i => .bind (.op0 (.natLit 1)) fun one =>
          .bind (.op2 .add i one) fun i' => .bind (.op0 (.boolLit false)) fun ff =>
          .op2 .pair i' ff))

/-- The index of `v` in `xs` (`xs.idxOf v`). -/
def idxProg (xs : var (.list .nat)) (v : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.boolLit false)) fun f =>
  .bind (.op2 .pair z f) fun st₀ =>
  .bind (.foldList xs st₀ fun st x => idxBody v st x) fun st => .op1 .fst st

/-- `mapE`: drop the indices at or above `len`, read the rest in `ΦSa`. -/
def mapEProg (ΦSa : var (.array .nat)) (len : var .nat) (l : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (Toolkit.filterList l fun i => .op2 .natLt i len) fun l' =>
  mapList l' fun i => .op2 .arrayGet ΦSa i

/-- `phiSD`: the base indices below `m` in `Φ` and not in `S`. -/
def phiSProg (m : var .nat) (Φ Sl : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range m) fun rm =>
  Toolkit.filterList rm fun v =>
    .bind (memProg v Φ) fun a => .bind (memProg v Sl) fun b => .bind (.op1 .not b) fun nb =>
    .op2 .and a nb

/-- `ptsD`: positions `n + v`. -/
def ptsProg (n : var .nat) (l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList l fun v => .op2 .add n v

/-- An entry of the transposed orbital colouring: `relColEntry` at `(j, i)`, with `c` the entry
`(a, b)` of `L`. -/
def tEntryProg (L : var (.array .nat)) (m c i j : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natEq j i) fun e =>
  .ite e (.op0 (.natLit 0))
    (.bind (mulProg j m) fun jm => .bind (.op2 .add jm i) fun idx =>
      .bind (.op2 .arrayGet L idx) fun x => .bind (.op2 .natEq x c) fun e' =>
      .ite e' (.op0 (.natLit 1)) (.op0 (.natLit 2)))

/-- `tcolD`: the colouring of the orbital of `(a, b)`, transposed. -/
def tcolProg (L : var (.array .nat)) (m a b : var .nat) : Prog S rec var (.array .nat) :=
  .bind (mulProg a m) fun am => .bind (.op2 .add am b) fun ab =>
  .bind (.op2 .arrayGet L ab) fun c =>
  matrixProg m fun i _ j => tEntryProg L m c i j

/-- An entry of the transpose. -/
def transEntryProg (W : var (.array .nat)) (m u v : var .nat) : Prog S rec var .nat :=
  .bind (mulProg v m) fun vm => .bind (.op2 .add vm u) fun i => .op2 .arrayGet W i

/-- `transD`: transposition. -/
def transProg (m : var .nat) (W : var (.array .nat)) : Prog S rec var (.array .nat) :=
  matrixProg m fun u _ v => transEntryProg W m u v

/-- The cell list of `v` after trimming: kept on `V₀`. -/
def trimEntryProg (V0 : var (.list .nat)) (fA : var (.array (.list .nat))) (v : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (memProg v V0) fun b => .ite b (.op2 .arrayGet fA v) (.op0 .nil)

/-- `trimD`: trim a Johnson leaf. -/
def trimProg (m : var .nat) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .fst o) fun tag => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .natEq tag two) fun is2 =>
  .ite is2
    (.bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun j => .bind (.op1 .fst j) fun V0 =>
      .bind (.op1 .snd j) fun j₂ => .bind (.op1 .fst j₂) fun cs => .bind (.op1 .snd j₂) fun j₃ =>
      .bind (.op1 .fst j₃) fun s => .bind (.op1 .snd j₃) fun fA =>
      .bind (.op1 .range m) fun rm =>
      .bind (mapList rm fun v => trimEntryProg V0 fA v) fun l =>
      .bind (.op1 .arrayOfList l) fun fA' => johnProg V0 cs s fA')
    (.ret o)

/-- The extended colour of `v`. -/
def extColProg (ΦS : var (.list .nat)) (col : var (.array .nat)) (v : var .nat) :
    Prog S rec var .nat :=
  .bind (memProg v ΦS) fun b =>
  .ite b
    (.bind (idxProg ΦS v) fun i => .bind (.op2 .arrayGet col i) fun c =>
      .bind (.op0 (.natLit 1)) fun one => .op2 .add c one)
    (.op0 (.natLit 0))

/-- The points of the base outside `ΦS`. -/
def restProg (rm ΦS : var (.list .nat)) : Prog S rec var (.list .nat) :=
  Toolkit.filterList rm fun w => .bind (memProg w ΦS) fun b => .op1 .not b

/-- The extended block of `v`. -/
def extBlkProg (ΦS : var (.list .nat)) (ΦSa : var (.array .nat)) (len : var .nat)
    (blk : var (.array (.list .nat))) (rest : var (.list .nat)) (v : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (memProg v ΦS) fun b =>
  .ite b
    (.bind (idxProg ΦS v) fun i => .bind (.op2 .arrayGet blk i) fun l => mapEProg ΦSa len l)
    (.ret rest)

/-- The extended cell list of `v`. -/
def extFProg (ΦS : var (.list .nat)) (fA : var (.array (.list .nat))) (v : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (memProg v ΦS) fun b =>
  .ite b (.bind (idxProg ΦS v) fun i => .op2 .arrayGet fA i) (.op0 .nil)

/-- The extension of a colored partition. -/
def extPartProg (m : var .nat) (ΦS : var (.list .nat)) (ΦSa : var (.array .nat))
    (len : var .nat) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun cb =>
  .bind (.op1 .fst cb) fun col => .bind (.op1 .snd cb) fun blk =>
  .bind (.op1 .range m) fun rm =>
  .bind (mapList rm fun v => extColProg ΦS col v) fun cl => .bind (.op1 .arrayOfList cl) fun col' =>
  .bind (restProg rm ΦS) fun rest =>
  .bind (mapList rm fun v => extBlkProg ΦS ΦSa len blk rest v) fun bl =>
  .bind (.op1 .arrayOfList bl) fun blk' => partProg col' blk'

/-- The extension of a Johnson embedding. -/
def extJohnProg (m : var .nat) (ΦS : var (.list .nat)) (ΦSa : var (.array .nat))
    (len : var .nat) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun j => .bind (.op1 .fst j) fun V0 =>
  .bind (.op1 .snd j) fun j₂ => .bind (.op1 .fst j₂) fun cs => .bind (.op1 .snd j₂) fun j₃ =>
  .bind (.op1 .fst j₃) fun s => .bind (.op1 .snd j₃) fun fA =>
  .bind (mapEProg ΦSa len V0) fun V0' => .bind (mapList cs fun c => mapEProg ΦSa len c) fun cs' =>
  .bind (.op1 .range m) fun rm => .bind (mapList rm fun v => extFProg ΦS fA v) fun fl =>
  .bind (.op1 .arrayOfList fl) fun fA' => johnProg V0' cs' s fA'

/-- `extD`: the extension of a leaf to the base. -/
def extProg (m : var .nat) (ΦS : var (.list .nat)) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .arrayOfList ΦS) fun ΦSa => .bind (.op1 .length ΦS) fun len =>
  .bind (.op1 .fst o) fun tag => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1 (extPartProg m ΦS ΦSa len o)
    (.bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq tag two) fun is2 =>
      .ite is2 (extJohnProg m ΦS ΦSa len o) (.ret o))

/-- The parameter `t = (m + 3) / 2` of `soj`. -/
def tParamProg (m : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 3)) fun three => .bind (.op2 .add m three) fun k => halfProg k

/-- The components leaf of colour `r`. -/
def compLeafProg (offs C : var (.array .nat)) (m : var .nat) (rm : var (.list .nat))
    (r : var .nat) : Prog S rec var outTy :=
  .bind (csCompPartProg offs C m rm r) fun lf => .bind (.op1 .snd lf) fun rest =>
  .bind (.op1 .fst rest) fun cb => .bind (.op1 .fst cb) fun col => .bind (.op1 .snd cb) fun blk =>
  partProg col blk

/-- `leavesOfD`: the components leaf of the least disconnected colour, or the trimmed leaves of
`soj`. -/
def leavesOfProg (m : var .nat) (C : var (.array .nat)) : Prog S rec var (.list outTy) :=
  .bind (csOffsProg m) fun offs => .bind (.op1 .range m) fun rm =>
  .bind (csDisconnProg offs C rm) fun ds =>
  .caseList ds
    (.bind (tParamProg m) fun t => .bind (sojProg m t C) fun ls => mapList ls fun o => trimProg m o)
    (fun r rs => .bind (.op2 .cons r rs) fun rl => .bind (Toolkit.minProg rl) fun r₀ =>
      .bind (compLeafProg offs C m rm r₀) fun o => .bind (.op0 .nil) fun nil => .op2 .cons o nil)

/-- The entries of `l` not in `T`, put in front of `T`. -/
def tupExtProg (l T : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  .bind (Toolkit.filterList l fun x => .bind (memProg x T) fun b => .op1 .not b) fun xs =>
  mapList xs fun x => .op2 .cons x T

/-- `tupStep`. -/
def tupStepProg (l : var (.list .nat)) (acc : var (.list (.list .nat))) :
    Prog S rec var (.list (.list .nat)) :=
  Align.joFlatMap acc fun T => tupExtProg l T

/-- `tuplesD`: `j` steps from `[[]]`. -/
def tuplesProg (l : var (.list .nat)) (j : var .nat) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range j) fun js => .bind (.op0 .nil) fun e => .bind (.op0 .nil) fun nil =>
  .bind (.op2 .cons e nil) fun init =>
  .foldList js init fun acc _ => tupStepProg l acc

/-- `pairsD`. -/
def pairsProg (m : var .nat) : Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op1 .range m) fun rm =>
  Align.joFlatMap rm fun a =>
    .bind (Toolkit.filterList rm fun b => .bind (.op2 .natEq b a) fun e => .op1 .not e) fun bs =>
    mapList bs fun b => .op2 .pair a b

end Programs

/-! ### Specs -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.halfProg (k : ℕ) :
    RunsWithin X body (Case2b.halfProg k) (k / 2) (9 * k + 7) := by
  have hstep : ∀ (st : ℕ × Bool) (_x : ℕ), RunsWithin X body (halfBody st) (halfStepD st) 7 := by
    intro st _
    unfold halfBody
    rcases st with ⟨q, odd⟩
    cases odd
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (q, false).2 = false from rfl) _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (q, true).2 = true from rfl) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .bool) (F := fun st _ => halfStepD st) (cf := fun _ => 7)
    (List.range k) ((0 : ℕ), false) fun acc x _ => hstep acc x
  rw [foldl_halfStep] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head, List.map_const', List.sum_replicate,
      List.length_range, smul_eq_mul]
    omega

theorem RunsWithin.idxProg (xs : List ℕ) (v : ℕ) :
    RunsWithin X body (Case2b.idxProg xs v) (xs.idxOf v) (10 * xs.length + 5) := by
  have hstep : ∀ (st : ℕ × Bool) (x : ℕ), RunsWithin X body (idxBody v st x) (idxStepD v st x)
      9 := by
    intro st x
    unfold idxBody
    rcases st with ⟨i, found⟩
    cases found
    · by_cases hx : x = v
      · have he : (x == v) = true := by simp [hx]
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (i, false).2 = false from rfl) _
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (show (x == v) = true from he) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [idxStepD, he, Prim.eval])
        case hc => simp [Prim.cost]
      · have he : (x == v) = false := by simp [hx]
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (i, false).2 = false from rfl) _
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (x == v) = false from he) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [idxStepD, he, Prim.eval])
        case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_pos (show (i, true).2 = true from rfl)
          ((RunsWithin.ret _).of_eq (by simp [idxStepD]))
      case hc => simp [Prim.cost]
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .bool) (F := idxStepD v) (cf := fun _ => 9)
    xs ((0 : ℕ), false) fun acc x _ => hstep acc x
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, foldl_idxStep])
  case hc =>
    simp only [Prim.cost, List.map_const', List.sum_replicate, smul_eq_mul]
    omega

theorem RunsWithin.mapEProg (ΦS l : List ℕ) :
    RunsWithin X body (Case2b.mapEProg ΦS.toArray ΦS.length l) (mapE ΦS l)
      (9 * l.length + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.filterList (P := fun i => decide (i < ΦS.length)) (c := 1)
      fun i _ => (RunsWithin.prim _ _).of_eq (by simp [Prim.eval]))
    exact RunsWithin.mapList_le (a' := .nat) (b' := .nat) (F := fun i => ΦS.getD i 0) (c := 1)
      fun i _ => (RunsWithin.prim _ _).of_eq
        (by simp [Prim.eval, List.getD_eq_getElem?_getD, Ty.default])
  case hc =>
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (List.length_filter_le _ _)) _) _) ?_
    omega

theorem RunsWithin.phiSProg (m : ℕ) (Φ S' : List ℕ) :
    RunsWithin X body (Case2b.phiSProg m Φ S') (phiSD m Φ S')
      (m * (3 * Φ.length + 3 * S'.length + 9) + m + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.filterList (a' := .nat) (P := fun v : ℕ => decide (v ∈ Φ ∧ v ∉ S'))
      (c := 3 * Φ.length + 3 * S'.length + 5) fun v _ => by
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.memProg v Φ)
          run_step (RunsWithin.memProg v S')
          run_step (RunsWithin.prim _ _)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
        case hc => simp [Prim.cost]; omega
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range]
    ring_nf
    omega

theorem RunsWithin.ptsProg (n : ℕ) (l : List ℕ) :
    RunsWithin X body (Case2b.ptsProg n l) (ptsD n l) (4 * l.length + 2) :=
  (RunsWithin.mapList_le (F := (n + ·)) (c := 1) fun v _ => RunsWithin.prim _ _).mono
    (by omega)

theorem RunsWithin.tEntryProg (L : Array ℕ) (m a b i j : ℕ) :
    RunsWithin X body (Case2b.tEntryProg L m (get L (a * m + b)) i j)
      (relColEntry L m a b j i) (3 * j + 9) := by
  unfold Case2b.tEntryProg relColEntry
  by_cases hji : j = i
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_pos (show (j == i) = true by simp [hji])
        ((RunsWithin.prim _ _).of_eq (by simp [hji, Prim.eval]))
    case hc => simp [Prim.cost]
  · have hji' : (j == i) = false := by simp [hji]
    by_cases hx : get L (j * m + i) = get L (a * m + b)
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg hji' _
        run_step (RunsWithin.mulProg j m)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_pos (show (get L (j * m + i) == get L (a * m + b)) = true by simp [hx])
          ((RunsWithin.prim _ _).of_eq (by simp [hji, hx, Prim.eval]))
      case hc => simp [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg hji' _
        run_step (RunsWithin.mulProg j m)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_neg
          (show (get L (j * m + i) == get L (a * m + b)) = false by simp [hx])
          ((RunsWithin.prim _ _).of_eq (by simp [hji, hx, Prim.eval]))
      case hc => simp [Prim.cost]; omega

theorem RunsWithin.tcolProg (L : Array ℕ) (m a b : ℕ) :
    RunsWithin X body (Case2b.tcolProg L m a b) (tcolD L m a b)
      (3 * a + 4 + matrixCost m (3 * m + 9)) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mulProg a m)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.matrixProg (c := 3 * m + 9) (F := fun i j => relColEntry L m a b j i)
      fun u _ v hv => (RunsWithin.tEntryProg L m a b u v).mono (by omega)
  case hc => simp [Prim.cost]; omega

theorem RunsWithin.transEntryProg (W : Array ℕ) (m u v : ℕ) :
    RunsWithin X body (Case2b.transEntryProg W m u v) (get W (v * m + u)) (3 * v + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mulProg v m)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.transProg (m : ℕ) (W : Array ℕ) :
    RunsWithin X body (Case2b.transProg m W) (transD m W) (matrixCost m (3 * m + 4)) :=
  RunsWithin.matrixProg (c := 3 * m + 4) (F := fun u v => get W (v * m + u))
    fun u _ v hv => (RunsWithin.transEntryProg W m u v).mono (by omega)

theorem RunsWithin.trimEntryProg (V0 : List ℕ) (fA : Array (List ℕ)) (v : ℕ) :
    RunsWithin X body (Case2b.trimEntryProg V0 fA v) (if v ∈ V0 then fA.getD v [] else [])
      (3 * V0.length + 3) := by
  by_cases h : v ∈ V0
  · rw [ite_eq_left h]
    refine RunsWithin.bind_le (RunsWithin.memProg v V0)
      (RunsWithin.ite_pos (decide_eq_true h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp [Prim.cost]
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg v V0)
      (RunsWithin.ite_neg (decide_eq_false h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp [Prim.cost]

/-- The cost of `trimProg` for `m` points and `|V₀| ≤ V`. -/
def trimCost (m V : ℕ) : ℕ := m * (3 * V + 6) + 2 * m + 30

theorem RunsWithin.trimProg (m : ℕ) (o : OutD) :
    RunsWithin X body (Case2b.trimProg m o) (trimD m o) (trimCost m o.2.2.1.length) := by
  unfold trimD
  by_cases h : o.1 = 2
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le (a' := .nat) (b' := .list .nat)
        (F := fun v => if v ∈ o.2.2.1 then o.2.2.2.2.2.getD v [] else [])
        fun v _ => RunsWithin.trimEntryProg o.2.2.1 o.2.2.2.2.2 v)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.johnProg _ _ _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map, trimCost]
      ring_nf
      omega
  · rw [ite_eq_right h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h]) (RunsWithin.ret _)
    case hc => simp [Prim.cost, trimCost]

theorem RunsWithin.extColProg (ΦS : List ℕ) (col : Array ℕ) (v : ℕ) :
    RunsWithin X body (Case2b.extColProg ΦS col v)
      (if v ∈ ΦS then get col (ΦS.idxOf v) + 1 else 0) (13 * ΦS.length + 10) := by
  by_cases h : v ∈ ΦS
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.memProg v ΦS)
      run_with RunsWithin.ite_pos (decide_eq_true h) _
      run_step (RunsWithin.idxProg ΦS v)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc => simp [Prim.cost]; omega
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg v ΦS)
      (RunsWithin.ite_neg (decide_eq_false h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp [Prim.cost]
    omega

theorem RunsWithin.restProg (rm ΦS : List ℕ) :
    RunsWithin X body (Case2b.restProg rm ΦS) (rm.filter fun w => decide (w ∉ ΦS))
      (rm.length * (3 * ΦS.length + 6) + 3) :=
  RunsWithin.filterList (a' := .nat) (P := fun w : ℕ => decide (w ∉ ΦS)) (c := 3 * ΦS.length + 2)
    fun w _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.memProg w ΦS)
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
      case hc => simp [Prim.cost]

theorem RunsWithin.extBlkProg (ΦS : List ℕ) (blk : Array (List ℕ)) (rest : List ℕ) (v : ℕ)
    {L : ℕ} (hL : ∀ i, (blk.getD i []).length ≤ L) :
    RunsWithin X body (Case2b.extBlkProg ΦS ΦS.toArray ΦS.length blk rest v)
      (if v ∈ ΦS then mapE ΦS (blk.getD (ΦS.idxOf v) []) else rest)
      (13 * ΦS.length + 9 * L + 13) := by
  by_cases h : v ∈ ΦS
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.memProg v ΦS)
      run_with RunsWithin.ite_pos (decide_eq_true h) _
      run_step (RunsWithin.idxProg ΦS v)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.mapEProg ΦS (blk.getD (ΦS.idxOf v) [])
    case hc =>
      have := hL (ΦS.idxOf v)
      simp only [Prim.cost]
      omega
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg v ΦS)
      (RunsWithin.ite_neg (decide_eq_false h) (RunsWithin.ret _)) ?_
    omega

theorem RunsWithin.extFProg (ΦS : List ℕ) (fA : Array (List ℕ)) (v : ℕ) :
    RunsWithin X body (Case2b.extFProg ΦS fA v)
      (if v ∈ ΦS then fA.getD (ΦS.idxOf v) [] else []) (13 * ΦS.length + 9) := by
  by_cases h : v ∈ ΦS
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.memProg v ΦS)
      run_with RunsWithin.ite_pos (decide_eq_true h) _
      run_step (RunsWithin.idxProg ΦS v)
      exact RunsWithin.prim _ _
    case hc => simp [Prim.cost]; omega
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg v ΦS)
      (RunsWithin.ite_neg (decide_eq_false h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp [Prim.cost]
    omega

/-- The cost of `extProg` for `m` base points, `|ΦS| = P` and leaf lists of length at most `L`
(`outSize`). -/
def extCost (m P L : ℕ) : ℕ := 2 * P + 60 + m * (32 * P + 9 * L + 40) + L * (9 * L + 8) + 9 * L

theorem RunsWithin.extPartProg (m : ℕ) (ΦS : List ℕ) (o : OutD) :
    RunsWithin X body (Case2b.extPartProg m ΦS ΦS.toArray ΦS.length o)
      (partD
        ((List.range m).map fun v =>
          if v ∈ ΦS then get o.2.1.1 (ΦS.idxOf v) + 1 else 0).toArray
        ((List.range m).map fun v =>
          if v ∈ ΦS then mapE ΦS (o.2.1.2.getD (ΦS.idxOf v) [])
          else (List.range m).filter fun w => decide (w ∉ ΦS)).toArray)
      (m * (32 * ΦS.length + 9 * outSize o + 40) + 30) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .nat)
      (F := fun v => if v ∈ ΦS then get o.2.1.1 (ΦS.idxOf v) + 1 else 0)
      fun v _ => RunsWithin.extColProg ΦS o.2.1.1 v)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.restProg (List.range m) ΦS)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .list .nat)
      (F := fun v => if v ∈ ΦS then mapE ΦS (o.2.1.2.getD (ΦS.idxOf v) [])
        else (List.range m).filter fun w => decide (w ∉ ΦS))
      fun v _ => RunsWithin.extBlkProg ΦS o.2.1.2 _ v (outSize_blk o))
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.partProg _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map]
    ring_nf
    omega

theorem RunsWithin.extJohnProg (m : ℕ) (ΦS : List ℕ) (o : OutD) :
    RunsWithin X body (Case2b.extJohnProg m ΦS ΦS.toArray ΦS.length o)
      (johnD (mapE ΦS o.2.2.1) (o.2.2.2.1.map (mapE ΦS)) o.2.2.2.2.1
        ((List.range m).map fun v =>
          if v ∈ ΦS then o.2.2.2.2.2.getD (ΦS.idxOf v) [] else []).toArray)
      (m * (13 * ΦS.length + 14) + outSize o * (9 * outSize o + 8) + 9 * outSize o + 40) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapEProg ΦS o.2.2.1)
    run_step (RunsWithin.mapList_le (a' := .list .nat) (b' := .list .nat) (F := mapE ΦS)
      (c := 9 * outSize o + 5) fun c hc =>
        (RunsWithin.mapEProg ΦS c).mono (by have := outSize_cell o hc; omega))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .list .nat)
      (F := fun v => if v ∈ ΦS then o.2.2.2.2.2.getD (ΦS.idxOf v) [] else [])
      fun v _ => RunsWithin.extFProg ΦS o.2.2.2.2.2 v)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.johnProg _ _ _ _
  case hc =>
    have h1 := outSize_V0 o
    have h2 := outSize_cs o
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map]
    have h3 : o.2.2.2.1.length * (9 * outSize o + 5 + 3) ≤ outSize o * (9 * outSize o + 8) :=
      Nat.mul_le_mul_right _ h2
    ring_nf at h3 ⊢
    omega

theorem RunsWithin.extProg (m : ℕ) (ΦS : List ℕ) (o : OutD) :
    RunsWithin X body (Case2b.extProg m ΦS o) (extD m ΦS o)
      (extCost m ΦS.length (outSize o)) := by
  unfold extD
  by_cases h1 : o.1 = 1
  · rw [ite_eq_left h1]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h1]) _
      exact RunsWithin.extPartProg m ΦS o
    case hc =>
      simp only [Prim.cost, Args.head, extCost]
      nlinarith
  · rw [ite_eq_right h1]
    by_cases h2 : o.1 = 2
    · rw [ite_eq_left h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h2]) _
        exact RunsWithin.extJohnProg m ΦS o
      case hc =>
        simp only [Prim.cost, Args.head, extCost]
        nlinarith
    · rw [ite_eq_right h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h2]) (RunsWithin.ret _)
      case hc =>
        simp only [Prim.cost, Args.head, extCost]
        omega

theorem cp2_count_le_size {C O : Type*} : ∀ t : CTree C O, t.count ≤ t.size
  | .leaf _ => le_refl 1
  | .node S k => by
    simp only [CTree.count, CTree.size]
    have : ∑ c ∈ S, (k c).count ≤ ∑ c ∈ S, ((k c).size + 1) :=
      Finset.sum_le_sum fun c _ => (cp2_count_le_size (k c)).trans (Nat.le_succ _)
    omega

theorem length_sojD (m t : ℕ) (C : Array ℕ) :
    (sojD m t C).length = (soj (colOf m C) t).count := by
  rw [← CTree.card_leafMs, ← sojD_leafMs]
  simp

theorem RunsWithin.tParamProg (m : ℕ) :
    RunsWithin X body (Case2b.tParamProg m) ((m + 3) / 2) (9 * m + 36) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.halfProg _
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

theorem RunsWithin.compLeafProg (m : ℕ) (C : Array ℕ) (r : ℕ) :
    RunsWithin X body (Case2b.compLeafProg (offsArr m) C m (List.range m) r) (compLeafD m C r)
      (compPartCost m + 16) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.csCompPartProg (offsArr m) C m r le_rfl (by simp))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.partProg _ _
  case hc => simp [Prim.cost]

/-- The cost of the `soj` branch of `leavesOfProg`, for a tree of size `sz`. -/
def sojBranchCost (m sz : ℕ) : ℕ :=
  9 * m + 36 + (300 * (m + 1) ^ 4 + 30 * m + 40 +
    (stepK m ((m + 3) / 2) ((m + 3) / 2) + 11) * (((m + 3) / 2 + 2) * sz)) +
    (sz * (trimCost m (outB m ((m + 3) / 2)) + 3) + 2)

/-- The size of the `soj` tree that `leavesOfProg` builds, `0` when a colour is disconnected and
no tree is built. -/
def sojSz (m : ℕ) (C : Array ℕ) : ℕ :=
  match disconnD (colFn m C) (List.range m) with
  | [] => (soj (colOf m C) ((m + 3) / 2)).size
  | _ :: _ => 0

/-- The cost of `leavesOfProg`, for a `soj` tree of size `sz`. -/
def leavesOfCost (m sz : ℕ) : ℕ :=
  10 * m + 9 + (m + 1) + disconnCost m + 1 + sojBranchCost m sz +
    (1 + (3 * (m * m) + 2) + (compPartCost m + 16) + 2)

theorem trimCost_mono (m : ℕ) {V V' : ℕ} (h : V ≤ V') : trimCost m V ≤ trimCost m V' := by
  unfold trimCost
  have := Nat.mul_le_mul_left m (show 3 * V + 6 ≤ 3 * V' + 6 by omega)
  omega

theorem RunsWithin.leavesOfProg (m : ℕ) (C : Array ℕ) :
    RunsWithin X body (Case2b.leavesOfProg m C) (leavesOfD m C) (leavesOfCost m (sojSz m C)) := by
  unfold leavesOfD sojSz
  have hrm : (List.range m).length ≤ m := by simp
  rcases hd : disconnD (colFn m C) (List.range m) with _ | ⟨r, rs⟩
  · -- the `soj` branch
    set t := (m + 3) / 2 with ht
    have hmt : m ≤ 2 * t := by omega
    have hout := sojProg_outSize (m := m) (t := t) C hmt
    have hlen : (worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t C)).2
        (splitI (tr_sojItems m t C)).1).length ≤ (soj (colOf m C) t).size :=
      (length_sojD m t C).le.trans (cp2_count_le_size _)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.csOffsProg m)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.csDisconnProg (offsArr m) C hrm)
      run_with Coherent.RunsWithin.caseList_eq_nil
        (show disconnD (fA (offsArr m) C) (List.range m) = [] from hd) _
      run_step (RunsWithin.tParamProg m)
      run_step (RunsWithin.sojProg m t C hmt)
      exact RunsWithin.mapList_le (a' := outTy) (b' := outTy) (F := trimD m)
        (c := trimCost m (outB m t)) fun o ho =>
          (RunsWithin.trimProg m o).mono (trimCost_mono m ((outSize_V0 o).trans (hout o ho)))
    case hc =>
      simp only [Prim.cost, Args.head, leavesOfCost, sojBranchCost]
      have := Nat.mul_le_mul_right (trimCost m (outB m t) + 3) hlen
      rw [← ht] at *
      omega
  · -- the components branch
    have hds : (r :: rs).length ≤ m * m := by
      rw [← hd]
      exact length_disconnD_le _ hrm
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.csOffsProg m)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.csDisconnProg (offsArr m) C hrm)
      run_with Coherent.RunsWithin.caseList_eq_cons
        (show disconnD (fA (offsArr m) C) (List.range m) = r :: rs from hd) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.csMinProg (r :: rs))
      run_step (RunsWithin.compLeafProg m C (minD (r :: rs)))
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Args.head, leavesOfCost]
      omega

theorem RunsWithin.tupExtProg (l T : List ℕ) :
    RunsWithin X body (Case2b.tupExtProg l T)
      ((l.filter fun x => decide (x ∉ T)).map (· :: T))
      (l.length * (3 * T.length + 10) + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.filterList (a' := .nat) (P := fun x : ℕ => decide (x ∉ T))
      (c := 3 * T.length + 2) fun x _ => by
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.memProg x T)
          exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
        case hc => simp [Prim.cost])
    exact RunsWithin.mapList_le (a' := .nat) (b' := .list .nat) (F := (· :: T)) (c := 1)
      fun x _ => RunsWithin.prim _ _
  case hc =>
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right
      (Nat.mul_le_mul_right _ (List.length_filter_le _ _)) _) _) ?_
    ring_nf
    omega

/-- The cost of `tupStepProg` on `A` tuples of length at most `j` over a list of `L` entries. -/
def tupStepCost (L A j : ℕ) : ℕ := A * (L * (3 * j + 10) + 5 + L + 6) + 4

theorem RunsWithin.tupStepProg (l : List ℕ) (acc : List (List ℕ)) {j : ℕ}
    (hj : ∀ T ∈ acc, T.length ≤ j) :
    RunsWithin X body (Case2b.tupStepProg l acc) (tupStep l acc)
      (tupStepCost l.length acc.length j) := by
  unfold Case2b.tupStepProg tupStep tupStepCost
  refine (Align.RunsWithin.joFlatMap (L := l.length) (c := l.length * (3 * j + 10) + 5)
    (fun T hT => (RunsWithin.tupExtProg l T).mono ?_) fun T _ => ?_).mono le_rfl
  · have := Nat.mul_le_mul_left l.length (show 3 * T.length + 10 ≤ 3 * j + 10 by
      have := hj T hT; omega)
    omega
  · rw [List.length_map]
    exact List.length_filter_le _ _

theorem mem_tuplesD_length {l : List ℕ} {j : ℕ} {T : List ℕ} (h : T ∈ tuplesD l j) :
    T.length = j :=
  ((mem_tuplesD l j).1 h).1

/-- The cost of `tuplesProg` for `L` entries and `j` steps. -/
def tuplesCost (L j : ℕ) : ℕ := j + 5 + j * (tupStepCost L ((L + 1) ^ j) j + 1)

theorem cp2_tuples_fold (l : List ℕ) (J : ℕ) : ∀ (xs : List ℕ) (i : ℕ), i + xs.length ≤ J →
    RunsWithin X body (Prog.foldList (a := .nat) (b := .list (.list .nat)) xs (tuplesD l i)
        fun acc _ => Case2b.tupStepProg l acc)
      (tuplesD l (i + xs.length)) (xs.length * (tupStepCost l.length ((l.length + 1) ^ J) J + 1))
  | [], i, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, i, h => by
    have hlen : (tuplesD l i).length ≤ (l.length + 1) ^ J :=
      (length_tuplesD_le l i).trans ((Nat.pow_le_pow_left (Nat.le_succ _) i).trans
        (Nat.pow_le_pow_right (Nat.succ_pos _) (by simp at h; omega)))
    have hstep := RunsWithin.tupStepProg (X := X) (body := body) l (tuplesD l i) (j := J)
      fun T hT => by rw [mem_tuplesD_length hT]; simp at h; omega
    have hrest := cp2_tuples_fold l J xs (i + 1) (by simp at h; omega)
    refine (RunsWithin.foldList_cons (hstep.of_eq (tuplesD_succ l i).symm) hrest).of_eq
      (by simp only [List.length_cons]; congr 1; omega) |>.mono ?_
    have : tupStepCost l.length (tuplesD l i).length J ≤
        tupStepCost l.length ((l.length + 1) ^ J) J := by
      unfold tupStepCost
      have := Nat.mul_le_mul_right (l.length * (3 * J + 10) + 5 + l.length + 6) hlen
      omega
    simp only [List.length_cons]
    ring_nf
    ring_nf at this
    omega

theorem RunsWithin.tuplesProg (l : List ℕ) (j : ℕ) :
    RunsWithin X body (Case2b.tuplesProg l j) (tuplesD l j) (tuplesCost l.length j) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact (cp2_tuples_fold l j (List.range j) 0 (by simp)).of_eq (by simp)
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, tuplesCost]
    omega

/-- The cost of `pairsProg`. -/
def pairsCost (m : ℕ) : ℕ := m + 1 + (m * (m * 10 + 6 + m + 6) + 4)

theorem RunsWithin.pairsProg (m : ℕ) :
    RunsWithin X body (Case2b.pairsProg m) (pairsD m) (pairsCost m) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact Align.RunsWithin.joFlatMap (a' := .nat) (b' := .prod .nat .nat) (L := m)
      (c := m * 10 + 6) (F := fun a : ℕ => ((List.range m).filter fun b => b != a).map (a, ·))
      (fun a _ => by
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.filterList (a' := .nat) (P := fun b : ℕ => b != a) (c := 2)
            fun b _ => by
              apply RunsWithin.mono
              case h =>
                run_step (RunsWithin.prim _ _)
                exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, bne])
              case hc => simp [Prim.cost])
          exact RunsWithin.mapList_le (a' := .nat) (b' := .prod .nat .nat) (F := (a, ·)) (c := 1)
            fun b _ => RunsWithin.prim _ _
        case hc =>
          refine le_trans (Nat.add_le_add_left (Nat.add_le_add_right
            (Nat.mul_le_mul_right _ (List.length_filter_le _ _)) _) _) ?_
          simp only [Prim.eval, List.length_range]
          omega)
      fun a _ => by
        rw [List.length_map]
        exact (List.length_filter_le _ _).trans (by simp)
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, pairsCost]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_halfProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (halfProg k₁) (halfProg k₂) := by
  unfold halfProg halfBody
  prog_wf

theorem wf_idxProg {xs₁ : var₁ (.list .nat)} {xs₂ : var₂ (.list .nat)} {v₁ : var₁ .nat}
    {v₂ : var₂ .nat} (hxs : ⟨.list .nat, xs₁, xs₂⟩ ∈ Γ) (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (idxProg xs₁ v₁) (idxProg xs₂ v₂) := by
  unfold idxProg idxBody
  prog_wf

theorem wf_mapEProg {a₁ : var₁ (.array .nat)} {a₂ : var₂ (.array .nat)} {n₁ : var₁ .nat}
    {n₂ : var₂ .nat} {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)}
    (ha : ⟨.array .nat, a₁, a₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (mapEProg a₁ n₁ l₁) (mapEProg a₂ n₂ l₂) := by
  unfold mapEProg Toolkit.filterList mapList
  prog_wf

theorem wf_phiSProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {Φ₁ S₁ : var₁ (.list .nat)}
    {Φ₂ S₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ)
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (phiSProg m₁ Φ₁ S₁) (phiSProg m₂ Φ₂ S₂) := by
  unfold phiSProg Toolkit.filterList memProg anyList
  prog_wf

theorem wf_ptsProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {l₁ : var₁ (.list .nat)}
    {l₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (ptsProg n₁ l₁) (ptsProg n₂ l₂) := by
  unfold ptsProg mapList
  prog_wf

theorem wf_tcolProg {L₁ : var₁ (.array .nat)} {L₂ : var₂ (.array .nat)} {m₁ a₁ b₁ : var₁ .nat}
    {m₂ a₂ b₂ : var₂ .nat} (hL : ⟨.array .nat, L₁, L₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ) (hb : ⟨.nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tcolProg L₁ m₁ a₁ b₁) (tcolProg L₂ m₂ a₂ b₂) := by
  unfold tcolProg tEntryProg mulProg matrixProg rowsProg mapList
  prog_wf

theorem wf_transProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {W₁ : var₁ (.array .nat)}
    {W₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (transProg m₁ W₁) (transProg m₂ W₂) := by
  unfold transProg transEntryProg mulProg matrixProg rowsProg mapList
  prog_wf

theorem wf_trimProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (trimProg m₁ o₁) (trimProg m₂ o₂) := by
  unfold trimProg trimEntryProg johnProg mkOutProg emptyNatArrProg emptyLstArrProg memProg
    anyList mapList
  prog_wf

theorem wf_extPartProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {Φ₁ : var₁ (.list .nat)}
    {Φ₂ : var₂ (.list .nat)} {a₁ : var₁ (.array .nat)} {a₂ : var₂ (.array .nat)}
    {n₁ : var₁ .nat} {n₂ : var₂ .nat} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (ha : ⟨.array .nat, a₁, a₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extPartProg m₁ Φ₁ a₁ n₁ o₁)
      (extPartProg m₂ Φ₂ a₂ n₂ o₂) := by
  unfold extPartProg extColProg restProg extBlkProg mapEProg idxProg idxBody partProg mkOutProg
    emptyLstArrProg memProg anyList Toolkit.filterList mapList
  prog_wf

theorem wf_extJohnProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {Φ₁ : var₁ (.list .nat)}
    {Φ₂ : var₂ (.list .nat)} {a₁ : var₁ (.array .nat)} {a₂ : var₂ (.array .nat)}
    {n₁ : var₁ .nat} {n₂ : var₂ .nat} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (ha : ⟨.array .nat, a₁, a₂⟩ ∈ Γ)
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extJohnProg m₁ Φ₁ a₁ n₁ o₁)
      (extJohnProg m₂ Φ₂ a₂ n₂ o₂) := by
  unfold extJohnProg extFProg mapEProg idxProg idxBody johnProg mkOutProg emptyNatArrProg
    emptyLstArrProg memProg anyList Toolkit.filterList mapList
  prog_wf

theorem wf_extProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {Φ₁ : var₁ (.list .nat)}
    {Φ₂ : var₂ (.list .nat)} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hΦ : ⟨.list .nat, Φ₁, Φ₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extProg m₁ Φ₁ o₁) (extProg m₂ Φ₂ o₂) := by
  unfold extProg
  refine .bind (.prim _ (.cons hΦ .nil)) fun a₁ a₂ => .bind (.prim _ (.cons (by simp [hΦ]) .nil))
    fun n₁ n₂ => .bind (.prim _ (.cons (by simp [ho]) .nil)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil)))
    fun _ _ => .ite (by simp) ?_ ?_
  · exact wf_extPartProg (by simp [hm]) (by simp [hΦ]) (by simp) (by simp) (by simp [ho])
  · exact .bind (.prim _ .nil) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .ite (by simp) (wf_extJohnProg (by simp [hm]) (by simp [hΦ]) (by simp) (by simp)
        (by simp [ho])) (.ret (by simp [ho]))

theorem cp2_wf_csOffsProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (csOffsProg m₁) (csOffsProg m₂) := by
  unfold csOffsProg
  prog_wf

theorem cp2_wf_csCompProg {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)}
    {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} {r₁ x₁ : var₁ .nat} {r₂ x₂ : var₂ .nat}
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (csCompProg o₁ c₁ ps₁ r₁ x₁)
      (csCompProg o₂ c₂ ps₂ r₂ x₂) := by
  unfold csCompProg csCompStepProg csMemProg csColProg anyList Toolkit.filterList
  prog_wf

theorem cp2_wf_csDisconnProg {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)}
    {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (csDisconnProg o₁ c₁ ps₁) (csDisconnProg o₂ c₂ ps₂) := by
  unfold csDisconnProg
  refine .bind ?_ fun cols₁ cols₂ => ?_
  · unfold csOffColsProg csFlatMap csColProg Toolkit.filterList mapList
    prog_wf
  · unfold Toolkit.filterList anyList
    refine .bind (.prim _ .nil) fun _ _ => .bind (.foldList (by simp) (by simp) fun _ _ _ _ =>
      .bind (.bind (.prim _ .nil) fun _ _ => .foldList (by simp [hps]) (by simp) fun _ _ _ _ =>
        .bind (.bind (cp2_wf_csCompProg (by simp [ho]) (by simp [hc]) (by simp [hps]) (by simp)
          (by simp)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
          .foldList (by simp [hps]) (by simp) fun _ _ _ _ =>
            .bind (.bind (by unfold csMemProg anyList; prog_wf) fun _ _ =>
              .prim _ (.cons (by simp) .nil)) fun _ _ =>
            .prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
        .prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .ite (by simp) (.prim _ (.cons (by simp) (.cons (by simp) .nil))) (.ret (by simp)))
      fun _ _ => .prim _ (.cons (by simp) .nil)

theorem wf_tParamProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tParamProg m₁) (tParamProg m₂) := by
  unfold tParamProg
  exact .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) (.cons (by simp) .nil))) fun _ _ => wf_halfProg (by simp)

theorem wf_compLeafProg {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)}
    {m₁ r₁ : var₁ .nat} {m₂ r₂ : var₂ .nat} {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)}
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (compLeafProg o₁ c₁ m₁ ps₁ r₁)
      (compLeafProg o₂ c₂ m₂ ps₂ r₂) := by
  unfold compLeafProg csCompPartProg
  refine .bind (.bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp [hm])
    (.cons (by simp) .nil))) fun _ _ => .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx => cp2_wf_csCompProg (hΓ (by simp [ho]))
      (hΓ (by simp [hc])) (hΓ (by simp [hps])) (hΓ (by simp [hr])) hx) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => by unfold csPartLeafProg; prog_wf)
    fun _ _ => ?_
  unfold partProg mkOutProg emptyLstArrProg
  prog_wf

theorem wf_leavesOfProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {C₁ : var₁ (.array .nat)}
    {C₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hC : ⟨.array .nat, C₁, C₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (leavesOfProg m₁ C₁) (leavesOfProg m₂ C₂) := by
  unfold leavesOfProg
  refine .bind (cp2_wf_csOffsProg hm) fun _ _ => .bind (.prim _ (.cons (by simp [hm]) .nil))
    fun _ _ => .bind (cp2_wf_csDisconnProg (by simp) (by simp [hC]) (by simp)) fun _ _ =>
    .caseList (by simp) ?_ fun _ _ _ _ => ?_
  · exact .bind (wf_tParamProg (by simp [hm])) fun _ _ =>
      .bind (wf_sojProg (by simp [hm]) (by simp) (by simp [hC])) fun _ _ =>
      wf_mapList (by simp) fun Γ' hΓ o₁ o₂ ho => wf_trimProg (hΓ (by simp [hm])) ho
  · exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .bind (by unfold Toolkit.minProg; prog_wf) fun _ _ =>
      .bind (wf_compLeafProg (by simp) (by simp [hC]) (by simp [hm]) (by simp) (by simp))
      fun _ _ => .bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_tuplesProg {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)} {j₁ : var₁ .nat}
    {j₂ : var₂ .nat} (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tuplesProg l₁ j₁) (tuplesProg l₂ j₂) := by
  unfold tuplesProg
  refine .bind (.prim _ (.cons hj .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil)))
    fun _ _ => .foldList (by simp) (by simp) fun acc₁ acc₂ _ _ => ?_
  unfold tupStepProg
  exact Align.wf_joFlatMap (by simp) fun Γ'' hΓ' T₁ T₂ hT => by
    unfold tupExtProg Toolkit.filterList memProg anyList mapList
    have hl' : ⟨.list .nat, l₁, l₂⟩ ∈ Γ'' := hΓ' (by simp [hl])
    prog_wf

theorem wf_pairsProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pairsProg m₁) (pairsProg m₂) := by
  unfold pairsProg
  refine .bind (.prim _ (.cons hm .nil)) fun rm₁ rm₂ => ?_
  exact Align.wf_joFlatMap (by simp) fun Γ' hΓ a₁ a₂ ha => by
    unfold Toolkit.filterList mapList
    have hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ' := hΓ (by simp)
    prog_wf

end Wf

end GraphIso.Case2b
