module

public import GraphIso.Sims.ConstructProg
public import GraphIso.Sims.Oracle

/-!
# The table operations in the cost language

Programs for `generate`, `stabilizer`, `kernel`, `mem` and `lift`, each building the complete
table it needs (`buildProg`) for a base order listing a window first (`frontBaseProg`), with
proofs that they compute the oracle's models within explicit bounds:

| program | cost bound |
|---|---|
| `generateProg` | `genCost n L = buildCost n L + 7 n² + 8 n + 30` |
| `stabProg` | `stabCost n L = buildCost n L + 7 n² + 10 n + 40` |
| `kernelProg` | `kerCost n L m = buildCost n L + 7 n² + 7 n + 3 m + 30` |
| `memProg` | `memCost n L = buildCost n L + siftCost n + 8 n + 25` |
| `liftProg` | `liftCost n L m = buildCost n L + m (12 n + 26) + 10 n + 3 m + 40` |

for `L` generators of degree `n` and a window of `m` points.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Programs

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The base order listing the window first. -/
def frontBaseProg (n : var .nat) (w : var Ty.win) : Prog S rec var (.array .nat) :=
  .bind (.op1 .fst w) fun pts => .bind (.op1 .snd w) fun mask =>
  .bind (.op1 .range n) fun rng => .bind (.op0 .nil) fun nl =>
  .bind (.foldList rng nl fun acc i =>
      .bind (.op2 .arrayGet mask i) fun mi => .ite mi (.ret acc) (.op2 .cons i acc)) fun rrev =>
  .bind (.op1 .reverse rrev) fun rest =>
  .bind (.op2 .append pts rest) fun l => .op1 .arrayOfList l

/-- The empty window. -/
def emptyWinProg (n : var .nat) : Prog S rec var Ty.win :=
  .bind (.op0 .nil) fun nl => .bind (.op0 (.boolLit false)) fun f =>
  .bind (.op2 .arrayMk n f) fun m => .op2 .pair nl m

/-- The window `[u]`. -/
def pointWinProg (n u : var .nat) : Prog S rec var Ty.win :=
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons u nl) fun pts =>
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .arrayMk n f) fun m₀ =>
  .bind (.op0 (.boolLit true)) fun t => .bind (.op2 .pair u t) fun wr =>
  .bind (.op0 .nil) fun nl' => .bind (.op2 .cons wr nl') fun ws =>
  .bind (.op2 .arrayUpdate m₀ ws) fun m => .op2 .pair pts m

/-- The elements of the entries in rows `≥ k`. -/
def entriesFromProg (k : var .nat) (ent : var (.list Ty.item)) : Prog S rec var Ty.gens :=
  .bind (.op0 .nil) fun nl =>
  .bind (.foldList ent nl fun acc e =>
      .bind (.op1 .fst e) fun l => .bind (.op2 .natLt l k) fun c =>
      .ite c (.ret acc) (.bind (.op1 .snd e) fun σ => .op2 .cons σ acc)) fun rev =>
  .op1 .reverse rev

/-- The table and entries for `gs` with the base order `b`, and the entries in rows `≥ k`. -/
def tableEntriesProg (n : var .nat) (b : var (.array .nat)) (gs : var Ty.gens) (k : var .nat) :
    Prog S rec var Ty.gens :=
  .bind (buildProg n b gs) fun st => .bind (.op1 .snd st) fun ep => .bind (.op1 .fst ep) fun ent =>
  entriesFromProg k ent

/-- Package generators as a group with no backend data. -/
def groupOfProg (n : var .nat) (hs : var Ty.gens) : Prog S rec var (Ty.group .unit) :=
  .bind (.op0 .unit) fun u => .bind (.op2 .pair hs u) fun hd => .op2 .pair n hd

/-- `generate`. -/
def generateProg (n : var .nat) (gs : var Ty.gens) : Prog S rec var (Ty.group .unit) :=
  .bind (emptyWinProg n) fun w => .bind (frontBaseProg n w) fun b =>
  .bind (.op0 (.natLit 0)) fun z => .bind (tableEntriesProg n b gs z) fun hs => groupOfProg n hs

/-- `stabilizer u`. -/
def stabProg (n : var .nat) (gs : var Ty.gens) (u : var .nat) : Prog S rec var (Ty.group .unit) :=
  .bind (pointWinProg n u) fun w => .bind (frontBaseProg n w) fun b =>
  .bind (.op0 (.natLit 1)) fun one => .bind (tableEntriesProg n b gs one) fun hs => groupOfProg n hs

/-- `kernel w`. -/
def kernelProg (n : var .nat) (gs : var Ty.gens) (w : var Ty.win) :
    Prog S rec var (Ty.group .unit) :=
  .bind (frontBaseProg n w) fun b => .bind (.op1 .fst w) fun pts =>
  .bind (.op1 .length pts) fun m =>
  .bind (tableEntriesProg n b gs m) fun hs => groupOfProg n hs

/-- `mem π`. -/
def memProg (n : var .nat) (gs : var Ty.gens) (π : var Ty.perm) : Prog S rec var .bool :=
  .bind (emptyWinProg n) fun w => .bind (frontBaseProg n w) fun b =>
  .bind (buildProg n b gs) fun st => .bind (.op1 .fst st) fun T =>
  .bind (.op0 (.natLit 0)) fun z => .bind (siftProg n b T z π) fun r =>
  .bind (.op1 .fst r) fun k => .op2 .natEq k n

/-- One row of the lift. -/
def liftBody (T : var Ty.table) (wa : var (.array .nat)) (π' : var Ty.perm) (cur : var Ty.perm)
    (i : var .nat) : Prog S rec var Ty.perm :=
  .bind (permApply π' i) fun pi => .bind (.op2 .arrayGet wa pi) fun t =>
  .bind (.op1 .snd cur) fun cinv => .bind (.op2 .arrayGet cinv t) fun j =>
  .bind (.op2 .arrayGet T i) fun row => .bind (.op2 .arrayGet row j) fun sl =>
  .caseOption sl (.ret cur) fun σ => permMul cur σ

/-- `lift w π'`. -/
def liftProg (n : var .nat) (gs : var Ty.gens) (w : var Ty.win) (π' : var Ty.perm) :
    Prog S rec var Ty.perm :=
  .bind (frontBaseProg n w) fun b => .bind (buildProg n b gs) fun st =>
  .bind (.op1 .fst st) fun T =>
  .bind (.op1 .fst w) fun pts => .bind (.op1 .arrayOfList pts) fun wa =>
  .bind (.op1 .length pts) fun m => .bind (.op1 .range m) fun is =>
  .bind (permOne n) fun e => .foldList is e fun cur i => liftBody T wa π' cur i

end Prog

/-! ### Functional facts -/

theorem foldl_filter_rev {α : Type} (p : α → Bool) :
    ∀ (l acc : List α),
      l.foldl (fun acc i => if p i then acc else i :: acc) acc =
        (l.filter fun i => !p i).reverse ++ acc
  | [], acc => by simp
  | i :: l, acc => by
    rw [List.foldl_cons, foldl_filter_rev p l]
    by_cases h : p i <;> simp [h]

theorem foldl_entries_rev (k : ℕ) :
    ∀ (ent : List Item) (acc : GensData),
      ent.foldl (fun acc e => if e.1 < k then acc else e.2 :: acc) acc =
        (entriesFrom k ent).reverse ++ acc
  | [], acc => by simp [entriesFrom]
  | e :: ent, acc => by
    rw [List.foldl_cons, foldl_entries_rev k ent]
    by_cases h : e.1 < k <;> simp [h, entriesFrom]

theorem frontBase_eq_fold (n : ℕ) (w : WinData) :
    frontBase n w = (w.1 ++ ((List.range n).foldl
      (fun acc i => if getB w.2 i then acc else i :: acc) []).reverse).toArray := by
  rw [foldl_filter_rev, List.append_nil, List.reverse_reverse]
  rfl

/-! ### Costs of the helpers -/

section Specs

variable {S : Signature} {a b' : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b') Ty.denote b'}
  {n : ℕ}

theorem RunsWithin.frontBaseProg (w : WinData) :
    RunsWithin X body (Sims.frontBaseProg n w) (frontBase n w) (7 * n + 2 * w.1.length + 8) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (f := fun acc i => .bind (.op2 .arrayGet w.2 i) fun mi => .ite mi (.ret acc) (.op2 .cons i acc))
    (F := fun acc i => if getB w.2 i then acc else i :: acc) (cf := fun _ => 3) (List.range n) []
    (fun acc i _ => by
      by_cases h : getB w.2 i = true
      · refine (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.ite_pos h (RunsWithin.ret _))
          (by simp [Prim.cost])).of_eq ?_
        simp [h]
      · refine (RunsWithin.bind_le (RunsWithin.prim _ _)
          (RunsWithin.ite_neg (Bool.eq_false_iff.2 h : getB w.2 i = false) (RunsWithin.prim _ _))
          (by simp [Prim.cost])).of_eq ?_
        simp [h, Prim.eval])
  rw [sum_map_const, List.length_range] at hfold
  have hlen : ((List.range n).foldl (fun acc i => if getB w.2 i then acc else i :: acc)
      []).length ≤ n := by
    rw [foldl_filter_rev, List.append_nil, List.length_reverse]
    exact (List.length_filter_le _ _).trans (by simp)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (frontBase_eq_fold n w).symm le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_reverse]
    simp only [Ty.denote] at hlen ⊢
    omega

theorem RunsWithin.emptyWinProg (n : ℕ) :
    RunsWithin X body (Sims.emptyWinProg n) (emptyWin n) (n + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    omega

theorem RunsWithin.pointWinProg (n u : ℕ) :
    RunsWithin X body (Sims.pointWinProg n u) (pointWin n u) (2 * n + 12) := by
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
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate,
      List.length_cons, List.length_nil]
    omega

theorem RunsWithin.entriesFromProg (k : ℕ) (ent : List Item) :
    RunsWithin X body (Sims.entriesFromProg k ent) (entriesFrom k ent) (7 * ent.length + 2) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := Ty.item) (b' := Ty.gens)
    (f := fun acc e => .bind (.op1 .fst e) fun l => .bind (.op2 .natLt l k) fun c =>
      .ite c (.ret acc) (.bind (.op1 .snd e) fun σ => .op2 .cons σ acc))
    (F := fun acc e => if e.1 < k then acc else e.2 :: acc) (cf := fun _ => 5) ent []
    (fun acc e _ => by
      by_cases h : e.1 < k
      · refine (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.bind_le
          (RunsWithin.prim _ _) (RunsWithin.ite_pos (decide_eq_true h) (RunsWithin.ret _)) le_rfl)
          (by simp [Prim.cost])).of_eq ?_
        simp [h]
      · refine (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.bind_le
          (RunsWithin.prim _ _) (RunsWithin.ite_neg (decide_eq_false h)
            (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) le_rfl)) le_rfl)
          (by simp [Prim.cost])).of_eq ?_
        simp [h, Prim.eval])
  rw [sum_map_const, foldl_entries_rev, List.append_nil] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le (List.reverse_reverse _) le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_reverse]
    have : (entriesFrom k ent).length ≤ ent.length := by
      rw [entriesFrom, List.length_map]
      exact List.length_filter_le _ _
    omega

theorem RunsWithin.tableEntriesProg {b : Array ℕ} {gs : GensData} (hb : BaseOrder n b)
    (hgs : GensData.AllValid n gs) (k : ℕ) :
    RunsWithin X body (Sims.tableEntriesProg n b gs k) (entriesFrom k (build n b gs).2.1)
      (buildCost n gs.length + 7 * (n * n) + 4) := by
  have hlen := (build_spec hb hgs).1.length_le
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.buildProg hb hgs)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.entriesFromProg k _
  case hc =>
    simp only [Prim.cost]
    have : 7 * (build n b gs).2.1.length ≤ 7 * (n * n) := Nat.mul_le_mul_left _ hlen
    change buildCost n gs.length + (1 + (1 + (7 * (build n b gs).2.1.length + 2))) ≤ _
    omega

theorem RunsWithin.groupOfProg (n : ℕ) (hs : GensData) :
    RunsWithin X body (Sims.groupOfProg n hs) ((n, hs, ()) : (Ty.group .unit).denote) 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

/-- The cost bound of `generate` from `L` generators. -/
def genCost (n L : ℕ) : ℕ := buildCost n L + 7 * (n * n) + 8 * n + 30

/-- The cost bound of `stabilizer` for `L` generators. -/
def stabCost (n L : ℕ) : ℕ := buildCost n L + 7 * (n * n) + 10 * n + 40

/-- The cost bound of `kernel` for `L` generators and a window of `m` points. -/
def kerCost (n L m : ℕ) : ℕ := buildCost n L + 7 * (n * n) + 7 * n + 3 * m + 30

/-- The cost bound of `mem` for `L` generators. -/
def memCost (n L : ℕ) : ℕ := buildCost n L + siftCost n + 8 * n + 25

/-- The cost bound of `lift` for `L` generators and a window of `m` points. -/
def liftCost (n L m : ℕ) : ℕ := buildCost n L + m * (12 * n + 26) + 10 * n + 3 * m + 40

theorem RunsWithin.generateProg {gs : GensData} (hgs : GensData.AllValid n gs) :
    RunsWithin X body (Sims.generateProg n gs) ((n, generateModel n gs, ()) :
      (Ty.group .unit).denote) (genCost n gs.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.emptyWinProg n)
    run_step (RunsWithin.frontBaseProg (emptyWin n))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.tableEntriesProg (frontBase_base (emptyWin_valid n)) hgs 0)
    exact RunsWithin.groupOfProg n _
  case hc =>
    simp only [Prim.cost, genCost, emptyWin, List.length_nil]
    omega

theorem RunsWithin.stabProg {gs : GensData} (hgs : GensData.AllValid n gs) {u : ℕ} (hu : u < n) :
    RunsWithin X body (Sims.stabProg n gs u) ((n, stabModel n gs u, ()) :
      (Ty.group .unit).denote) (stabCost n gs.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.pointWinProg n u)
    run_step (RunsWithin.frontBaseProg (pointWin n u))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.tableEntriesProg (frontBase_base (pointWin_valid hu)) hgs 1)
    exact RunsWithin.groupOfProg n _
  case hc =>
    simp only [Prim.cost, stabCost, pointWin, List.length_singleton]
    omega

theorem RunsWithin.kernelProg {gs : GensData} (hgs : GensData.AllValid n gs) {w : WinData}
    (hw : w.Valid n) :
    RunsWithin X body (Sims.kernelProg n gs w) ((n, kernelModel n gs w, ()) :
      (Ty.group .unit).denote) (kerCost n gs.length w.1.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.frontBaseProg w)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.tableEntriesProg (frontBase_base hw) hgs w.1.length)
    exact RunsWithin.groupOfProg n _
  case hc =>
    simp only [Prim.cost, Prim.eval, kerCost, Args.head_cons]
    omega

theorem RunsWithin.memProg {gs : GensData} (hgs : GensData.AllValid n gs) {π : PermData}
    (hπ : π.Valid n) :
    RunsWithin X body (Sims.memProg n gs π) (memModel n gs π) (memCost n gs.length) := by
  have hb := frontBase_base (emptyWin_valid n)
  have hT : SlotsValid n (build n (frontBase n (emptyWin n)) gs).1 :=
    (build_spec hb hgs).1.wf.slotsValid
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.emptyWinProg n)
    run_step (RunsWithin.frontBaseProg (emptyWin n))
    run_step (RunsWithin.buildProg hb hgs)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.siftProg hT (Nat.zero_le n) hπ)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, memCost, emptyWin, List.length_nil]
    omega

theorem RunsWithin.liftBody {T : Table} (hT : SlotsValid n T) (wa : Array ℕ) (π' : PermData)
    {cur : PermData} (hcur : cur.Valid n) (i : ℕ) :
    RunsWithin X body (Sims.liftBody T wa π' cur i) (liftStep T wa π' cur i) (12 * n + 21) := by
  rcases hs : slot T i (get cur.2 (get wa (get π'.1 i))) with _ | σ
  · have hF : liftStep T wa π' cur i = cur := by simp [liftStep, hs]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.permApply _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      change RunsWithin X body
        (Prog.caseOption (a := Ty.perm) (slot T i (get cur.2 (get wa (get π'.1 i)))) _ _) _ _
      rw [hs]
      exact RunsWithin.caseOption_none (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost]
      omega
  · have hF : liftStep T wa π' cur i = cur.mul σ := by simp [liftStep, hs]
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.permApply _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      change RunsWithin X body
        (Prog.caseOption (a := Ty.perm) (slot T i (get cur.2 (get wa (get π'.1 i)))) _ _) _ _
      rw [hs]
      exact RunsWithin.caseOption_some (RunsWithin.permMul hcur (hT hs))
    case hc =>
      simp only [Prim.cost]
      omega

theorem RunsWithin.liftProg {gs : GensData} (hgs : GensData.AllValid n gs) {w : WinData}
    (hw : w.Valid n) (π' : PermData) :
    RunsWithin X body (Sims.liftProg n gs w π') (liftModel n gs w π')
      (liftCost n gs.length w.1.length) := by
  have hb := frontBase_base hw
  have hT : SlotsValid n (build n (frontBase n w) gs).1 := (build_spec hb hgs).1.wf.slotsValid
  have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := .nat) (b' := Ty.perm)
    (f := fun cur i => Sims.liftBody (build n (frontBase n w) gs).1 w.1.toArray π' cur i)
    (F := liftStep (build n (frontBase n w) gs).1 w.1.toArray π')
    (I := fun cur : PermData => cur.Valid n)
    (c := 12 * n + 21) (List.range w.1.length) (PermData.one n)
    (fun cur hcur i _ => ⟨RunsWithin.liftBody hT _ π' hcur i, by
      unfold liftStep
      split
      · exact hcur
      · rename_i σ hσ
        exact hcur.mul (hT hσ)⟩) (PermData.valid_one n)).1
  rw [List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.frontBaseProg w)
    run_step (RunsWithin.buildProg hb hgs)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permOne n)
    exact hfold
  case hc =>
    simp only [Prim.cost, Prim.eval, liftCost, Args.head_cons]
    have : w.1.length * (12 * n + 26) = w.1.length * (12 * n + 21 + 1) + 4 * w.1.length := by
      ring
    omega

end Specs

end GraphIso.Sims
