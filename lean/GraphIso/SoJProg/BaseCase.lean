module

public import GraphIso.SoJProg.Johnson
public import GraphIso.SoJProg.BaseCaseData

/-!
# The base case as programs

Step 0 of milestone 11's `bstep` as costed programs (`PLAN-14.md` §7 item 4), reading the
relation through the row offsets of `SoJProg/Twins.lean`.

* `insertsProg`, `permsProg`, `enumsProg`: all permutations of a list by insertion (mathlib's
  `List.permutations'Aux` and `List.permutations'`); the permutations of the cell indices
  decode to `enums` (`enums_decode`). The cost is `k! · poly(k)` for `k` cells.
* `nbrCodeProg`, `nbrCodeArrProg`: the binary code of a point along an enumeration
  (`nbrCodeD`, decoded by `nbrCode_decode`).
* `colBlkProg`: the blocks of `colPart` for a colour array (`colBlkD`, `colPart_decode`);
  `baseLeafProg`: the leaf `colPart V₁ (nbrCode A (choiceCells ch))` (`baseLeaf_decode`).

Each program has an explicit cost and a well-formedness lemma `wf_*`.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Cost GraphIso GraphIso.Programs

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Insert `t` at every position of `l`. -/
def insertsProg (t : var .nat) (l : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .reverse l) fun lr => .bind (.op0 .nil) fun nil =>
  .bind (.op0 .nil) fun nilL => .bind (.op2 .cons t nil) fun tl =>
  .bind (.op2 .cons tl nilL) fun A₀ => .bind (.op2 .pair nil A₀) fun st₀ =>
  .bind (.foldList lr st₀ fun st y =>
      .bind (.op1 .fst st) fun s => .bind (.op1 .snd st) fun A =>
      .bind (.op2 .cons y s) fun ys => .bind (.op2 .cons t ys) fun tys =>
      .bind (mapList A fun p => .op2 .cons y p) fun A' =>
      .bind (.op2 .cons tys A') fun A'' => .op2 .pair ys A'') fun fin =>
  .op1 .snd fin

/-- All permutations of `l`. -/
def permsProg (l : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .reverse l) fun lr => .bind (.op0 .nil) fun e => .bind (.op0 .nil) fun nilL =>
  .bind (.op2 .cons e nilL) fun acc₀ =>
  .foldList lr acc₀ fun acc t =>
    .bind (.op0 .nil) fun res₀ =>
    .bind (.foldList acc res₀ fun res p =>
        .bind (insertsProg t p) fun ins => .bind (.op1 .reverse ins) fun rins =>
        .op2 .append rins res) fun res =>
    .op1 .reverse res

/-- The enumerations of the cells `0, …, k - 1`. -/
def enumsProg (k : var .nat) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range k) fun rk => permsProg rk

/-- The code of `x` along the enumeration `js` of cell indices. -/
def nbrCodeProg (offs : var (.array .nat)) (a : var (.array .bool)) (js : var (.list .nat))
    (x : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .reverse js) fun jr => .bind (.op0 (.natLit 0)) fun z =>
  .foldList jr z fun acc j =>
    .bind (relAtProg offs a x j) fun b => .bind (.op2 .add acc acc) fun acc2 =>
    .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add acc2 one) fun acc21 =>
    .ite b (.ret acc21) (.ret acc2)

/-- The codes of the points `0, …, m - 1` along `js`. -/
def nbrCodeArrProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (js : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range m) fun is => .bind (mapList is fun x => nbrCodeProg offs a js x) fun l =>
  .op1 .arrayOfList l

/-- The blocks of `colPart V col` at the points `0, …, m - 1`. -/
def colBlkProg (m : var .nat) (V : var (.list .nat)) (col : var (.array .nat)) :
    Prog S rec var (.array (.list .nat)) :=
  .bind (.op1 .range m) fun is =>
  .bind (mapList is fun x => .bind (.op2 .arrayGet col x) fun cx =>
      Toolkit.filterList V fun y => .bind (.op2 .arrayGet col y) fun cy => .op2 .natEq cy cx)
    fun l =>
  .op1 .arrayOfList l

/-- The leaf of the base case along the enumeration `js`: colours and blocks. -/
def baseLeafProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (V : var (.list .nat)) (js : var (.list .nat)) :
    Prog S rec var (.prod (.array .nat) (.array (.list .nat))) :=
  .bind (nbrCodeArrProg m offs a js) fun col => .bind (colBlkProg m V col) fun blk =>
  .op2 .pair col blk

end Programs

/-! ### Data -/

/-- One step of `insertsProg`'s fold: the suffix and its insertions. -/
def insStep (t : ℕ) (st : List ℕ × List (List ℕ)) (y : ℕ) : List ℕ × List (List ℕ) :=
  (y :: st.1, (t :: y :: st.1) :: st.2.map (y :: ·))

theorem inserts_fold (t : ℕ) (l : List ℕ) :
    l.reverse.foldl (insStep t) ([], [[t]]) = (l, List.permutations'Aux t l) := by
  rw [List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons y l ih => rw [List.foldr_cons, ih]; rfl

theorem perms_fold (l : List ℕ) :
    l.reverse.foldl (fun acc t => acc.flatMap (List.permutations'Aux t)) [[]] =
      l.permutations' := by
  rw [List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.foldr_cons, ih]; rfl

theorem flat_fold (t : ℕ) : ∀ (acc r : List (List ℕ)),
    acc.foldl (fun res p => (List.permutations'Aux t p).reverse ++ res) r =
      (acc.flatMap (List.permutations'Aux t)).reverse ++ r
  | [], r => by simp
  | p :: acc, r => by
    rw [List.foldl_cons, flat_fold t acc, List.flatMap_cons, List.reverse_append,
      List.append_assoc]

theorem length_of_mem_inserts {t : ℕ} : ∀ {l q : List ℕ}, q ∈ List.permutations'Aux t l →
    q.length = l.length + 1
  | [], q, h => by
    simp only [List.permutations'Aux, List.mem_singleton] at h
    simp [h]
  | y :: l, q, h => by
    simp only [List.permutations'Aux, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨q', hq', rfl⟩
    · simp
    · simp [length_of_mem_inserts hq']

theorem length_flatMap_inserts {t i : ℕ} : ∀ {acc : List (List ℕ)},
    (∀ p ∈ acc, p.length = i) →
    (acc.flatMap (List.permutations'Aux t)).length = acc.length * (i + 1)
  | [], _ => by simp
  | p :: acc, h => by
    rw [List.flatMap_cons, List.length_append, List.length_permutations'Aux,
      h p List.mem_cons_self, length_flatMap_inserts fun q hq => h q (List.mem_cons_of_mem _ hq),
      List.length_cons, Nat.succ_mul]
    omega

/-- One step of `nbrCodeProg`'s fold. -/
def codeStep (k : ℕ) (a : Array Bool) (x acc j : ℕ) : ℕ :=
  if relAt k a x j then acc + acc + 1 else acc + acc

theorem code_fold (k : ℕ) (a : Array Bool) (x : ℕ) (js : List ℕ) :
    js.reverse.foldl (codeStep k a x) 0 = nbrCodeD k a js x := by
  rw [List.foldl_reverse, nbrCodeD]
  induction js with
  | nil => rfl
  | cons j js ih =>
    rw [List.foldr_cons, ih, List.map_cons, Nat.ofDigits_cons, codeStep]
    split_ifs <;> omega

/-! ### Costs -/

/-- The cost of `insertsProg` on a list of length `n`. -/
def insertsCost (n : ℕ) : ℕ := n * (4 * n + 9) + n + 7

/-- The cost of `permsProg` on a list of length `k`: `k! · poly(k)`. -/
def permsCost (k : ℕ) : ℕ := k * (k.factorial * (insertsCost k + 3 * k + 6) + 3) + k + 4

/-- The cost of `enumsProg k`. -/
def enumsCost (k : ℕ) : ℕ := permsCost k + k + 1

/-- The cost of `nbrCodeProg` along an enumeration of length `n`. -/
def nbrCodeCost (n : ℕ) : ℕ := 9 * n + 2

/-- The cost of `nbrCodeArrProg`. -/
def nbrCodeArrCost (m n : ℕ) : ℕ := m * (nbrCodeCost n + 3) + 2 * m + 4

/-- The cost of `colBlkProg` for a list of length `n₁`. -/
def colBlkCost (m n₁ : ℕ) : ℕ := m * (6 * n₁ + 7) + 2 * m + 4

/-- The cost of `baseLeafProg`. -/
def baseLeafCost (m n₁ n : ℕ) : ℕ := nbrCodeArrCost m n + colBlkCost m n₁ + 1

theorem insertsCost_mono {n n' : ℕ} (h : n ≤ n') : insertsCost n ≤ insertsCost n' := by
  unfold insertsCost
  have := Nat.mul_le_mul h (show 4 * n + 9 ≤ 4 * n' + 9 by omega)
  omega

/-! ### Specs -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.insertsProg (t : ℕ) (l : List ℕ) :
    RunsWithin X body (SoJProg.insertsProg t l) (List.permutations'Aux t l)
      (insertsCost l.length) := by
  have hfold := foldList_idx (X := X) (body := body) (a' := .nat)
    (b' := .prod (.list .nat) (.list (.list .nat)))
    (f := fun st y => Prog.bind (.op1 .fst st) fun s => .bind (.op1 .snd st) fun A =>
      .bind (.op2 .cons y s) fun ys => .bind (.op2 .cons t ys) fun tys =>
      .bind (mapList A fun p => .op2 .cons y p) fun A' =>
      .bind (.op2 .cons tys A') fun A'' => .op2 .pair ys A'')
    (F := insStep t) (I := fun j st => st.2.length = j + 1) (c := 4 * l.length + 8)
    (n := l.length) l.reverse 0 ([], [[t]]) (by simp) (fun j st hj hst y _ => by
      refine ⟨?_, by simp [insStep, hst]⟩
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.mapList_le (F := fun p => y :: p) (c := 1) fun p _ =>
          RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, Prim.eval, hst]
        omega) rfl
  rw [inserts_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, List.length_reverse, insertsCost]
    have : l.length * (4 * l.length + 8 + 1) = l.length * (4 * l.length + 9) := by ring
    omega

theorem RunsWithin.permsProg (l : List ℕ) :
    RunsWithin X body (SoJProg.permsProg l) l.permutations' (permsCost l.length) := by
  have hfold := foldList_idx (X := X) (body := body) (a' := .nat) (b' := .list (.list .nat))
    (f := fun acc t => Prog.bind (.op0 .nil) fun res₀ =>
      .bind (.foldList acc res₀ fun res p =>
        .bind (SoJProg.insertsProg t p) fun ins => .bind (.op1 .reverse ins) fun rins =>
        .op2 .append rins res) fun res => .op1 .reverse res)
    (F := fun acc t => acc.flatMap (List.permutations'Aux t))
    (I := fun i acc => acc.length ≤ i.factorial ∧ ∀ p ∈ acc, p.length = i)
    (c := l.length.factorial * (insertsCost l.length + 3 * l.length + 6) + 2) (n := l.length)
    l.reverse 0 [[]] (by simp) (fun i acc hi hacc t _ => by
      have hinner := RunsWithin.foldList_inv (X := X) (body := body) (a' := .list .nat)
        (b' := .list (.list .nat)) (I := fun _ => True) (c := insertsCost i + 2 * i + 4)
        (f := fun res p => Prog.bind (SoJProg.insertsProg t p) fun ins =>
          .bind (.op1 .reverse ins) fun rins => .op2 .append rins res)
        (F := fun res p => (List.permutations'Aux t p).reverse ++ res) acc []
        (fun res _ p hp => by
          refine ⟨?_, trivial⟩
          apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.insertsProg t p)
            run_step (RunsWithin.prim _ _)
            exact RunsWithin.prim_le rfl le_rfl
          case hc =>
            simp only [Prim.cost, Prim.eval, Args.head, List.length_reverse,
              List.length_permutations'Aux, hacc.2 p hp]
            omega) trivial
      rw [flat_fold, List.append_nil] at hinner
      have hlen := length_flatMap_inserts (t := t) hacc.2
      refine ⟨?_, ?_, ?_⟩
      · have h1 : acc.length ≤ l.length.factorial := hacc.1.trans (Nat.factorial_le hi.le)
        have h2 := insertsCost_mono hi.le
        have h3 : acc.length * (insertsCost i + 2 * i + 4 + 1 + (i + 1)) ≤
            l.length.factorial * (insertsCost l.length + 3 * l.length + 6) :=
          Nat.mul_le_mul h1 (by omega)
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step hinner.1
          exact RunsWithin.prim_le (List.reverse_reverse _) le_rfl
        case hc =>
          simp only [Prim.cost, Args.head, List.length_reverse, hlen]
          rw [Nat.mul_add] at h3
          omega
      · rw [hlen, Nat.factorial_succ, Nat.mul_comm]
        exact Nat.mul_le_mul_left _ hacc.1
      · intro q hq
        obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
        rw [length_of_mem_inserts hq, hacc.2 p hp]) ⟨by simp, by simp⟩
  rw [perms_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.1
  case hc =>
    simp only [Prim.cost, Args.head, List.length_reverse, permsCost]
    have : l.length * (l.length.factorial * (insertsCost l.length + 3 * l.length + 6) + 2 + 1) =
        l.length * (l.length.factorial * (insertsCost l.length + 3 * l.length + 6) + 3) := by
      ring
    omega

/-- **The enumerations as a program**: through `enums_decode`, the decoded choices
`choiceOf m cs js` of its output are exactly `enums (famOf m cs)`. -/
theorem RunsWithin.enumsProg (k : ℕ) :
    RunsWithin X body (SoJProg.enumsProg k) (List.range k).permutations' (enumsCost k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.permsProg _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, enumsCost]
    omega

theorem RunsWithin.nbrCodeProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) (js : List ℕ) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJProg.nbrCodeProg offs a js x) (nbrCodeD k a js x)
      (nbrCodeCost js.length) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (f := fun acc j => Prog.bind (SoJProg.relAtProg offs a x j) fun b =>
      .bind (.op2 .add acc acc) fun acc2 => .bind (.op0 (.natLit 1)) fun one =>
      .bind (.op2 .add acc2 one) fun acc21 => .ite b (.ret acc21) (.ret acc2))
    (F := codeStep k a x) (cf := fun _ => 7) js.reverse 0 fun acc j _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.relAtProg offs a x j)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        rw [relAt_of_offs hoffs hx j, codeStep]
        by_cases h : relAt k a x j
        · simp only [h, ↓reduceIte]
          exact RunsWithin.ite_true (RunsWithin.ret _)
        · simp only [h, Bool.false_eq_true, ↓reduceIte]
          exact RunsWithin.ite_false (RunsWithin.ret _)
      case hc => simp [Prim.cost]
  rw [code_fold, sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head, List.length_reverse, nbrCodeCost]
    omega

theorem RunsWithin.nbrCodeArrProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) (js : List ℕ) :
    RunsWithin X body (SoJProg.nbrCodeArrProg m offs a js) (nbrCodeArrD m k a js)
      (nbrCodeArrCost m js.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (F := nbrCodeD k a js) (c := nbrCodeCost js.length)
      fun x hx => RunsWithin.nbrCodeProg hoffs a js (by simpa [Prim.eval] using hx))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map,
      nbrCodeArrCost]
    omega

theorem RunsWithin.colBlkProg (m : ℕ) (V : List ℕ) (col : Array ℕ) :
    RunsWithin X body (SoJProg.colBlkProg m V col) (colBlkD m V col) (colBlkCost m V.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le
      (F := fun x => V.filter fun y => get col y == get col x) (c := 6 * V.length + 4)
      fun x _ => by
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          exact Toolkit.RunsWithin.filterList (c := 2) fun y _ =>
            RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) le_rfl
        case hc =>
          simp only [Prim.cost]
          omega)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map, colBlkCost]
    have : m * (6 * V.length + 4 + 3) = m * (6 * V.length + 7) := by ring
    omega

/-- **The leaf of the base case as a program**: through `baseLeaf_decode` (with
`cpartOf`), its output is `colPart V₁ (nbrCode A (choiceCells (choiceOf m cs js)))`. -/
theorem RunsWithin.baseLeafProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) (V js : List ℕ) :
    RunsWithin X body (SoJProg.baseLeafProg m offs a V js)
      (nbrCodeArrD m k a js, colBlkD m V (nbrCodeArrD m k a js))
      (baseLeafCost m V.length js.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.nbrCodeArrProg hoffs a js)
    run_step (RunsWithin.colBlkProg m V _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, baseLeafCost]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ k₁ t₁ x₁ : var₁ .nat} {m₂ k₂ t₂ x₂ : var₂ .nat}
  {offs₁ col₁ : var₁ (.array .nat)} {offs₂ col₂ : var₂ (.array .nat)}
  {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
  {l₁ V₁ js₁ : var₁ (.list .nat)} {l₂ V₂ js₂ : var₂ (.list .nat)}

theorem wf_insertsProg (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (insertsProg t₁ l₁) (insertsProg t₂ l₂) := by
  unfold insertsProg mapList
  prog_wf

theorem wf_permsProg (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permsProg l₁) (permsProg l₂) := by
  unfold permsProg insertsProg mapList
  prog_wf

theorem wf_enumsProg (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (enumsProg k₁) (enumsProg k₂) :=
  .bind (.prim _ (.cons hk .nil)) fun _ _ => wf_permsProg (by simp)

theorem wf_nbrCodeProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hjs : ⟨.list .nat, js₁, js₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nbrCodeProg offs₁ a₁ js₁ x₁)
      (nbrCodeProg offs₂ a₂ js₂ x₂) := by
  unfold nbrCodeProg relAtProg
  prog_wf

theorem wf_codeArrProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hjs : ⟨.list .nat, js₁, js₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nbrCodeArrProg m₁ offs₁ a₁ js₁)
      (nbrCodeArrProg m₂ offs₂ a₂ js₂) := by
  unfold nbrCodeArrProg nbrCodeProg relAtProg mapList
  prog_wf

theorem wf_colBlkProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (colBlkProg m₁ V₁ col₁) (colBlkProg m₂ V₂ col₂) := by
  unfold colBlkProg Toolkit.filterList mapList
  prog_wf

theorem wf_baseLeafProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hjs : ⟨.list .nat, js₁, js₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (baseLeafProg m₁ offs₁ a₁ V₁ js₁)
      (baseLeafProg m₂ offs₂ a₂ V₂ js₂) :=
  .bind (wf_codeArrProg hm hoffs ha hjs) fun _ _ =>
    .bind (wf_colBlkProg (by simp [hm]) (by simp [hV]) (by simp)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.SoJProg
