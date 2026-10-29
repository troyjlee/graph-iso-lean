module

public import GraphIso.SoJProg.Twins
public import GraphIso.SoJProg.JohnsonData

/-!
# The Johnson test as programs

Step 2 of milestone 11's `bstep` as costed programs (`PLAN-14.md` §7 item 3), reading the
relation through the row offsets of `SoJProg/Twins.lean`.

* `nbrProg`, `fOfProg`, `sOfProg`: the neighbourhood `nbrD`, its complement `fOfD`, `sOf`.
* `nextRowProg`, `pascalProg`, `chooseProg`: Pascal's triangle row by row (`pascalRow`) and the
  binomial coefficient `Nat.choose`, without multiplication.
* `johnsonTestProg`: the test `|V₁'| = C(|V₂|, s)`, decoded by `johnsonTest_decode`.
* `fArrProg`, `johnsonLeafProg`: the leaf data `⟨V₁', s, f⟩` (the cells are the input cells),
  decoded by `jembOf` and `johnson_decode` to the Johnson embedding of the model.

Each program has an explicit polynomial cost in `m` (points), `n₁ = |V₁|` and `k = |cs|`, and a
well-formedness lemma `wf_*`.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Cost GraphIso GraphIso.Programs GraphIso.SplitJohnson

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The cells related to `x`, as indices. -/
def nbrProg (offs : var (.array .nat)) (a : var (.array .bool)) (k x : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .range k) fun rk => Toolkit.filterList rk fun j => relAtProg offs a x j

/-- The neighbourhood of `x` after complementing (if `2 d₁ > k`). -/
def fOfProg (offs : var (.array .nat)) (a : var (.array .bool)) (k d₁ x : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .add d₁ d₁) fun dd => .bind (.op2 .natLt k dd) fun big =>
  .ite big
    (.bind (.op1 .range k) fun rk => Toolkit.filterList rk fun j =>
      .bind (relAtProg offs a x j) fun b => .op1 .not b)
    (nbrProg offs a k x)

/-- `sOf v d₁`. -/
def sOfProg (v d₁ : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .add d₁ d₁) fun dd => .bind (.op2 .natLt v dd) fun big =>
  .ite big (.op2 .sub v d₁) (.ret d₁)

/-- The next row of Pascal's triangle. -/
def nextRowProg (row : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nil =>
  .bind (.op2 .pair z nil) fun st₀ =>
  .bind (.foldList row st₀ fun st x =>
      .bind (.op1 .fst st) fun prev => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .add prev x) fun s => .bind (.op2 .cons s acc) fun acc' =>
      .op2 .pair x acc') fun fin =>
  .bind (.op1 .fst fin) fun last => .bind (.op1 .snd fin) fun acc =>
  .bind (.op2 .cons last acc) fun acc' => .op1 .reverse acc'

/-- Row `n` of Pascal's triangle. -/
def pascalProg (n : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range n) fun is => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .cons one nil) fun row₀ =>
  .foldList is row₀ fun row _ => nextRowProg row

/-- The binomial coefficient `C(n, s)`. -/
def chooseProg (n s : var .nat) : Prog S rec var .nat :=
  .bind (pascalProg n) fun row => .bind (.op1 .arrayOfList row) fun arr => .op2 .arrayGet arr s

/-- The Johnson test for the points of `V₁` without twins and of degree `d₁`. -/
def johnsonTestProg (offs : var (.array .nat)) (a : var (.array .bool)) (k : var .nat)
    (V₁ : var (.list .nat)) (d₁ : var .nat) : Prog S rec var .bool :=
  .bind (tfDegProg offs a k V₁ d₁) fun V₁' => .bind (.op1 .length V₁') fun n =>
  .bind (sOfProg k d₁) fun s => .bind (chooseProg k s) fun c => .op2 .natEq n c

/-- The neighbourhoods after complementing, at the points `0, …, m - 1`. -/
def fArrProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (k d₁ : var .nat) : Prog S rec var (.array (.list .nat)) :=
  .bind (.op1 .range m) fun is => .bind (mapList is fun x => fOfProg offs a k d₁ x) fun l =>
  .op1 .arrayOfList l

/-- The leaf data `⟨V₁', s, f⟩` of the Johnson case. -/
def johnsonLeafProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (k : var .nat) (V₁ : var (.list .nat)) (d₁ : var .nat) :
    Prog S rec var (.prod (.list .nat) (.prod .nat (.array (.list .nat)))) :=
  .bind (tfDegProg offs a k V₁ d₁) fun V₁' => .bind (sOfProg k d₁) fun s =>
  .bind (fArrProg m offs a k d₁) fun fA => .bind (.op2 .pair s fA) fun sf =>
  .op2 .pair V₁' sf

end Programs

/-! ### Data -/

/-- One step of `nextRowProg`'s fold: the previous entry and the reversed output. -/
def nextRowStep (st : ℕ × List ℕ) (x : ℕ) : ℕ × List ℕ := (x, (st.1 + x) :: st.2)

/-- The model of `nextRowProg`. -/
def nextRowD (row : List ℕ) : List ℕ :=
  let fin := row.foldl nextRowStep (0, [])
  (fin.1 :: fin.2).reverse

theorem nextRow_fold : ∀ (row : List ℕ) (p : ℕ) (acc : List ℕ),
    let fin := row.foldl nextRowStep (p, acc)
    (fin.1 :: fin.2).reverse = acc.reverse ++ List.zipWith (· + ·) (p :: row) (row ++ [0])
  | [], p, acc => by simp
  | x :: row, p, acc => by
    simp only [List.foldl_cons, nextRowStep]
    rw [nextRow_fold row x ((p + x) :: acc)]
    simp

theorem nextRowD_eq (row : List ℕ) :
    nextRowD row = List.zipWith (· + ·) (0 :: row) (row ++ [0]) := by
  have h := nextRow_fold row 0 []
  simp only [List.reverse_nil, List.nil_append] at h
  exact h

theorem pascal_fold (n : ℕ) :
    (List.range n).foldl (fun row (_ : ℕ) => nextRowD row) [1] = pascalRow n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      nextRowD_eq, pascalRow]

theorem get_pascalRow (n s : ℕ) : get (pascalRow n).toArray s = n.choose s := by
  rw [get, Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← pascalRow_getD,
    List.getD_eq_getElem?_getD]

/-! ### Costs -/

/-- The cost of `nbrProg`. -/
def nbrCost (k : ℕ) : ℕ := 8 * k + 4

/-- The cost of `fOfProg`. -/
def fOfCost (k : ℕ) : ℕ := 9 * k + 7

/-- The cost of `nextRowProg` on a row of length `l`. -/
def nextRowCost (l : ℕ) : ℕ := 7 * l + 8

/-- The cost of `pascalProg n`. -/
def pascalCost (n : ℕ) : ℕ := n * (nextRowCost n + 1) + n + 4

/-- The cost of `chooseProg n`. -/
def chooseCost (n : ℕ) : ℕ := pascalCost n + n + 3

/-- The cost of `johnsonTestProg`. -/
def johnsonTestCost (n₁ k : ℕ) : ℕ := tfDegCost n₁ k + n₁ + chooseCost k + 6

/-- The cost of `fArrProg`. -/
def fArrCost (m k : ℕ) : ℕ := m * (fOfCost k + 3) + 2 * m + 4

/-- The cost of `johnsonLeafProg`. -/
def johnsonLeafCost (m n₁ k : ℕ) : ℕ := tfDegCost n₁ k + fArrCost m k + 6

/-! ### Specs -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.nbrProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJProg.nbrProg offs a k x) (nbrD k a x) (nbrCost k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact (Toolkit.RunsWithin.filterList (c := 3) fun j _ =>
      RunsWithin.relAtProg offs a x j).of_eq
      (by rw [nbrD]; exact List.filter_congr fun j _ => relAt_of_offs hoffs hx j)
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, nbrCost]
    omega

theorem RunsWithin.fOfProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) (d₁ : ℕ) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJProg.fOfProg offs a k d₁ x) (fOfD k a d₁ x) (fOfCost k) := by
  by_cases h : k < 2 * d₁
  · have he : Prim.eval Prim.natLt (Args.cons k (Args.cons (Prim.eval Prim.add
        (Args.cons d₁ (Args.cons d₁ Args.nil))) Args.nil)) = true := by
      show decide (k < d₁ + d₁) = true
      exact decide_eq_true (by omega)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      rw [he]
      apply RunsWithin.ite_true
      run_step (RunsWithin.prim _ _)
      exact (Toolkit.RunsWithin.filterList (c := 4) (P := fun j => !relAt k a x j) fun j _ =>
        RunsWithin.bind_le (RunsWithin.relAtProg offs a x j)
          (RunsWithin.prim_le (by simp only [Prim.eval, relAt_of_offs hoffs hx j]) le_rfl)
          (by simp [Prim.cost])).of_eq (by simp only [Prim.eval, fOfD, h, ↓reduceIte])
    case hc =>
      simp only [Prim.cost, Args.head, Prim.eval, List.length_range, fOfCost]
      omega
  · have he : Prim.eval Prim.natLt (Args.cons k (Args.cons (Prim.eval Prim.add
        (Args.cons d₁ (Args.cons d₁ Args.nil))) Args.nil)) = false := by
      show decide (k < d₁ + d₁) = false
      exact decide_eq_false (by omega)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      rw [he]
      apply RunsWithin.ite_false
      exact (RunsWithin.nbrProg hoffs a hx).of_eq (by simp only [fOfD, h, ↓reduceIte])
    case hc =>
      simp only [Prim.cost, nbrCost, fOfCost]
      omega

theorem RunsWithin.sOfProg (v d₁ : ℕ) :
    RunsWithin X body (SoJProg.sOfProg v d₁) (sOf v d₁) 4 := by
  by_cases h : v < 2 * d₁
  · have he : Prim.eval Prim.natLt (Args.cons v (Args.cons (Prim.eval Prim.add
        (Args.cons d₁ (Args.cons d₁ Args.nil))) Args.nil)) = true := by
      show decide (v < d₁ + d₁) = true
      exact decide_eq_true (by omega)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      rw [he]
      exact RunsWithin.ite_true (RunsWithin.prim_le (by simp [Prim.eval, sOf, h]) le_rfl)
    case hc => simp [Prim.cost]
  · have he : Prim.eval Prim.natLt (Args.cons v (Args.cons (Prim.eval Prim.add
        (Args.cons d₁ (Args.cons d₁ Args.nil))) Args.nil)) = false := by
      show decide (v < d₁ + d₁) = false
      exact decide_eq_false (by omega)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      rw [he]
      exact RunsWithin.ite_false ((RunsWithin.ret _).of_eq (by simp [sOf, h]))
    case hc => simp [Prim.cost]

theorem RunsWithin.nextRowProg (row : List ℕ) :
    RunsWithin X body (SoJProg.nextRowProg row) (nextRowD row) (nextRowCost row.length) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list .nat))
    (f := fun st x => Prog.bind (.op1 .fst st) fun prev => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .add prev x) fun s => .bind (.op2 .cons s acc) fun acc' =>
      .op2 .pair x acc')
    (F := nextRowStep) (cf := fun _ => 5) row (0, []) fun st x _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp [Prim.cost]
  have hlen : ∀ (row : List ℕ) (st : ℕ × List ℕ),
      (row.foldl nextRowStep st).2.length = st.2.length + row.length := by
    intro row
    induction row with
    | nil => simp
    | cons x row ih =>
      intro st
      rw [List.foldl_cons, ih]
      simp [nextRowStep]
      omega
  rw [sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_cons, hlen, List.length_nil,
      nextRowCost]
    omega

/-- A fold whose body, at step `j < n`, keeps a step-indexed invariant `I j` and, under it, has
a functional model `F` and a uniform cost bound `c`. -/
theorem foldList_idx {a' b' : Ty} {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    {F : b'.denote → a'.denote → b'.denote} {I : ℕ → b'.denote → Prop} {c n : ℕ} :
    ∀ (xs : List a'.denote) (i : ℕ) (init : b'.denote), i + xs.length ≤ n →
      (∀ j acc, j < n → I j acc → ∀ x ∈ xs,
        RunsWithin X body (f acc x) (F acc x) c ∧ I (j + 1) (F acc x)) →
      I i init →
      RunsWithin X body (.foldList xs init f) (xs.foldl F init) (xs.length * (c + 1)) ∧
        I (i + xs.length) (xs.foldl F init)
  | [], i, init, _, _, hI => ⟨by simpa using RunsWithin.foldList_nil, by simpa using hI⟩
  | x :: xs, i, init, hn, hf, hI => by
    simp only [List.length_cons] at hn
    obtain ⟨h₁, hI₁⟩ := hf i init (by omega) hI x List.mem_cons_self
    obtain ⟨h₂, hI₂⟩ := foldList_idx xs (i + 1) (F init x) (by omega)
      (fun j acc hj hacc y hy => hf j acc hj hacc y (List.mem_cons_of_mem _ hy)) hI₁
    refine ⟨(RunsWithin.foldList_cons h₁ h₂).mono ?_, ?_⟩
    · simp only [List.length_cons, Nat.succ_mul]
      omega
    · rw [List.foldl_cons, List.length_cons, ← Nat.add_assoc, Nat.add_right_comm]
      exact hI₂

theorem RunsWithin.pascalProg (n : ℕ) :
    RunsWithin X body (SoJProg.pascalProg n) (pascalRow n) (pascalCost n) := by
  have hfold := foldList_idx (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (f := fun row _ => SoJProg.nextRowProg row) (F := fun row _ => nextRowD row)
    (I := fun j row => row = pascalRow j) (c := nextRowCost n) (n := n) (List.range n) 0 [1]
    (by simp) (fun j row hj hrow _ _ => by
      subst hrow
      refine ⟨(RunsWithin.nextRowProg _).mono ?_, ?_⟩
      · simp only [nextRowCost, length_pascalRow]
        omega
      · rw [nextRowD_eq, pascalRow]) rfl
  rw [pascal_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold.1
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, pascalCost]
    omega

theorem RunsWithin.chooseProg (n s : ℕ) :
    RunsWithin X body (SoJProg.chooseProg n s) (n.choose s) (chooseCost n) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.pascalProg n)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (get_pascalRow n s) le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, length_pascalRow, chooseCost]
    omega

/-- **The Johnson test as a program**: through `johnsonTest_decode`, its output is the test
`|V₁'| = C(|V₂|, s)` of the model. -/
theorem RunsWithin.johnsonTestProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) {V₁ : List ℕ}
    (hV₁ : ∀ x ∈ V₁, x < m) (d₁ : ℕ) :
    RunsWithin X body (SoJProg.johnsonTestProg offs a k V₁ d₁)
      ((tfDegD V₁ k a d₁).length == k.choose (sOf k d₁)) (johnsonTestCost V₁.length k) := by
  have hl : (tfDegD V₁ k a d₁).length ≤ V₁.length := List.length_filter_le _ _
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.tfDegProg hoffs a hV₁ d₁)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.sOfProg k d₁)
    run_step (RunsWithin.chooseProg k _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, johnsonTestCost]
    omega

theorem RunsWithin.fArrProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) (d₁ : ℕ) :
    RunsWithin X body (SoJProg.fArrProg m offs a k d₁) (fArrD m k a d₁) (fArrCost m k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (F := fOfD k a d₁) (c := fOfCost k) fun x hx =>
      RunsWithin.fOfProg hoffs a d₁ (by simpa [Prim.eval] using hx))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map, fArrCost]
    omega

/-- **The Johnson leaf as a program**: through `jembOf` and `johnson_decode`, its output
`⟨V₁', s, f⟩` with the input cells decodes to the Johnson embedding
`⟨tfDeg V₁ V₂ A d₁, V₂, sOf |V₂| d₁, fOf V₂ A d₁⟩` of the model. -/
theorem RunsWithin.johnsonLeafProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) {V₁ : List ℕ}
    (hV₁ : ∀ x ∈ V₁, x < m) (d₁ : ℕ) :
    RunsWithin X body (SoJProg.johnsonLeafProg m offs a k V₁ d₁)
      (tfDegD V₁ k a d₁, sOf k d₁, fArrD m k a d₁) (johnsonLeafCost m V₁.length k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.tfDegProg hoffs a hV₁ d₁)
    run_step (RunsWithin.sOfProg k d₁)
    run_step (RunsWithin.fArrProg hoffs a d₁)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, johnsonLeafCost]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ k₁ n₁ s₁ x₁ d₁ : var₁ .nat} {m₂ k₂ n₂ s₂ x₂ d₂ : var₂ .nat}
  {offs₁ : var₁ (.array .nat)} {offs₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)}
  {a₂ : var₂ (.array .bool)} {V₁ row₁ : var₁ (.list .nat)} {V₂ row₂ : var₂ (.list .nat)}

theorem wf_nbrProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nbrProg offs₁ a₁ k₁ x₁) (nbrProg offs₂ a₂ k₂ x₂) := by
  unfold nbrProg relAtProg Toolkit.filterList
  prog_wf

theorem wf_fOfProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fOfProg offs₁ a₁ k₁ d₁ x₁)
      (fOfProg offs₂ a₂ k₂ d₂ x₂) := by
  unfold fOfProg nbrProg relAtProg Toolkit.filterList
  prog_wf

theorem wf_sOfProg (hv : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sOfProg k₁ d₁) (sOfProg k₂ d₂) := by
  unfold sOfProg
  prog_wf

theorem wf_nextRowProg (hrow : ⟨.list .nat, row₁, row₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (nextRowProg row₁) (nextRowProg row₂) := by
  unfold nextRowProg
  prog_wf

theorem wf_pascalProg (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pascalProg n₁) (pascalProg n₂) := by
  unfold pascalProg nextRowProg
  prog_wf

theorem wf_chooseProg (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (chooseProg n₁ s₁) (chooseProg n₂ s₂) := by
  unfold chooseProg pascalProg nextRowProg
  prog_wf

theorem wf_johnsonTestProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (johnsonTestProg offs₁ a₁ k₁ V₁ d₁)
      (johnsonTestProg offs₂ a₂ k₂ V₂ d₂) := by
  unfold johnsonTestProg
  exact .bind (wf_tfDegProg hoffs ha hk hV hd) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_sOfProg (by simp [hk]) (by simp [hd])) fun _ _ =>
    .bind (wf_chooseProg (by simp [hk]) (by simp)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_fArrProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fArrProg m₁ offs₁ a₁ k₁ d₁)
      (fArrProg m₂ offs₂ a₂ k₂ d₂) := by
  unfold fArrProg fOfProg nbrProg relAtProg Toolkit.filterList mapList
  prog_wf

theorem wf_johnsonLeafProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (johnsonLeafProg m₁ offs₁ a₁ k₁ V₁ d₁)
      (johnsonLeafProg m₂ offs₂ a₂ k₂ V₂ d₂) := by
  unfold johnsonLeafProg
  exact .bind (wf_tfDegProg hoffs ha hk hV hd) fun _ _ =>
    .bind (wf_sOfProg (by simp [hk]) (by simp [hd])) fun _ _ =>
    .bind (wf_fArrProg (by simp [hm]) (by simp [hoffs]) (by simp [ha]) (by simp [hk])
      (by simp [hd])) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.SoJProg
