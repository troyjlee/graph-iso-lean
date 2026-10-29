module

public import GraphIso.SoJProg.TwinsData
public import GraphIso.Toolkit.Labels
public import GraphIso.Toolkit.Orbital

/-!
# Twins and degrees as programs

Step 1 of milestone 11's `bstep` as costed programs (`PLAN-14.md` §7 item 2). The relation is
read through an array `offs` of row offsets (`offs[x] = x k`, computed by `offsetsProg`), so
no program multiplies; every spec takes `hoffs : ∀ x < m, get offs x = x * k`.

* `offsetsProg`, `relAtProg`, `degProg`, `twinProg`, `twProg`, `tfDegProg`, `dedupProg`,
  `degsProg`, `bigDegsProg`, `optMinProg`, `pairProg` (`Nat.pair`), `twinColProg`,
  `twinBlkProg`, `twinPartProg`, `minBigDegProg`: each computes its data model of
  `SoJProg/TwinsData.lean` within an explicit polynomial cost, in terms of `m` (points),
  `n₁ = |V₁|` and `k = |cs|`; each has a well-formedness lemma `wf_*`.
* Through the decoding theorems of `TwinsData.lean`, they compute milestone 11's `deg`, `tw`,
  `twinCls`, `tfDeg`, `bigDegs` (with its least element) and `twinPart`.
-/

@[expose] public section

namespace GraphIso.SoJProg

open Cost GraphIso GraphIso.Programs

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The row offsets `x k` for `x < m`. -/
def offsetsProg (m k : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range m) fun is => .bind (.op0 (.natLit 0)) fun z =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .pair z nil) fun st₀ =>
  .bind (.foldList is st₀ fun st _ =>
      .bind (.op1 .fst st) fun off => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .cons off acc) fun acc' => .bind (.op2 .add off k) fun off' =>
      .op2 .pair off' acc') fun fin =>
  .bind (.op1 .snd fin) fun racc => .bind (.op1 .reverse racc) fun l => .op1 .arrayOfList l

/-- The relation between `x` and the `j`-th cell. -/
def relAtProg (offs : var (.array .nat)) (a : var (.array .bool)) (x j : var .nat) :
    Prog S rec var .bool :=
  .bind (.op2 .arrayGet offs x) fun o => .bind (.op2 .add o j) fun i => .op2 .arrayGet a i

/-- The degree of `x`. -/
def degProg (offs : var (.array .nat)) (a : var (.array .bool)) (k x : var .nat) :
    Prog S rec var .nat :=
  .bind (.op1 .range k) fun rk => Toolkit.countList rk fun j => relAtProg offs a x j

/-- Boolean equality. -/
def boolEqProg (b c : var .bool) : Prog S rec var .bool :=
  .bind (.op2 .and b c) fun bc => .bind (.op1 .not b) fun nb => .bind (.op1 .not c) fun nc =>
  .bind (.op2 .and nb nc) fun nbc => .op2 .or bc nbc

/-- The twin class of `x` in `V₁`. -/
def twinProg (offs : var (.array .nat)) (a : var (.array .bool)) (k : var .nat)
    (V₁ : var (.list .nat)) (x : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range k) fun rk => Toolkit.filterList V₁ fun x' =>
    allList rk fun j => .bind (relAtProg offs a x j) fun b =>
      .bind (relAtProg offs a x' j) fun c => boolEqProg b c

/-- The size of the twin class of `x`. -/
def twProg (offs : var (.array .nat)) (a : var (.array .bool)) (k : var .nat)
    (V₁ : var (.list .nat)) (x : var .nat) : Prog S rec var .nat :=
  .bind (twinProg offs a k V₁ x) fun l => .op1 .length l

/-- The points of `V₁` without twins and of degree `d`. -/
def tfDegProg (offs : var (.array .nat)) (a : var (.array .bool)) (k : var .nat)
    (V₁ : var (.list .nat)) (d : var .nat) : Prog S rec var (.list .nat) :=
  Toolkit.filterList V₁ fun x =>
    .bind (twProg offs a k V₁ x) fun tw => .bind (.op0 (.natLit 1)) fun one =>
    .bind (.op2 .natEq tw one) fun e₁ => .bind (degProg offs a k x) fun dg =>
    .bind (.op2 .natEq dg d) fun e₂ => .op2 .and e₁ e₂

/-- Remove repetitions, keeping first occurrences. -/
def dedupProg (l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList l nil fun acc x =>
      .bind (anyList acc fun y => .op2 .natEq y x) fun seen =>
      .ite seen (.ret acc) (.op2 .cons x acc)) fun r =>
  .op1 .reverse r

/-- The degrees of the points of `V₁`, without repetitions. -/
def degsProg (offs : var (.array .nat)) (a : var (.array .bool)) (k : var .nat)
    (V₁ : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (mapList V₁ fun x => degProg offs a k x) fun ds => dedupProg ds

/-- The degrees whose points without twins are more than `t`. -/
def bigDegsProg (t : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (k : var .nat) (V₁ : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (degsProg offs a k V₁) fun ds => Toolkit.filterList ds fun d =>
    .bind (tfDegProg offs a k V₁ d) fun l => .bind (.op1 .length l) fun n => .op2 .natLt t n

/-- The least entry of a list, if any. -/
def optMinProg (l : var (.list .nat)) : Prog S rec var (.option .nat) :=
  .caseList l (.op0 .none) fun c _ =>
    .bind (.foldList l c fun acc d =>
      .bind (.op2 .natLt d acc) fun lt => .ite lt (.ret d) (.ret acc)) fun mn =>
    .op1 .some mn

/-- `Nat.pair`. -/
def pairProg (x y : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natLt x y) fun lt =>
  .ite lt (.bind (Toolkit.mulProg y y) fun yy => .op2 .add yy x)
    (.bind (Toolkit.mulProg x x) fun xx => .bind (.op2 .add xx x) fun s => .op2 .add s y)

/-- The colours of `twinPart` at the points `0, …, m - 1`. -/
def twinColProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (k : var .nat) (V₁ : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range m) fun is =>
  .bind (mapList is fun x => .bind (twProg offs a k V₁ x) fun tw =>
      .bind (degProg offs a k x) fun dg => pairProg tw dg) fun l =>
  .op1 .arrayOfList l

/-- The blocks of `twinPart` at the points `0, …, m - 1`. -/
def twinBlkProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (k : var .nat) (V₁ : var (.list .nat)) : Prog S rec var (.array (.list .nat)) :=
  .bind (.op1 .range m) fun is =>
  .bind (mapList is fun x => .bind (twProg offs a k V₁ x) fun tw =>
      .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natEq tw one) fun e =>
      .ite e (.bind (degProg offs a k x) fun dg => tfDegProg offs a k V₁ dg)
        (twinProg offs a k V₁ x)) fun l =>
  .op1 .arrayOfList l

/-- `twinPart` on data: the colour array and the block array. -/
def twinPartProg (m k : var .nat) (a : var (.array .bool)) (V₁ : var (.list .nat)) :
    Prog S rec var (.prod (.array .nat) (.array (.list .nat))) :=
  .bind (offsetsProg m k) fun offs => .bind (twinColProg m offs a k V₁) fun col =>
  .bind (twinBlkProg m offs a k V₁) fun blk => .op2 .pair col blk

/-- The least degree whose points without twins are more than `t`, if any. -/
def minBigDegProg (t : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (k : var .nat) (V₁ : var (.list .nat)) : Prog S rec var (.option .nat) :=
  .bind (bigDegsProg t offs a k V₁) fun ds => optMinProg ds

end Programs

/-! ### Costs -/

/-- The cost of `degProg`. -/
def degCost (k : ℕ) : ℕ := 8 * k + 2

/-- The cost of `twinProg`. -/
def twinCost (n₁ k : ℕ) : ℕ := n₁ * (13 * k + 5) + k + 4

/-- The cost of `twProg`. -/
def twCost (n₁ k : ℕ) : ℕ := twinCost n₁ k + n₁ + 2

/-- The cost of `tfDegProg`. -/
def tfDegCost (n₁ k : ℕ) : ℕ := n₁ * (twCost n₁ k + degCost k + 12) + 3

/-- The cost of `dedupProg` on a list of length `n`. -/
def dedupCost (n : ℕ) : ℕ := n * (3 * n + 5) + n + 3

/-- The cost of `degsProg`. -/
def degsCost (n₁ k : ℕ) : ℕ := n₁ * (degCost k + 3) + 2 + dedupCost n₁

/-- The cost of `bigDegsProg`. -/
def bigDegsCost (n₁ k : ℕ) : ℕ := degsCost n₁ k + n₁ * (tfDegCost n₁ k + n₁ + 7) + 3

/-- The cost of `twinColProg`. -/
def twinColCost (m n₁ k : ℕ) : ℕ :=
  m * (twCost n₁ k + degCost k + 3 * (n₁ + k) + 10) + 2 * m + 4

/-- The cost of `twinBlkProg`. -/
def twinBlkCost (m n₁ k : ℕ) : ℕ :=
  m * (twCost n₁ k + degCost k + tfDegCost n₁ k + twinCost n₁ k + 6) + 2 * m + 4

/-- The cost of `twinPartProg`. -/
def twinPartCost (m n₁ k : ℕ) : ℕ := 10 * m + 10 + twinColCost m n₁ k + twinBlkCost m n₁ k

/-- The cost of `minBigDegProg`. -/
def minBigDegCost (n₁ k : ℕ) : ℕ := bigDegsCost n₁ k + 3 * n₁ + 4

/-! ### Specs -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem offsets_fold (k : ℕ) : ∀ (n : ℕ),
    (List.range n).foldl (fun st (_ : ℕ) => (st.1 + k, st.1 :: st.2)) ((0 : ℕ), ([] : List ℕ)) =
      (n * k, ((List.range n).map (· * k)).reverse)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, offsets_fold k n]
    simp [Nat.succ_mul]

theorem RunsWithin.offsetsProg (m k : ℕ) :
    RunsWithin X body (SoJProg.offsetsProg m k) ((List.range m).map (· * k)).toArray
      (10 * m + 9) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list .nat))
    (f := fun st _ => Prog.bind (.op1 .fst st) fun off => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .cons off acc) fun acc' => .bind (.op2 .add off k) fun off' =>
      .op2 .pair off' acc')
    (F := fun st _ => (st.1 + k, st.1 :: st.2)) (cf := fun _ => 5) (List.range m) (0, [])
    fun st _ _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp [Prim.cost]
  rw [offsets_fold, sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_reverse,
      List.length_map]
    omega

theorem RunsWithin.relAtProg (offs : Array ℕ) (a : Array Bool) (x j : ℕ) :
    RunsWithin X body (SoJProg.relAtProg offs a x j) (getB a (get offs x + j)) 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem relAt_of_offs {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    {a : Array Bool} {x : ℕ} (hx : x < m) (j : ℕ) : getB a (get offs x + j) = relAt k a x j := by
  rw [hoffs x hx, relAt]

theorem RunsWithin.degProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJProg.degProg offs a k x) (degD k a x) (degCost k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact (Toolkit.RunsWithin.countList (c := 3) fun j _ => RunsWithin.relAtProg offs a x j).of_eq
      (by rw [degD]; congr 1; exact List.filter_congr fun j _ => relAt_of_offs hoffs hx j)
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, degCost]
    omega

theorem RunsWithin.boolEqProg (b c : Bool) :
    RunsWithin X body (SoJProg.boolEqProg b c) (b == c) 5 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by cases b <;> cases c <;> rfl) le_rfl
  case hc => simp [Prim.cost]

theorem twinD_eq {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {V₁ : List ℕ} (hV₁ : ∀ x ∈ V₁, x < m) {x : ℕ} (hx : x < m) :
    V₁.filter (fun x' => (List.range k).all fun j =>
      getB a (get offs x + j) == getB a (get offs x' + j)) = twinD V₁ k a x := by
  unfold twinD
  refine List.filter_congr fun x' hx' => ?_
  congr 1
  funext j
  rw [relAt_of_offs hoffs hx, relAt_of_offs hoffs (hV₁ x' hx')]

theorem RunsWithin.twinProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {V₁ : List ℕ} (hV₁ : ∀ x ∈ V₁, x < m) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJProg.twinProg offs a k V₁ x) (twinD V₁ k a x)
      (twinCost V₁.length k) := by
  have hf := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := V₁)
    (p := fun x' => allList (a' := .nat) (List.range k : (Ty.list .nat).denote) fun j =>
      Prog.bind (SoJProg.relAtProg offs a x j)
      fun b => Prog.bind (SoJProg.relAtProg offs a x' j) fun c => SoJProg.boolEqProg b c)
    (P := fun x' => (List.range k).all fun j =>
      getB a (get offs x + j) == getB a (get offs x' + j)) (c := k * 13 + 1) fun x' _ => by
      refine (RunsWithin.allList_le (c := 11) fun j _ => ?_).mono
        (by simp only [List.length_range]; omega)
      exact RunsWithin.bind_le (RunsWithin.relAtProg offs a x j)
        (RunsWithin.bind_le (RunsWithin.relAtProg offs a x' j) (RunsWithin.boolEqProg _ _) le_rfl)
        (by omega)
  rw [twinD_eq hoffs a hV₁ hx] at hf
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hf
  case hc =>
    simp only [Prim.cost, Args.head, twinCost]
    have : V₁.length * (k * 13 + 1 + 4) = V₁.length * (13 * k + 5) := by ring
    omega

theorem length_twinD_le (V₁ : List ℕ) (k : ℕ) (a : Array Bool) (x : ℕ) :
    (twinD V₁ k a x).length ≤ V₁.length := List.length_filter_le _ _

theorem RunsWithin.twProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {V₁ : List ℕ} (hV₁ : ∀ x ∈ V₁, x < m) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJProg.twProg offs a k V₁ x) (twD V₁ k a x) (twCost V₁.length k) := by
  have hle := length_twinD_le V₁ k a x
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.twinProg hoffs a hV₁ hx)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, twCost]
    omega

theorem RunsWithin.tfDegProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {V₁ : List ℕ} (hV₁ : ∀ x ∈ V₁, x < m) (d : ℕ) :
    RunsWithin X body (SoJProg.tfDegProg offs a k V₁ d) (tfDegD V₁ k a d)
      (tfDegCost V₁.length k) := by
  have hf := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := V₁)
    (p := fun x => Prog.bind (SoJProg.twProg offs a k V₁ x) fun tw =>
      .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natEq tw one) fun e₁ =>
      .bind (SoJProg.degProg offs a k x) fun dg => .bind (.op2 .natEq dg d) fun e₂ =>
      .op2 .and e₁ e₂)
    (P := fun x => twD V₁ k a x == 1 && degD k a x == d)
    (c := twCost V₁.length k + degCost k + 4) fun x hx => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.twProg hoffs a hV₁ (hV₁ x hx))
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.degProg hoffs a (hV₁ x hx))
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost]
        omega
  apply hf.mono
  simp only [tfDegCost]
  have : V₁.length * (twCost V₁.length k + degCost k + 4 + 4) ≤
      V₁.length * (twCost V₁.length k + degCost k + 12) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem any_beq_eq_contains (acc : List ℕ) (x : ℕ) :
    (acc.any fun y => y == x) = acc.contains x := by
  rw [List.contains_eq_any_beq]
  congr 1
  funext y
  cases h : (y == x) <;> cases h' : (x == y) <;> simp_all [beq_iff_eq]

/-- One step of `dedupProg`'s fold keeps the accumulator duplicate-free and inside `l`. -/
theorem dedup_step {l acc : List ℕ} (hacc : acc.Nodup ∧ ∀ y ∈ acc, y ∈ l) {x : ℕ}
    (hx : x ∈ l) :
    (if acc.contains x then acc else x :: acc).Nodup ∧
      ∀ y ∈ (if acc.contains x then acc else x :: acc), y ∈ l := by
  by_cases h : acc.contains x = true
  · simp only [h, ↓reduceIte]
    exact hacc
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    refine ⟨List.nodup_cons.2 ⟨by simpa using h, hacc.1⟩, ?_⟩
    rintro y (_ | ⟨_, hy⟩)
    · exact hx
    · exact hacc.2 y hy

theorem dedup_fold {l : List ℕ} : ∀ (l' acc : List ℕ), (∀ x ∈ l', x ∈ l) →
    acc.Nodup ∧ (∀ y ∈ acc, y ∈ l) →
    (l'.foldl (fun acc x => if acc.contains x then acc else x :: acc) acc).Nodup ∧
      ∀ y ∈ l'.foldl (fun acc x => if acc.contains x then acc else x :: acc) acc, y ∈ l
  | [], _, _, h => h
  | x :: l', acc, hl', h => by
    rw [List.foldl_cons]
    exact dedup_fold l' _ (fun y hy => hl' y (List.mem_cons_of_mem _ hy))
      (dedup_step h (hl' x List.mem_cons_self))

theorem length_dedupD_le (l : List ℕ) : (dedupD l).length ≤ l.length := by
  have h := dedup_fold (l := l) l [] (fun _ hx => hx) ⟨List.nodup_nil, by simp⟩
  rw [dedupD, List.length_reverse]
  exact (List.subperm_of_subset h.1 h.2).length_le

theorem RunsWithin.dedupProg (l : List ℕ) :
    RunsWithin X body (SoJProg.dedupProg l) (dedupD l) (dedupCost l.length) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (I := fun acc => acc.Nodup ∧ ∀ y ∈ acc, y ∈ l) (c := 3 * l.length + 3)
    (f := fun acc x => Prog.bind (anyList acc fun y => .op2 .natEq y x) fun seen =>
      Prog.ite seen (.ret acc) (.op2 .cons x acc))
    (F := fun acc x => if acc.contains x then acc else x :: acc) l [] (fun acc hacc x hx => by
      have hlen : acc.length ≤ l.length :=
        (List.subperm_of_subset hacc.1 hacc.2).length_le
      have hany := RunsWithin.anyList_le (X := X) (body := body) (xs := acc)
        (p := fun y => Prog.op2 (S := S) .natEq y x) (P := fun y => y == x) (c := 1)
        fun y _ => RunsWithin.prim_le rfl le_rfl
      rw [any_beq_eq_contains] at hany
      refine ⟨RunsWithin.bind_le (c₂ := 2) hany ?_ (by omega), dedup_step hacc hx⟩
      by_cases h : acc.contains x = true
      · simp only [h, ↓reduceIte]
        exact (RunsWithin.ite_true (RunsWithin.ret _)).mono (by omega)
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        exact (RunsWithin.ite_false (RunsWithin.prim _ _)).mono (by simp [Prim.cost]))
    ⟨List.nodup_nil, by simp⟩
  have hr := (List.subperm_of_subset hfold.2.1 hfold.2.2).length_le
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, dedupCost]
    have : l.length * (3 * l.length + 3 + 1) + l.length = l.length * (3 * l.length + 5) := by
      ring
    omega

theorem RunsWithin.degsProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {V₁ : List ℕ} (hV₁ : ∀ x ∈ V₁, x < m) :
    RunsWithin X body (SoJProg.degsProg offs a k V₁) (degsD V₁ k a) (degsCost V₁.length k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapList_le (c := degCost k) fun x hx => RunsWithin.degProg hoffs a
      (hV₁ x hx))
    exact RunsWithin.dedupProg _
  case hc =>
    simp only [degsCost, List.length_map]
    omega

theorem length_degsD_le (V₁ : List ℕ) (k : ℕ) (a : Array Bool) :
    (degsD V₁ k a).length ≤ V₁.length :=
  (length_dedupD_le _).trans (by simp)

theorem RunsWithin.bigDegsProg {m k : ℕ} {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) {V₁ : List ℕ} (hV₁ : ∀ x ∈ V₁, x < m) (t : ℕ) :
    RunsWithin X body (SoJProg.bigDegsProg t offs a k V₁) (bigDegsD t V₁ k a)
      (bigDegsCost V₁.length k) := by
  have hf := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := degsD V₁ k a)
    (p := fun d => Prog.bind (SoJProg.tfDegProg offs a k V₁ d) fun l =>
      .bind (.op1 .length l) fun n => .op2 .natLt t n)
    (P := fun d => decide (t < (tfDegD V₁ k a d).length))
    (c := tfDegCost V₁.length k + V₁.length + 2) fun d _ => by
      have hl : (tfDegD V₁ k a d).length ≤ V₁.length := List.length_filter_le _ _
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.tfDegProg hoffs a hV₁ d)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, Args.head]
        omega
  have hd := length_degsD_le V₁ k a
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.degsProg hoffs a hV₁)
    exact hf
  case hc =>
    simp only [bigDegsCost]
    have : (degsD V₁ k a).length * (tfDegCost V₁.length k + V₁.length + 2 + 4) ≤
        V₁.length * (tfDegCost V₁.length k + V₁.length + 7) :=
      Nat.mul_le_mul hd (by omega)
    omega

theorem optMin_fold (c : ℕ) (cs : List ℕ) :
    (c :: cs).foldl (fun acc d => if d < acc then d else acc) c = cs.foldl min c := by
  rw [List.foldl_cons]
  simp only [lt_irrefl, ↓reduceIte]
  have : ∀ (l : List ℕ) (acc : ℕ),
      l.foldl (fun acc d => if d < acc then d else acc) acc = l.foldl min acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons d l ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      split_ifs <;> omega
  exact this cs c

theorem RunsWithin.optMinProg (l : List ℕ) :
    RunsWithin X body (SoJProg.optMinProg l) (optMin l) (3 * l.length + 4) := by
  cases l with
  | nil =>
    exact (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono (by simp [Prim.cost])
  | cons c cs =>
    have hfold := RunsWithin.foldList_inv (X := X) (body := body) (I := fun _ => True)
      (c := 2) (a' := .nat) (b' := .nat)
      (f := fun (acc : Ty.nat.denote) (d : Ty.nat.denote) =>
        Prog.bind (.op2 .natLt d acc) fun lt => Prog.ite lt (.ret d) (.ret acc))
      (F := fun acc d => if d < acc then d else acc) (c :: cs) c (fun acc _ d _ => by
        refine ⟨?_, trivial⟩
        by_cases h : d < acc
        · refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
          simp only [Prim.eval, h, decide_true, ↓reduceIte]
          exact (RunsWithin.ite_true (RunsWithin.ret _)).mono (by omega)
        · refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
          simp only [Prim.eval, h, decide_false, ↓reduceIte]
          exact (RunsWithin.ite_false (RunsWithin.ret _)).mono (by omega)) trivial
    rw [optMin_fold] at hfold
    refine (RunsWithin.caseList_cons ((hfold.1.bind (RunsWithin.prim .some _)))).mono ?_
    simp only [Prim.cost, List.length_cons]
    omega

theorem RunsWithin.pairProg (x y : ℕ) :
    RunsWithin X body (SoJProg.pairProg x y) (Nat.pair x y) (3 * (x + y) + 7) := by
  by_cases h : x < y
  · have he : Prim.eval Prim.natLt (Args.cons x (Args.cons y Args.nil)) = true := by
      simp [Prim.eval, h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      rw [he]
      apply RunsWithin.ite_true
      run_step (Toolkit.RunsWithin.mulProg y y)
      exact RunsWithin.prim_le (by simp [Prim.eval, Nat.pair, h]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega
  · have he : Prim.eval Prim.natLt (Args.cons x (Args.cons y Args.nil)) = false := by
      simp [Prim.eval, h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      rw [he]
      apply RunsWithin.ite_false
      run_step (Toolkit.RunsWithin.mulProg x x)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval, Nat.pair, h]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega

theorem degD_le (k : ℕ) (a : Array Bool) (x : ℕ) : degD k a x ≤ k := by
  unfold degD
  exact (List.length_filter_le _ _).trans (by simp)

theorem RunsWithin.twinColProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) {V₁ : List ℕ}
    (hV₁ : ∀ x ∈ V₁, x < m) :
    RunsWithin X body (SoJProg.twinColProg m offs a k V₁) (twinColD m V₁ k a)
      (twinColCost m V₁.length k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (F := fun x => Nat.pair (twD V₁ k a x) (degD k a x))
      (c := twCost V₁.length k + degCost k + 3 * (V₁.length + k) + 7) fun x hx => by
        have hxm : x < m := by simpa [Prim.eval] using hx
        have h1 := length_twinD_le V₁ k a x
        have h2 := degD_le k a x
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.twProg hoffs a hV₁ hxm)
          run_step (RunsWithin.degProg hoffs a hxm)
          exact RunsWithin.pairProg _ _
        case hc =>
          simp only [twD]
          omega)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map,
      twinColCost]
    have : m * (twCost V₁.length k + degCost k + 3 * (V₁.length + k) + 7 + 3) ≤
        m * (twCost V₁.length k + degCost k + 3 * (V₁.length + k) + 10) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem RunsWithin.twinBlkProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) {V₁ : List ℕ}
    (hV₁ : ∀ x ∈ V₁, x < m) :
    RunsWithin X body (SoJProg.twinBlkProg m offs a k V₁) (twinBlkD m V₁ k a)
      (twinBlkCost m V₁.length k) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (F := fun x => if twD V₁ k a x == 1 then
        tfDegD V₁ k a (degD k a x) else twinD V₁ k a x)
      (c := twCost V₁.length k + degCost k + tfDegCost V₁.length k + twinCost V₁.length k + 3)
      fun x hx => by
        have hxm : x < m := by simpa [Prim.eval] using hx
        by_cases h : twD V₁ k a x = 1
        · apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.twProg hoffs a hV₁ hxm)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            simp only [Prim.eval, h, beq_self_eq_true, ↓reduceIte]
            apply RunsWithin.ite_true
            run_step (RunsWithin.degProg hoffs a hxm)
            exact RunsWithin.tfDegProg hoffs a hV₁ _
          case hc =>
            simp only [Prim.cost]
            omega
        · have h' : (twD V₁ k a x == 1) = false := by simpa using h
          apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.twProg hoffs a hV₁ hxm)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            simp only [Prim.eval, h', Bool.false_eq_true, ↓reduceIte]
            apply RunsWithin.ite_false
            exact RunsWithin.twinProg hoffs a hV₁ hxm
          case hc =>
            simp only [Prim.cost]
            omega)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map,
      twinBlkCost]
    have : m * (twCost V₁.length k + degCost k + tfDegCost V₁.length k + twinCost V₁.length k +
        3 + 3) ≤ m * (twCost V₁.length k + degCost k + tfDegCost V₁.length k +
          twinCost V₁.length k + 6) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

theorem get_offsets {m k x : ℕ} (hx : x < m) :
    get ((List.range m).map (· * k)).toArray x = x * k := by
  rw [get, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_range hx]
  rfl

/-- **`twinPart` as a program**: through `twinPart_decode`, its output decodes (by `cpartOf`)
to milestone 11's `twinPart`. -/
theorem RunsWithin.twinPartProg (m k : ℕ) (a : Array Bool) {V₁ : List ℕ}
    (hV₁ : ∀ x ∈ V₁, x < m) :
    RunsWithin X body (SoJProg.twinPartProg m k a V₁) (twinColD m V₁ k a, twinBlkD m V₁ k a)
      (twinPartCost m V₁.length k) := by
  have hoffs : ∀ x < m, get ((List.range m).map (· * k)).toArray x = x * k :=
    fun _ hx => get_offsets hx
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.offsetsProg m k)
    run_step (RunsWithin.twinColProg hoffs a hV₁)
    run_step (RunsWithin.twinBlkProg hoffs a hV₁)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, twinPartCost]
    omega

/-- **The least big degree as a program**: through `optMin_bigDegs`, its output is the least
element of milestone 11's `bigDegs`, if any. -/
theorem RunsWithin.minBigDegProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) {V₁ : List ℕ}
    (hV₁ : ∀ x ∈ V₁, x < m) (t : ℕ) :
    RunsWithin X body (SoJProg.minBigDegProg t offs a k V₁) (optMin (bigDegsD t V₁ k a))
      (minBigDegCost V₁.length k) := by
  have hl : (bigDegsD t V₁ k a).length ≤ V₁.length :=
    (List.length_filter_le _ _).trans (length_degsD_le V₁ k a)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.bigDegsProg hoffs a hV₁ t)
    exact RunsWithin.optMinProg _
  case hc =>
    simp only [minBigDegCost]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ k₁ t₁ x₁ y₁ d₁ : var₁ .nat} {m₂ k₂ t₂ x₂ y₂ d₂ : var₂ .nat}
  {offs₁ : var₁ (.array .nat)} {offs₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)}
  {a₂ : var₂ (.array .bool)} {V₁ : var₁ (.list .nat)} {V₂ : var₂ (.list .nat)}

theorem wf_offsetsProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (offsetsProg m₁ k₁) (offsetsProg m₂ k₂) := by
  unfold offsetsProg
  prog_wf

theorem wf_degProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (degProg offs₁ a₁ k₁ x₁) (degProg offs₂ a₂ k₂ x₂) := by
  unfold degProg relAtProg Toolkit.countList
  prog_wf

theorem wf_twinProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinProg offs₁ a₁ k₁ V₁ x₁)
      (twinProg offs₂ a₂ k₂ V₂ x₂) := by
  unfold twinProg relAtProg boolEqProg Toolkit.filterList allList
  prog_wf

theorem wf_twProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twProg offs₁ a₁ k₁ V₁ x₁) (twProg offs₂ a₂ k₂ V₂ x₂) := by
  unfold twProg twinProg relAtProg boolEqProg Toolkit.filterList allList
  prog_wf

theorem wf_tfDegProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tfDegProg offs₁ a₁ k₁ V₁ d₁)
      (tfDegProg offs₂ a₂ k₂ V₂ d₂) := by
  unfold tfDegProg twProg twinProg degProg relAtProg boolEqProg Toolkit.filterList
    Toolkit.countList allList
  prog_wf

theorem wf_dedupProg (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (dedupProg V₁) (dedupProg V₂) := by
  unfold dedupProg anyList
  prog_wf

theorem wf_degsProg (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (degsProg offs₁ a₁ k₁ V₁) (degsProg offs₂ a₂ k₂ V₂) := by
  unfold degsProg dedupProg degProg relAtProg Toolkit.countList mapList anyList
  prog_wf

theorem wf_bigDegsProg (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (bigDegsProg t₁ offs₁ a₁ k₁ V₁)
      (bigDegsProg t₂ offs₂ a₂ k₂ V₂) := by
  unfold bigDegsProg degsProg tfDegProg twProg twinProg dedupProg degProg relAtProg boolEqProg
    Toolkit.filterList Toolkit.countList mapList anyList allList
  prog_wf

theorem wf_optMinProg (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (optMinProg V₁) (optMinProg V₂) := by
  unfold optMinProg
  prog_wf

theorem wf_pairProg (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) (hy : ⟨.nat, y₁, y₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pairProg x₁ y₁) (pairProg x₂ y₂) := by
  unfold pairProg Toolkit.mulProg
  prog_wf

theorem wf_twinColProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinColProg m₁ offs₁ a₁ k₁ V₁)
      (twinColProg m₂ offs₂ a₂ k₂ V₂) := by
  unfold twinColProg pairProg twProg twinProg degProg relAtProg boolEqProg Toolkit.filterList
    Toolkit.countList Toolkit.mulProg mapList allList
  prog_wf

theorem wf_twinBlkProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinBlkProg m₁ offs₁ a₁ k₁ V₁)
      (twinBlkProg m₂ offs₂ a₂ k₂ V₂) := by
  unfold twinBlkProg tfDegProg twProg twinProg degProg relAtProg boolEqProg Toolkit.filterList
    Toolkit.countList mapList allList
  prog_wf

theorem wf_twinPartProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinPartProg m₁ k₁ a₁ V₁) (twinPartProg m₂ k₂ a₂ V₂) := by
  unfold twinPartProg
  exact .bind (wf_offsetsProg hm hk) fun _ _ =>
    .bind (wf_twinColProg (by simp [hm]) (by simp) (by simp [ha]) (by simp [hk]) (by simp [hV]))
    fun _ _ =>
    .bind (wf_twinBlkProg (by simp [hm]) (by simp) (by simp [ha]) (by simp [hk]) (by simp [hV]))
    fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_minBigDegProg (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hoffs : ⟨.array .nat, offs₁, offs₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (minBigDegProg t₁ offs₁ a₁ k₁ V₁)
      (minBigDegProg t₂ offs₂ a₂ k₂ V₂) :=
  .bind (wf_bigDegsProg ht hoffs ha hk hV) fun _ _ => wf_optMinProg (by simp)

end Wf

end GraphIso.SoJProg
