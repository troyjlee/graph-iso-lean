module

public import GraphIso.Case3.Pipeline
public import GraphIso.Case2b.Case2bProg
public import GraphIso.Coherent.WLProg

/-!
# Case 3 on data: the programs of the structures

Stage 14i, item 4 (`PLAN-14.md` §13), the programs without backend calls of the data pipeline of
`GraphIso/Case3/Pipeline.lean`:

* `wlCProg`: milestone 10's `k`-ary Weisfeiler–Leman program (`wlProg`), the refined array;
* `tOfProg`: the threshold `(m' + 1) / 2`;
* `smallLeafProg`: the colored partition by a vertex colouring;
* `skelProg`: the individualized 2-skeleton restricted to a class (milestone 10's `pad2Prog`
  read in the refinement);
* `outcomeProg`: the structures at one good list (`outcomeD`), through stage 14h's
  `leavesOfProg` and `extProg`; its cost `outCostD` is explicit, polynomial in `|V|`, `k`, the
  base size and linear in the size `outSzD` of the `soj` tree it builds;
* `allStructsProg`, `firstStructProg`, `twinsFlagProg`: all structures (over the good lists of
  stage 14c's `goodListProg`, at most `k (|V|^k + 1)` of them), the first structure, and the
  twins flag, each from the colouring; the cost of all structures is `structsCost`, for uniform
  bounds on the per-list cost (`outCostD`) and the `soj` size (`outSzD`); every structure has
  size at most `M + outB |V| (|V| + 2)` (`outSize_outcomeD_le`).

Each computes its data model (`RunsWithin.*`) and is well formed.
-/

@[expose] public section

namespace GraphIso.Case3

open Finset GraphIso GraphIso.Cost GraphIso.Programs GraphIso.SplitJohnson GraphIso.SoJProg
  GraphIso.SoJTree GraphIso.Coherent GraphIso.Case2b

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The `k`-ary refinement of a colouring, the array only. -/
def wlCProg (k m : var .nat) (col : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (Coherent.wlProg k m col) fun r => .op1 .fst r

/-- The threshold `(m + 1) / 2`. -/
def tOfProg (m : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add m one) fun m₁ => Case2b.halfProg m₁

/-- The colored partition by a vertex colouring (`smallLeafD`). -/
def smallLeafProg (col : var (.list .nat)) : Prog S rec var outTy :=
  .bind (.op1 .arrayOfList col) fun colA => .bind (.op1 .length col) fun l =>
  .bind (.op1 .range l) fun rl =>
  .bind (mapList rl fun u => Coherent.classProg colA rl u) fun blks =>
  .bind (.op1 .arrayOfList blks) fun blkA => SoJTree.partProg colA blkA

/-- One entry of the restricted 2-skeleton. -/
def skelEntryProg (W : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk : var (.list .nat)) (l : var .nat) (zA CA : var (.array .nat)) (i j : var .nat) :
    Prog S rec var .nat :=
  .bind (.op2 .arrayGet CA i) fun u => .bind (.op2 .arrayGet CA j) fun v =>
  .bind (Coherent.pad2Prog pw rk l zA u v) fun code => .op2 .arrayGet W code

/-- The individualized 2-skeleton restricted to the class `C`, an `s × s` array (`skelCD`). -/
def skelProg (W : var (.array .nat)) (pw : var (.array (.array .nat))) (rk : var (.list .nat))
    (l : var .nat) (zA : var (.array .nat)) (C : var (.list .nat)) (s : var .nat) :
    Prog S rec var (.array .nat) :=
  .bind (.op1 .arrayOfList C) fun CA =>
  Toolkit.matrixProg s fun i _ j => skelEntryProg W pw rk l zA CA i j

/-- The structures of a good list with small classes: the extended colored partition. -/
def smallBranchProg (M : var .nat) (V : var (.list .nat)) (col : var (.list .nat)) :
    Prog S rec var (.list outTy) :=
  .bind (smallLeafProg col) fun o => .bind (Case2b.extProg M V o) fun o' =>
  .bind (.op0 .nil) fun nil => .op2 .cons o' nil

/-- The structures of a good list with a dominant class: the leaves of the restricted
2-skeleton, extended along the base indices of the class. -/
def domBranchProg (M : var .nat) (VA W : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rk : var (.list .nat)) (l : var .nat) (zA colA : var (.array .nat))
    (rm : var (.list .nat)) (u₀ : var .nat) : Prog S rec var (.list outTy) :=
  .bind (Coherent.classProg colA rm u₀) fun C =>
  .bind (mapList C fun i => .op2 .arrayGet VA i) fun CB =>
  .bind (.op1 .length CB) fun s =>
  .bind (skelProg W pw rk l zA C s) fun sk =>
  .bind (Case2b.leavesOfProg s sk) fun ls =>
  mapList ls fun o => Case2b.extProg M CB o

/-- **The structures at a good list** (`outcomeD`). -/
def outcomeProg (M : var .nat) (V : var (.list .nat)) (VA W : var (.array .nat))
    (pw : var (.array (.array .nat))) (rk rm : var (.list .nat)) (t : var .nat)
    (z : var (.list .nat)) : Prog S rec var (.list outTy) :=
  .bind (.op1 .length z) fun l => .bind (.op1 .arrayOfList z) fun zA =>
  .bind (Coherent.col1Prog W pw rk rm l zA) fun col =>
  .bind (.op1 .arrayOfList col) fun colA =>
  .bind (Coherent.domProg col colA rm t) fun dom =>
  .caseOption dom (smallBranchProg M V col)
    fun u₀ => domBranchProg M VA W pw rk l zA colA rm u₀

/-- **All structures** from the colouring `col` of the `k`-tuples of `V` (`allStructsD`). -/
def allStructsProg (M k : var .nat) (V : var (.list .nat)) (col : var (.array .nat)) :
    Prog S rec var (.list outTy) :=
  .bind (.op1 .length V) fun m => .bind (.op1 .arrayOfList V) fun VA =>
  .bind (wlCProg k m col) fun W =>
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (Coherent.pwTabProg m rk rm) fun pw =>
  .bind (tOfProg m) fun t =>
  .bind (SoJProg.goodListProg W k m t) fun gl =>
  Align.joFlatMap gl fun z => outcomeProg M V VA W pw rk rm t z

/-- **The first structure** (`firstStructD`). -/
def firstStructProg (M k : var .nat) (V : var (.list .nat)) (col : var (.array .nat)) :
    Prog S rec var (.option outTy) :=
  .bind (.op1 .length V) fun m => .bind (.op1 .arrayOfList V) fun VA =>
  .bind (wlCProg k m col) fun W =>
  .bind (.op1 .range k) fun rk => .bind (.op1 .range m) fun rm =>
  .bind (Coherent.pwTabProg m rk rm) fun pw =>
  .bind (tOfProg m) fun t =>
  .bind (SoJProg.goodListProg W k m t) fun gl =>
  .caseList gl (.op0 .none) fun z _ =>
    .bind (outcomeProg M V VA W pw rk rm t z) fun os =>
    .caseList os (.op0 .none) fun o _ => .op1 .some o

/-- **The twins flag** (`twinsD`): no good list. -/
def twinsFlagProg (k m : var .nat) (col : var (.array .nat)) : Prog S rec var .bool :=
  .bind (wlCProg k m col) fun W => .bind (tOfProg m) fun t =>
  .bind (SoJProg.goodListProg W k m t) fun gl =>
  .caseList gl (.op0 (.boolLit true)) fun _ _ => .op0 (.boolLit false)

end Programs

/-! ### Small facts -/

theorem c3p_toArray_getD {α : Type} (l : List α) (i : ℕ) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

theorem c3p_get_toArray (l : List ℕ) (i : ℕ) : get l.toArray i = l.getD i 0 :=
  c3p_toArray_getD l i 0

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.wlCProg (k m : ℕ) (col : Array ℕ) :
    RunsWithin X body (Case3.wlCProg k m col) (wlCD k m col) (wlCost k m + 1) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.wlProg k m col)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.tOfProg (m : ℕ) :
    RunsWithin X body (Case3.tOfProg m) (tOf m) (9 * m + 18) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.halfProg _
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

/-- The cost of `smallLeafProg` on a colouring of `m` points. -/
def smallLeafCost (m : ℕ) : ℕ := 3 * m + 3 + (m + 1) + (m * (6 * m + 6) + 2) + (m + 1) + 12

theorem RunsWithin.smallLeafProg (col : List ℕ) :
    RunsWithin X body (Case3.smallLeafProg col) (smallLeafD col) (smallLeafCost col.length) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := List.range col.length) (f := fun u => Coherent.classProg col.toArray
      (List.range col.length) u) (F := classA col) (c := 6 * col.length + 3)
    fun u _ => RunsWithin.classProg col u
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hmap
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.partProg _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_map,
      smallLeafCost]
    have : col.length * (6 * col.length + 3 + 3) = col.length * (6 * col.length + 6) := by ring
    omega

theorem RunsWithin.skelEntryProg (W : Array ℕ) (pw : Array (Array ℕ)) (k l : ℕ) (zA : Array ℕ)
    (C : List ℕ) (i j : ℕ) :
    RunsWithin X body (Case3.skelEntryProg W pw (List.range k) l zA C.toArray i j)
      (get W (codePad2 pw k l zA (C.getD i 0) (C.getD j 0))) (8 * k + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.pad2Prog pw k l zA _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    simp only [Prim.eval, Ty.default, c3p_toArray_getD]
    rfl
  case hc =>
    simp only [Prim.cost]
    omega

/-- The cost of `skelProg` on a class of `c` points, an `s × s` array. -/
def skelCost (k c s : ℕ) : ℕ := c + 1 + Toolkit.matrixCost s (8 * k + 4)

theorem RunsWithin.skelProg (W : Array ℕ) (k m : ℕ) (z C : List ℕ) (s : ℕ) :
    RunsWithin X body
      (Case3.skelProg W (pwTab k m) (List.range k) z.length z.toArray C s)
      (skelCD k m W z C s) (skelCost k C.length s) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact Toolkit.RunsWithin.matrixProg (F := fun i j =>
      get W (codePad2 (pwTab k m) k z.length z.toArray (C.getD i 0) (C.getD j 0)))
      fun u _ v _ => RunsWithin.skelEntryProg W (pwTab k m) k z.length z.toArray C u v
  case hc =>
    simp only [Prim.cost, Args.head_cons, skelCost]
    omega

theorem outSize_smallLeafD_le (col : List ℕ) : outSize (smallLeafD col) ≤ col.length := by
  unfold smallLeafD partD
  refine sp_outSize_le (fun l hl => ?_) (by simp) (by simp) (by simp) (by simp)
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨u, _, rfl⟩ := hl
  exact length_classA_le col u

theorem RunsWithin.smallBranchProg (M : ℕ) (V col : List ℕ) :
    RunsWithin X body (Case3.smallBranchProg M V col) [extD M V (smallLeafD col)]
      (smallLeafCost col.length + extCost M V.length col.length + 2) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.smallLeafProg col)
    run_step (RunsWithin.extProg M V _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    have := extCost_mono M V.length (outSize_smallLeafD_le col)
    simp only [Prim.cost]
    omega

/-- The cost of `domBranchProg`: a vertex colouring of `m` points, a class of `s` points, a
`soj` tree of size `sz`. -/
def domCost (M k m s sz : ℕ) : ℕ :=
  (6 * m + 3) + (s * 4 + 2) + (s + 1) + skelCost k s s + leavesOfCost s sz +
    ((sz + 1) * (extCost M s (outB s ((s + 3) / 2)) + 3) + 2)

theorem RunsWithin.domBranchProg (M k : ℕ) (V : List ℕ) (W : Array ℕ) (z col : List ℕ)
    (u₀ : ℕ) :
    RunsWithin X body
      (Case3.domBranchProg M V.toArray W (pwTab k V.length) (List.range k) z.length z.toArray
        col.toArray (List.range col.length) u₀)
      ((leavesOfD (classB V (classA col u₀)).length
          (skelCD k V.length W z (classA col u₀) (classB V (classA col u₀)).length)).map
        (extD M (classB V (classA col u₀))))
      (domCost M k col.length (classB V (classA col u₀)).length
        (sojSz (classB V (classA col u₀)).length
          (skelCD k V.length W z (classA col u₀) (classB V (classA col u₀)).length))) := by
  have hmapCB := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := classA col u₀) (f := fun i => Prog.op2 .arrayGet V.toArray i)
    (F := fun i => V.getD i 0) (c := 1)
    fun i _ => (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, Ty.default])
  have hext : ∀ o ∈ leavesOfD (classB V (classA col u₀)).length
      (skelCD k V.length W z (classA col u₀) (classB V (classA col u₀)).length),
      RunsWithin X body (Case2b.extProg M (classB V (classA col u₀)) o)
        (extD M (classB V (classA col u₀)) o)
        (extCost M (classB V (classA col u₀)).length
          (outB (classB V (classA col u₀)).length
            (((classB V (classA col u₀)).length + 3) / 2))) := fun o ho =>
    (RunsWithin.extProg M _ o).mono (extCost_mono _ _ (outSize_leavesOfD _ _ o ho))
  have hmapE := RunsWithin.mapList_le (X := X) (body := body) (a' := outTy) (b' := outTy)
    (f := fun o => Case2b.extProg M (classB V (classA col u₀)) o)
    (F := extD M (classB V (classA col u₀))) hext
  have hlen := length_leavesOfD_le (classB V (classA col u₀)).length
    (skelCD k V.length W z (classA col u₀) (classB V (classA col u₀)).length)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.classProg col u₀)
    run_step hmapCB
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.skelProg W k V.length z (classA col u₀) _)
    run_step (RunsWithin.leavesOfProg _ _)
    exact hmapE
  case hc =>
    have h1 := Nat.mul_le_mul_right (extCost M (classB V (classA col u₀)).length
      (outB (classB V (classA col u₀)).length
        (((classB V (classA col u₀)).length + 3) / 2)) + 3) hlen
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, length_classB,
      domCost] at h1 ⊢
    omega

/-- The cost of the prefix of `outcomeProg`: the vertex colouring and its large class. -/
def outPrefixCost (k m L : ℕ) : ℕ :=
  2 * (L + 1) + (m * (7 * k + 5) + 2) + (m + 1) + (m * (6 * m + 9) + 1) + 1

/-- **The cost of `outcomeProg` at a good list `z`**: polynomial, linear in the size of the `soj`
tree built (`outSzD`). -/
def outCostD (M k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) : ℕ :=
  outPrefixCost k V.length z.length +
    match domA (col1D k V.length W z) (tOf V.length) with
    | none => smallLeafCost V.length + extCost M V.length V.length + 2
    | some u₀ =>
      domCost M k V.length (classB V (classA (col1D k V.length W z) u₀)).length
        (sojSz (classB V (classA (col1D k V.length W z) u₀)).length
          (skelCD k V.length W z (classA (col1D k V.length W z) u₀)
            (classB V (classA (col1D k V.length W z) u₀)).length))

/-- **The structures at a good list, as a program.** -/
theorem RunsWithin.outcomeProg (M k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) :
    RunsWithin X body
      (Case3.outcomeProg M V V.toArray W (pwTab k V.length) (List.range k)
        (List.range V.length) (tOf V.length) z)
      (outcomeD M k V W z) (outCostD M k V W z) := by
  set col := col1D k V.length W z with hcol
  have hlen : col.length = V.length := length_col1D W z
  have hdom := RunsWithin.domProg (X := X) (body := body) col (tOf V.length)
  rw [hlen] at hdom
  have hc1 := RunsWithin.col1Prog (X := X) (body := body) W (pwTab k V.length) k V.length
    z.length z.toArray
  rcases hd : domA col (tOf V.length) with _ | u₀
  · rw [hd] at hdom
    have hsb := RunsWithin.smallBranchProg (X := X) (body := body) M V col
    rw [hlen] at hsb
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hc1
      run_step (RunsWithin.prim _ _)
      run_step hdom
      run_with RunsWithin.caseOpt_eq_none (show (none : Option ℕ) = none from rfl) _
      refine hsb.of_eq ?_
      unfold outcomeD
      rw [← hcol, hd]
    case hc =>
      unfold outCostD
      rw [← hcol, hd]
      simp only [Prim.cost, Args.head_cons, outPrefixCost, length_col1A]
      omega
  · rw [hd] at hdom
    have hdb := RunsWithin.domBranchProg (X := X) (body := body) M k V W z col u₀
    rw [hlen] at hdb
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hc1
      run_step (RunsWithin.prim _ _)
      run_step hdom
      run_with RunsWithin.caseOpt_eq_some (show (some u₀ : Option ℕ) = some u₀ from rfl) _
      refine hdb.of_eq ?_
      unfold outcomeD
      rw [← hcol, hd]
    case hc =>
      unfold outCostD
      rw [← hcol, hd]
      simp only [Prim.cost, Args.head_cons, outPrefixCost, length_col1A]
      omega

theorem c3p_outB_mono {m m' q q' : ℕ} (hm : m ≤ m') (hq : q ≤ q') : outB m q ≤ outB m' q' := by
  unfold outB
  have := Nat.mul_le_mul hm hm
  omega

/-- **The size of every structure** of a good list is at most `M + outB |V| (|V| + 2)`. -/
theorem outSize_outcomeD_le (M k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) :
    ∀ o ∈ outcomeD M k V W z, outSize o ≤ M + outB V.length (V.length + 2) := by
  intro o ho
  unfold outcomeD at ho
  split at ho
  · rw [List.mem_singleton] at ho
    subst ho
    refine (outSize_extD_le _ _ _).trans (Nat.add_le_add_left ?_ M)
    refine (outSize_smallLeafD_le _).trans ?_
    rw [length_col1D]
    unfold outB
    omega
  · rename_i u₀ _
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    refine (outSize_extD_le _ _ _).trans (Nat.add_le_add_left ?_ M)
    refine (outSize_leavesOfD _ _ o' ho').trans (c3p_outB_mono ?_ ?_)
    · rw [length_classB]
      exact (length_classA_le _ _).trans (le_of_eq (length_col1D _ _))
    · have : (classB V (classA (col1D k V.length W z) u₀)).length ≤ V.length := by
        rw [length_classB]
        exact (length_classA_le _ _).trans (le_of_eq (length_col1D _ _))
      omega

/-- The cost of the common prefix: the refinement, the tables, the threshold and the good
lists, for `m` points. -/
def pipePrefixCost (k m : ℕ) : ℕ :=
  (m + 1) + (m + 1) + (wlCost k m + 1) + (k + 1) + (m + 1) + pwTabCost k m + (9 * m + 18) +
    goodListCost k m

/-- **The cost of all structures**: the prefix, then at most `k (m^k + 1)` good lists, each of
cost at most `Cz` with at most `Z + 1` structures. -/
def structsCost (k m Cz Z : ℕ) : ℕ :=
  pipePrefixCost k m + (k * (m ^ k + 1) * (Cz + (Z + 1) + 6) + 4)

theorem length_goodListsD_le (k m : ℕ) (W : Array ℕ) :
    (goodListsD k m W).length ≤ k * (m ^ k + 1) :=
  (List.length_filter_le _ _).trans (length_cands_le k m)

/-- **All structures, as a program**, for uniform bounds `Cz` on the cost and `Z` on the `soj`
size at each good list. -/
theorem RunsWithin.allStructsProg (M k : ℕ) (V : List ℕ) (col : Array ℕ) {Cz Z : ℕ}
    (hC : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outCostD M k V (wlCD k V.length col) z ≤ Cz)
    (hZ : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outSzD k V (wlCD k V.length col) z ≤ Z) :
    RunsWithin X body (Case3.allStructsProg M k V col) (allStructsD M k V col)
      (structsCost k V.length Cz Z) := by
  have hfm := Align.RunsWithin.joFlatMap (X := X) (body := body) (a' := .list .nat) (b' := outTy)
    (xs := goodListsD k V.length (wlCD k V.length col))
    (f := fun z => Case3.outcomeProg M V V.toArray (wlCD k V.length col) (pwTab k V.length)
      (List.range k) (List.range V.length) (tOf V.length) z)
    (F := outcomeD M k V (wlCD k V.length col)) (c := Cz) (L := Z + 1)
    (fun z hz => (RunsWithin.outcomeProg M k V _ z).mono (hC z hz))
    (fun z hz => (length_outcomeD_le M V _ z).trans (Nat.add_le_add_right (hZ z hz) 1))
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
    have := Nat.mul_le_mul_right (Cz + (Z + 1) + 6) hgl
    simp only [Prim.cost, Prim.eval, Args.head_cons, structsCost, pipePrefixCost]
    omega

/-- **The first structure, as a program.** -/
theorem RunsWithin.firstStructProg (M k : ℕ) (V : List ℕ) (col : Array ℕ) {Cz : ℕ}
    (hC : ∀ z ∈ goodListsD k V.length (wlCD k V.length col),
      outCostD M k V (wlCD k V.length col) z ≤ Cz) :
    RunsWithin X body (Case3.firstStructProg M k V col) (firstStructD M k V col)
      (pipePrefixCost k V.length + Cz + 4) := by
  unfold firstStructD
  rcases hgl : goodListsD k V.length (wlCD k V.length col) with _ | ⟨z, zs⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.wlCProg k _ col)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.pwTabProg k _)
      run_step (RunsWithin.tOfProg _)
      run_step (SoJProg.RunsWithin.goodListProg _ k _ _)
      run_with Coherent.RunsWithin.caseList_eq_nil hgl _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, pipePrefixCost]
      omega
  · have hz := (RunsWithin.outcomeProg (X := X) (body := body) M k V (wlCD k V.length col)
      z).mono (hC z (by rw [hgl]; exact List.mem_cons_self))
    rcases hos : outcomeD M k V (wlCD k V.length col) z with _ | ⟨o, os⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.wlCProg k _ col)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.pwTabProg k _)
        run_step (RunsWithin.tOfProg _)
        run_step (SoJProg.RunsWithin.goodListProg _ k _ _)
        run_with Coherent.RunsWithin.caseList_eq_cons hgl _
        run_step hz
        run_with Coherent.RunsWithin.caseList_eq_nil hos _
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, hos])
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head_cons, pipePrefixCost]
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.wlCProg k _ col)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.pwTabProg k _)
        run_step (RunsWithin.tOfProg _)
        run_step (SoJProg.RunsWithin.goodListProg _ k _ _)
        run_with Coherent.RunsWithin.caseList_eq_cons hgl _
        run_step hz
        run_with Coherent.RunsWithin.caseList_eq_cons hos _
        exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval, hos])
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head_cons, pipePrefixCost]
        omega

/-- **The twins flag, as a program.** -/
theorem RunsWithin.twinsFlagProg (k m : ℕ) (col : Array ℕ) :
    RunsWithin X body (Case3.twinsFlagProg k m col) (twinsD k m col)
      (wlCost k m + 1 + (9 * m + 18) + goodListCost k m + 2) := by
  unfold twinsD
  rcases hgl : goodListsD k m (wlCD k m col) with _ | ⟨z, zs⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.wlCProg k m col)
      run_step (RunsWithin.tOfProg m)
      run_step (SoJProg.RunsWithin.goodListProg _ k m _)
      run_with Coherent.RunsWithin.caseList_eq_nil hgl _
      exact RunsWithin.prim _ _
    case hc => simp only [Prim.cost]; omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.wlCProg k m col)
      run_step (RunsWithin.tOfProg m)
      run_step (SoJProg.RunsWithin.goodListProg _ k m _)
      run_with Coherent.RunsWithin.caseList_eq_cons hgl _
      exact RunsWithin.prim _ _
    case hc => simp only [Prim.cost]; omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_wlCProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} {col₁ : var₁ (.array .nat)}
    {col₂ : var₂ (.array .nat)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (wlCProg k₁ m₁ col₁) (wlCProg k₂ m₂ col₂) := by
  unfold wlCProg
  exact .bind (wf_wlProg hk hm hcol) fun _ _ => .prim _ (.cons (by simp) .nil)

theorem wf_tOfProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tOfProg m₁) (tOfProg m₂) := by
  unfold tOfProg
  exact .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) (.cons (by simp) .nil))) fun _ _ => wf_halfProg (by simp)

theorem wf_smallLeafProg {col₁ : var₁ (.list .nat)} {col₂ : var₂ (.list .nat)}
    (hcol : ⟨.list .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (smallLeafProg col₁) (smallLeafProg col₂) := by
  unfold smallLeafProg
  exact .bind (.prim _ (.cons hcol .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hcol]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ hΓ _ _ hu =>
      wf_classProg (hΓ (by simp)) (hΓ (by simp)) hu) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => wf_partProg (by simp) (by simp)

theorem wf_skelEntryProg {W₁ zA₁ CA₁ : var₁ (.array .nat)} {W₂ zA₂ CA₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ : var₁ (.list .nat)} {rk₂ : var₂ (.list .nat)} {l₁ i₁ j₁ : var₁ .nat}
    {l₂ i₂ j₂ : var₂ .nat} (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hzA : ⟨.array .nat, zA₁, zA₂⟩ ∈ Γ)
    (hCA : ⟨.array .nat, CA₁, CA₂⟩ ∈ Γ) (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (skelEntryProg W₁ pw₁ rk₁ l₁ zA₁ CA₁ i₁ j₁)
      (skelEntryProg W₂ pw₂ rk₂ l₂ zA₂ CA₂ i₂ j₂) := by
  unfold skelEntryProg
  exact .bind (.prim _ (.cons hCA (.cons hi .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hCA]) (.cons (by simp [hj]) .nil))) fun _ _ =>
    .bind (wf_pad2Prog (by simp [hpw]) (by simp [hrk]) (by simp [hl]) (by simp [hzA]) (by simp)
      (by simp)) fun _ _ =>
    .prim _ (.cons (by simp [hW]) (.cons (by simp) .nil))

theorem c3p_wf_rowsProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (Toolkit.rowsProg m₁) (Toolkit.rowsProg m₂) := by
  unfold Toolkit.rowsProg
  prog_wf

/-- A matrix program is well formed when its entry program is, in every larger context. -/
theorem c3p_wf_matrixProg {m₁ : var₁ .nat} {m₂ : var₂ .nat}
    {f₁ : var₁ .nat → var₁ .nat → var₁ .nat → Prog S rec var₁ .nat}
    {f₂ : var₂ .nat → var₂ .nat → var₂ .nat → Prog S rec var₂ .nat}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hf : ∀ Γ' : WfCtx var₁ var₂, Γ ⊆ Γ' → ∀ u₁ u₂ o₁ o₂ v₁ v₂, ⟨.nat, u₁, u₂⟩ ∈ Γ' →
      ⟨.nat, o₁, o₂⟩ ∈ Γ' → ⟨.nat, v₁, v₂⟩ ∈ Γ' → Prog.Wf r Γ' (f₁ u₁ o₁ v₁) (f₂ u₂ o₂ v₂)) :
    Prog.Wf r Γ (Toolkit.matrixProg m₁ f₁) (Toolkit.matrixProg m₂ f₂) := by
  unfold Toolkit.matrixProg
  refine .bind (c3p_wf_rowsProg hm) fun prs₁ prs₂ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun is₁ is₂ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ p₁ p₂ hp => ?_) fun _ _ => ?_
  · refine .bind (.prim _ (.cons hp .nil)) fun u₁ u₂ =>
      .bind (.prim _ (.cons (by simp [hp]) .nil)) fun o₁ o₂ =>
      wf_mapList (by simp [hΓ (by simp : (⟨.list .nat, is₁, is₂⟩ : Σ t : Ty, var₁ t × var₂ t) ∈
        ⟨.list .nat, is₁, is₂⟩ :: ⟨.list (.prod .nat .nat), prs₁, prs₂⟩ :: Γ)])
        fun Γ'' hΓ' v₁ v₂ hv => hf Γ'' (fun x hx => hΓ' (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (hΓ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))))))
          u₁ u₂ o₁ o₂ v₁ v₂ (hΓ' (by simp)) (hΓ' (by simp)) hv
  · prog_wf

theorem wf_skelProg {W₁ zA₁ : var₁ (.array .nat)} {W₂ zA₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ C₁ : var₁ (.list .nat)} {rk₂ C₂ : var₂ (.list .nat)} {l₁ s₁ : var₁ .nat}
    {l₂ s₂ : var₂ .nat} (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hzA : ⟨.array .nat, zA₁, zA₂⟩ ∈ Γ)
    (hC : ⟨.list .nat, C₁, C₂⟩ ∈ Γ) (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (skelProg W₁ pw₁ rk₁ l₁ zA₁ C₁ s₁)
      (skelProg W₂ pw₂ rk₂ l₂ zA₂ C₂ s₂) := by
  unfold skelProg
  refine .bind (.prim _ (.cons hC .nil)) fun _ _ => c3p_wf_matrixProg (by simp [hs])
    fun Γ' hΓ _ _ _ _ _ _ hu _ hv => wf_skelEntryProg (hΓ (by simp [hW])) (hΓ (by simp [hpw]))
      (hΓ (by simp [hrk])) (hΓ (by simp [hl])) (hΓ (by simp [hzA])) (hΓ (by simp)) hu hv

theorem wf_smallBranchProg {M₁ : var₁ .nat} {M₂ : var₂ .nat} {V₁ col₁ : var₁ (.list .nat)}
    {V₂ col₂ : var₂ (.list .nat)} (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hcol : ⟨.list .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (smallBranchProg M₁ V₁ col₁)
      (smallBranchProg M₂ V₂ col₂) := by
  unfold smallBranchProg
  exact .bind (wf_smallLeafProg hcol) fun _ _ =>
    .bind (wf_extProg (by simp [hM]) (by simp [hV]) (by simp)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_domBranchProg {M₁ l₁ u₁ : var₁ .nat} {M₂ l₂ u₂ : var₂ .nat}
    {VA₁ W₁ zA₁ colA₁ : var₁ (.array .nat)} {VA₂ W₂ zA₂ colA₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rk₁ rm₁ : var₁ (.list .nat)} {rk₂ rm₂ : var₂ (.list .nat)} (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ)
    (hVA : ⟨.array .nat, VA₁, VA₂⟩ ∈ Γ) (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hl : ⟨.nat, l₁, l₂⟩ ∈ Γ) (hzA : ⟨.array .nat, zA₁, zA₂⟩ ∈ Γ)
    (hcolA : ⟨.array .nat, colA₁, colA₂⟩ ∈ Γ) (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (domBranchProg M₁ VA₁ W₁ pw₁ rk₁ l₁ zA₁ colA₁ rm₁ u₁)
      (domBranchProg M₂ VA₂ W₂ pw₂ rk₂ l₂ zA₂ colA₂ rm₂ u₂) := by
  unfold domBranchProg
  exact .bind (wf_classProg hcolA hrm hu) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ hΓ _ _ hi =>
      .prim _ (.cons (hΓ (by simp [hVA])) (.cons hi .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_skelProg (by simp [hW]) (by simp [hpw]) (by simp [hrk]) (by simp [hl])
      (by simp [hzA]) (by simp) (by simp)) fun _ _ =>
    .bind (wf_leavesOfProg (by simp) (by simp)) fun _ _ =>
    wf_mapList (by simp) fun _ hΓ _ _ ho => wf_extProg (hΓ (by simp [hM])) (hΓ (by simp)) ho

theorem wf_outcomeProg {M₁ t₁ : var₁ .nat} {M₂ t₂ : var₂ .nat}
    {V₁ rk₁ rm₁ z₁ : var₁ (.list .nat)} {V₂ rk₂ rm₂ z₂ : var₂ (.list .nat)}
    {VA₁ W₁ : var₁ (.array .nat)} {VA₂ W₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hVA : ⟨.array .nat, VA₁, VA₂⟩ ∈ Γ) (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hrm : ⟨.list .nat, rm₁, rm₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hz : ⟨.list .nat, z₁, z₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (outcomeProg M₁ V₁ VA₁ W₁ pw₁ rk₁ rm₁ t₁ z₁)
      (outcomeProg M₂ V₂ VA₂ W₂ pw₂ rk₂ rm₂ t₂ z₂) := by
  unfold outcomeProg
  exact .bind (.prim _ (.cons hz .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hz]) .nil)) fun _ _ =>
    .bind (wf_col1Prog (by simp [hW]) (by simp [hpw]) (by simp [hrk]) (by simp [hrm]) (by simp)
      (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_domProg (by simp) (by simp) (by simp [hrm]) (by simp [ht])) fun _ _ =>
    .caseOption (by simp) (wf_smallBranchProg (by simp [hM]) (by simp [hV]) (by simp))
      fun _ _ => wf_domBranchProg (by simp [hM]) (by simp [hVA]) (by simp [hW]) (by simp [hpw])
        (by simp [hrk]) (by simp) (by simp) (by simp) (by simp [hrm]) (by simp)

theorem wf_allStructsProg {M₁ k₁ : var₁ .nat} {M₂ k₂ : var₂ .nat} {V₁ : var₁ (.list .nat)}
    {V₂ : var₂ (.list .nat)} {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)}
    (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (allStructsProg M₁ k₁ V₁ col₁)
      (allStructsProg M₂ k₂ V₂ col₂) := by
  unfold allStructsProg
  exact .bind (.prim _ (.cons hV .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hV]) .nil)) fun _ _ =>
    .bind (wf_wlCProg (by simp [hk]) (by simp) (by simp [hcol])) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hk]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_pwTabProg (by simp) (by simp) (by simp)) fun _ _ =>
    .bind (wf_tOfProg (by simp)) fun _ _ =>
    .bind (wf_goodListProg (by simp) (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    Align.wf_joFlatMap (by simp) fun _ hΓ _ _ hz =>
      wf_outcomeProg (hΓ (by simp [hM])) (hΓ (by simp [hV])) (hΓ (by simp)) (hΓ (by simp))
        (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) hz

theorem wf_firstStructProg {M₁ k₁ : var₁ .nat} {M₂ k₂ : var₂ .nat} {V₁ : var₁ (.list .nat)}
    {V₂ : var₂ (.list .nat)} {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)}
    (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (firstStructProg M₁ k₁ V₁ col₁)
      (firstStructProg M₂ k₂ V₂ col₂) := by
  unfold firstStructProg
  exact .bind (.prim _ (.cons hV .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hV]) .nil)) fun _ _ =>
    .bind (wf_wlCProg (by simp [hk]) (by simp) (by simp [hcol])) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hk]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_pwTabProg (by simp) (by simp) (by simp)) fun _ _ =>
    .bind (wf_tOfProg (by simp)) fun _ _ =>
    .bind (wf_goodListProg (by simp) (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    .caseList (by simp) (.prim _ .nil) fun _ _ _ _ =>
      .bind (wf_outcomeProg (by simp [hM]) (by simp [hV]) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp)) fun _ _ =>
      .caseList (by simp) (.prim _ .nil) fun _ _ _ _ => .prim _ (.cons (by simp) .nil)

theorem wf_twinsFlagProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} {col₁ : var₁ (.array .nat)}
    {col₂ : var₂ (.array .nat)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinsFlagProg k₁ m₁ col₁) (twinsFlagProg k₂ m₂ col₂) := by
  unfold twinsFlagProg
  exact .bind (wf_wlCProg hk hm hcol) fun _ _ => .bind (wf_tOfProg (by simp [hm])) fun _ _ =>
    .bind (wf_goodListProg (by simp) (by simp [hk]) (by simp [hm]) (by simp)) fun _ _ =>
    .caseList (by simp) (.prim _ .nil) fun _ _ _ _ => .prim _ .nil

end Wf

end GraphIso.Case3
