module

public import GraphIso.SoJTree.LeafData
public import GraphIso.SoJProg.DLTest

/-!
# Leaves of Split-or-Johnson as costed programs

Stage 14d, item 2 (`PLAN-14.md` §8): programs computing, on runtime values, the leaf data
functions of `GraphIso/SoJTree/LeafData.lean`. They make no backend calls.

* Constructors: `noneProg`, `partProg`, `johnProg` (`noneD`, `partD`, `johnD`).
* `addPieceProg` and `extendOutProg`: `addPieceD` and `extendD` (the colour function of the
  extension is read from an array).
* `setEqProg`, `famSubProg`, `famEqProg`, `outEqProg`: equality of point sets, of indexed cell
  families and of decoded leaves.
* `mapPtsProg`, `actOutProg`: a permutation acting on point lists and on leaf data.

**Size.** `outSize o` is the length of the longest list inside the leaf data (blocks, points,
cells, cell indices). The array sizes do not enter: the programs read the arrays only at
indices below `m`. The action does not increase the size (`outSize_actOutD_le`), so an orbit
computation can bound every iterate by the size of its start. The costs of `outEqProg` and
`actOutProg` are polynomials in `m` and a bound `s` on the sizes (`outEqCost`, `actOutCost`),
at most `200 (m + 1)² (s + 1)³` and `150 (m + 1) (s + 1)²` (`outEqCost_le`, `actOutCost_le`).

Every program has a well-formedness lemma `wf_…`.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.Cost GraphIso.Programs
  GraphIso.Sims

/-! ### Size -/

section Size

/-- The length of the longest list of a list of lists. -/
def ldMaxLen (ls : List (List ℕ)) : ℕ := (ls.map List.length).foldr max 0

/-- **The size of leaf data**: the length of the longest list inside it. -/
def outSize (o : OutD) : ℕ :=
  max (ldMaxLen o.2.1.2.toList) (max o.2.2.1.length (max o.2.2.2.1.length
    (max (ldMaxLen o.2.2.2.1) (ldMaxLen o.2.2.2.2.2.toList))))

theorem ld_le_maxLen {ls : List (List ℕ)} {l : List ℕ} (h : l ∈ ls) : l.length ≤ ldMaxLen ls := by
  induction ls with
  | nil => simp at h
  | cons l' ls ih =>
    simp only [ldMaxLen, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem ld_maxLen_le {ls : List (List ℕ)} {s : ℕ} (h : ∀ l ∈ ls, l.length ≤ s) :
    ldMaxLen ls ≤ s := by
  induction ls with
  | nil => simp [ldMaxLen]
  | cons l' ls ih =>
    simp only [ldMaxLen, List.map_cons, List.foldr_cons] at ih ⊢
    exact max_le (h l' List.mem_cons_self) (ih fun l hl => h l (List.mem_cons_of_mem _ hl))

theorem ld_length_getD_le (ls : List (List ℕ)) (x : ℕ) :
    (ls.getD x []).length ≤ ldMaxLen ls := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : ls[x]? with _ | l
  · simp
  · exact ld_le_maxLen (List.mem_of_getElem? h)

theorem ld_length_arr_getD_le (a : Array (List ℕ)) (x : ℕ) :
    (a.getD x []).length ≤ ldMaxLen a.toList := by
  have : a.getD x [] = a.toList.getD x [] := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [this]
  exact ld_length_getD_le _ x

theorem outSize_blk (o : OutD) (x : ℕ) : (o.2.1.2.getD x []).length ≤ outSize o :=
  (ld_length_arr_getD_le _ x).trans (le_max_left _ _)

theorem outSize_V0 (o : OutD) : o.2.2.1.length ≤ outSize o :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem outSize_cs (o : OutD) : o.2.2.2.1.length ≤ outSize o :=
  ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem outSize_cell (o : OutD) {c : List ℕ} (hc : c ∈ o.2.2.2.1) : c.length ≤ outSize o :=
  (ld_le_maxLen hc).trans <| (le_max_left _ _).trans <| (le_max_right _ _).trans <|
    (le_max_right _ _).trans (le_max_right _ _)

theorem outSize_fA (o : OutD) (x : ℕ) : (o.2.2.2.2.2.getD x []).length ≤ outSize o :=
  (ld_length_arr_getD_le _ x).trans <| (le_max_right _ _).trans <| (le_max_right _ _).trans <|
    (le_max_right _ _).trans (le_max_right _ _)

theorem length_mapPtsD_le (m : ℕ) (σ : PermData) (l : List ℕ) :
    (mapPtsD m σ l).length ≤ l.length := by
  simpa [mapPtsD] using List.length_filter_le _ _

theorem ld_maxLen_map_range_le (m : ℕ) (f : ℕ → List ℕ) {s : ℕ}
    (h : ∀ x < m, (f x).length ≤ s) :
    ldMaxLen ((List.range m).map f).toArray.toList ≤ s := by
  refine ld_maxLen_le fun l hl => ?_
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  exact h x hx

/-- **The action does not increase the size.** -/
theorem outSize_actOutD_le (m : ℕ) (σ : PermData) (o : OutD) :
    outSize (actOutD m σ o) ≤ outSize o := by
  unfold actOutD
  split_ifs with h₁ h₂
  · simp only [outSize, partD, List.length_nil, ldMaxLen, List.map_nil, List.foldr_nil,
      Array.toList_empty, max_self, Nat.max_zero]
    exact ld_maxLen_map_range_le m _ fun x _ =>
      (length_mapPtsD_le m σ _).trans (outSize_blk o _)
  · simp only [outSize, johnD, List.length_map]
    refine max_le (by simp [ldMaxLen]) (max_le ((length_mapPtsD_le m σ _).trans (outSize_V0 o))
      (max_le (outSize_cs o) (max_le ?_ ?_)))
    · refine ld_maxLen_le fun l hl => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      exact (length_mapPtsD_le m σ c).trans (outSize_cell o hc)
    · exact ld_maxLen_map_range_le m _ fun x _ => outSize_fA o _
  · exact le_rfl

end Size

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The empty array of numbers. -/
def emptyNatArrProg : Prog S rec var (.array .nat) :=
  .bind (.op0 .nil) fun l => .op1 .arrayOfList l

/-- The empty array of lists. -/
def emptyLstArrProg : Prog S rec var (.array (.list .nat)) :=
  .bind (.op0 .nil) fun l => .op1 .arrayOfList l

/-- Assemble leaf data from its fields. -/
def mkOutProg (tag : var .nat) (col : var (.array .nat)) (blk : var (.array (.list .nat)))
    (V0 : var (.list .nat)) (cs : var (.list (.list .nat))) (s : var .nat)
    (fA : var (.array (.list .nat))) : Prog S rec var outTy :=
  .bind (.op2 .pair s fA) fun sf => .bind (.op2 .pair cs sf) fun csf =>
  .bind (.op2 .pair V0 csf) fun r₂ => .bind (.op2 .pair col blk) fun r₁ =>
  .bind (.op2 .pair r₁ r₂) fun r => .op2 .pair tag r

/-- The leaf `none` (`noneD`). -/
def noneProg : Prog S rec var outTy :=
  .bind (.op0 (.natLit 0)) fun z => .bind emptyNatArrProg fun ca =>
  .bind emptyLstArrProg fun ba => .bind (.op0 .nil) fun V0 => .bind (.op0 .nil) fun cs =>
  .bind emptyLstArrProg fun fA => mkOutProg z ca ba V0 cs z fA

/-- A colored partition (`partD`). -/
def partProg (col : var (.array .nat)) (blk : var (.array (.list .nat))) :
    Prog S rec var outTy :=
  .bind (.op0 (.natLit 1)) fun one => .bind (.op0 (.natLit 0)) fun z =>
  .bind (.op0 .nil) fun V0 => .bind (.op0 .nil) fun cs =>
  .bind emptyLstArrProg fun fA => mkOutProg one col blk V0 cs z fA

/-- A Johnson embedding (`johnD`). -/
def johnProg (V0 : var (.list .nat)) (cs : var (.list (.list .nat))) (s : var .nat)
    (fA : var (.array (.list .nat))) : Prog S rec var outTy :=
  .bind (.op0 (.natLit 2)) fun two => .bind emptyNatArrProg fun ca =>
  .bind emptyLstArrProg fun ba => mkOutProg two ca ba V0 cs s fA

/-- The colour of `x` after adding the piece `D`: `0` on `D`, else `col[x] + 1`. -/
def apColProg (D : var (.list .nat)) (col : var (.array .nat)) (x : var .nat) :
    Prog S rec var .nat :=
  .bind (memProg x D) fun b =>
  .ite b (.op0 (.natLit 0))
    (.bind (.op2 .arrayGet col x) fun v => .bind (.op0 (.natLit 1)) fun one => .op2 .add v one)

/-- The block of `x` after adding the piece `D`: `D` on `D`, else `blk[x]`. -/
def apBlkProg (D : var (.list .nat)) (blk : var (.array (.list .nat))) (x : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (memProg x D) fun b => .ite b (.ret D) (.op2 .arrayGet blk x)

/-- **`addPieceD`.** -/
def addPieceProg (m : var .nat) (D : var (.list .nat)) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .fst o) fun tag => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1
    (.bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun r₁ =>
      .bind (.op1 .fst r₁) fun col => .bind (.op1 .snd r₁) fun blk =>
      .bind (.op1 .range m) fun xs =>
      .bind (mapList xs fun x => apColProg D col x) fun cl =>
      .bind (.op1 .arrayOfList cl) fun col' =>
      .bind (mapList xs fun x => apBlkProg D blk x) fun bl =>
      .bind (.op1 .arrayOfList bl) fun blk' => partProg col' blk')
    (.ret o)

/-- The colour of `y` after the extension: `2 col[y]` on `V₁`, else `2 row[y] + 1`. -/
def exColProg (V₁ : var (.list .nat)) (col row : var (.array .nat)) (y : var .nat) :
    Prog S rec var .nat :=
  .bind (memProg y V₁) fun b =>
  .ite b (.bind (.op2 .arrayGet col y) fun v => .op2 .add v v)
    (.bind (.op2 .arrayGet row y) fun w => .bind (.op2 .add w w) fun w₂ =>
      .bind (.op0 (.natLit 1)) fun one => .op2 .add w₂ one)

/-- Whether `z` lies outside `V₁` with the colour `ry`. -/
def exTestProg (V₁ : var (.list .nat)) (row : var (.array .nat)) (ry z : var .nat) :
    Prog S rec var .bool :=
  .bind (memProg z V₁) fun iz => .bind (.op1 .not iz) fun nz =>
  .bind (.op2 .arrayGet row z) fun rz => .bind (.op2 .natEq rz ry) fun e => .op2 .and nz e

/-- The block of `y` after the extension: `blk[y]` on `V₁`, else its colour class outside
`V₁` among `xs`. -/
def exBlkProg (V₁ : var (.list .nat)) (blk : var (.array (.list .nat))) (row : var (.array .nat))
    (xs : var (.list .nat)) (y : var .nat) : Prog S rec var (.list .nat) :=
  .bind (memProg y V₁) fun b =>
  .ite b (.op2 .arrayGet blk y)
    (.bind (.op2 .arrayGet row y) fun ry => Toolkit.filterList xs fun z => exTestProg V₁ row ry z)

/-- **`extendD`**, the colours outside `V₁` read from the array `row`. -/
def extendOutProg (m : var .nat) (V₁ : var (.list .nat)) (row : var (.array .nat))
    (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .fst o) fun tag => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1
    (.bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun r₁ =>
      .bind (.op1 .fst r₁) fun col => .bind (.op1 .snd r₁) fun blk =>
      .bind (.op1 .range m) fun xs =>
      .bind (mapList xs fun y => exColProg V₁ col row y) fun cl =>
      .bind (.op1 .arrayOfList cl) fun col' =>
      .bind (mapList xs fun y => exBlkProg V₁ blk row xs y) fun bl =>
      .bind (.op1 .arrayOfList bl) fun blk' => partProg col' blk')
    (.ret o)

/-- Whether `i` lies in both lists or in neither. -/
def setEqElProg (l l' : var (.list .nat)) (i : var .nat) : Prog S rec var .bool :=
  .bind (memProg i l) fun a => .bind (memProg i l') fun b => csBeqProg a b

/-- **`setEqD`.** -/
def setEqProg (m : var .nat) (l l' : var (.list .nat)) : Prog S rec var .bool :=
  .bind (.op1 .range m) fun is => allList is fun i => setEqElProg l l' i

/-- Whether the cell `c` equals the cell `j'` of `ca'`. -/
def famSubInProg (m : var .nat) (c : var (.list .nat)) (ca' : var (.array (.list .nat)))
    (j' : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet ca' j') fun c' => setEqProg m c c'

/-- Whether the cell `j` of `ca` equals some cell of `ca'` indexed in `js'`. -/
def famSubElProg (m : var .nat) (ca ca' : var (.array (.list .nat))) (js' : var (.list .nat))
    (j : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet ca j) fun c => anyList js' fun j' => famSubInProg m c ca' j'

/-- **`famSubD`**, through arrays of the cells. -/
def famSubProg (m : var .nat) (cs : var (.list (.list .nat))) (js : var (.list .nat))
    (cs' : var (.list (.list .nat))) (js' : var (.list .nat)) : Prog S rec var .bool :=
  .bind (.op1 .arrayOfList cs) fun ca => .bind (.op1 .arrayOfList cs') fun ca' =>
  allList js fun j => famSubElProg m ca ca' js' j

/-- **`famEqD`.** -/
def famEqProg (m : var .nat) (cs : var (.list (.list .nat))) (js : var (.list .nat))
    (cs' : var (.list (.list .nat))) (js' : var (.list .nat)) : Prog S rec var .bool :=
  .bind (famSubProg m cs js cs' js') fun a => .bind (famSubProg m cs' js' cs js) fun b =>
  .op2 .and a b

/-- The comparison of two colored partitions at the point `x`. -/
def eqPartElProg (m : var .nat) (col col' : var (.array .nat))
    (blk blk' : var (.array (.list .nat))) (x : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet col x) fun a => .bind (.op2 .arrayGet col' x) fun a' =>
  .bind (.op2 .natEq a a') fun e => .bind (.op2 .arrayGet blk x) fun b =>
  .bind (.op2 .arrayGet blk' x) fun b' => .bind (setEqProg m b b') fun f => .op2 .and e f

/-- The comparison of the cell families of two Johnson embeddings at the point `x`. -/
def eqJohnElProg (m : var .nat) (cs cs' : var (.list (.list .nat)))
    (fA fA' : var (.array (.list .nat))) (x : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet fA x) fun js => .bind (.op2 .arrayGet fA' x) fun js' =>
  famEqProg m cs js cs' js'

/-- The comparison when `o` is a colored partition; `t1'` says whether `o'` is one. -/
def eqPartProg (m : var .nat) (o o' : var outTy) (t1' : var .bool) : Prog S rec var .bool :=
  .bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun r₁ =>
  .bind (.op1 .fst r₁) fun col => .bind (.op1 .snd r₁) fun blk =>
  .bind (.op1 .snd o') fun q => .bind (.op1 .fst q) fun q₁ =>
  .bind (.op1 .fst q₁) fun col' => .bind (.op1 .snd q₁) fun blk' =>
  .bind (.op1 .range m) fun xs =>
  .bind (allList xs fun x => eqPartElProg m col col' blk blk' x) fun all => .op2 .and t1' all

/-- The comparison when `o` is a Johnson embedding; `t2'` says whether `o'` is one. -/
def eqJohnProg (m : var .nat) (o o' : var outTy) (t2' : var .bool) : Prog S rec var .bool :=
  .bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun r₂ =>
  .bind (.op1 .fst r₂) fun V0 => .bind (.op1 .snd r₂) fun r₃ =>
  .bind (.op1 .fst r₃) fun cs => .bind (.op1 .snd r₃) fun r₄ =>
  .bind (.op1 .fst r₄) fun s => .bind (.op1 .snd r₄) fun fA =>
  .bind (.op1 .snd o') fun q => .bind (.op1 .snd q) fun q₂ =>
  .bind (.op1 .fst q₂) fun V0' => .bind (.op1 .snd q₂) fun q₃ =>
  .bind (.op1 .fst q₃) fun cs' => .bind (.op1 .snd q₃) fun q₄ =>
  .bind (.op1 .fst q₄) fun s' => .bind (.op1 .snd q₄) fun fA' =>
  .bind (setEqProg m V0 V0') fun e₁ => .bind (.op2 .and t2' e₁) fun a₁ =>
  .bind (.op1 .length cs) fun lc => .bind (.op1 .range lc) fun rc =>
  .bind (.op1 .length cs') fun lc' => .bind (.op1 .range lc') fun rc' =>
  .bind (famEqProg m cs rc cs' rc') fun e₂ => .bind (.op2 .and a₁ e₂) fun a₂ =>
  .bind (.op2 .natEq s s') fun e₃ => .bind (.op2 .and a₂ e₃) fun a₃ =>
  .bind (.op1 .range m) fun xs =>
  .bind (allList xs fun x => eqJohnElProg m cs cs' fA fA' x) fun e₄ => .op2 .and a₃ e₄

/-- **`outEqD`.** -/
def outEqProg (m : var .nat) (o o' : var outTy) : Prog S rec var .bool :=
  .bind (.op1 .fst o) fun t => .bind (.op1 .fst o') fun t' =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .natEq t one) fun t1 => .bind (.op2 .natEq t' one) fun t1' =>
  .bind (.op2 .natEq t two) fun t2 => .bind (.op2 .natEq t' two) fun t2' =>
  .ite t1 (eqPartProg m o o' t1')
    (.ite t2 (eqJohnProg m o o' t2')
      (.bind (.op1 .not t1') fun a => .bind (.op1 .not t2') fun b => .op2 .and a b))

/-- **`mapPtsD`.** -/
def mapPtsProg (m : var .nat) (σ : var Ty.perm) (l : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (Toolkit.filterList l fun i => .op2 .natLt i m) fun l₁ =>
  .bind (.op1 .fst σ) fun f => mapList l₁ fun i => .op2 .arrayGet f i

/-- The colour of `v` after the action: `col[inv[v]]`. -/
def actColProg (col inv : var (.array .nat)) (v : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .arrayGet inv v) fun u => .op2 .arrayGet col u

/-- The block of `v` after the action: `σ (blk[inv[v]])`. -/
def actBlkProg (m : var .nat) (σ : var Ty.perm) (blk : var (.array (.list .nat)))
    (inv : var (.array .nat)) (v : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet inv v) fun u => .bind (.op2 .arrayGet blk u) fun b => mapPtsProg m σ b

/-- The cell indices of `v` after the action: `fA[inv[v]]`. -/
def actFProg (fA : var (.array (.list .nat))) (inv : var (.array .nat)) (v : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet inv v) fun u => .op2 .arrayGet fA u

/-- The action on a colored partition. -/
def actPartProg (m : var .nat) (σ : var Ty.perm) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun r₁ =>
  .bind (.op1 .fst r₁) fun col => .bind (.op1 .snd r₁) fun blk =>
  .bind (.op1 .snd σ) fun inv => .bind (.op1 .range m) fun xs =>
  .bind (mapList xs fun v => actColProg col inv v) fun cl =>
  .bind (.op1 .arrayOfList cl) fun col' =>
  .bind (mapList xs fun v => actBlkProg m σ blk inv v) fun bl =>
  .bind (.op1 .arrayOfList bl) fun blk' => partProg col' blk'

/-- The action on a Johnson embedding. -/
def actJohnProg (m : var .nat) (σ : var Ty.perm) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun r₂ =>
  .bind (.op1 .fst r₂) fun V0 => .bind (.op1 .snd r₂) fun r₃ =>
  .bind (.op1 .fst r₃) fun cs => .bind (.op1 .snd r₃) fun r₄ =>
  .bind (.op1 .fst r₄) fun s => .bind (.op1 .snd r₄) fun fA =>
  .bind (.op1 .snd σ) fun inv =>
  .bind (mapPtsProg m σ V0) fun V0' =>
  .bind (mapList cs fun B => mapPtsProg m σ B) fun cs' =>
  .bind (.op1 .range m) fun xs =>
  .bind (mapList xs fun v => actFProg fA inv v) fun fl =>
  .bind (.op1 .arrayOfList fl) fun fA' => johnProg V0' cs' s fA'

/-- **`actOutD`.** -/
def actOutProg (m : var .nat) (σ : var Ty.perm) (o : var outTy) : Prog S rec var outTy :=
  .bind (.op1 .fst o) fun t => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natEq t one) fun t1 =>
  .ite t1 (actPartProg m σ o)
    (.bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq t two) fun t2 =>
      .ite t2 (actJohnProg m σ o) (.ret o))

end Programs

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.emptyNatArrProg :
    RunsWithin X body SoJTree.emptyNatArrProg (#[] : Array ℕ) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
    (by simp [Prim.cost, Prim.eval])

theorem RunsWithin.emptyLstArrProg :
    RunsWithin X body SoJTree.emptyLstArrProg (#[] : Array (List ℕ)) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
    (by simp [Prim.cost, Prim.eval])

theorem RunsWithin.mkOutProg (tag : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) (V0 : List ℕ)
    (cs : List (List ℕ)) (s : ℕ) (fA : Array (List ℕ)) :
    RunsWithin X body (SoJTree.mkOutProg tag col blk V0 cs s fA)
      ((tag, ((col, blk), (V0, (cs, (s, fA))))) : OutD) 6 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.noneProg : RunsWithin X body SoJTree.noneProg noneD 15 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step RunsWithin.emptyNatArrProg
    run_step RunsWithin.emptyLstArrProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step RunsWithin.emptyLstArrProg
    exact RunsWithin.mkOutProg _ _ _ _ _ _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.partProg (col : Array ℕ) (blk : Array (List ℕ)) :
    RunsWithin X body (SoJTree.partProg col blk) (partD col blk) 12 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step RunsWithin.emptyLstArrProg
    exact RunsWithin.mkOutProg _ _ _ _ _ _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.johnProg (V0 : List ℕ) (cs : List (List ℕ)) (s : ℕ) (fA : Array (List ℕ)) :
    RunsWithin X body (SoJTree.johnProg V0 cs s fA) (johnD V0 cs s fA) 11 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step RunsWithin.emptyNatArrProg
    run_step RunsWithin.emptyLstArrProg
    exact RunsWithin.mkOutProg _ _ _ _ _ _ _
  case hc => simp [Prim.cost]

/-! #### Pieces and extensions -/

theorem RunsWithin.apColProg (D : List ℕ) (col : Array ℕ) (x : ℕ) :
    RunsWithin X body (SoJTree.apColProg D col x) (if x ∈ D then 0 else get col x + 1)
      (3 * D.length + 5) := by
  by_cases h : x ∈ D
  · rw [ite_eq_left h]
    refine RunsWithin.bind_le (RunsWithin.memProg x D)
      (RunsWithin.ite_pos (decide_eq_true h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp [Prim.cost]
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg x D)
      (RunsWithin.ite_neg (decide_eq_false h) ((RunsWithin.prim _ _).bind
        ((RunsWithin.prim _ _).bind (RunsWithin.prim_le rfl le_rfl)))) ?_
    simp [Prim.cost]

theorem RunsWithin.apBlkProg (D : List ℕ) (blk : Array (List ℕ)) (x : ℕ) :
    RunsWithin X body (SoJTree.apBlkProg D blk x) (if x ∈ D then D else blk.getD x [])
      (3 * D.length + 3) := by
  by_cases h : x ∈ D
  · rw [ite_eq_left h]
    refine RunsWithin.bind_le (RunsWithin.memProg x D)
      (RunsWithin.ite_pos (decide_eq_true h) (RunsWithin.ret _)) ?_
    omega
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg x D)
      (RunsWithin.ite_neg (decide_eq_false h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp [Prim.cost]

/-- The cost of `addPieceProg` for `m` points and a piece of `d` points. -/
def addPieceCost (m d : ℕ) : ℕ := m * (6 * d + 15) + 3 * m + 30

theorem RunsWithin.addPieceProg (m : ℕ) (D : List ℕ) (o : OutD) :
    RunsWithin X body (SoJTree.addPieceProg m D o) (addPieceD m D o)
      (addPieceCost m D.length) := by
  unfold addPieceD
  by_cases h : o.1 = 1
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun x _ => RunsWithin.apColProg D o.2.1.1 x)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun x _ => RunsWithin.apBlkProg D o.2.1.2 x)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.partProg _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
        addPieceCost]
      ring_nf
      omega
  · rw [ite_eq_right h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h]) (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost, addPieceCost]
      omega

theorem RunsWithin.exColProg (V₁ : List ℕ) (col row : Array ℕ) (y : ℕ) :
    RunsWithin X body (SoJTree.exColProg V₁ col row y)
      (if y ∈ V₁ then 2 * get col y else 2 * get row y + 1) (3 * V₁.length + 6) := by
  by_cases h : y ∈ V₁
  · rw [ite_eq_left h]
    refine RunsWithin.bind_le (RunsWithin.memProg y V₁)
      (RunsWithin.ite_pos (decide_eq_true h) ((RunsWithin.prim _ _).bind
        (RunsWithin.prim_le (show get col y + get col y = 2 * get col y by omega) le_rfl))) ?_
    simp [Prim.cost]
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg y V₁)
      (RunsWithin.ite_neg (decide_eq_false h) ((RunsWithin.prim _ _).bind
        ((RunsWithin.prim _ _).bind ((RunsWithin.prim _ _).bind
          (RunsWithin.prim_le (show get row y + get row y + 1 = 2 * get row y + 1 by omega)
            le_rfl))))) ?_
    simp [Prim.cost]

theorem RunsWithin.exTestProg (V₁ : List ℕ) (row : Array ℕ) (ry z : ℕ) :
    RunsWithin X body (SoJTree.exTestProg V₁ row ry z) (decide (z ∉ V₁ ∧ get row z = ry))
      (3 * V₁.length + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.memProg z V₁)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine RunsWithin.prim_le
      (show (!decide (z ∈ V₁) && (get row z == ry)) = _ from ?_) le_rfl
    by_cases h₁ : z ∈ V₁ <;> by_cases h₂ : get row z = ry <;> simp [h₁, h₂]
  case hc => simp [Prim.cost]

/-- The cost of `exBlkProg` for `v` points in `V₁` and at most `M` candidates. -/
def exBlkCost (v M : ℕ) : ℕ := 3 * v + 6 + M * (3 * v + 9)

theorem RunsWithin.exBlkProg (V₁ : List ℕ) (blk : Array (List ℕ)) (row : Array ℕ)
    {xs : List ℕ} {M : ℕ} (hM : xs.length ≤ M) (y : ℕ) :
    RunsWithin X body (SoJTree.exBlkProg V₁ blk row xs y)
      (if y ∈ V₁ then blk.getD y [] else
        xs.filter fun z => decide (z ∉ V₁ ∧ get row z = get row y)) (exBlkCost V₁.length M) := by
  by_cases h : y ∈ V₁
  · rw [ite_eq_left h]
    refine RunsWithin.bind_le (RunsWithin.memProg y V₁)
      (RunsWithin.ite_pos (decide_eq_true h) (RunsWithin.prim_le rfl le_rfl)) ?_
    simp only [Prim.cost, exBlkCost]
    omega
  · rw [ite_eq_right h]
    refine RunsWithin.bind_le (RunsWithin.memProg y V₁)
      (RunsWithin.ite_neg (decide_eq_false h) ((RunsWithin.prim _ _).bind
        (Toolkit.RunsWithin.filterList fun z _ => RunsWithin.exTestProg V₁ row _ z))) ?_
    have := Nat.mul_le_mul_right (3 * V₁.length + 5 + 4) hM
    simp only [Prim.cost, exBlkCost]
    ring_nf at this ⊢
    omega

/-- The cost of `extendOutProg` for `m` points and `v` points in `V₁`. -/
def extendOutCost (m v : ℕ) : ℕ := m * (exBlkCost v m + 3 * v + 12) + 3 * m + 30

theorem RunsWithin.extendOutProg (m : ℕ) (V₁ : List ℕ) (row : Array ℕ) (o : OutD) :
    RunsWithin X body (SoJTree.extendOutProg m V₁ row o) (extendD m V₁ (get row) o)
      (extendOutCost m V₁.length) := by
  unfold extendD
  by_cases h : o.1 = 1
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun y _ => RunsWithin.exColProg V₁ o.2.1.1 row y)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mapList_le fun y _ =>
        RunsWithin.exBlkProg V₁ o.2.1.2 row (xs := List.range m) (M := m) (by simp) y)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.partProg _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
        extendOutCost]
      ring_nf
      omega
  · rw [ite_eq_right h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h]) (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost, extendOutCost]
      omega

/-! #### Equality -/

theorem RunsWithin.setEqElProg (l l' : List ℕ) (i : ℕ) :
    RunsWithin X body (SoJTree.setEqElProg l l' i) (decide (i ∈ l ↔ i ∈ l'))
      (3 * l.length + 3 * l'.length + 7) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.memProg i l)
    run_step (RunsWithin.memProg i l')
    refine (RunsWithin.csBeqProg _ _).of_eq ?_
    by_cases h₁ : i ∈ l <;> by_cases h₂ : i ∈ l' <;> simp [h₁, h₂]
  case hc => omega

/-- The cost of `setEqProg` for `m` points and lists of at most `L` entries. -/
def setEqCost (m L : ℕ) : ℕ := m * (6 * L + 10) + 2

theorem RunsWithin.setEqProg (m : ℕ) {l l' : List ℕ} {L : ℕ} (hl : l.length ≤ L)
    (hl' : l'.length ≤ L) :
    RunsWithin X body (SoJTree.setEqProg m l l') (setEqD m l l') (setEqCost m L) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.allList_le (c := 6 * L + 7) fun i _ =>
      (RunsWithin.setEqElProg l l' i).mono (by omega)
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, setEqCost]
    ring_nf
    omega

theorem ld_toArray_getD (cs : List (List ℕ)) (j : ℕ) : cs.toArray.getD j [] = cs.getD j [] := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem RunsWithin.famSubInProg (m : ℕ) (c : List ℕ) (ca' : Array (List ℕ)) (j' : ℕ) {L : ℕ}
    (hc : c.length ≤ L) (hca : (ca'.getD j' []).length ≤ L) :
    RunsWithin X body (SoJTree.famSubInProg m c ca' j') (setEqD m c (ca'.getD j' []))
      (setEqCost m L + 1) :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.setEqProg m hc hca)
    (by simp [Prim.cost]; omega)

theorem RunsWithin.famSubElProg (m : ℕ) (ca ca' : Array (List ℕ)) {js' : List ℕ} (j : ℕ)
    {J L : ℕ} (hjs' : js'.length ≤ J) (hca : ∀ j, (ca.getD j []).length ≤ L)
    (hca' : ∀ j, (ca'.getD j []).length ≤ L) :
    RunsWithin X body (SoJTree.famSubElProg m ca ca' js' j)
      (js'.any fun j' => setEqD m (ca.getD j []) (ca'.getD j' []))
      (J * (setEqCost m L + 3) + 2) := by
  refine RunsWithin.bind_le (RunsWithin.prim _ _)
    (RunsWithin.anyList_le fun j' _ => RunsWithin.famSubInProg m _ ca' j' (hca j) (hca' j')) ?_
  have := Nat.mul_le_mul_right (setEqCost m L + 3) hjs'
  simp only [Prim.cost]
  ring_nf at this ⊢
  omega

/-- The cost of `famSubProg` for `m` points, at most `K` cells of at most `L` points, and at
most `J` indices. -/
def famSubCost (m K J L : ℕ) : ℕ := 2 * K + J * (J * (setEqCost m L + 3) + 4) + 3

theorem RunsWithin.famSubProg (m : ℕ) {cs cs' : List (List ℕ)} {js js' : List ℕ} {K J L : ℕ}
    (hK : cs.length ≤ K) (hK' : cs'.length ≤ K) (hJ : js.length ≤ J) (hJ' : js'.length ≤ J)
    (hL : ∀ c ∈ cs, c.length ≤ L) (hL' : ∀ c ∈ cs', c.length ≤ L) :
    RunsWithin X body (SoJTree.famSubProg m cs js cs' js') (famSubD m cs js cs' js')
      (famSubCost m K J L) := by
  have hb : ∀ (cs : List (List ℕ)), (∀ c ∈ cs, c.length ≤ L) →
      ∀ j, (cs.toArray.getD j []).length ≤ L := fun cs h j => by
    rw [ld_toArray_getD]
    exact (ld_length_getD_le cs j).trans (ld_maxLen_le h)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.allList_le fun j _ =>
      RunsWithin.famSubElProg m cs.toArray cs'.toArray j hJ' (hb cs hL) (hb cs' hL')).of_eq ?_
    simp only [famSubD, ld_toArray_getD]
  case hc =>
    have := Nat.mul_le_mul_right (J * (setEqCost m L + 3) + 2 + 2) hJ
    simp only [Prim.cost, Args.head, famSubCost]
    ring_nf at this ⊢
    omega

/-- The cost of `famEqProg`. -/
def famEqCost (m K J L : ℕ) : ℕ := 2 * famSubCost m K J L + 1

theorem RunsWithin.famEqProg (m : ℕ) {cs cs' : List (List ℕ)} {js js' : List ℕ} {K J L : ℕ}
    (hK : cs.length ≤ K) (hK' : cs'.length ≤ K) (hJ : js.length ≤ J) (hJ' : js'.length ≤ J)
    (hL : ∀ c ∈ cs, c.length ≤ L) (hL' : ∀ c ∈ cs', c.length ≤ L) :
    RunsWithin X body (SoJTree.famEqProg m cs js cs' js') (famEqD m cs js cs' js')
      (famEqCost m K J L) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.famSubProg m hK hK' hJ hJ' hL hL')
    run_step (RunsWithin.famSubProg m hK' hK hJ' hJ hL' hL)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, famEqCost]
    omega

theorem RunsWithin.eqPartElProg (m : ℕ) (col col' : Array ℕ) (blk blk' : Array (List ℕ))
    (x : ℕ) {L : ℕ} (hb : (blk.getD x []).length ≤ L) (hb' : (blk'.getD x []).length ≤ L) :
    RunsWithin X body (SoJTree.eqPartElProg m col col' blk blk' x)
      (get col x == get col' x && setEqD m (blk.getD x []) (blk'.getD x []))
      (setEqCost m L + 6) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.setEqProg m hb hb')
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

/-- The cost of `eqPartProg` for `m` points and leaves of size at most `s`. -/
def eqPartCost (m s : ℕ) : ℕ := m * (setEqCost m s + 8) + m + 12

theorem RunsWithin.eqPartProg (m : ℕ) (o o' : OutD) (t1' : Bool) {s : ℕ} (ho : outSize o ≤ s)
    (ho' : outSize o' ≤ s) :
    RunsWithin X body (SoJTree.eqPartProg m o o' t1')
      (t1' && (List.range m).all fun x =>
        get o.2.1.1 x == get o'.2.1.1 x && setEqD m (o.2.1.2.getD x []) (o'.2.1.2.getD x []))
      (eqPartCost m s) := by
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
    run_step (RunsWithin.allList_le fun x _ =>
      RunsWithin.eqPartElProg m o.2.1.1 o'.2.1.1 o.2.1.2 o'.2.1.2 x
        ((outSize_blk o x).trans ho) ((outSize_blk o' x).trans ho'))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, eqPartCost]
    ring_nf
    omega

theorem RunsWithin.eqJohnElProg (m : ℕ) (cs cs' : List (List ℕ)) (fA fA' : Array (List ℕ))
    (x : ℕ) {K J L : ℕ} (hK : cs.length ≤ K) (hK' : cs'.length ≤ K)
    (hJ : (fA.getD x []).length ≤ J) (hJ' : (fA'.getD x []).length ≤ J)
    (hL : ∀ c ∈ cs, c.length ≤ L) (hL' : ∀ c ∈ cs', c.length ≤ L) :
    RunsWithin X body (SoJTree.eqJohnElProg m cs cs' fA fA' x)
      (famEqD m cs (fA.getD x []) cs' (fA'.getD x [])) (famEqCost m K J L + 2) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.famEqProg m hK hK' hJ hJ' hL hL'
  case hc =>
    simp only [Prim.cost]
    omega

/-- The cost of `eqJohnProg` for `m` points and leaves of size at most `s`. -/
def eqJohnCost (m s : ℕ) : ℕ :=
  setEqCost m s + 4 * s + famEqCost m s s s + m * (famEqCost m s s s + 4) + m + 30

theorem RunsWithin.eqJohnProg (m : ℕ) (o o' : OutD) (t2' : Bool) {s : ℕ} (ho : outSize o ≤ s)
    (ho' : outSize o' ≤ s) :
    RunsWithin X body (SoJTree.eqJohnProg m o o' t2')
      (t2' && setEqD m o.2.2.1 o'.2.2.1 &&
        famEqD m o.2.2.2.1 (List.range o.2.2.2.1.length) o'.2.2.2.1
          (List.range o'.2.2.2.1.length) &&
        o.2.2.2.2.1 == o'.2.2.2.2.1 && (List.range m).all fun x =>
          famEqD m o.2.2.2.1 (o.2.2.2.2.2.getD x []) o'.2.2.2.1 (o'.2.2.2.2.2.getD x []))
      (eqJohnCost m s) := by
  have hK := (outSize_cs o).trans ho
  have hK' := (outSize_cs o').trans ho'
  have hL : ∀ c ∈ o.2.2.2.1, c.length ≤ s := fun c hc => (outSize_cell o hc).trans ho
  have hL' : ∀ c ∈ o'.2.2.2.1, c.length ≤ s := fun c hc => (outSize_cell o' hc).trans ho'
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
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.setEqProg m ((outSize_V0 o).trans ho) ((outSize_V0 o').trans ho'))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.famEqProg m hK hK'
      (show (List.range o.2.2.2.1.length).length ≤ s by simpa using hK)
      (show (List.range o'.2.2.2.1.length).length ≤ s by simpa using hK') hL hL')
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.allList_le fun x _ =>
      RunsWithin.eqJohnElProg m o.2.2.2.1 o'.2.2.2.1 o.2.2.2.2.2 o'.2.2.2.2.2 x hK hK'
        ((outSize_fA o x).trans ho) ((outSize_fA o' x).trans ho') hL hL')
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, eqJohnCost]
    ring_nf
    omega

/-- The cost of `outEqProg` for `m` points and leaves of size at most `s`. -/
def outEqCost (m s : ℕ) : ℕ := eqPartCost m s + eqJohnCost m s + 15

theorem RunsWithin.outEqProg (m : ℕ) (o o' : OutD) {s : ℕ} (ho : outSize o ≤ s)
    (ho' : outSize o' ≤ s) :
    RunsWithin X body (SoJTree.outEqProg m o o') (outEqD m o o') (outEqCost m s) := by
  unfold outEqD
  by_cases h₁ : o.1 = 1
  · rw [ite_eq_left h₁]
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
      exact RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h₁])
        (RunsWithin.eqPartProg m o o' _ ho ho')
    case hc =>
      simp only [Prim.cost, outEqCost]
      omega
  · rw [ite_eq_right h₁]
    by_cases h₂ : o.1 = 2
    · rw [ite_eq_left h₂]
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
        exact RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h₁])
          (RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h₂])
            (RunsWithin.eqJohnProg m o o' _ ho ho'))
      case hc =>
        simp only [Prim.cost, outEqCost]
        omega
    · rw [ite_eq_right h₂]
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
        exact RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h₁])
          (RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h₂])
            ((RunsWithin.prim _ _).bind ((RunsWithin.prim _ _).bind
              (RunsWithin.prim_le rfl le_rfl))))
      case hc =>
        simp only [Prim.cost, outEqCost]
        omega

/-! #### The action of a permutation -/

/-- The cost of `mapPtsProg` for lists of at most `L` entries. -/
def mapPtsCost (L : ℕ) : ℕ := 9 * L + 6

theorem RunsWithin.mapPtsProg (m : ℕ) (σ : PermData) {l : List ℕ} {L : ℕ} (hl : l.length ≤ L) :
    RunsWithin X body (SoJTree.mapPtsProg m σ l) (mapPtsD m σ l) (mapPtsCost L) := by
  apply RunsWithin.mono
  case h =>
    run_step (Toolkit.RunsWithin.filterList (P := fun i => decide (i < m)) (c := 1) fun i _ =>
      RunsWithin.prim_le rfl le_rfl)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.mapList_le (c := 1) fun i _ => RunsWithin.prim_le rfl le_rfl).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ ((List.length_filter_le _ _).trans hl)) _)
  case hc =>
    have h₁ := Nat.mul_le_mul_right 5 hl
    simp only [Prim.cost, mapPtsCost]
    omega

theorem RunsWithin.actColProg (col inv : Array ℕ) (v : ℕ) :
    RunsWithin X body (SoJTree.actColProg col inv v) (get col (get inv v)) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])

theorem RunsWithin.actBlkProg (m : ℕ) (σ : PermData) (blk : Array (List ℕ)) (inv : Array ℕ)
    (v : ℕ) {L : ℕ} (hL : (blk.getD (get inv v) []).length ≤ L) :
    RunsWithin X body (SoJTree.actBlkProg m σ blk inv v)
      (mapPtsD m σ (blk.getD (get inv v) [])) (mapPtsCost L + 2) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.mapPtsProg m σ hL
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.actFProg (fA : Array (List ℕ)) (inv : Array ℕ) (v : ℕ) :
    RunsWithin X body (SoJTree.actFProg fA inv v) (fA.getD (get inv v) []) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])

/-- The cost of `actPartProg` for `m` points and leaves of size at most `s`. -/
def actPartCost (m s : ℕ) : ℕ := m * (mapPtsCost s + 13) + 3 * m + 25

theorem RunsWithin.actPartProg (m : ℕ) (σ : PermData) (o : OutD) {s : ℕ} (ho : outSize o ≤ s) :
    RunsWithin X body (SoJTree.actPartProg m σ o)
      (partD ((List.range m).map fun v => get o.2.1.1 (get σ.2 v)).toArray
        ((List.range m).map fun v => mapPtsD m σ (o.2.1.2.getD (get σ.2 v) [])).toArray)
      (actPartCost m s) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun v _ => RunsWithin.actColProg o.2.1.1 σ.2 v)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun v _ =>
      RunsWithin.actBlkProg m σ o.2.1.2 σ.2 v ((outSize_blk o _).trans ho))
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.partProg _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
      actPartCost]
    ring_nf
    omega

/-- The cost of `actJohnProg` for `m` points and leaves of size at most `s`. -/
def actJohnCost (m s : ℕ) : ℕ := s * (mapPtsCost s + 3) + mapPtsCost s + 7 * m + 30

theorem RunsWithin.actJohnProg (m : ℕ) (σ : PermData) (o : OutD) {s : ℕ} (ho : outSize o ≤ s) :
    RunsWithin X body (SoJTree.actJohnProg m σ o)
      (johnD (mapPtsD m σ o.2.2.1) (o.2.2.2.1.map (mapPtsD m σ)) o.2.2.2.2.1
        ((List.range m).map fun v => o.2.2.2.2.2.getD (get σ.2 v) []).toArray)
      (actJohnCost m s) := by
  have hK := (outSize_cs o).trans ho
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
    run_step (RunsWithin.mapPtsProg m σ ((outSize_V0 o).trans ho))
    run_step (RunsWithin.mapList_le fun B hB =>
      RunsWithin.mapPtsProg m σ (l := B) ((outSize_cell o hB).trans ho))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun v _ => RunsWithin.actFProg o.2.2.2.2.2 σ.2 v)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.johnProg _ _ _ _
  case hc =>
    have := Nat.mul_le_mul_right (mapPtsCost s + 3) hK
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
      actJohnCost]
    omega

/-- The cost of `actOutProg` for `m` points and leaves of size at most `s`. -/
def actOutCost (m s : ℕ) : ℕ := actPartCost m s + actJohnCost m s + 10

theorem RunsWithin.actOutProg (m : ℕ) (σ : PermData) (o : OutD) {s : ℕ} (ho : outSize o ≤ s) :
    RunsWithin X body (SoJTree.actOutProg m σ o) (actOutD m σ o) (actOutCost m s) := by
  unfold actOutD
  by_cases h₁ : o.1 = 1
  · rw [ite_eq_left h₁]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h₁])
        (RunsWithin.actPartProg m σ o ho)
    case hc =>
      simp only [Prim.cost, actOutCost]
      omega
  · rw [ite_eq_right h₁]
    by_cases h₂ : o.1 = 2
    · rw [ite_eq_left h₂]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h₁]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h₂])
          (RunsWithin.actJohnProg m σ o ho)
      case hc =>
        simp only [Prim.cost, actOutCost]
        omega
    · rw [ite_eq_right h₂]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h₁]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h₂]) (RunsWithin.ret _)
      case hc =>
        simp only [Prim.cost, actOutCost]
        omega

/-! #### Polynomial bounds -/

theorem setEqCost_le (m L : ℕ) : setEqCost m L ≤ 10 * (m + 1) * (L + 1) := by
  unfold setEqCost
  nlinarith

theorem ld_poly_aux {M T : ℕ} (hM : 1 ≤ M) (hT : 1 ≤ T) :
    T ≤ T ^ 2 ∧ T ^ 2 ≤ T ^ 3 ∧ 1 ≤ T ^ 2 ∧ T ^ 2 ≤ M * T ^ 2 ∧ T ^ 3 ≤ M * T ^ 3 ∧
      M ≤ M * T ^ 2 ∧ M * T ≤ M * T ^ 2 ∧ M * T ^ 3 ≤ M ^ 2 * T ^ 3 ∧ M * T ≤ M ^ 2 * T ^ 3 ∧
      M ≤ M ^ 2 * T ^ 3 ∧ T ≤ M ^ 2 * T ^ 3 ∧ 1 ≤ M ^ 2 * T ^ 3 ∧ M ^ 2 * T ≤ M ^ 2 * T ^ 3 := by
  have h₂ : 1 ≤ T ^ 2 := Nat.one_le_pow _ _ hT
  have h₃ : 1 ≤ T ^ 3 := Nat.one_le_pow _ _ hT
  have hM2 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ hM
  have a₁ : T ≤ T ^ 2 := by nlinarith
  have a₂ : T ^ 2 ≤ T ^ 3 := by nlinarith
  have a₃ : M ≤ M ^ 2 := by nlinarith
  refine ⟨a₁, a₂, h₂, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

theorem famEqCost_le (m s : ℕ) : famEqCost m s s s ≤ 50 * (m + 1) * (s + 1) ^ 3 := by
  have h := setEqCost_le m s
  calc famEqCost m s s s
      ≤ 2 * (2 * (s + 1) + (s + 1) * ((s + 1) * (10 * (m + 1) * (s + 1) + 3) + 4) + 3) + 1 := by
        unfold famEqCost famSubCost
        gcongr <;> omega
    _ ≤ 50 * (m + 1) * (s + 1) ^ 3 := by
        obtain ⟨T, hT⟩ : ∃ T, T = s + 1 := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M, M = m + 1 := ⟨_, rfl⟩
        rw [← hT, ← hM]
        obtain ⟨h₁, h₂, h₃, h₄, h₅, -⟩ := ld_poly_aux (M := M) (T := T) (by omega) (by omega)
        nlinarith

/-- **The cost of comparing two leaves** of size at most `s` is at most
`200 (m + 1)² (s + 1)³`. -/
theorem outEqCost_le (m s : ℕ) : outEqCost m s ≤ 200 * (m + 1) ^ 2 * (s + 1) ^ 3 := by
  have h₁ := setEqCost_le m s
  have h₂ := famEqCost_le m s
  calc outEqCost m s
      ≤ (m + 1) * (10 * (m + 1) * (s + 1) + 8) + (m + 1) + 12 +
          (10 * (m + 1) * (s + 1) + 4 * (s + 1) + 50 * (m + 1) * (s + 1) ^ 3 +
            (m + 1) * (50 * (m + 1) * (s + 1) ^ 3 + 4) + (m + 1) + 30) + 15 := by
        unfold outEqCost eqPartCost eqJohnCost
        gcongr <;> omega
    _ ≤ 200 * (m + 1) ^ 2 * (s + 1) ^ 3 := by
        obtain ⟨T, hT⟩ : ∃ T, T = s + 1 := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M, M = m + 1 := ⟨_, rfl⟩
        rw [← hT, ← hM]
        obtain ⟨-, -, -, -, -, -, -, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ :=
          ld_poly_aux (M := M) (T := T) (by omega) (by omega)
        nlinarith

/-- **The cost of moving a leaf** of size at most `s` is at most `150 (m + 1) (s + 1)²`. -/
theorem actOutCost_le (m s : ℕ) : actOutCost m s ≤ 150 * (m + 1) * (s + 1) ^ 2 := by
  calc actOutCost m s
      ≤ (m + 1) * (9 * (s + 1) + 6 + 13) + 3 * (m + 1) + 25 +
          ((s + 1) * (9 * (s + 1) + 6 + 3) + (9 * (s + 1) + 6) + 7 * (m + 1) + 30) + 10 := by
        unfold actOutCost actPartCost actJohnCost mapPtsCost
        gcongr <;> omega
    _ ≤ 150 * (m + 1) * (s + 1) ^ 2 := by
        obtain ⟨T, hT⟩ : ∃ T, T = s + 1 := ⟨_, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M, M = m + 1 := ⟨_, rfl⟩
        rw [← hT, ← hM]
        obtain ⟨h₁, -, h₃, h₄, -, h₆, h₇, -⟩ := ld_poly_aux (M := M) (T := T) (by omega) (by omega)
        nlinarith

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ x₁ s₁ t₁ : var₁ .nat} {m₂ x₂ s₂ t₂ : var₂ .nat}
  {c₁ c₁' i₁ : var₁ (.array .nat)} {c₂ c₂' i₂ : var₂ (.array .nat)}
  {D₁ E₁ l₁ l₁' : var₁ (.list .nat)} {D₂ E₂ l₂ l₂' : var₂ (.list .nat)}
  {B₁ B₁' : var₁ (.array (.list .nat))} {B₂ B₂' : var₂ (.array (.list .nat))}
  {L₁ L₁' : var₁ (.list (.list .nat))} {L₂ L₂' : var₂ (.list (.list .nat))}
  {o₁ o₁' : var₁ outTy} {o₂ o₂' : var₂ outTy} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm}
  {b₁ : var₁ .bool} {b₂ : var₂ .bool}

theorem wf_emptyNatArrProg :
    Prog.Wf (S := S) (rec := rec) r Γ (emptyNatArrProg (var := var₁)) emptyNatArrProg := by
  unfold emptyNatArrProg
  prog_wf

theorem wf_emptyLstArrProg :
    Prog.Wf (S := S) (rec := rec) r Γ (emptyLstArrProg (var := var₁)) emptyLstArrProg := by
  unfold emptyLstArrProg
  prog_wf

theorem wf_noneProg : Prog.Wf (S := S) (rec := rec) r Γ (noneProg (var := var₁)) noneProg := by
  unfold noneProg mkOutProg emptyNatArrProg emptyLstArrProg
  prog_wf

theorem wf_partProg (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (partProg c₁ B₁) (partProg c₂ B₂) := by
  unfold partProg mkOutProg emptyLstArrProg
  prog_wf

theorem wf_johnProg (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hL : ⟨.list (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (johnProg D₁ L₁ s₁ B₁) (johnProg D₂ L₂ s₂ B₂) := by
  unfold johnProg mkOutProg emptyNatArrProg emptyLstArrProg
  prog_wf

theorem wf_apColProg (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (apColProg D₁ c₁ x₁) (apColProg D₂ c₂ x₂) := by
  unfold apColProg memProg anyList
  prog_wf

theorem wf_apBlkProg (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (apBlkProg D₁ B₁ x₁) (apBlkProg D₂ B₂ x₂) := by
  unfold apBlkProg memProg anyList
  prog_wf

theorem wf_addPieceProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (addPieceProg m₁ D₁ o₁) (addPieceProg m₂ D₂ o₂) := by
  unfold addPieceProg apColProg apBlkProg partProg mkOutProg emptyLstArrProg memProg anyList
    mapList
  prog_wf

theorem wf_exColProg (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hc' : ⟨.array .nat, c₁', c₂'⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (exColProg D₁ c₁ c₁' x₁) (exColProg D₂ c₂ c₂' x₂) := by
  unfold exColProg memProg anyList
  prog_wf

theorem wf_exTestProg (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (exTestProg D₁ c₁ t₁ x₁) (exTestProg D₂ c₂ t₂ x₂) := by
  unfold exTestProg memProg anyList
  prog_wf

theorem wf_exBlkProg (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (exBlkProg D₁ B₁ c₁ E₁ x₁) (exBlkProg D₂ B₂ c₂ E₂ x₂) := by
  unfold exBlkProg exTestProg memProg anyList Toolkit.filterList
  prog_wf

theorem wf_extendOutProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extendOutProg m₁ D₁ c₁ o₁) (extendOutProg m₂ D₂ c₂ o₂) := by
  unfold extendOutProg exColProg exBlkProg exTestProg partProg mkOutProg emptyLstArrProg memProg
    anyList Toolkit.filterList mapList
  prog_wf

theorem wf_setEqElProg (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) (hl' : ⟨.list .nat, l₁', l₂'⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (setEqElProg l₁ l₁' x₁) (setEqElProg l₂ l₂' x₂) := by
  unfold setEqElProg memProg csBeqProg anyList
  prog_wf

theorem wf_setEqProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ)
    (hl' : ⟨.list .nat, l₁', l₂'⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (setEqProg m₁ l₁ l₁') (setEqProg m₂ l₂ l₂') := by
  unfold setEqProg
  refine .bind (.prim _ (.cons hm .nil)) fun i₁ i₂ => wf_allList (by simp) ?_
  intro Γ' hΓ x₁ x₂ hx
  exact wf_setEqElProg (hΓ (by simp [hl])) (hΓ (by simp [hl'])) hx

theorem wf_famSubProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hL : ⟨.list (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hL' : ⟨.list (.list .nat), L₁', L₂'⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (famSubProg m₁ L₁ D₁ L₁' E₁)
      (famSubProg m₂ L₂ D₂ L₂' E₂) := by
  unfold famSubProg
  refine .bind (.prim _ (.cons hL .nil)) fun a₁ a₂ =>
    .bind (.prim _ (.cons (by simp [hL']) .nil)) fun a₁' a₂' => wf_allList (by simp [hD]) ?_
  intro Γ' hΓ j₁ j₂ hj
  unfold famSubElProg
  refine .bind (.prim _ (.cons (hΓ (by simp)) (.cons hj .nil))) fun c₁ c₂ =>
    wf_anyList (by simp [hΓ (show ⟨.list .nat, E₁, E₂⟩ ∈ _ by simp [hE])]) ?_
  intro Γ'' hΓ' k₁ k₂ hk
  unfold famSubInProg
  refine .bind (.prim _ (.cons (hΓ' (by simp [hΓ (show ⟨.array (.list .nat), a₁', a₂'⟩ ∈ _ by
    simp)])) (.cons hk .nil))) fun d₁ d₂ => wf_setEqProg ?_ ?_ (by simp)
  · exact List.mem_cons_of_mem _ (hΓ' (List.mem_cons_of_mem _ (hΓ (by simp [hm]))))
  · exact List.mem_cons_of_mem _ (hΓ' (by simp))

theorem wf_famEqProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hL : ⟨.list (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hL' : ⟨.list (.list .nat), L₁', L₂'⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (famEqProg m₁ L₁ D₁ L₁' E₁)
      (famEqProg m₂ L₂ D₂ L₂' E₂) := by
  unfold famEqProg
  exact .bind (wf_famSubProg hm hL hD hL' hE) fun a₁ a₂ =>
    .bind (wf_famSubProg (by simp [hm]) (by simp [hL']) (by simp [hE]) (by simp [hL])
      (by simp [hD])) fun b₁ b₂ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_eqPartElProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hc' : ⟨.array .nat, c₁', c₂'⟩ ∈ Γ) (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ)
    (hB' : ⟨.array (.list .nat), B₁', B₂'⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (eqPartElProg m₁ c₁ c₁' B₁ B₁' x₁)
      (eqPartElProg m₂ c₂ c₂' B₂ B₂' x₂) := by
  unfold eqPartElProg
  refine .bind (.prim _ (.cons hc (.cons hx .nil))) fun a₁ a₂ =>
    .bind (.prim _ (.cons (by simp [hc']) (.cons (by simp [hx]) .nil))) fun a₁' a₂' =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun e₁ e₂ =>
    .bind (.prim _ (.cons (by simp [hB]) (.cons (by simp [hx]) .nil))) fun b₁ b₂ =>
    .bind (.prim _ (.cons (by simp [hB']) (.cons (by simp [hx]) .nil))) fun b₁' b₂' =>
    .bind (wf_setEqProg (by simp [hm]) (by simp) (by simp)) fun f₁ f₂ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_eqJohnElProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hL : ⟨.list (.list .nat), L₁, L₂⟩ ∈ Γ)
    (hL' : ⟨.list (.list .nat), L₁', L₂'⟩ ∈ Γ) (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ)
    (hB' : ⟨.array (.list .nat), B₁', B₂'⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (eqJohnElProg m₁ L₁ L₁' B₁ B₁' x₁)
      (eqJohnElProg m₂ L₂ L₂' B₂ B₂' x₂) := by
  unfold eqJohnElProg
  exact .bind (.prim _ (.cons hB (.cons hx .nil))) fun a₁ a₂ =>
    .bind (.prim _ (.cons (by simp [hB']) (.cons (by simp [hx]) .nil))) fun a₁' a₂' =>
    wf_famEqProg (by simp [hm]) (by simp [hL]) (by simp) (by simp [hL']) (by simp)

theorem wf_eqPartProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ)
    (ho' : ⟨outTy, o₁', o₂'⟩ ∈ Γ) (hb : ⟨.bool, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (eqPartProg m₁ o₁ o₁' b₁) (eqPartProg m₂ o₂ o₂' b₂) := by
  unfold eqPartProg
  refine .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [ho']) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_allList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_eqPartElProg (hΓ (by simp [hm])) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp))
        (hΓ (by simp)) hx) fun _ _ => .prim _ (.cons (by simp [hb]) (.cons (by simp) .nil))

theorem wf_eqJohnProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ)
    (ho' : ⟨outTy, o₁', o₂'⟩ ∈ Γ) (hb : ⟨.bool, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (eqJohnProg m₁ o₁ o₁' b₁) (eqJohnProg m₂ o₂ o₂' b₂) := by
  unfold eqJohnProg
  refine .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp [ho']) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_setEqProg (by simp [hm]) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hb]) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_famEqProg (by simp [hm]) (by simp) (by simp) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_allList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_eqJohnElProg (hΓ (by simp [hm])) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp))
        (hΓ (by simp)) hx) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_outEqProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ)
    (ho' : ⟨outTy, o₁', o₂'⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (outEqProg m₁ o₁ o₁') (outEqProg m₂ o₂ o₂') := by
  unfold outEqProg
  refine .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [ho']) .nil))
    fun _ _ => .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) (wf_eqPartProg (by simp [hm]) (by simp [ho]) (by simp [ho']) (by simp))
      (.ite (by simp) (wf_eqJohnProg (by simp [hm]) (by simp [ho]) (by simp [ho']) (by simp))
        (.bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
          .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
          .prim _ (.cons (by simp) (.cons (by simp) .nil))))

theorem wf_mapPtsProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (mapPtsProg m₁ σ₁ l₁) (mapPtsProg m₂ σ₂ l₂) := by
  unfold mapPtsProg Toolkit.filterList mapList
  prog_wf

theorem wf_actColProg (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hi : ⟨.array .nat, i₁, i₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (actColProg c₁ i₁ x₁) (actColProg c₂ i₂ x₂) := by
  unfold actColProg
  prog_wf

theorem wf_actBlkProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ) (hi : ⟨.array .nat, i₁, i₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (actBlkProg m₁ σ₁ B₁ i₁ x₁) (actBlkProg m₂ σ₂ B₂ i₂ x₂) := by
  unfold actBlkProg
  exact .bind (.prim _ (.cons hi (.cons hx .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hB]) (.cons (by simp) .nil))) fun _ _ =>
    wf_mapPtsProg (by simp [hm]) (by simp [hσ]) (by simp)

theorem wf_actFProg (hB : ⟨.array (.list .nat), B₁, B₂⟩ ∈ Γ) (hi : ⟨.array .nat, i₁, i₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (actFProg B₁ i₁ x₁) (actFProg B₂ i₂ x₂) := by
  unfold actFProg
  prog_wf

theorem wf_actPartProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (actPartProg m₁ σ₁ o₁) (actPartProg m₂ σ₂ o₂) := by
  unfold actPartProg
  exact .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hσ]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_actColProg (hΓ (by simp)) (hΓ (by simp)) hx) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_actBlkProg (hΓ (by simp [hm])) (hΓ (by simp [hσ])) (hΓ (by simp)) (hΓ (by simp)) hx)
      fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => wf_partProg (by simp) (by simp)

theorem wf_actJohnProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (actJohnProg m₁ σ₁ o₁) (actJohnProg m₂ σ₂ o₂) := by
  unfold actJohnProg
  exact .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp [hσ]) .nil)) fun _ _ =>
    .bind (wf_mapPtsProg (by simp [hm]) (by simp [hσ]) (by simp)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_mapPtsProg (hΓ (by simp [hm])) (hΓ (by simp [hσ])) hx) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_actFProg (hΓ (by simp)) (hΓ (by simp)) hx) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    wf_johnProg (by simp) (by simp) (by simp) (by simp)

theorem wf_actOutProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (actOutProg m₁ σ₁ o₁) (actOutProg m₂ σ₂ o₂) := by
  unfold actOutProg
  exact .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) (wf_actPartProg (by simp [hm]) (by simp [hσ]) (by simp [ho]))
      (.bind (.prim _ .nil) fun _ _ =>
        .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
        .ite (by simp) (wf_actJohnProg (by simp [hm]) (by simp [hσ]) (by simp [ho]))
          (.ret (by simp [ho])))

end Wf

end GraphIso.SoJTree
