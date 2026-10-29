module

public import GraphIso.SoJTree.Frame
public import GraphIso.SoJTree.LeafProg
public import GraphIso.SoJProg.Twins
public import GraphIso.SoJProg.Johnson
public import GraphIso.SoJProg.BaseCase
public import GraphIso.Graph.LiftProg
public import GraphIso.Solver.Coherent

/-!
# One step of a frame as a costed program

Stage 14d (`PLAN-14.md` §8, item 4): `stepProg m t fr` computes `stepD m t fr` (one level of
milestone 11's `bsoj` on data, `GraphIso/SoJTree/Frame.lean`) from the stage 14c programs and
the leaf programs of `GraphIso/SoJTree/LeafProg.lean`. It makes no backend calls and no
`.recur` call.

* The levels, each a named program with its specification and well-formedness lemma:
  `contI` (`sp_contProg`), `cohI` (`sp_cohIProg`, within `116000 B^7 (1 + w)`), `dlI`
  (`sp_dlProg`, within `330000 B^8 (1 + w)`), the base case (`sp_baseProg`), the `d`-ary step
  (`sp_daryProg`) and `bstepI` (`sp_bstepProg`, within `500000 (B^12 + 46658)^8 (1 + w)`),
  for a bound `B` on the sizes (`m`, `k² + 1`, `m + 2k + |V₁| + 1`, the cells; see each
  statement) and `w` the work of the level. Outside the
  base case, `k^d ≤ (kn)^6 + 1` and `d^d ≤ (kn)^6 + 46656` (`sp_pow_arity_le`,
  `sp_pow_self_arity_le`, for `n ≤ 2t` points).
* `FrameD.ValidP m q t`: a valid frame with at most `2t` points, at most `q` cells of at most
  `m` points, wrapper operations on at most `m` points and `|wr| + 4|cs| ≤ 4q + 1`; it passes to
  the child frames (`stepD_validP`).
* `RunsWithin.stepProg`: under `ValidP m q t`, `stepProg` runs within
  `stepK m q t · (1 + stepWork m t fr + |leaves|)`, with `stepK` an explicit polynomial in
  `m + q + t` (`wf_stepProg` for well-formedness).
* **Leaf sizes**: under `ValidP m q t`, the leaves of a step have `outSize` at most
  `outB m q = m² + m + q + 1` (`stepD_outSize`): blocks are filters of `V₁` or of `0, …, m - 1`,
  components of `cohSojD` (at most `m² + 1` points) or pieces of at most `m` points, Johnson
  leaves have at most `q` cells of at most `m` points, and the wrapper keeps the bound.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.Cost GraphIso.Programs
  GraphIso.Sims

/-! ### Splitting items -/

section Split

/-- The leaves and the child frames of a list of items, in order. -/
def splitI (l : List Item) : List OutD × List FrameD :=
  (l.filterMap Sum.getLeft?, l.filterMap Sum.getRight?)

@[simp] theorem splitI_nil : splitI [] = ([], []) := rfl

@[simp] theorem splitI_inl (o : OutD) : splitI [.inl o] = ([o], []) := rfl

@[simp] theorem splitI_inr (fr : FrameD) : splitI [.inr fr] = ([], [fr]) := rfl

theorem splitI_append (l l' : List Item) :
    splitI (l ++ l') = ((splitI l).1 ++ (splitI l').1, (splitI l).2 ++ (splitI l').2) := by
  simp [splitI, List.filterMap_append]

theorem splitI_flatMap {β : Type*} (L : List β) (F : β → List Item) :
    splitI (L.flatMap F) =
      (L.flatMap fun c => (splitI (F c)).1, L.flatMap fun c => (splitI (F c)).2) := by
  induction L with
  | nil => rfl
  | cons c L ih => simp [List.flatMap_cons, splitI_append, ih]

theorem splitI_map (L : List OutD) : splitI (L.map Sum.inl) = (L, []) := by
  induction L with
  | nil => rfl
  | cons o L ih =>
    rw [List.map_cons, show (Sum.inl o :: L.map Sum.inl : List Item) =
      [Sum.inl o] ++ L.map Sum.inl from rfl, splitI_append, ih]
    rfl

theorem splitI_wrap (m : ℕ) (ops : List WrapOp) (l : List Item) :
    splitI (l.map (wrapItem m ops)) =
      ((splitI l).1.map (wrapD m ops),
        (splitI l).2.map fun ch => (ch.V₁, ch.cs, ch.a, ch.wr ++ ops)) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.map_cons, show wrapItem m ops i :: l.map (wrapItem m ops) =
      [wrapItem m ops i] ++ l.map (wrapItem m ops) from rfl, splitI_append, ih,
      show i :: l = [i] ++ l from rfl, splitI_append]
    cases i <;> rfl

theorem stepD_eq (m t : ℕ) (fr : FrameD) :
    stepD m t fr = ((splitI (bstepI m t fr.V₁ fr.cs fr.a).1).1.map (wrapD m fr.wr),
      (splitI (bstepI m t fr.V₁ fr.cs fr.a).1).2.map
        fun ch => (ch.V₁, ch.cs, ch.a, ch.wr ++ fr.wr)) := by
  rw [← splitI_wrap]
  rfl

/-- The last branch of `dlI`: the big colour classes `C₂` of cells and `C₁` of points of the
colouring `f`. -/
def sp_dlBigI (m t k : ℕ) (V₁' : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (D : List ℕ)
    (f : ℕ → ℕ → ℕ) : List Item × ℕ :=
  let col₂ := ((List.range k).map fun j => f (m + j) (m + j)).toArray
  let C₂ := bigL (List.range k) (get col₂) (2 * k / 3)
  let colP := ((List.range m).map fun y => f y y).toArray
  let C₁ := bigL V₁' (get colP) t
  if C₁ = [] then
    ([.inl (addPieceD m D (partD colP (colBlkD m V₁' colP)))], 0)
  else if constRectL C₁ C₂ (Coherent.get2 (rectArr m k f)) then
    let js := (List.range k).filter fun j => j ∉ C₂
    ([shrinkI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp D]], 0)
  else cohI m t k cs D (diffD V₁' C₁) C₁ C₂ f

/-- `dlI` after a dominant colour of the first individualization. -/
def sp_dlSkelI (m t : ℕ) (V₁' : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (d : ℕ)
    (wl : Array ℕ) (xd D : List ℕ) : List Item × ℕ :=
  let k := cs.length
  let W2 := (Coherent.wlA 2 (V₁'.length + k) (sqCodeArr V₁' k a (skelArrD wl d k xd))).1
  let f := fA (offsArr (m + k)) (cQArr m V₁' k W2)
  let col₂ := ((List.range k).map fun j => f (m + j) (m + j)).toArray
  if allSmallL (List.range k) (get col₂) (2 * k / 3) then
    let js := pickSideD V₁' k a (selThirdL (List.range k) (get col₂))
    ([shrinkI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp D]], 0)
  else sp_dlBigI m t k V₁' cs a D f

theorem sp_dlI_eq (m t : ℕ) (V₁ V₁' : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (d : ℕ)
    (wl : Array ℕ) (xd : List ℕ) :
    dlI m t V₁ V₁' cs a d wl xd =
      match Coherent.domA
          (Coherent.col1A wl (Coherent.pwTab d cs.length) d cs.length xd.length xd.toArray)
          (2 * cs.length / 3) with
      | none =>
        let js := pickSideD V₁' cs.length a (selThirdL (List.range cs.length)
          (get (Coherent.col1A wl (Coherent.pwTab d cs.length) d cs.length xd.length
            xd.toArray).toArray))
        ([shrinkI cs.length V₁' (subCells cs js) (restrictRel m cs.length a js)
          [pieceOp (diffD V₁ V₁')]], 0)
      | some _ => sp_dlSkelI m t V₁' cs a d wl xd (diffD V₁ V₁') := by
  rfl

/-- The `d`-ary branch of `bstepI`. -/
def sp_daryI (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (d₁ : ℕ) :
    List Item × ℕ :=
  let k := cs.length
  let V₁' := tfDegD V₁ k a d₁
  let d := arity k (sOf k d₁) V₁'.length
  let col := daryArr k d (V₁'.map (fOfD k a d₁))
  let S := bigTwinsD k d col
  if S ≠ [] then
    let js := pickSideD V₁' k a S
    ([recI k V₁' (subCells cs js) (restrictRel m k a js) [pieceOp (diffD V₁ V₁')]], 0)
  else
    let wl := (Coherent.wlA d k col).1
    let xs := goodList wl d k (2 * k / 3)
    let r := xs.map (dlI m t V₁ V₁' cs a d wl)
    (r.flatMap Prod.fst, xs.length + (r.map Prod.snd).sum)

theorem sp_bstepI_eq (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a : Array Bool) :
    bstepI m t V₁ cs a =
      match optMin (bigDegsD t V₁ cs.length a) with
      | none => ([.inl (partD (twinColD m V₁ cs.length a) (twinBlkD m V₁ cs.length a))], 0)
      | some d₁ =>
        if (tfDegD V₁ cs.length a d₁).length = cs.length.choose (sOf cs.length d₁) then
          ([.inl (johnD (tfDegD V₁ cs.length a d₁) cs (sOf cs.length d₁)
            (fArrD m cs.length a d₁))], 0)
        else if IsBase t cs.length then
          ((List.range cs.length).permutations'.map fun js =>
            .inl (partD (nbrCodeArrD m cs.length a js)
              (colBlkD m V₁ (nbrCodeArrD m cs.length a js))),
            (List.range cs.length).permutations'.length)
        else sp_daryI m t V₁ cs a d₁ := by
  rfl

end Split

/-! ### Small programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Concatenate a list of lists. -/
def sp_flattenProg {t : Ty} (ls : var (.list (.list t))) : Prog S rec var (.list t) :=
  .bind (.op1 .reverse ls) fun rr => .bind (.op0 .nil) fun nil =>
  .foldList rr nil fun acc row => .op2 .append row acc

/-- One step of `x / 3`: the state `(quotient, remainder)`. -/
def sp_div3Step (st : var (.prod .nat .nat)) : Prog S rec var (.prod .nat .nat) :=
  .bind (.op1 .fst st) fun q => .bind (.op1 .snd st) fun r =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq r two) fun full =>
  .ite full
    (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add q one) fun q' =>
      .bind (.op0 (.natLit 0)) fun z => .op2 .pair q' z)
    (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add r one) fun r' => .op2 .pair q r')

/-- `x / 3`. -/
def sp_div3Prog (x : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .range x) fun rx => .bind (.op0 (.natLit 0)) fun z =>
  .bind (.op2 .pair z z) fun st₀ =>
  .bind (.foldList rx st₀ fun st _ => sp_div3Step st) fun st => .op1 .fst st

/-- The points of `V` not in `V'` (`diffD`). -/
def sp_diffProg (V V' : var (.list .nat)) : Prog S rec var (.list .nat) :=
  Toolkit.filterList V fun x => .bind (SoJProg.memProg x V') fun b => .op1 .not b

/-- The cells with the listed indices (`subCells`). -/
def sp_subCellsProg (cs : var (.list (.list .nat))) (js : var (.list .nat)) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .arrayOfList cs) fun ca => mapList js fun j => .op2 .arrayGet ca j

/-- The relation restricted to the listed cells (`restrictRel`), with the row offsets
`offs` of `a`. -/
def sp_restrictRelProg (m : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (js : var (.list .nat)) : Prog S rec var (.array .bool) :=
  .bind (.op1 .range m) fun xs =>
  .bind (mapList xs fun x => mapList js fun j => relAtProg offs a x j) fun rows =>
  .bind (sp_flattenProg rows) fun l => .op1 .arrayOfList l

/-- A piece (`pieceOp`). -/
def sp_pieceProg (D : var (.list .nat)) : Prog S rec var wrapTy :=
  .bind (.op0 (.boolLit false)) fun f => .bind emptyNatArrProg fun e =>
  .bind (.op2 .pair D e) fun De => .op2 .pair f De

/-- A frame from its fields. -/
def sp_frameProg (V : var (.list .nat)) (cs : var (.list (.list .nat))) (a : var (.array .bool))
    (ops : var (.list wrapTy)) : Prog S rec var frameTy :=
  .bind (.op2 .pair a ops) fun ao => .bind (.op2 .pair cs ao) fun cao => .op2 .pair V cao

/-- A leaf as a split pair. -/
def sp_leafPair (o : var outTy) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op0 .nil) fun nf => .bind (.op0 .nil) fun nl => .bind (.op2 .cons o nl) fun l =>
  .op2 .pair l nf

/-- A frame as a split pair. -/
def sp_framePair (fr : var frameTy) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op0 .nil) fun nf => .bind (.op0 .nil) fun nl => .bind (.op2 .cons fr nf) fun l =>
  .op2 .pair nl l

/-- The guarded call `recI`, as a split pair. -/
def sp_recIProg (k : var .nat) (V : var (.list .nat)) (cs : var (.list (.list .nat)))
    (a : var (.array .bool)) (ops : var (.list wrapTy)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op1 .length cs) fun n => .bind (.op2 .natLt n k) fun lt =>
  .ite lt (.bind (sp_frameProg V cs a ops) fun fr => sp_framePair fr)
    (.bind noneProg fun o => sp_leafPair o)

/-- The guarded call `shrinkI`, as a split pair. -/
def sp_shrinkIProg (k : var .nat) (V : var (.list .nat)) (cs : var (.list (.list .nat)))
    (a : var (.array .bool)) (ops : var (.list wrapTy)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op1 .length cs) fun n => .bind (.op2 .add n n) fun n2 => .bind (.op2 .add n2 n) fun n3 =>
  .bind (.op2 .add k k) fun k2 => .bind (.op2 .natLt k2 n3) fun big =>
  .bind (.op1 .not big) fun small => .bind (.op2 .natLt n k) fun lt =>
  .bind (.op2 .and small lt) fun ok =>
  .ite ok (.bind (sp_frameProg V cs a ops) fun fr => sp_framePair fr)
    (.bind noneProg fun o => sp_leafPair o)

/-- One wrapper operation on leaf data (`opD`). -/
def sp_opProg (m : var .nat) (o : var outTy) (op : var wrapTy) : Prog S rec var outTy :=
  .bind (.op1 .fst op) fun b => .bind (.op1 .snd op) fun Dr =>
  .bind (.op1 .fst Dr) fun D => .bind (.op1 .snd Dr) fun row =>
  .ite b (extendOutProg m D row o) (addPieceProg m D o)

/-- The wrapper operations on leaf data (`wrapD`). -/
def sp_wrapDProg (m : var .nat) (ops : var (.list wrapTy)) (o : var outTy) :
    Prog S rec var outTy :=
  .foldList ops o fun o op => sp_opProg m o op

/-- Append wrapper operations to a frame. -/
def sp_rewrapProg (ops : var (.list wrapTy)) (fr : var frameTy) : Prog S rec var frameTy :=
  .bind (.op1 .fst fr) fun V => .bind (.op1 .snd fr) fun r₁ =>
  .bind (.op1 .fst r₁) fun cs => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun a => .bind (.op1 .snd r₂) fun ops₀ =>
  .bind (.op2 .append ops₀ ops) fun ops' => sp_frameProg V cs a ops'

end Prog


/-! ### The programs of one level -/

section Prog2

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `idxQ`: the index in `V₁' ⊔ V₂` of a point `u < m` or of the cell `u - m`. -/
def sp_idxQProg (m k : var .nat) (ps : var (.list .nat)) (u : var .nat) :
    Prog S rec var (.option .nat) :=
  .bind (.op2 .natLt u m) fun lt =>
  .ite lt
    (.bind (SoJProg.memProg u ps) fun mem =>
      .ite mem (.bind (Graph.idxOfProg ps u) fun i => .op1 .some i) (.op0 .none))
    (.bind (.op2 .add m k) fun mk => .bind (.op2 .natLt u mk) fun lt₂ =>
      .ite lt₂
        (.bind (.op1 .length ps) fun p => .bind (.op2 .sub u m) fun j =>
          .bind (.op2 .add p j) fun r => .op1 .some r)
        (.op0 .none))

/-- `cQd`, with the row offsets `offs₂` of `W2`. -/
def sp_cQdProg (m k : var .nat) (ps : var (.list .nat)) (offs₂ W2 : var (.array .nat))
    (u v : var .nat) : Prog S rec var .nat :=
  .bind (sp_idxQProg m k ps u) fun iu => .bind (sp_idxQProg m k ps v) fun iv =>
  .caseOption iu (.op0 (.natLit 0)) fun i => .caseOption iv (.op0 (.natLit 0)) fun j =>
    .bind (.op2 .arrayGet offs₂ j) fun o => .bind (.op2 .add o i) fun idx =>
    .op2 .arrayGet W2 idx

/-- `cQArr`. -/
def sp_cQArrProg (m k : var .nat) (ps : var (.list .nat)) (W2 : var (.array .nat)) :
    Prog S rec var (.array .nat) :=
  .bind (.op1 .length ps) fun p => .bind (.op2 .add p k) fun N' =>
  .bind (offsetsProg N' N') fun offs₂ =>
  .bind (.op2 .add m k) fun N => .bind (.op1 .range N) fun rN =>
  .bind (mapList rN fun u => mapList rN fun v => sp_cQdProg m k ps offs₂ W2 u v) fun rows =>
  .bind (sp_flattenProg rows) fun l => .op1 .arrayOfList l

/-- `skelArrD`, with the table `pw = pwTab d k` and `rd = [0, d)`. -/
def sp_skelArrProg (wl : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rd : var (.list .nat)) (k : var .nat) (xd : var (.list .nat)) :
    Prog S rec var (.array .nat) :=
  .bind (.op1 .length xd) fun l => .bind (.op1 .arrayOfList xd) fun xA =>
  .bind (.op1 .range k) fun rk =>
  .bind (mapList rk fun j => mapList rk fun i =>
    .bind (Coherent.pad2Prog pw rd l xA i j) fun c => .op2 .arrayGet wl c) fun rows =>
  .bind (sp_flattenProg rows) fun ls => .op1 .arrayOfList ls

/-- The base-case test `IsBase t k`. -/
def sp_isBaseProg (t k : var .nat) : Prog S rec var .bool :=
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .add t t) fun t₂ =>
  .bind (clogProg two t₂) fun L => .bind (Coherent.mulNProg L L) fun L₂ =>
  .bind (Coherent.mulNProg L₂ L) fun L₃ => .bind (.op0 (.natLit 27)) fun c =>
  .bind (Coherent.mulNProg c L₃) fun r => .bind (Coherent.mulNProg k k) fun k₂ =>
  .bind (.op2 .natLt r k₂) fun big => .op1 .not big

/-- The colours `f (o + j) (o + j)` for `j < r`, as an array. -/
def sp_diagProg (offs c : var (.array .nat)) (o r : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range r) fun rr =>
  .bind (mapList rr fun j => .bind (.op2 .add o j) fun u => csColProg offs c u u) fun l =>
  .op1 .arrayOfList l

/-- `rectArr`. -/
def sp_rectProg (offs c : var (.array .nat)) (m k : var .nat) :
    Prog S rec var (.array (.array .nat)) :=
  .bind (.op1 .range m) fun rm => .bind (.op1 .range k) fun rk =>
  .bind (mapList rm fun y =>
    .bind (mapList rk fun j => .bind (.op2 .add m j) fun v => csColProg offs c y v) fun l =>
    .op1 .arrayOfList l) fun rows => .op1 .arrayOfList rows

/-- `cellUD`. -/
def sp_cellUDProg (m k : var .nat) (ca : var (.array (.list .nat))) (l : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .add m k) fun mk =>
  .bind (Toolkit.filterList l fun i =>
    .bind (.op2 .natLt i m) fun lt => .bind (.op1 .not lt) fun ge =>
    .bind (.op2 .natLt i mk) fun lt₂ => .op2 .and ge lt₂) fun l' =>
  .bind (mapList l' fun i => .bind (.op2 .sub i m) fun j => .op2 .arrayGet ca j) fun rows =>
  .bind (sp_flattenProg rows) fun u => .bind (.op1 .range m) fun rm =>
  Toolkit.filterList rm fun y => SoJProg.memProg y u

/-- `dedupCellsD`. -/
def sp_dedupProg (m : var .nat) (ls : var (.list (.list .nat))) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (.op0 .nil) fun nil =>
  .foldList ls nil fun acc l =>
    .bind (anyList acc fun l' => setEqProg m l l') fun dup =>
    .ite dup (.ret acc)
      (.bind (.op0 .nil) fun nl => .bind (.op2 .cons l nl) fun sl => .op2 .append acc sl)

/-- The entry of `bipRelX` for a point `x` and a cell. -/
def sp_bipEntryProg (m k N g x : var .nat) (ca : var (.array (.list .nat)))
    (offs c : var (.array .nat)) (W₂ : var (.list (.list .nat))) (cell : var (.list .nat)) :
    Prog S rec var .bool :=
  anyList W₂ fun l =>
    .bind (sp_cellUDProg m k ca l) fun cu => .bind (setEqProg m cu cell) fun e =>
    .bind (anyList l fun y =>
      .bind (.op2 .natLt y N) fun lt => .bind (csColProg offs c x y) fun v =>
      .bind (.op2 .natEq v g) fun eq => .op2 .and lt eq) fun hit => .op2 .and e hit

/-- `bipRelX`. -/
def sp_bipRelXProg (m k N g : var .nat) (ca : var (.array (.list .nat)))
    (offs c : var (.array .nat)) (W₂ cells : var (.list (.list .nat))) :
    Prog S rec var (.array .bool) :=
  .bind (.op1 .range m) fun rm =>
  .bind (mapList rm fun x => mapList cells fun cell =>
    sp_bipEntryProg m k N g x ca offs c W₂ cell) fun rows =>
  .bind (sp_flattenProg rows) fun l => .op1 .arrayOfList l

/-- Concatenate a list of split pairs. -/
def sp_catProg (prs : var (.list (.prod (.list outTy) (.list frameTy)))) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (mapList prs fun pr => .op1 .fst pr) fun ls => .bind (sp_flattenProg ls) fun l =>
  .bind (mapList prs fun pr => .op1 .snd pr) fun fs => .bind (sp_flattenProg fs) fun f =>
  .op2 .pair l f

/-- The bipartite branch of `contI`: the cells, the relation and the guarded call. -/
def sp_contBigProg (m k : var .nat) (ca : var (.array (.list .nat))) (offs c : var (.array .nat))
    (W₂ : var (.list (.list .nat))) (g : var .nat) (W DW D₁ D₂ : var (.list .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (mapList W₂ fun l => sp_cellUDProg m k ca l) fun us =>
  .bind (sp_dedupProg m us) fun cells => .bind (.op2 .add m k) fun N =>
  .bind (sp_bipRelXProg m k N g ca offs c W₂ cells) fun rel =>
  .bind (sp_pieceProg DW) fun o₃ => .bind (sp_pieceProg D₂) fun o₂ =>
  .bind (sp_pieceProg D₁) fun o₁ => .bind (.op0 .nil) fun nl =>
  .bind (.op2 .cons o₁ nl) fun l₁ => .bind (.op2 .cons o₂ l₁) fun l₂ =>
  .bind (.op2 .cons o₃ l₂) fun ops => sp_shrinkIProg k W cells rel ops

/-- The branch of `contI` with few ideal points: a partition leaf. -/
def sp_contSmallProg (m : var .nat) (W DW D₁ D₂ : var (.list .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind emptyNatArrProg fun e => .bind (colBlkProg m W e) fun blk =>
  .bind (partProg e blk) fun p => .bind (addPieceProg m DW p) fun p₃ =>
  .bind (addPieceProg m D₂ p₃) fun p₂ => .bind (addPieceProg m D₁ p₂) fun p₁ =>
  sp_leafPair p₁

/-- `contI` at a `bip` leaf `(W₁, W₂, g)`. -/
def sp_contBipProg (m t k : var .nat) (ca : var (.array (.list .nat)))
    (D₁ D₂ C₁ : var (.list .nat)) (offs c : var (.array .nat)) (W₁ : var (.list .nat))
    (W₂ : var (.list (.list .nat))) (g : var .nat) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op1 .range m) fun rm =>
  .bind (Toolkit.filterList rm fun y => SoJProg.memProg y W₁) fun W =>
  .bind (sp_diffProg C₁ W) fun DW =>
  .bind (.op1 .length W) fun lw => .bind (.op2 .natLt t lw) fun gt =>
  .ite gt (sp_contBigProg m k ca offs c W₂ g W DW D₁ D₂) (sp_contSmallProg m W DW D₁ D₂)

/-- **`cohCont` on data** (`contI`), as a split pair. -/
def sp_contProg (m t k : var .nat) (ca : var (.array (.list .nat)))
    (D₁ D₂ C₁ : var (.list .nat)) (offs c : var (.array .nat)) (o : var (.option cohLeafTy)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .caseOption o (.bind noneProg fun n => sp_leafPair n) fun lf =>
  .bind (.op1 .fst lf) fun tag => .bind (.op1 .snd lf) fun r =>
  .bind (.op1 .fst r) fun cb => .bind (.op1 .snd r) fun wg =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .natEq tag z) fun is0 =>
  .ite is0
    (.bind (.op1 .fst cb) fun col => .bind (.op1 .snd cb) fun blk =>
      .bind (partProg col blk) fun p => .bind (addPieceProg m D₂ p) fun p₂ =>
      .bind (addPieceProg m D₁ p₂) fun p₁ => sp_leafPair p₁)
    (.bind (.op1 .fst wg) fun W₁ => .bind (.op1 .snd wg) fun r₂ =>
      .bind (.op1 .fst r₂) fun W₂ => .bind (.op1 .snd r₂) fun g =>
      sp_contBipProg m t k ca D₁ D₂ C₁ offs c W₁ W₂ g)

/-- **The `cohSoj` level on data** (`cohI`), as a split pair, for the colouring `fA offs c`
on all points and cells. -/
def sp_cohIProg (m t k : var .nat) (ca : var (.array (.list .nat))) (D₁ D₂ C₁ C₂ : var (.list .nat))
    (offs c : var (.array .nat)) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op2 .add m k) fun N =>
  .bind (mapList C₂ fun j => .op2 .add m j) fun C₂' =>
  .bind (cohSojProg N c C₁ C₂') fun res =>
  .bind (.op1 .fst res) fun isNode => .bind (.op1 .snd res) fun r =>
  .bind (.op1 .fst r) fun opts => .bind (.op1 .snd r) fun leaves =>
  .ite isNode
    (.bind (mapList opts fun y => .bind (.op2 .arrayGet leaves y) fun o =>
      sp_contProg m t k ca D₁ D₂ C₁ offs c o) fun prs => sp_catProg prs)
    (.bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayGet leaves z) fun o =>
      sp_contProg m t k ca D₁ D₂ C₁ offs c o)

/-- A guarded call on the listed cells, as a split pair (`shrinkI` on `subCells`). -/
def sp_callProg (m k : var .nat) (V' : var (.list .nat)) (cs : var (.list (.list .nat)))
    (offsA : var (.array .nat)) (a : var (.array .bool)) (D js : var (.list .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (sp_subCellsProg cs js) fun cs' => .bind (sp_restrictRelProg m offsA a js) fun a' =>
  .bind (sp_pieceProg D) fun op => .bind (.op0 .nil) fun nl => .bind (.op2 .cons op nl) fun ops =>
  sp_shrinkIProg k V' cs' a' ops

/-- A guarded call on the cells chosen by `selThird` and Exercise 5.5's side. -/
def sp_selCallProg (m k : var .nat) (V' : var (.list .nat)) (cs : var (.list (.list .nat)))
    (offsA : var (.array .nat)) (a : var (.array .bool)) (D rk : var (.list .nat))
    (colA : var (.array .nat)) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (selThirdProg rk colA) fun sel => .bind (pickSideProg V' k a sel) fun js =>
  sp_callProg m k V' cs offsA a D js

/-- The last branch of `dlI`: the big colour classes `C₂` of cells and `C₁` of points. -/
def sp_dlBigProg (m t k t₂ : var .nat) (V₁' : var (.list .nat)) (cs : var (.list (.list .nat)))
    (ca : var (.array (.list .nat))) (a : var (.array .bool)) (offsA : var (.array .nat))
    (rk D : var (.list .nat)) (offsN cQA col₂ : var (.array .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (bigProg rk col₂ t₂) fun C₂ =>
  .bind (.op0 (.natLit 0)) fun z => .bind (sp_diagProg offsN cQA z m) fun colP =>
  .bind (bigProg V₁' colP t) fun C₁ =>
  .caseList C₁
    (.bind (colBlkProg m V₁' colP) fun blk => .bind (partProg colP blk) fun p =>
      .bind (addPieceProg m D p) fun p' => sp_leafPair p')
    fun _ _ =>
      .bind (sp_rectProg offsN cQA m k) fun rect =>
      .bind (constRectProg C₁ C₂ rect) fun cr =>
      .ite cr
        (.bind (Toolkit.filterList rk fun j =>
            .bind (SoJProg.memProg j C₂) fun b => .op1 .not b) fun js =>
          sp_callProg m k V₁' cs offsA a D js)
        (.bind (sp_diffProg V₁' C₁) fun D₂ =>
          sp_cohIProg m t k ca D D₂ C₁ C₂ offsN cQA)

/-- `dlI` after a dominant colour of the first individualization: the skeleton, its classical
refinement `W2` and the colouring `cQ` of points and cells. -/
def sp_dlSkelProg (m t k t₂ : var .nat) (V₁' : var (.list .nat))
    (cs : var (.list (.list .nat))) (ca : var (.array (.list .nat))) (a : var (.array .bool))
    (offsA wl : var (.array .nat)) (pw : var (.array (.array .nat)))
    (rd rk D xd : var (.list .nat)) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (sp_skelArrProg wl pw rd k xd) fun Y =>
  .bind (cohProg V₁' k a Y) fun W2p => .bind (.op1 .fst W2p) fun W2 =>
  .bind (sp_cQArrProg m k V₁' W2) fun cQA =>
  .bind (.op2 .add m k) fun N => .bind (csOffsProg N) fun offsN =>
  .bind (sp_diagProg offsN cQA m k) fun col₂ =>
  .bind (allSmallProg rk col₂ t₂) fun sm =>
  .ite sm (sp_selCallProg m k V₁' cs offsA a D rk col₂)
    (sp_dlBigProg m t k t₂ V₁' cs ca a offsA rk D offsN cQA col₂)

/-- **`dlCont` on data** (`dlI`), as a split pair, after the choice `xd`. -/
def sp_dlProg (m t k t₂ : var .nat) (V₁' : var (.list .nat)) (cs : var (.list (.list .nat)))
    (ca : var (.array (.list .nat))) (a : var (.array .bool)) (offsA wl : var (.array .nat))
    (pw : var (.array (.array .nat))) (rd rk D : var (.list .nat)) (xd : var (.list .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op1 .length xd) fun l => .bind (.op1 .arrayOfList xd) fun xA =>
  .bind (Coherent.col1Prog wl pw rd rk l xA) fun col1 =>
  .bind (.op1 .arrayOfList col1) fun c1A => .bind (.op1 .length col1) fun n1 =>
  .bind (.op1 .range n1) fun rn => .bind (Coherent.domProg col1 c1A rn t₂) fun dm =>
  .caseOption dm (sp_selCallProg m k V₁' cs offsA a D rk c1A)
    fun _ => sp_dlSkelProg m t k t₂ V₁' cs ca a offsA wl pw rd rk D xd

/-- The base case, as a split pair. -/
def sp_baseProg (m k : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (V₁ : var (.list .nat)) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (enumsProg k) fun es =>
  .bind (mapList es fun js => .bind (baseLeafProg m offs a V₁ js) fun cb =>
    .bind (.op1 .fst cb) fun col => .bind (.op1 .snd cb) fun blk => partProg col blk) fun ls =>
  .bind (.op0 .nil) fun nf => .op2 .pair ls nf

/-- The `d`-ary step with a big twin class: a guarded call on one side. -/
def sp_daryRecProg (m k : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (V₁' : var (.list .nat)) (cs : var (.list (.list .nat))) (D S' : var (.list .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (pickSideProg V₁' k a S') fun js =>
  .bind (sp_subCellsProg cs js) fun cs' => .bind (sp_restrictRelProg m offs a js) fun a' =>
  .bind (sp_pieceProg D) fun op => .bind (.op0 .nil) fun nl =>
  .bind (.op2 .cons op nl) fun ops => sp_recIProg k V₁' cs' a' ops

/-- The `d`-ary step without big twin classes: the Design Lemma options, and `dlI` at each. -/
def sp_daryDLProg (m t k d : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (V₁' : var (.list .nat)) (cs : var (.list (.list .nat))) (D : var (.list .nat))
    (hs : var (.list (.list .nat))) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (daryWLProg k d hs) fun wp => .bind (.op1 .fst wp) fun wl =>
  .bind (.op2 .add k k) fun k₂ => .bind (sp_div3Prog k₂) fun t₂ =>
  .bind (goodListProg wl d k t₂) fun xs =>
  .bind (.op1 .arrayOfList cs) fun ca => .bind (.op1 .range d) fun rd =>
  .bind (.op1 .range k) fun rk => .bind (Coherent.pwTabProg k rd rk) fun pw =>
  .bind (mapList xs fun xd => sp_dlProg m t k t₂ V₁' cs ca a offs wl pw rd rk D xd)
  fun rs => sp_catProg rs

/-- The `d`-ary step and its continuations, as a split pair. -/
def sp_daryProg (m t k : var .nat) (offs : var (.array .nat)) (a : var (.array .bool))
    (V₁ : var (.list .nat)) (cs : var (.list (.list .nat))) (d₁ : var .nat) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (tfDegProg offs a k V₁ d₁) fun V₁' => .bind (sOfProg k d₁) fun s =>
  .bind (.op1 .length V₁') fun n₁ => .bind (arityProg k s n₁) fun d =>
  .bind (mapList V₁' fun x => fOfProg offs a k d₁ x) fun hs =>
  .bind (daryArrProg k d hs) fun col => .bind (bigTwinsProg k d col) fun S' =>
  .bind (sp_diffProg V₁ V₁') fun D =>
  .caseList S' (sp_daryDLProg m t k d offs a V₁' cs D hs)
    fun _ _ => sp_daryRecProg m k offs a V₁' cs D S'

/-- **One level of `bsoj` on data** (`bstepI`), as a split pair. -/
def sp_bstepProg (m t : var .nat) (V₁ : var (.list .nat)) (cs : var (.list (.list .nat)))
    (a : var (.array .bool)) : Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op1 .length cs) fun k => .bind (offsetsProg m k) fun offs =>
  .bind (minBigDegProg t offs a k V₁) fun od =>
  .caseOption od
    (.bind (twinPartProg m k a V₁) fun cb => .bind (.op1 .fst cb) fun col =>
      .bind (.op1 .snd cb) fun blk => .bind (partProg col blk) fun p => sp_leafPair p)
    fun d₁ =>
      .bind (johnsonTestProg offs a k V₁ d₁) fun jt =>
      .ite jt
        (.bind (johnsonLeafProg m offs a k V₁ d₁) fun jl => .bind (.op1 .fst jl) fun V0 =>
          .bind (.op1 .snd jl) fun sf => .bind (.op1 .fst sf) fun s =>
          .bind (.op1 .snd sf) fun fA' => .bind (johnProg V0 cs s fA') fun j => sp_leafPair j)
        (.bind (sp_isBaseProg t k) fun ib =>
          .ite ib (sp_baseProg m k offs a V₁) (sp_daryProg m t k offs a V₁ cs d₁))

/-- **One step of a frame** (`stepD`): one level of `bsoj`, the leaves wrapped and the
wrapper appended to the child frames. No backend calls, no `.recur`. -/
def stepProg (m t : var .nat) (fr : var frameTy) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (.op1 .fst fr) fun V₁ => .bind (.op1 .snd fr) fun r₁ =>
  .bind (.op1 .fst r₁) fun cs => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun a => .bind (.op1 .snd r₂) fun wr =>
  .bind (sp_bstepProg m t V₁ cs a) fun pr => .bind (.op1 .fst pr) fun ls =>
  .bind (.op1 .snd pr) fun fs =>
  .bind (mapList ls fun o => sp_wrapDProg m wr o) fun ls' =>
  .bind (mapList fs fun ch => sp_rewrapProg wr ch) fun fs' => .op2 .pair ls' fs'

end Prog2

/-! ### Specifications of the small programs -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem sp_sum_len_add_two {α : Type*} (ls : List (List α)) :
    (ls.map fun x => x.length + 1 + 1).sum = (ls.map List.length).sum + 2 * ls.length := by
  induction ls with
  | nil => rfl
  | cons r ls ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem RunsWithin.sp_flattenProg {t : Ty} (ls : List (List t.denote)) :
    RunsWithin X body (SoJTree.sp_flattenProg ls) ls.flatten
      (3 * ls.length + (ls.map List.length).sum + 3) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .list t) (b' := .list t)
    (f := fun acc row => Prog.op2 .append row acc) (F := fun acc row => row ++ acc)
    (cf := fun row => row.length + 1) ls.reverse []
    fun acc row _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  rw [foldl_append_rev] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head, List.map_reverse, List.sum_reverse]
    rw [sp_sum_len_add_two]
    omega

theorem sp_div3_foldl (x : ℕ) :
    (List.range x).foldl (fun st (_ : ℕ) => if st.2 = 2 then (st.1 + 1, 0) else (st.1, st.2 + 1))
      (0, 0) = (x / 3, x % 3) := by
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs with h
    · rw [Prod.mk.injEq]
      omega
    · rw [Prod.mk.injEq]
      omega

theorem RunsWithin.sp_div3Step (q r : ℕ) :
    RunsWithin X body (SoJTree.sp_div3Step (q, r))
      (if (q, r).2 = 2 then ((q, r).1 + 1, 0) else ((q, r).1, (q, r).2 + 1)) 10 := by
  by_cases h : r = 2
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (r == 2) = true by simp [h]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc => simp [Prim.cost]
  · rw [ite_eq_right h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (r == 2) = false by simp [h]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc => simp [Prim.cost]

theorem RunsWithin.sp_div3Prog (x : ℕ) :
    RunsWithin X body (SoJTree.sp_div3Prog x) (x / 3) (12 * x + 5) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .nat) (f := fun st _ => SoJTree.sp_div3Step st)
    (F := fun st (_ : ℕ) => if st.2 = 2 then (st.1 + 1, 0) else (st.1, st.2 + 1))
    (cf := fun _ => 10) (List.range x) (0, 0) fun st _ _ => by
      obtain ⟨q, r⟩ := st
      exact RunsWithin.sp_div3Step q r
  rw [sp_div3_foldl, sum_map_const, List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head]
    omega

theorem RunsWithin.sp_diffProg (V V' : List ℕ) :
    RunsWithin X body (SoJTree.sp_diffProg V V') (diffD V V')
      (V.length * (3 * V'.length + 6) + 3) := by
  refine (Toolkit.RunsWithin.filterList (a' := .nat) (c := 3 * V'.length + 2)
    (P := fun x => decide (x ∉ V')) fun x _ => ?_).of_eq ?_ |>.mono ?_
  · refine RunsWithin.bind_le (SoJProg.RunsWithin.memProg x V')
      (RunsWithin.prim_le (by simp [Prim.eval]) le_rfl) (by simp [Prim.cost])
  · rfl
  · nlinarith

theorem RunsWithin.sp_subCellsProg (cs : List (List ℕ)) (js : List ℕ) :
    RunsWithin X body (SoJTree.sp_subCellsProg cs js) (subCells cs js)
      (cs.length + js.length * 4 + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.mapList_le (a' := .nat) (b' := .list .nat) (c := 1)
      (F := fun j => cs.getD j []) fun j _ => RunsWithin.prim_le
        (by simp [Prim.eval, Ty.default, Array.getD_eq_getD_getElem?,
          List.getD_eq_getElem?_getD]) le_rfl)
  case hc =>
    simp only [Prim.cost, Args.head]
    omega

theorem RunsWithin.sp_restrictRelProg {m k : ℕ} {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) (js : List ℕ) :
    RunsWithin X body (SoJTree.sp_restrictRelProg m offs a js) (restrictRel m k a js)
      (m * (js.length * 6 + 5) + 2 * m * (js.length + 3) + 8) := by
  have hrows : ∀ x ∈ List.range m, RunsWithin X body
      (Programs.mapList (a' := .nat) (b' := .bool) js fun j => relAtProg offs a x j)
      (js.map fun j => relAt k a x j) (js.length * 6 + 2) := by
    intro x hx
    refine RunsWithin.mapList_le (a' := .nat) (b' := .bool) (c := 3) fun j _ =>
      (RunsWithin.relAtProg offs a x j).of_eq ?_
    rw [relAt, hoffs x (List.mem_range.1 hx)]
  have hfl := RunsWithin.sp_flattenProg (X := X) (body := body) (t := .bool)
    ((List.range m).map fun x => js.map fun j => relAt k a x j)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le hrows)
    run_step hfl
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have hsum : (((List.range m).map fun x => js.map fun j => relAt k a x j).map
        List.length).sum = m * js.length := by
      simp [List.map_map, Function.comp_def]
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map, hsum,
      List.length_flatten]
    ring_nf
    omega

theorem RunsWithin.sp_pieceProg (D : List ℕ) :
    RunsWithin X body (SoJTree.sp_pieceProg D) (pieceOp D) 5 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step RunsWithin.emptyNatArrProg
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.sp_frameProg (V : List ℕ) (cs : List (List ℕ)) (a : Array Bool)
    (ops : List WrapOp) :
    RunsWithin X body (SoJTree.sp_frameProg V cs a ops) ((V, cs, a, ops) : FrameD) 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.sp_leafPair (o : OutD) :
    RunsWithin X body (SoJTree.sp_leafPair o) (splitI [.inl o]) 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.sp_framePair (fr : FrameD) :
    RunsWithin X body (SoJTree.sp_framePair fr) (splitI [.inr fr]) 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.sp_recIProg (k : ℕ) (V : List ℕ) (cs : List (List ℕ)) (a : Array Bool)
    (ops : List WrapOp) :
    RunsWithin X body (SoJTree.sp_recIProg k V cs a ops) (splitI [recI k V cs a ops])
      (cs.length + 22) := by
  unfold recI
  by_cases h : cs.length < k
  · rw [ite_eq_left h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show decide (cs.length < k) = true by simp [h]) _
      run_step (RunsWithin.sp_frameProg _ _ _ _)
      exact RunsWithin.sp_framePair _
    case hc => simp only [Prim.cost, Args.head]; omega
  · rw [ite_eq_right h]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show decide (cs.length < k) = false by simp [h]) _
      run_step RunsWithin.noneProg
      exact RunsWithin.sp_leafPair _
    case hc => simp only [Prim.cost, Args.head]; omega

theorem RunsWithin.sp_shrinkIProg (k : ℕ) (V : List ℕ) (cs : List (List ℕ)) (a : Array Bool)
    (ops : List WrapOp) :
    RunsWithin X body (SoJTree.sp_shrinkIProg k V cs a ops) (splitI [shrinkI k V cs a ops])
      (cs.length + 28) := by
  unfold shrinkI
  have hb : (!decide (k + k < cs.length + cs.length + cs.length) && decide (cs.length < k)) =
      decide (3 * cs.length ≤ 2 * k ∧ cs.length < k) := by
    by_cases h1 : 3 * cs.length ≤ 2 * k <;> by_cases h2 : cs.length < k <;> simp [h1, h2] <;> omega
  by_cases h : 3 * cs.length ≤ 2 * k ∧ cs.length < k
  · rw [ite_eq_left h]
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
      run_with RunsWithin.ite_pos (by simp only [Prim.eval]; rw [hb]; simp [h]) _
      run_step (RunsWithin.sp_frameProg _ _ _ _)
      exact RunsWithin.sp_framePair _
    case hc => simp only [Prim.cost, Args.head]; omega
  · rw [ite_eq_right h]
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
      run_with RunsWithin.ite_neg (by simp only [Prim.eval]; rw [hb]; simp [h]) _
      run_step RunsWithin.noneProg
      exact RunsWithin.sp_leafPair _
    case hc => simp only [Prim.cost, Args.head]; omega

/-- The cost of a wrapper operation on leaf data, for lists of at most `L` points. -/
def opCost (m L : ℕ) : ℕ := extendOutCost m L + addPieceCost m L + 5

theorem extendOutCost_mono (m : ℕ) {v v' : ℕ} (h : v ≤ v') :
    extendOutCost m v ≤ extendOutCost m v' := by
  unfold extendOutCost exBlkCost
  have : m * (3 * v + 9) ≤ m * (3 * v' + 9) := Nat.mul_le_mul_left _ (by omega)
  have : m * (3 * v + 6 + m * (3 * v + 9) + 3 * v + 12) ≤
      m * (3 * v' + 6 + m * (3 * v' + 9) + 3 * v' + 12) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem addPieceCost_mono (m : ℕ) {d d' : ℕ} (h : d ≤ d') :
    addPieceCost m d ≤ addPieceCost m d' := by
  unfold addPieceCost
  have : m * (6 * d + 15) ≤ m * (6 * d' + 15) := Nat.mul_le_mul_left _ (by omega)
  omega

theorem RunsWithin.sp_opProg (m : ℕ) (o : OutD) (op : WrapOp) {L : ℕ}
    (hL : op.2.1.length ≤ L) :
    RunsWithin X body (SoJTree.sp_opProg m o op) (opD m op o) (opCost m L) := by
  obtain ⟨b, D, row⟩ := op
  simp only at hL
  unfold opD
  cases b
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_false (RunsWithin.addPieceProg m D o)
    case hc =>
      simp only [Prim.cost, opCost]
      have := addPieceCost_mono m hL
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_true (RunsWithin.extendOutProg m D row o)
    case hc =>
      simp only [Prim.cost, opCost]
      have := extendOutCost_mono m hL
      omega

theorem RunsWithin.sp_wrapDProg (m : ℕ) (ops : List WrapOp) (o : OutD) {L : ℕ}
    (hL : ∀ op ∈ ops, op.2.1.length ≤ L) :
    RunsWithin X body (SoJTree.sp_wrapDProg m ops o) (wrapD m ops o)
      (ops.length * (opCost m L + 1)) :=
  (RunsWithin.foldList_inv (a' := wrapTy) (b' := outTy) (I := fun _ => True) (c := opCost m L)
    ops o
    (fun o' _ op hop => ⟨RunsWithin.sp_opProg m o' op (hL op hop), trivial⟩) trivial).1

theorem RunsWithin.sp_rewrapProg (ops : List WrapOp) (fr : FrameD) :
    RunsWithin X body (SoJTree.sp_rewrapProg ops fr) ((fr.V₁, fr.cs, fr.a, fr.wr ++ ops) : FrameD)
      (fr.wr.length + 10) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.sp_frameProg _ _ _ _
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, FrameD.wr]
    omega

end Specs

/-! ### Specifications: the refined colouring -/

section Specs2

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.sp_idxQProg (m k : ℕ) (ps : List ℕ) (u : ℕ) :
    RunsWithin X body (SoJTree.sp_idxQProg m k ps u) (idxQ m ps k u) (12 * ps.length + 20) := by
  unfold idxQ
  by_cases h1 : u < m
  · rw [ite_eq_left h1]
    by_cases h2 : u ∈ ps
    · rw [ite_eq_left h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show decide (u < m) = true by simp [h1]) _
        run_step (SoJProg.RunsWithin.memProg u ps)
        run_with RunsWithin.ite_pos (show decide (u ∈ ps) = true by simp [h2]) _
        run_step (Graph.RunsWithin.idxOfProg ps u)
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp only [Prim.cost]; omega
    · rw [ite_eq_right h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show decide (u < m) = true by simp [h1]) _
        run_step (SoJProg.RunsWithin.memProg u ps)
        run_with RunsWithin.ite_neg (show decide (u ∈ ps) = false by simp [h2]) _
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp only [Prim.cost]; omega
  · rw [ite_eq_right h1]
    by_cases h2 : u < m + k
    · rw [ite_eq_left h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show decide (u < m) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show decide (u < m + k) = true by simp [h2]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp only [Prim.cost, Args.head]; omega
    · rw [ite_eq_right h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show decide (u < m) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show decide (u < m + k) = false by simp [h2]) _
        exact RunsWithin.prim_le rfl le_rfl
      case hc => simp only [Prim.cost]; omega

theorem idxQ_lt {m k : ℕ} {ps : List ℕ} {u i : ℕ} (h : idxQ m ps k u = some i) :
    i < ps.length + k := by
  unfold idxQ at h
  split_ifs at h with h1 h2 h3
  · cases h
    have := List.idxOf_lt_length_iff.2 h2
    omega
  · cases h
    omega

theorem RunsWithin.sp_cQdProg (m k : ℕ) (ps : List ℕ) {offs₂ : Array ℕ}
    (hoffs : ∀ j < ps.length + k, get offs₂ j = j * (ps.length + k)) (W2 : Array ℕ) (u v : ℕ) :
    RunsWithin X body (SoJTree.sp_cQdProg m k ps offs₂ W2 u v) (cQd m ps k W2 u v)
      (24 * ps.length + 46) := by
  unfold cQd
  rcases hu : idxQ m ps k u with _ | i
  · apply RunsWithin.mono
    case h =>
      run_step (hu ▸ RunsWithin.sp_idxQProg m k ps u)
      run_step (RunsWithin.sp_idxQProg m k ps v)
      run_with RunsWithin.caseOption_none _
      exact RunsWithin.prim_le rfl le_rfl
    case hc => simp only [Prim.cost]; omega
  rcases hv : idxQ m ps k v with _ | j
  · apply RunsWithin.mono
    case h =>
      run_step (hu ▸ RunsWithin.sp_idxQProg m k ps u)
      run_step (hv ▸ RunsWithin.sp_idxQProg m k ps v)
      run_with RunsWithin.caseOption_some _
      run_with RunsWithin.caseOption_none _
      exact RunsWithin.prim_le rfl le_rfl
    case hc => simp only [Prim.cost]; omega
  have hj := idxQ_lt hv
  apply RunsWithin.mono
  case h =>
    run_step (hu ▸ RunsWithin.sp_idxQProg m k ps u)
    run_step (hv ▸ RunsWithin.sp_idxQProg m k ps v)
    run_with RunsWithin.caseOption_some _
    run_with RunsWithin.caseOption_some _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine RunsWithin.prim_le ?_ le_rfl
    simp only [Prim.eval, Ty.default]
    show W2.getD (get offs₂ j + i) 0 = get W2 (i + j * (ps.length + k))
    rw [hoffs j hj, get, Nat.add_comm]
  case hc => simp only [Prim.cost]; omega

/-- The cost of `sp_cQArrProg` for `p` points, `k` cells and `N = m + k`. -/
def cQArrCost (p k N : ℕ) : ℕ :=
  11 * (p + k) + N * (N * (24 * p + 49) + 5) + 2 * N * N + 4 * N + 20

theorem RunsWithin.sp_cQArrProg (m k : ℕ) (ps : List ℕ) (W2 : Array ℕ) :
    RunsWithin X body (SoJTree.sp_cQArrProg m k ps W2) (cQArr m ps k W2)
      (cQArrCost ps.length k (m + k)) := by
  have hoffs : ∀ j < ps.length + k,
      get ((List.range (ps.length + k)).map (· * (ps.length + k))).toArray j =
        j * (ps.length + k) := fun _ hj => get_offsets hj
  have hrows : ∀ u ∈ List.range (m + k), RunsWithin X body
      (Programs.mapList (a' := .nat) (b' := .nat) (List.range (m + k)) fun v =>
        SoJTree.sp_cQdProg m k ps ((List.range (ps.length + k)).map
          (· * (ps.length + k))).toArray W2 u v)
      ((List.range (m + k)).map fun v => cQd m ps k W2 u v)
      ((m + k) * (24 * ps.length + 49) + 2) := by
    intro u _
    exact (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 24 * ps.length + 46)
      fun v _ => RunsWithin.sp_cQdProg (X := X) (body := body) m k ps hoffs W2 u v).mono
        (le_of_eq (by simp))
  have hfl := RunsWithin.sp_flattenProg (X := X) (body := body) (t := .nat)
    ((List.range (m + k)).map fun u => (List.range (m + k)).map fun v => cQd m ps k W2 u v)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.offsetsProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le hrows)
    run_step hfl
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have hsum : (((List.range (m + k)).map fun u => (List.range (m + k)).map fun v =>
        cQd m ps k W2 u v).map List.length).sum = (m + k) * (m + k) := by
      simp [List.map_map, Function.comp_def]
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map, hsum,
      List.length_flatten, cQArrCost]
    ring_nf
    omega

/-- The cost of `sp_skelArrProg` for `k` cells, arity `d` and a choice of length `l`. -/
def skelArrCost (k d l : ℕ) : ℕ := k * (k * (8 * d + 5) + 5) + 2 * k * k + 4 * k + 2 * l + 12

theorem RunsWithin.sp_skelArrProg (wl : Array ℕ) (d k : ℕ) (xd : List ℕ) :
    RunsWithin X body (SoJTree.sp_skelArrProg wl (Coherent.pwTab d k) (List.range d) k xd)
      (skelArrD wl d k xd) (skelArrCost k d xd.length) := by
  have hrows : ∀ j ∈ List.range k, RunsWithin X body
      (Programs.mapList (a' := .nat) (b' := .nat) (List.range k) fun i =>
        Prog.bind (Coherent.pad2Prog (Coherent.pwTab d k) (List.range d) xd.length xd.toArray i j)
          fun c => .op2 .arrayGet wl c)
      ((List.range k).map fun i =>
        get wl (Coherent.codePad2 (Coherent.pwTab d k) d xd.length xd.toArray i j))
      (k * (8 * d + 5) + 2) := by
    intro j _
    refine (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 8 * d + 2) fun i _ =>
      RunsWithin.bind_le (Coherent.RunsWithin.pad2Prog _ _ _ _ i j)
        (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])).mono
      (by simp only [List.length_range]; ring_nf; omega)
  have hfl := RunsWithin.sp_flattenProg (X := X) (body := body) (t := .nat)
    ((List.range k).map fun j => (List.range k).map fun i =>
      get wl (Coherent.codePad2 (Coherent.pwTab d k) d xd.length xd.toArray i j))
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le hrows)
    run_step hfl
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have hsum : (((List.range k).map fun j => (List.range k).map fun i =>
        get wl (Coherent.codePad2 (Coherent.pwTab d k) d xd.length xd.toArray i j)).map
          List.length).sum =
        k * k := by
      simp [List.map_map, Function.comp_def]
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map, hsum,
      List.length_flatten, skelArrCost]
    ring_nf
    omega

theorem RunsWithin.sp_isBaseProg (t k : ℕ) :
    RunsWithin X body (SoJTree.sp_isBaseProg t k) (decide (IsBase t k))
      (clogCost 2 (t + t) + 3 * Nat.clog 2 (t + t) +
        3 * (Nat.clog 2 (t + t) * Nat.clog 2 (t + t)) + 3 * k + 100) := by
  have hv : (!decide (27 * (Nat.clog 2 (t + t) * Nat.clog 2 (t + t) * Nat.clog 2 (t + t)) <
      k * k)) = decide (IsBase t k) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt, decide_eq_true_eq]
    unfold IsBase
    rw [show 2 * t = t + t by ring]
    constructor <;> intro h <;> nlinarith
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.clogProg _ _)
    run_step (Coherent.RunsWithin.mulNProg _ _)
    run_step (Coherent.RunsWithin.mulNProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.mulNProg _ _)
    run_step (Coherent.RunsWithin.mulNProg _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le hv le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

theorem RunsWithin.sp_diagProg (offs c : Array ℕ) (o r : ℕ) :
    RunsWithin X body (SoJTree.sp_diagProg offs c o r)
      ((List.range r).map fun j => fA offs c (o + j) (o + j)).toArray (9 * r + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 4)
      (F := fun j => fA offs c (o + j) (o + j)) fun j _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.csColProg offs c _ _)
          (by simp [Prim.cost]))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map]
    omega

theorem RunsWithin.sp_rectProg (offs c : Array ℕ) (m k : ℕ) :
    RunsWithin X body (SoJTree.sp_rectProg offs c m k) (rectArr m k (fA offs c))
      (m * (8 * k + 9) + k + 5) := by
  have hrows : ∀ y ∈ List.range m, RunsWithin X body
      (Prog.bind (Programs.mapList (a' := .nat) (b' := .nat) (List.range k) fun j =>
        Prog.bind (.op2 .add m j) fun v => csColProg offs c y v) fun l => .op1 .arrayOfList l)
      ((List.range k).map fun j => fA offs c y (m + j)).toArray (8 * k + 4) := by
    intro y _
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 4)
        (F := fun j => fA offs c y (m + j)) fun j _ =>
          RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.csColProg offs c _ _)
            (by simp [Prim.cost]))
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, Args.head, List.length_range, List.length_map]
      omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le hrows)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map]
    ring_nf
    omega

theorem sp_getD_cells_le {cs : List (List ℕ)} {M : ℕ} (hcs : ∀ c ∈ cs, c.length ≤ M) (j : ℕ) :
    (cs.getD j []).length ≤ M := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[j]? with _ | c
  · simp
  · exact hcs c (List.mem_of_getElem? h)

theorem sp_sum_le {α : Type*} (l : List α) (f : α → ℕ) {M : ℕ} (h : ∀ x ∈ l, f x ≤ M) :
    (l.map f).sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := h x List.mem_cons_self
    have := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    nlinarith

theorem RunsWithin.sp_cellUDProg (m k : ℕ) (cs : List (List ℕ)) (l : List ℕ) {M : ℕ}
    (hM : 1 ≤ M) (hm : m ≤ M) (hl : l.length ≤ M) (hcs : ∀ c ∈ cs, c.length ≤ M) :
    RunsWithin X body (SoJTree.sp_cellUDProg m k cs.toArray l) (cellUD m k cs l)
      (40 * M ^ 3) := by
  set l' := l.filter fun i => decide (m ≤ i ∧ i < m + k) with hl'
  have hfilt := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := l)
    (c := 4) (P := fun i => decide (m ≤ i ∧ i < m + k))
    (p := fun i => Prog.bind (.op2 .natLt i m) fun lt => .bind (.op1 .not lt) fun ge =>
      .bind (.op2 .natLt i (m + k)) fun lt₂ => .op2 .and ge lt₂) fun i _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        refine RunsWithin.prim_le ?_ le_rfl
        simp only [Prim.eval]
        rw [Bool.eq_iff_iff]
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
          Nat.not_lt]
      case hc => simp [Prim.cost]
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := l') (c := 2) (F := fun i => cs.getD (i - m) [])
    (f := fun i => Prog.bind (.op2 .sub i m) fun j => .op2 .arrayGet cs.toArray j) fun i _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le (by
        simp [Prim.eval, Ty.default, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD])
        le_rfl) (by simp [Prim.cost])
  have hfl := RunsWithin.sp_flattenProg (X := X) (body := body) (t := .nat)
    (l'.map fun i => cs.getD (i - m) [])
  set u := (l'.map fun i => cs.getD (i - m) []).flatten with hu
  have hlen' : l'.length ≤ M := (List.length_filter_le _ _).trans hl
  have hsum : ((l'.map fun i => cs.getD (i - m) []).map List.length).sum ≤ M * M := by
    rw [List.map_map]
    exact (sp_sum_le l' _ fun i _ => sp_getD_cells_le hcs _).trans
      (Nat.mul_le_mul_right _ hlen')
  have hulen : u.length ≤ M * M := by
    rw [hu, List.length_flatten]
    exact hsum
  have hmem := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := List.range m) (c := 3 * u.length + 1) (P := fun y => decide (y ∈ u))
    (p := fun y => SoJProg.memProg y u) fun y _ => SoJProg.RunsWithin.memProg y u
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfilt
    run_step hmap
    run_step hfl
    run_step (RunsWithin.prim _ _)
    exact hmem.of_eq (by rw [cellUD, List.flatMap_def])
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, List.length_map]
    have h1 : l'.length * (2 + 3) ≤ 5 * M := by omega
    have h2 : m * (3 * u.length + 1 + 4) ≤ M * (3 * (M * M) + 5) :=
      Nat.mul_le_mul hm (by omega)
    have h3 : l.length * (4 + 4) ≤ 8 * M := by omega
    have hM2 : M ≤ M * M := Nat.le_mul_of_pos_left _ hM
    have hM3 : M * M ≤ M ^ 3 := by
      rw [pow_succ, pow_two]
      exact Nat.le_mul_of_pos_right _ hM
    have e : M * (3 * (M * M) + 5) = 3 * M ^ 3 + 5 * M := by ring
    omega

theorem sp_pow_le {M : ℕ} (hM : 1 ≤ M) {i j : ℕ} (h : i ≤ j) : M ^ i ≤ M ^ j :=
  Nat.pow_le_pow_right hM h

theorem sp_dedup_fold (m B : ℕ) : ∀ (xs acc : List (List ℕ)), acc.length + xs.length ≤ B →
    (∀ l ∈ acc, l.length ≤ B) → (∀ l ∈ xs, l.length ≤ B) →
    RunsWithin X body (Prog.foldList (a := .list .nat) (b := .list (.list .nat)) xs acc
        fun acc l => Prog.bind (anyList acc fun l' => SoJTree.setEqProg m l l') fun dup =>
        .ite dup (.ret acc)
          (.bind (.op0 .nil) fun nl => .bind (.op2 .cons l nl) fun sl => .op2 .append acc sl))
      (xs.foldl (fun acc l => if acc.any (setEqD m l) then acc else acc ++ [l]) acc)
      (xs.length * (B * (setEqCost m B + 2) + B + 9))
  | [], acc, _, _, _ => by simpa using RunsWithin.foldList_nil
  | l :: xs, acc, hn, hacc, hxs => by
    have hl : l.length ≤ B := hxs l List.mem_cons_self
    have hany := RunsWithin.anyList_le (X := X) (body := body) (a' := .list .nat) (xs := acc)
      (c := setEqCost m B) (P := setEqD m l)
      (p := fun l' => SoJTree.setEqProg m l l') fun l' hl' =>
        RunsWithin.setEqProg m hl (hacc l' hl')
    simp only [List.length_cons] at hn
    have hacc₁ : acc.length ≤ B := by omega
    have hmul : acc.length * (setEqCost m B + 2) ≤ B * (setEqCost m B + 2) :=
      Nat.mul_le_mul_right _ hacc₁
    by_cases hd : acc.any (setEqD m l) = true
    · have ih := sp_dedup_fold m B xs acc (by omega) hacc
        fun l' hl' => hxs l' (List.mem_cons_of_mem _ hl')
      refine (RunsWithin.foldList_cons (c₂ := xs.length * (B * (setEqCost m B + 2) + B + 9))
        (RunsWithin.bind_le hany (RunsWithin.ite_pos hd (RunsWithin.ret _)) le_rfl) ?_).mono ?_
      · simpa only [List.foldl_cons, hd, ite_true] using ih
      · simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega
    · have hd' : acc.any (setEqD m l) = false := by simpa using hd
      have ih := sp_dedup_fold m B xs (acc ++ [l]) (by simp; omega)
        (fun l' hl' => by
          rcases List.mem_append.1 hl' with h | h
          · exact hacc l' h
          · rw [List.mem_singleton.1 h]
            exact hl)
        fun l' hl' => hxs l' (List.mem_cons_of_mem _ hl')
      refine (RunsWithin.foldList_cons (c₂ := xs.length * (B * (setEqCost m B + 2) + B + 9))
        (c₁ := acc.length * (setEqCost m B + 2) + 1 + (1 + (acc.length + 3))) (acc := acc ++ [l])
        (RunsWithin.bind_le hany (RunsWithin.ite_neg hd' ?_) le_rfl) ?_).mono ?_
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.prim _ _
        case hc =>
          simp only [Prim.cost, Args.head]
          omega
      · simpa only [List.foldl_cons, hd', Bool.false_eq_true, ite_false, Prim.eval] using ih
      · simp only [List.length_cons]
        rw [Nat.succ_mul]
        omega

theorem RunsWithin.sp_dedupProg (m : ℕ) (ls : List (List ℕ)) {B : ℕ} (hB : 1 ≤ B)
    (hm : m ≤ B) (hn : ls.length ≤ B) (hls : ∀ l ∈ ls, l.length ≤ B) :
    RunsWithin X body (SoJTree.sp_dedupProg m ls) (dedupCellsD m ls) (33 * B ^ 4) := by
  have h := sp_dedup_fold (X := X) (body := body) m B ls [] (by simpa using hn) (by simp) hls
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost, setEqCost]
    have h1 : m * (6 * B + 10) ≤ B * (6 * B + 10) := Nat.mul_le_mul_right _ hm
    have h2 : ls.length * (B * (B * (6 * B + 10) + 2 + 2 + 2) + B + 9) ≤
        B * (B * (B * (6 * B + 10) + 2 + 2 + 2) + B + 9) := Nat.mul_le_mul_right _ hn
    have h3 : ls.length * (B * (m * (6 * B + 10) + 2 + 2) + B + 9) ≤
        ls.length * (B * (B * (6 * B + 10) + 2 + 2 + 2) + B + 9) :=
      Nat.mul_le_mul_left _ (by nlinarith)
    have e : B * (B * (B * (6 * B + 10) + 2 + 2 + 2) + B + 9) =
        6 * B ^ 4 + 10 * B ^ 3 + 7 * B ^ 2 + 9 * B := by ring
    have p1 := sp_pow_le hB (show 1 ≤ 4 by norm_num)
    have p2 := sp_pow_le hB (show 2 ≤ 4 by norm_num)
    have p3 := sp_pow_le hB (show 3 ≤ 4 by norm_num)
    simp only [pow_one] at p1
    omega

theorem sp_length_cellUD (m k : ℕ) (cs : List (List ℕ)) (l : List ℕ) :
    (cellUD m k cs l).length ≤ m :=
  (List.length_filter_le _ _).trans (List.length_range).le

theorem RunsWithin.sp_bipEntryProg (m k N g x : ℕ) (cs : List (List ℕ)) (offs c : Array ℕ)
    (W₂ : List (List ℕ)) (cell : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hW : W₂.length ≤ B) (hW' : ∀ l ∈ W₂, l.length ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B)
    (hcell : cell.length ≤ B) :
    RunsWithin X body (SoJTree.sp_bipEntryProg m k N g x cs.toArray offs c W₂ cell)
      (W₂.any fun l => setEqD m (cellUD m k cs l) cell &&
        l.any fun y => decide (y < N) && fA offs c x y == g) (75 * B ^ 4) := by
  have p2 := sp_pow_le hB (show 2 ≤ 3 by norm_num)
  have p1 := sp_pow_le hB (show 1 ≤ 3 by norm_num)
  simp only [pow_one] at p1
  have e3 : B * B ^ 3 = B ^ 4 := by ring
  have e2 : B * B = B ^ 2 := by ring
  refine (RunsWithin.anyList_le (c := 70 * B ^ 3) fun l hl => ?_).mono ?_
  · have hl' := hW' l hl
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.sp_cellUDProg m k cs l hB hm hl' hcs)
      run_step (RunsWithin.setEqProg m ((sp_length_cellUD m k cs l).trans hm) hcell)
      run_step (RunsWithin.anyList_le (c := 6)
        (P := fun y => decide (y < N) && fA offs c x y == g) fun y _ => by
          apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.csColProg offs c x y)
            run_step (RunsWithin.prim _ _)
            exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
          case hc => simp [Prim.cost])
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, setEqCost]
      have h1 : m * (6 * B + 10) ≤ B * (6 * B + 10) := Nat.mul_le_mul_right _ hm
      have h2 : l.length * (6 + 2) ≤ B * 8 := Nat.mul_le_mul_right _ hl'
      have e : B * (6 * B + 10) = 6 * B ^ 2 + 10 * B := by ring
      omega
  · have h1 : W₂.length * (70 * B ^ 3 + 2) ≤ B * (70 * B ^ 3 + 2) := Nat.mul_le_mul_right _ hW
    have e : B * (70 * B ^ 3 + 2) = 70 * B ^ 4 + 2 * B := by ring
    have p4 := sp_pow_le hB (show 1 ≤ 4 by norm_num)
    simp only [pow_one] at p4
    omega

theorem RunsWithin.sp_bipRelXProg (m k N g : ℕ) (cs : List (List ℕ)) (offs c : Array ℕ)
    (W₂ cells : List (List ℕ)) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hW : W₂.length ≤ B) (hW' : ∀ l ∈ W₂, l.length ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B)
    (hc : cells.length ≤ B) (hc' : ∀ cell ∈ cells, cell.length ≤ B) :
    RunsWithin X body (SoJTree.sp_bipRelXProg m k N g cs.toArray offs c W₂ cells)
      (bipRelX m N k cs (fA offs c) g W₂ cells) (100 * B ^ 6) := by
  have hrows := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .list .bool) (xs := List.range m) (c := cells.length * (75 * B ^ 4 + 3) + 2)
    (F := fun x => cells.map fun cell => W₂.any fun l => setEqD m (cellUD m k cs l) cell &&
        l.any fun y => decide (y < N) && fA offs c x y == g)
    (f := fun x => mapList (a' := .list .nat) cells fun cell =>
      SoJTree.sp_bipEntryProg m k N g x cs.toArray offs c W₂ cell) fun x _ =>
      RunsWithin.mapList_le fun cell hcell =>
        RunsWithin.sp_bipEntryProg m k N g x cs offs c W₂ cell hB hm hW hW' hcs (hc' cell hcell)
  have hfl := RunsWithin.sp_flattenProg (X := X) (body := body) (t := .bool)
    ((List.range m).map fun x => cells.map fun cell => W₂.any fun l =>
      setEqD m (cellUD m k cs l) cell && l.any fun y => decide (y < N) && fA offs c x y == g)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hrows
    run_step hfl
    exact RunsWithin.prim_le (by simp [Prim.eval, bipRelX, List.flatMap_def]) le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, List.length_map,
      List.map_map, List.length_flatten, Function.comp_def, sum_map_const]
    have h1 : cells.length * (75 * B ^ 4 + 3) ≤ B * (75 * B ^ 4 + 3) :=
      Nat.mul_le_mul_right _ hc
    have h2 : m * (cells.length * (75 * B ^ 4 + 3) + 2 + 3) ≤ B * (B * (75 * B ^ 4 + 3) + 5) :=
      Nat.mul_le_mul hm (by omega)
    have h3 : m * cells.length ≤ B * B := Nat.mul_le_mul hm hc
    have e : B * (B * (75 * B ^ 4 + 3) + 5) = 75 * B ^ 6 + 3 * B ^ 2 + 5 * B := by ring
    have e2 : B * B = B ^ 2 := by ring
    have p1 := sp_pow_le hB (show 1 ≤ 6 by norm_num)
    have p2 := sp_pow_le hB (show 2 ≤ 6 by norm_num)
    simp only [pow_one] at p1
    omega

theorem sp_dedup_foldl (m : ℕ) : ∀ (xs acc : List (List ℕ)),
    (xs.foldl (fun acc l => if acc.any (setEqD m l) then acc else acc ++ [l]) acc).length ≤
      acc.length + xs.length ∧
    ∀ c ∈ xs.foldl (fun acc l => if acc.any (setEqD m l) then acc else acc ++ [l]) acc,
      c ∈ acc ∨ c ∈ xs
  | [], acc => ⟨by simp, fun c hc => .inl hc⟩
  | l :: xs, acc => by
    simp only [List.foldl_cons]
    split
    · obtain ⟨h₁, h₂⟩ := sp_dedup_foldl m xs acc
      refine ⟨by simp only [List.length_cons]; omega, fun c hc => ?_⟩
      rcases h₂ c hc with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · obtain ⟨h₁, h₂⟩ := sp_dedup_foldl m xs (acc ++ [l])
      refine ⟨?_, fun c hc => ?_⟩
      · simp only [List.length_cons, List.length_append, List.length_nil] at h₁ ⊢
        omega
      rcases h₂ c hc with h | h
      · rcases List.mem_append.1 h with h | h
        · exact .inl h
        · exact .inr (List.mem_singleton.1 h ▸ List.mem_cons_self)
      · exact .inr (List.mem_cons_of_mem _ h)

theorem sp_length_dedupCellsD (m : ℕ) (ls : List (List ℕ)) :
    (dedupCellsD m ls).length ≤ ls.length := by
  have h := (sp_dedup_foldl m ls []).1
  rw [List.length_nil, Nat.zero_add] at h
  exact h

theorem sp_mem_dedupCellsD {m : ℕ} {ls : List (List ℕ)} {c : List ℕ}
    (h : c ∈ dedupCellsD m ls) : c ∈ ls := by
  rcases (sp_dedup_foldl m ls []).2 c h with h | h
  · exact absurd h List.not_mem_nil
  · exact h

theorem sp_sum_add_len (prs : List (List OutD × List FrameD)) :
    (prs.map fun pr => pr.1.length + pr.2.length).sum =
      ((prs.map Prod.fst).map List.length).sum + ((prs.map Prod.snd).map List.length).sum := by
  induction prs with
  | nil => rfl
  | cons pr prs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

theorem RunsWithin.sp_catProg (prs : List (List OutD × List FrameD)) :
    RunsWithin X body (SoJTree.sp_catProg prs)
      ((prs.map Prod.fst).flatten, (prs.map Prod.snd).flatten)
      (14 * prs.length + (prs.map fun pr => pr.1.length + pr.2.length).sum + 11) := by
  have h₁ := RunsWithin.mapList_le (X := X) (body := body) (a' := .prod (.list outTy)
    (.list frameTy)) (b' := .list outTy) (xs := prs) (c := 1) (F := Prod.fst)
    (f := fun pr => .op1 .fst pr) fun _ _ => RunsWithin.prim_le rfl le_rfl
  have h₂ := RunsWithin.mapList_le (X := X) (body := body) (a' := .prod (.list outTy)
    (.list frameTy)) (b' := .list frameTy) (xs := prs) (c := 1) (F := Prod.snd)
    (f := fun pr => .op1 .snd pr) fun _ _ => RunsWithin.prim_le rfl le_rfl
  apply RunsWithin.mono
  case h =>
    run_step h₁
    run_step (RunsWithin.sp_flattenProg (t := outTy) (prs.map Prod.fst))
    run_step h₂
    run_step (RunsWithin.sp_flattenProg (t := frameTy) (prs.map Prod.snd))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, List.length_map, sp_sum_add_len]
    omega

theorem sp_cat_splitI {β : Type*} (L : List β) (F : β → List Item) :
    (((L.map fun b => splitI (F b)).map Prod.fst).flatten,
      ((L.map fun b => splitI (F b)).map Prod.snd).flatten) = splitI (L.flatMap F) := by
  rw [splitI_flatMap, List.flatMap_def, List.flatMap_def, List.map_map, List.map_map]
  rfl

/-- Size bounds on a leaf of `cohSojD`. -/
def LeafOK (B : ℕ) : Option SoJProg.LeafD → Prop
  | none => True
  | some (_, _, (W₁, W₂, _)) => W₁.length ≤ B ∧ W₂.length ≤ B ∧ ∀ l ∈ W₂, l.length ≤ B

theorem sp_leafOK_partLeaf (B : ℕ) (col : Array ℕ) (blk : Array (List ℕ)) :
    LeafOK B (some (partLeaf col blk)) := by
  simp [LeafOK, partLeaf]

theorem sp_leafOK_bipLeaf {B : ℕ} {W₁ : List ℕ} {W₂ : List (List ℕ)} (g : ℕ)
    (h₁ : W₁.length ≤ B) (h₂ : W₂.length ≤ B) (h₃ : ∀ l ∈ W₂, l.length ≤ B) :
    LeafOK B (some (bipLeaf W₁ W₂ g)) :=
  ⟨h₁, h₂, h₃⟩

/-- **The leaves of `cohSojD` are small.** -/
theorem sp_cohSojD_leafOK (f : ℕ → ℕ → ℕ) (N : ℕ) {C₁ C₂ : List ℕ} {B : ℕ}
    (h₁ : C₁.length ≤ B) (h₂ : C₂.length * C₂.length + 1 ≤ B) :
    (∀ o, cohSojD f N C₁ C₂ = .leaf o → LeafOK B o) ∧
      ∀ opts kk, cohSojD f N C₁ C₂ = .node opts kk → ∀ y, LeafOK B (kk y) := by
  have hC₂ : C₂.length ≤ B := by nlinarith
  have hcomp : ∀ r y, (compD f C₂ r y).length ≤ B := fun r y =>
    (length_compD_le f C₂ r y).trans h₂
  have hsing : ∀ L : List ℕ, ∀ l ∈ L.map fun z => [z], l.length ≤ B := by
    intro L l hl
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hl
    simp only [List.length_singleton]
    nlinarith
  have hfilt : ∀ p : ℕ → Bool, (C₁.filter p).length ≤ B := fun p =>
    (List.length_filter_le _ _).trans h₁
  refine ⟨fun o h => ?_, fun opts kk h y => ?_⟩
  · unfold cohSojD imprimTree at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | (cases h; exact sp_leafOK_partLeaf _ _ _)
      | (cases h; trivial)
      | skip
    · cases h
      exact sp_leafOK_bipLeaf _ h₁ (by simp [hC₂]) fun l hl => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hl
        exact hcomp _ _
  · unfold cohSojD imprimTree at h
    repeat' split at h
    all_goals first
      | (cases h; done)
      | skip
    · cases h
      exact sp_leafOK_bipLeaf _ h₁ ((List.length_map _).le.trans (hcomp _ _)) (hsing _)
    · cases h
      exact sp_leafOK_partLeaf _ _ _
    · cases h
      beta_reduce
      unfold primLeaf
      repeat' split
      · exact sp_leafOK_bipLeaf _ (hfilt _)
          ((List.length_map _).le.trans ((List.length_filter_le _ _).trans hC₂)) (hsing _)
      · trivial
      · exact sp_leafOK_partLeaf _ _ _

theorem sp_addPieceCost_le {m d B : ℕ} (hm : m ≤ B) (hd : d ≤ B) :
    addPieceCost m d ≤ 6 * B ^ 2 + 18 * B + 30 := by
  unfold addPieceCost
  have h : m * (6 * d + 15) ≤ B * (6 * B + 15) := Nat.mul_le_mul hm (by omega)
  have e : B * (6 * B + 15) = 6 * B ^ 2 + 15 * B := by ring
  omega

theorem RunsWithin.sp_contBigProg (m k g : ℕ) (cs : List (List ℕ)) (offs c : Array ℕ)
    (W₂ : List (List ℕ)) (W DW D₁ D₂ : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hcs : ∀ c ∈ cs, c.length ≤ B) (hW₂ : W₂.length ≤ B) (hW₂' : ∀ l ∈ W₂, l.length ≤ B) :
    RunsWithin X body (SoJTree.sp_contBigProg m k cs.toArray offs c W₂ g W DW D₁ D₂)
      (splitI [shrinkI k W (dedupCellsD m (W₂.map (cellUD m k cs)))
        (bipRelX m (m + k) k cs (fA offs c) g W₂ (dedupCellsD m (W₂.map (cellUD m k cs))))
        [pieceOp DW, pieceOp D₂, pieceOp D₁]]) (250 * B ^ 6) := by
  set us := W₂.map (cellUD m k cs) with hus
  have hus₁ : us.length ≤ B := by rw [hus, List.length_map]; exact hW₂
  have hus₂ : ∀ l ∈ us, l.length ≤ B := fun l hl => by
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact (sp_length_cellUD m k cs l').trans hm
  have hc₁ : (dedupCellsD m us).length ≤ B := (sp_length_dedupCellsD m us).trans hus₁
  have hc₂ : ∀ cell ∈ dedupCellsD m us, cell.length ≤ B := fun cell h =>
    hus₂ cell (sp_mem_dedupCellsD h)
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat)
    (b' := .list .nat) (xs := W₂) (c := 40 * B ^ 3) (F := cellUD m k cs)
    (f := fun l => SoJTree.sp_cellUDProg m k cs.toArray l) fun l hl =>
      RunsWithin.sp_cellUDProg m k cs l hB hm (hW₂' l hl) hcs
  apply RunsWithin.mono
  case h =>
    run_step hmap
    run_step (RunsWithin.sp_dedupProg m us hB hm hus₁ hus₂)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.sp_bipRelXProg m k (m + k) g cs offs c W₂ (dedupCellsD m us) hB hm
      hW₂ hW₂' hcs hc₁ hc₂)
    run_step (RunsWithin.sp_pieceProg _)
    run_step (RunsWithin.sp_pieceProg _)
    run_step (RunsWithin.sp_pieceProg _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.sp_shrinkIProg _ _ _ _ _
  case hc =>
    simp only [Prim.cost]
    have p1 := sp_pow_le hB (show 1 ≤ 6 by norm_num)
    have p4 := sp_pow_le hB (show 4 ≤ 6 by norm_num)
    simp only [pow_one] at p1
    have hm₂ : W₂.length * (40 * B ^ 3 + 3) ≤ B * (40 * B ^ 3 + 3) :=
      Nat.mul_le_mul_right _ hW₂
    have e₃ : B * (40 * B ^ 3 + 3) = 40 * B ^ 4 + 3 * B := by ring
    omega

theorem RunsWithin.sp_contSmallProg (m : ℕ) (W DW D₁ D₂ : List ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hm : m ≤ B) (hW : W.length ≤ B) (hDW : DW.length ≤ B) (hD₁ : D₁.length ≤ B)
    (hD₂ : D₂.length ≤ B) :
    RunsWithin X body (SoJTree.sp_contSmallProg m W DW D₁ D₂)
      (splitI [.inl (addPieceD m D₁ (addPieceD m D₂ (addPieceD m DW
        (partD #[] (colBlkD m W #[])))))]) (200 * B ^ 2) := by
  have a₁ := sp_addPieceCost_le hm hD₁
  have a₂ := sp_addPieceCost_le hm hD₂
  have a₃ := sp_addPieceCost_le hm hDW
  apply RunsWithin.mono
  case h =>
    run_step RunsWithin.emptyNatArrProg
    run_step (RunsWithin.colBlkProg m W _)
    run_step (RunsWithin.partProg _ _)
    run_step (RunsWithin.addPieceProg m DW _)
    run_step (RunsWithin.addPieceProg m D₂ _)
    run_step (RunsWithin.addPieceProg m D₁ _)
    exact RunsWithin.sp_leafPair _
  case hc =>
    simp only [colBlkCost]
    have hcb : m * (6 * W.length + 7) ≤ B * (6 * B + 7) := Nat.mul_le_mul hm (by omega)
    have e₃ : B * (6 * B + 7) = 6 * B ^ 2 + 7 * B := by ring
    have p1 : B ≤ B ^ 2 := by nlinarith
    omega

theorem RunsWithin.sp_contBipProg (m t k g : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ : List ℕ)
    (offs c : Array ℕ) (W₁ : List ℕ) (W₂ : List (List ℕ)) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hcs : ∀ c ∈ cs, c.length ≤ B) (hD₁ : D₁.length ≤ B) (hD₂ : D₂.length ≤ B)
    (hC₁ : C₁.length ≤ B) (hW₁ : W₁.length ≤ B) (hW₂ : W₂.length ≤ B)
    (hW₂' : ∀ l ∈ W₂, l.length ≤ B) {tag : ℕ} (htag : tag ≠ 0) (cb : Array ℕ × Array (List ℕ)) :
    RunsWithin X body (SoJTree.sp_contBipProg m t k cs.toArray D₁ D₂ C₁ offs c W₁ W₂ g)
      (splitI [contI m t k cs D₁ D₂ C₁ (fA offs c) (some (tag, cb, (W₁, W₂, g)))])
      (300 * B ^ 6) := by
  set W := (List.range m).filter fun y => decide (y ∈ W₁) with hWdef
  have hWm : W.length ≤ m := (List.length_filter_le _ _).trans (List.length_range).le
  have hDW : (diffD C₁ W).length ≤ B := (List.length_filter_le _ _).trans hC₁
  have hfilt := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := List.range m) (c := 3 * W₁.length + 1) (P := fun y => decide (y ∈ W₁))
    (p := fun y => SoJProg.memProg y W₁) fun y _ => SoJProg.RunsWithin.memProg y W₁
  have hfm : m * (3 * W₁.length + 1 + 4) ≤ B * (3 * B + 5) := Nat.mul_le_mul hm (by omega)
  have hdm : C₁.length * (3 * W.length + 6) ≤ B * (3 * B + 6) :=
    Nat.mul_le_mul hC₁ (by omega)
  have e₁ : B * (3 * B + 5) = 3 * B ^ 2 + 5 * B := by ring
  have e₂ : B * (3 * B + 6) = 3 * B ^ 2 + 6 * B := by ring
  have p1 := sp_pow_le hB (show 1 ≤ 6 by norm_num)
  have p2 := sp_pow_le hB (show 2 ≤ 6 by norm_num)
  simp only [pow_one] at p1
  by_cases hW : t < W.length
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hfilt
      run_step (RunsWithin.sp_diffProg C₁ W)
      run_step (RunsWithin.prim_le rfl (c := m + 1) (by
        simp only [Prim.cost, Args.head]
        exact Nat.succ_le_succ hWm))
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_pos (by simp only [Prim.eval, decide_eq_true_eq]; exact hW)
      refine (RunsWithin.sp_contBigProg m k g cs offs c W₂ W (diffD C₁ W) D₁ D₂ hB hm hcs hW₂
        hW₂').of_eq ?_
      simp only [contI, htag, ite_false, ← hWdef]
      rw [ite_eq_right (by omega)]
    case hc =>
      simp only [Prim.cost, Args.head, List.length_range]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hfilt
      run_step (RunsWithin.sp_diffProg C₁ W)
      run_step (RunsWithin.prim_le rfl (c := m + 1) (by
        simp only [Prim.cost, Args.head]
        exact Nat.succ_le_succ hWm))
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_neg (by simp only [Prim.eval, decide_eq_false_iff_not]; exact hW)
      refine (RunsWithin.sp_contSmallProg m W (diffD C₁ W) D₁ D₂ hB hm (hWm.trans hm) hDW hD₁
        hD₂).of_eq ?_
      simp only [contI, htag, ite_false, ← hWdef]
      rw [ite_eq_left (by omega)]
    case hc =>
      simp only [Prim.cost, Args.head, List.length_range]
      omega

/-- **`cohCont` on data, the program.** -/
theorem RunsWithin.sp_contProg (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ : List ℕ)
    (offs c : Array ℕ) (o : Option SoJProg.LeafD) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hcs : ∀ c ∈ cs, c.length ≤ B) (hD₁ : D₁.length ≤ B) (hD₂ : D₂.length ≤ B)
    (hC₁ : C₁.length ≤ B) (ho : LeafOK B o) :
    RunsWithin X body (SoJTree.sp_contProg m t k cs.toArray D₁ D₂ C₁ offs c o)
      (splitI [contI m t k cs D₁ D₂ C₁ (fA offs c) o]) (320 * B ^ 6) := by
  have p2 := sp_pow_le hB (show 2 ≤ 6 by norm_num)
  have p1 := sp_pow_le hB (show 1 ≤ 6 by norm_num)
  simp only [pow_one] at p1
  have a₁ := sp_addPieceCost_le hm hD₁
  have a₂ := sp_addPieceCost_le hm hD₂
  rcases o with _ | ⟨tag, cb, ⟨W₁, W₂, g⟩⟩
  · apply RunsWithin.mono
    case h =>
      apply RunsWithin.caseOption_none
      run_step RunsWithin.noneProg
      exact RunsWithin.sp_leafPair _
    case hc => omega
  obtain ⟨hW₁, hW₂, hW₂'⟩ := ho
  by_cases htag : tag = 0
  · apply RunsWithin.mono
    case h =>
      apply RunsWithin.caseOption_some
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_pos (by simp [Prim.eval, htag])
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.partProg _ _)
      run_step (RunsWithin.addPieceProg m D₂ _)
      run_step (RunsWithin.addPieceProg m D₁ _)
      exact (RunsWithin.sp_leafPair _).of_eq (by simp [contI, htag, Prim.eval])
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      apply RunsWithin.caseOption_some
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_neg (by simp [Prim.eval, htag])
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.sp_contBipProg m t k g cs D₁ D₂ C₁ offs c W₁ W₂ hB hm hcs hD₁ hD₂ hC₁
        hW₁ hW₂ hW₂' htag cb
    case hc =>
      simp only [Prim.cost]
      omega

theorem sp_cohSojCost_le {N B : ℕ} (hB : 1 ≤ B) (hN : N ≤ B) :
    SoJProg.cohSojCost N ≤ 115584 * B ^ 7 := by
  have h := SoJProg.cohSojCost_le N
  have h' : (N + 1) ^ 7 ≤ (2 * B) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have e : (2 * B) ^ 7 = 128 * B ^ 7 := by ring
  omega

theorem sp_cohI_leaf (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ C₂ : List ℕ) (c : Array ℕ)
    {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B) (hD₁ : D₁.length ≤ B)
    (hD₂ : D₂.length ≤ B) (hC₁ : C₁.length ≤ B) (hC₂ : C₂.length * C₂.length + 1 ≤ B)
    (hN : m + k + C₁.length + C₂.length ≤ B) {o : Option SoJProg.LeafD}
    (hD : cohSojD (fA (offsArr (m + k)) c) (m + k) C₁ (C₂.map (m + ·)) = .leaf o) :
    RunsWithin X body (SoJTree.sp_cohIProg m t k cs.toArray D₁ D₂ C₁ C₂ (offsArr (m + k)) c)
      (splitI [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) o]) (116000 * B ^ 7) := by
  have hcoh := SoJProg.RunsWithin.cohSojProg (X := X) (body := body) (m + k) c C₁
    (C₂.map (m + ·))
  rw [hD] at hcoh
  have ho : LeafOK B o := (sp_cohSojD_leafOK _ _ hC₁ (by simpa using hC₂)).1 o hD
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := C₂) (c := 1) (F := (m + ·)) (f := fun j => .op2 .add m j) fun _ _ =>
      RunsWithin.prim_le rfl le_rfl
  have hc := sp_cohSojCost_le hB (show m + k + C₁.length + (C₂.map (m + ·)).length ≤ B by
    simpa using hN)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hmap
    run_step hcoh
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    apply RunsWithin.ite_neg rfl
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim_le (v := o) (by simp [Prim.eval, toRes]) le_rfl)
    exact RunsWithin.sp_contProg m t k cs D₁ D₂ C₁ _ c o hB hm hcs hD₁ hD₂ hC₁ ho
  case hc =>
    simp only [Prim.cost]
    have p6 := sp_pow_le hB (show 6 ≤ 7 by norm_num)
    have p1 := sp_pow_le hB (show 1 ≤ 7 by norm_num)
    simp only [pow_one] at p1
    have : C₂.length ≤ B := by nlinarith
    omega

theorem sp_cohI_node (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ C₂ : List ℕ) (c : Array ℕ)
    {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B) (hD₁ : D₁.length ≤ B)
    (hD₂ : D₂.length ≤ B) (hC₁ : C₁.length ≤ B) (hC₂ : C₂.length * C₂.length + 1 ≤ B)
    (hN : m + k + C₁.length + C₂.length ≤ B) (hC₂k : ∀ j ∈ C₂, j < k) {opts : List ℕ}
    {kk : ℕ → Option SoJProg.LeafD}
    (hD : cohSojD (fA (offsArr (m + k)) c) (m + k) C₁ (C₂.map (m + ·)) = .node opts kk) :
    RunsWithin X body (SoJTree.sp_cohIProg m t k cs.toArray D₁ D₂ C₁ C₂ (offsArr (m + k)) c)
      (splitI (opts.map fun y => contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)))
      (116000 * B ^ 7 * (1 + opts.length)) := by
  have hcoh := SoJProg.RunsWithin.cohSojProg (X := X) (body := body) (m + k) c C₁
    (C₂.map (m + ·))
  rw [hD] at hcoh
  have hko : ∀ y, LeafOK B (kk y) :=
    (sp_cohSojD_leafOK _ _ hC₁ (by simpa using hC₂)).2 opts kk hD
  have hopts : ∀ y ∈ opts, y < m + k := fun y hy => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ((cohSojD_node_sublist hD).subset hy)
    have := hC₂k j hj
    omega
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := C₂) (c := 1) (F := (m + ·)) (f := fun j => .op2 .add m j) fun _ _ =>
      RunsWithin.prim_le rfl le_rfl
  have hc := sp_cohSojCost_le hB (N := m + k + C₁.length + C₂.length) hN
  have hprs := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .prod (.list outTy) (.list frameTy)) (xs := opts) (c := 320 * B ^ 6 + 1)
    (F := fun y => splitI [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)])
    (f := fun y => .bind (.op2 .arrayGet ((List.range (m + k)).map kk).toArray y) fun o =>
      SoJTree.sp_contProg m t k cs.toArray D₁ D₂ C₁ (offsArr (m + k)) c o) fun y hy =>
      RunsWithin.bind_le (RunsWithin.prim_le (v := kk y)
        (by simp [Prim.eval, getD_toArray_range _ _ (hopts y hy)]) le_rfl)
        (RunsWithin.sp_contProg m t k cs D₁ D₂ C₁ _ c (kk y) hB hm hcs hD₁ hD₂ hC₁ (hko y))
        (by simp [Prim.cost]; omega)
  have hcat := RunsWithin.sp_catProg (X := X) (body := body)
    (opts.map fun y => splitI [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)])
  rw [sp_cat_splitI opts fun y => [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)],
    flatMap_singleton_eq] at hcat
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hmap
    run_step hcoh
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    apply RunsWithin.ite_pos rfl
    run_step hprs
    exact hcat
  case hc =>
    simp only [Prim.cost, List.map_map, Function.comp_def, List.length_map]
    have hsum : (opts.map fun y => (splitI [contI m t k cs D₁ D₂ C₁
        (fA (offsArr (m + k)) c) (kk y)]).1.length +
        (splitI [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)]).2.length).sum =
        opts.length := by
      have h1 : ∀ y, (splitI [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)]).1.length +
          (splitI [contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y)]).2.length = 1 :=
        fun y => by rcases contI m t k cs D₁ D₂ C₁ (fA (offsArr (m + k)) c) (kk y) <;> rfl
      simp only [h1, sum_map_const, Nat.mul_one]
    have p6 := sp_pow_le hB (show 6 ≤ 7 by norm_num)
    have p1 := sp_pow_le hB (show 1 ≤ 7 by norm_num)
    simp only [pow_one] at p1
    have : C₂.length ≤ B := by nlinarith
    have hl : opts.length * (320 * B ^ 6 + 1 + 3 + 15) ≤ opts.length * (116000 * B ^ 7) :=
      Nat.mul_le_mul_left _ (by omega)
    have e' : opts.length * (320 * B ^ 6 + 1 + 3 + 15) =
        opts.length * (320 * B ^ 6 + 1 + 3) + 15 * opts.length := by ring
    have e : 116000 * B ^ 7 * (1 + opts.length) =
        116000 * B ^ 7 + opts.length * (116000 * B ^ 7) := by ring
    omega

/-- **The `cohSoj` level on data, the program**: `cohI` as a split pair, within
`116000 B^7 (1 + w)` for its work `w` (the number of options). -/
theorem RunsWithin.sp_cohIProg (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ C₂ : List ℕ)
    (c : Array ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B)
    (hD₁ : D₁.length ≤ B) (hD₂ : D₂.length ≤ B) (hC₁ : C₁.length ≤ B)
    (hC₂ : C₂.length * C₂.length + 1 ≤ B) (hN : m + k + C₁.length + C₂.length ≤ B)
    (hC₂k : ∀ j ∈ C₂, j < k) :
    RunsWithin X body (SoJTree.sp_cohIProg m t k cs.toArray D₁ D₂ C₁ C₂ (offsArr (m + k)) c)
      (splitI (cohI m t k cs D₁ D₂ C₁ C₂ (fA (offsArr (m + k)) c)).1)
      (116000 * B ^ 7 * (1 + (cohI m t k cs D₁ D₂ C₁ C₂ (fA (offsArr (m + k)) c)).2)) := by
  rcases hD : cohSojD (fA (offsArr (m + k)) c) (m + k) C₁ (C₂.map (m + ·)) with o | ⟨opts, kk⟩
  · simp only [cohI, hD, Nat.add_zero, Nat.mul_one]
    exact sp_cohI_leaf m t k cs D₁ D₂ C₁ C₂ c hB hm hcs hD₁ hD₂ hC₁ hC₂ hN hD
  · simp only [cohI, hD]
    exact sp_cohI_node m t k cs D₁ D₂ C₁ C₂ c hB hm hcs hD₁ hD₂ hC₁ hC₂ hN hC₂k hD

theorem sp_length_selThirdL (S : List ℕ) (col : ℕ → ℕ) : (selThirdL S col).length ≤ S.length := by
  unfold selThirdL
  dsimp only
  split <;> exact List.length_filter_le _ _

theorem sp_length_pickSideD (ps : List ℕ) (q : ℕ) (a : Array Bool) {S : List ℕ}
    (hS : S.length ≤ q) : (pickSideD ps q a S).length ≤ q := by
  unfold pickSideD
  split
  · exact hS
  · exact (List.length_filter_le _ _).trans (List.length_range).le

/-- A guarded call on the listed cells. -/
theorem RunsWithin.sp_callProg (m k : ℕ) (V' : List ℕ) (cs : List (List ℕ)) {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) (D js : List ℕ) {B : ℕ}
    (hB : 1 ≤ B) (hm : m ≤ B) (hcs : cs.length ≤ B) (hjs : js.length ≤ B) :
    RunsWithin X body (SoJTree.sp_callProg m k V' cs offs a D js)
      (splitI [shrinkI k V' (subCells cs js) (restrictRel m k a js) [pieceOp D]])
      (80 * B ^ 2) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.sp_subCellsProg cs js)
    run_step (RunsWithin.sp_restrictRelProg hoffs a js)
    run_step (RunsWithin.sp_pieceProg D)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.sp_shrinkIProg _ _ _ _ _
  case hc =>
    simp only [Prim.cost, subCells, List.length_map]
    have h1 : m * (js.length * 6 + 5) ≤ B * (B * 6 + 5) := Nat.mul_le_mul hm (by omega)
    have h2 : 2 * m * (js.length + 3) ≤ 2 * B * (B + 3) := Nat.mul_le_mul (by omega) (by omega)
    have e : B * (B * 6 + 5) + 2 * B * (B + 3) = 8 * B ^ 2 + 11 * B := by ring
    have p1 : B ≤ B ^ 2 := by nlinarith
    omega

/-- A guarded call on the cells chosen by `selThird` and Exercise 5.5. -/
theorem RunsWithin.sp_selCallProg (m k : ℕ) (V' : List ℕ) (hV' : ∀ x ∈ V', x < m)
    (cs : List (List ℕ)) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool)
    (D : List ℕ) (colA : Array ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hk : k ≤ B)
    (hcs : cs.length ≤ B) (hV : V'.length ≤ B) :
    RunsWithin X body (SoJTree.sp_selCallProg m k V' cs offs a D (List.range k) colA)
      (splitI [shrinkI k V' (subCells cs (pickSideD V' k a (selThirdL (List.range k) (get colA))))
        (restrictRel m k a (pickSideD V' k a (selThirdL (List.range k) (get colA))))
        [pieceOp D]]) (1000 * B ^ 3) := by
  have hT : (selThirdL (List.range k) (get colA)).length ≤ k :=
    (sp_length_selThirdL _ _).trans (List.length_range).le
  have hjs := sp_length_pickSideD V' k a hT
  apply RunsWithin.mono
  case h =>
    run_step (SoJProg.RunsWithin.selThirdProg (List.range k) colA)
    run_step (SoJProg.RunsWithin.pickSideProg V' hV' k a _)
    exact RunsWithin.sp_callProg m k V' cs hoffs a D _ hB hm hcs (hjs.trans hk)
  case hc =>
    simp only [selThirdCost, pickCost, List.length_range]
    have h1 : (k + 1) ^ 3 ≤ (2 * B) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : V'.length * (3 * m + 6) ≤ B * (3 * B + 6) := Nat.mul_le_mul hV (by omega)
    have h3 : V'.length * (V'.length * (8 * (selThirdL (List.range k) (get colA)).length + 5) + 5)
        ≤ B * (B * (8 * B + 5) + 5) :=
      Nat.mul_le_mul hV (by have := Nat.mul_le_mul hV (show 8 * (selThirdL (List.range k)
        (get colA)).length + 5 ≤ 8 * B + 5 by omega); omega)
    have e : B * (3 * B + 6) + B * (B * (8 * B + 5) + 5) = 8 * B ^ 3 + 8 * B ^ 2 + 11 * B := by
      ring
    have e' : (2 * B) ^ 3 = 8 * B ^ 3 := by ring
    have p1 : B ≤ B ^ 3 := by nlinarith [sp_pow_le hB (show 1 ≤ 3 by norm_num)]
    have p2 : B ^ 2 ≤ B ^ 3 := sp_pow_le hB (by norm_num)
    omega

theorem sp_bigL_sub (S : List ℕ) (col : ℕ → ℕ) (t : ℕ) : ∀ x ∈ bigL S col t, x ∈ S :=
  fun _ h => (List.mem_filter.1 h).1

theorem sp_length_bigL (S : List ℕ) (col : ℕ → ℕ) (t : ℕ) : (bigL S col t).length ≤ S.length :=
  List.length_filter_le _ _

/-- The constant-rectangle branch of `dlI`: a guarded call on the cells outside `C₂`. -/
theorem sp_dlBig_rect (m k : ℕ) (V₁' C₂ : List ℕ) (cs : List (List ℕ)) {offs : Array ℕ}
    (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) (D : List ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hm : m ≤ B) (hk : k ≤ B) (hC₂ : C₂.length ≤ B) (hcs : cs.length ≤ B) :
    RunsWithin X body (Prog.bind (Toolkit.filterList (a' := .nat) (List.range k) fun j =>
        Prog.bind (SoJProg.memProg j C₂) fun b => .op1 .not b) fun js =>
        SoJTree.sp_callProg m k V₁' cs offs a D js)
      (splitI [shrinkI k V₁' (subCells cs ((List.range k).filter fun j => j ∉ C₂))
        (restrictRel m k a ((List.range k).filter fun j => j ∉ C₂)) [pieceOp D]])
      (100 * B ^ 2) := by
  have hf := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := List.range k) (c := 3 * C₂.length + 2) (P := fun j => decide (j ∉ C₂))
    (p := fun j => Prog.bind (SoJProg.memProg j C₂) fun b => .op1 .not b) fun j _ =>
      RunsWithin.bind_le (SoJProg.RunsWithin.memProg j C₂)
        (RunsWithin.prim_le (by simp [Prim.eval]) le_rfl) (by simp [Prim.cost])
  have hjs : ((List.range k).filter fun j => decide (j ∉ C₂)).length ≤ B :=
    (List.length_filter_le _ _).trans ((List.length_range).le.trans hk)
  refine RunsWithin.bind_le hf (RunsWithin.sp_callProg m k V₁' cs hoffs a D _ hB hm hcs hjs) ?_
  simp only [List.length_range]
  have h1 : k * (3 * C₂.length + 2 + 4) ≤ B * (3 * B + 6) := Nat.mul_le_mul hk (by omega)
  have e : B * (3 * B + 6) = 3 * B ^ 2 + 6 * B := by ring
  have p1 : B ≤ B ^ 2 := by nlinarith
  omega

/-- The branch of `dlI` with a non-constant rectangle: `cohI`. -/
theorem sp_dlBig_coh (m t k : ℕ) (V₁' C₁ C₂ : List ℕ) (cs : List (List ℕ)) (D : List ℕ)
    (c : Array ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B)
    (hD : D.length ≤ B) (hV : V₁'.length ≤ B) (hC₁ : C₁.length ≤ V₁'.length)
    (hC₂ : C₂.length * C₂.length + 1 ≤ B) (hN : m + k + C₁.length + C₂.length ≤ B)
    (hC₂k : ∀ j ∈ C₂, j < k) :
    RunsWithin X body (Prog.bind (SoJTree.sp_diffProg V₁' C₁) fun D₂ =>
        SoJTree.sp_cohIProg m t k cs.toArray D D₂ C₁ C₂ (offsArr (m + k)) c)
      (splitI (cohI m t k cs D (diffD V₁' C₁) C₁ C₂ (fA (offsArr (m + k)) c)).1)
      (116100 * B ^ 7 *
        (1 + (cohI m t k cs D (diffD V₁' C₁) C₁ C₂ (fA (offsArr (m + k)) c)).2)) := by
  have hD₂ : (diffD V₁' C₁).length ≤ B := (List.length_filter_le _ _).trans hV
  refine RunsWithin.bind_le (RunsWithin.sp_diffProg V₁' C₁)
    (RunsWithin.sp_cohIProg m t k cs D (diffD V₁' C₁) C₁ C₂ c hB hm hcs hD hD₂ (hC₁.trans hV)
      hC₂ hN hC₂k) ?_
  have h1 : V₁'.length * (3 * C₁.length + 6) ≤ B * (3 * B + 6) := Nat.mul_le_mul hV (by omega)
  have e : B * (3 * B + 6) = 3 * B ^ 2 + 6 * B := by ring
  have p1 : B ≤ B ^ 7 := by nlinarith [sp_pow_le hB (show 1 ≤ 7 by norm_num)]
  have p2 : B ^ 2 ≤ B ^ 7 := sp_pow_le hB (by norm_num)
  have e' : ∀ w : ℕ, 116100 * B ^ 7 * (1 + w) = 116000 * B ^ 7 * (1 + w) + 100 * B ^ 7 * (1 + w) :=
    fun w => by ring
  rw [e']
  have : 100 * B ^ 7 ≤ 100 * B ^ 7 * (1 + (cohI m t k cs D (diffD V₁' C₁) C₁ C₂
      (fA (offsArr (m + k)) c)).2) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The last branch of `dlI`, the program.** -/
theorem RunsWithin.sp_dlBigProg (m t k : ℕ) (V₁' : List ℕ) (cs : List (List ℕ))
    {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool) (D : List ℕ)
    (c : Array ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hkk : k * k + 1 ≤ B)
    (hN : m + 2 * k + V₁'.length ≤ B) (hD : D.length ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B)
    (hcsl : cs.length ≤ B) :
    RunsWithin X body (SoJTree.sp_dlBigProg m t k (2 * k / 3) V₁' cs cs.toArray a offs
        (List.range k) D (offsArr (m + k)) c
        ((List.range k).map fun j => fA (offsArr (m + k)) c (m + j) (m + j)).toArray)
      (splitI (sp_dlBigI m t k V₁' cs a D (fA (offsArr (m + k)) c)).1)
      (117000 * B ^ 7 * (1 + (sp_dlBigI m t k V₁' cs a D (fA (offsArr (m + k)) c)).2)) := by
  set f := fA (offsArr (m + k)) c with hf
  set col₂ := ((List.range k).map fun j => f (m + j) (m + j)).toArray with hcol₂
  set C₂ := bigL (List.range k) (get col₂) (2 * k / 3) with hC₂
  set colP := ((List.range m).map fun y => f y y).toArray with hcolP
  set C₁ := bigL V₁' (get colP) t with hC₁
  have hC₂l : C₂.length ≤ k := (sp_length_bigL _ _ _).trans (List.length_range).le
  have hC₁l : C₁.length ≤ V₁'.length := sp_length_bigL _ _ _
  have hC₂k : ∀ j ∈ C₂, j < k := fun j hj => List.mem_range.1 (sp_bigL_sub _ _ _ j hj)
  have hk : k ≤ B := by omega
  have hV : V₁'.length ≤ B := by omega
  have hC₂B : C₂.length * C₂.length + 1 ≤ B := by nlinarith
  have hdiag := (RunsWithin.sp_diagProg (X := X) (body := body) (offsArr (m + k)) c 0 m).of_eq
    (show _ = colP by simp only [Nat.zero_add, hcolP, hf])
  have p1 : B ≤ B ^ 7 := by nlinarith [sp_pow_le hB (show 1 ≤ 7 by norm_num)]
  have p2 : B ^ 2 ≤ B ^ 7 := sp_pow_le hB (by norm_num)
  have hpre : k * (7 * k + 9) + 2 + 1 + (9 * m + 5) + (V₁'.length * (7 * V₁'.length + 9) + 2) + 1
      ≤ 60 * B ^ 2 := by
    have h1 : k * (7 * k + 9) ≤ B * (7 * B + 9) := Nat.mul_le_mul hk (by omega)
    have h2 : V₁'.length * (7 * V₁'.length + 9) ≤ B * (7 * B + 9) := Nat.mul_le_mul hV (by omega)
    have e : B * (7 * B + 9) = 7 * B ^ 2 + 9 * B := by ring
    have p1 : B ≤ B ^ 2 := by nlinarith
    omega
  rcases hC₁e : C₁ with _ | ⟨y, ys⟩
  · have hval : sp_dlBigI m t k V₁' cs a D f =
        ([.inl (addPieceD m D (partD colP (colBlkD m V₁' colP)))], 0) := by
      simp only [sp_dlBigI, ← hcolP, ← hC₁, hC₁e, ite_true]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (SoJProg.RunsWithin.bigProg (List.range k) col₂ (2 * k / 3))
      run_step (RunsWithin.prim _ _)
      run_step hdiag
      run_step (SoJProg.RunsWithin.bigProg V₁' colP t)
      rw [← hC₁, hC₁e]
      apply RunsWithin.caseList_nil
      run_step (SoJProg.RunsWithin.colBlkProg m V₁' colP)
      run_step (RunsWithin.partProg _ _)
      run_step (RunsWithin.addPieceProg m D _)
      exact RunsWithin.sp_leafPair _
    case hc =>
      simp only [Prim.cost, List.length_range, colBlkCost, Nat.add_zero, Nat.mul_one]
      have a₁ := sp_addPieceCost_le hm hD
      have h3 : m * (6 * V₁'.length + 7) ≤ B * (6 * B + 7) := Nat.mul_le_mul hm (by omega)
      have e : B * (6 * B + 7) = 6 * B ^ 2 + 7 * B := by ring
      omega
  have hne : C₁ ≠ [] := by rw [hC₁e]; exact List.cons_ne_nil _ _
  have hR := RunsWithin.sp_rectProg (X := X) (body := body) (offsArr (m + k)) c m k
  have hcr := SoJProg.RunsWithin.constRectProg (X := X) (body := body) C₁ C₂ (rectArr m k f)
  have hrect : m * (8 * k + 9) + k + 5 + (C₁.length * (C₂.length * 5 + 3) + 8) ≤ 40 * B ^ 2 := by
    have h1 : m * (8 * k + 9) ≤ B * (8 * B + 9) := Nat.mul_le_mul hm (by omega)
    have h2 : C₁.length * (C₂.length * 5 + 3) ≤ B * (B * 5 + 3) :=
      Nat.mul_le_mul (hC₁l.trans hV) (by omega)
    have e : B * (8 * B + 9) + B * (B * 5 + 3) = 13 * B ^ 2 + 12 * B := by ring
    have p1 : B ≤ B ^ 2 := by nlinarith
    omega
  by_cases hct : constRectL C₁ C₂ (Coherent.get2 (rectArr m k f)) = true
  · have hval : sp_dlBigI m t k V₁' cs a D f =
        ([shrinkI k V₁' (subCells cs ((List.range k).filter fun j => j ∉ C₂))
          (restrictRel m k a ((List.range k).filter fun j => j ∉ C₂)) [pieceOp D]], 0) := by
      simp only [sp_dlBigI, ← hcolP, ← hC₁, ← hcol₂, ← hC₂, hne, hct, ite_true, ite_false]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (SoJProg.RunsWithin.bigProg (List.range k) col₂ (2 * k / 3))
      run_step (RunsWithin.prim _ _)
      run_step hdiag
      run_step (SoJProg.RunsWithin.bigProg V₁' colP t)
      rw [← hC₁, hC₁e]
      apply RunsWithin.caseList_cons
      rw [← hC₁e]
      run_step hR
      run_step hcr
      apply RunsWithin.ite_pos hct
      exact sp_dlBig_rect m k V₁' C₂ cs hoffs a D hB hm hk (hC₂l.trans hk) hcsl
    case hc =>
      simp only [Prim.cost, List.length_range, Nat.add_zero, Nat.mul_one]
      omega
  · have hct' : constRectL C₁ C₂ (Coherent.get2 (rectArr m k f)) = false := by simpa using hct
    have hval : sp_dlBigI m t k V₁' cs a D f = cohI m t k cs D (diffD V₁' C₁) C₁ C₂ f := by
      simp only [sp_dlBigI, ← hcolP, ← hC₁, ← hcol₂, ← hC₂, hne, hct', ite_false,
        Bool.false_eq_true]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (SoJProg.RunsWithin.bigProg (List.range k) col₂ (2 * k / 3))
      run_step (RunsWithin.prim _ _)
      run_step hdiag
      run_step (SoJProg.RunsWithin.bigProg V₁' colP t)
      rw [← hC₁, hC₁e]
      apply RunsWithin.caseList_cons
      rw [← hC₁e]
      run_step hR
      run_step hcr
      apply RunsWithin.ite_neg hct'
      exact sp_dlBig_coh m t k V₁' C₁ C₂ cs D c hB hm hcs hD hV hC₁l hC₂B (by omega) hC₂k
    case hc =>
      simp only [Prim.cost, List.length_range, ← hf]
      have e' : ∀ w : ℕ, 117000 * B ^ 7 * (1 + w) =
          116100 * B ^ 7 * (1 + w) + 900 * B ^ 7 * (1 + w) := fun w => by ring
      rw [e']
      have : 900 * B ^ 7 ≤ 900 * B ^ 7 * (1 + (cohI m t k cs D (diffD V₁' C₁) C₁ C₂ f).2) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega

/-- **The Weisfeiler–Leman cost**, from the bounds of `GraphIso/Solver/Coherent.lean`. -/
theorem sp_wlCost_le (d v : ℕ) :
    Coherent.wlCost d v ≤ 603 * (v ^ d + 1) ^ 3 * ((v + 2) * (d + 2)) ^ 2 * (d ^ d + 1) := by
  have h₁ := Coherent.infoCost_le v d
  have h₂ := Coherent.wlRunCost_le v d
  have hA : v ^ d + 1 ≤ (v ^ d + 1) ^ 3 :=
    Nat.le_self_pow (by norm_num) _
  have h₃ : 114 * (v ^ d + 1) * ((v + 2) * (d + 2)) ^ 2 * (d ^ d + 1) ≤
      114 * (v ^ d + 1) ^ 3 * ((v + 2) * (d + 2)) ^ 2 * (d ^ d + 1) := by
    gcongr
  unfold Coherent.wlCost
  nlinarith

theorem sp_wlCost2_le {n B : ℕ} (hn : n + 1 ≤ B) : Coherent.wlCost 2 n ≤ 192960 * B ^ 8 := by
  have h := sp_wlCost_le 2 n
  have h₁ : n ^ 2 + 1 ≤ B ^ 2 := by nlinarith
  have h₂ : (n + 2) * (2 + 2) ≤ 8 * B := by omega
  have h₃ : (n ^ 2 + 1) ^ 3 * ((n + 2) * (2 + 2)) ^ 2 * (2 ^ 2 + 1) ≤
      (B ^ 2) ^ 3 * (8 * B) ^ 2 * 5 := by
    gcongr
    norm_num
  have e : (B ^ 2) ^ 3 * (8 * B) ^ 2 * 5 = 320 * B ^ 8 := by ring
  have e' : 603 * (n ^ 2 + 1) ^ 3 * ((n + 2) * (2 + 2)) ^ 2 * (2 ^ 2 + 1) =
      603 * ((n ^ 2 + 1) ^ 3 * ((n + 2) * (2 + 2)) ^ 2 * (2 ^ 2 + 1)) := by ring
  omega

theorem sp_sqCodeArrCost_le {m p q B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hpq : p + q ≤ B) :
    sqCodeArrCost m p q ≤ 200 * B ^ 3 := by
  unfold sqCodeArrCost Coherent.tupsCost Coherent.extCost
  have h₁ : p * (3 * m + 5) ≤ B * (3 * B + 5) := Nat.mul_le_mul (by omega) (by omega)
  have h₂ : q * (3 * q + 5) ≤ B * (3 * B + 5) := Nat.mul_le_mul (by omega) (by omega)
  have h₃ : (p + q) ^ 2 ≤ B ^ 2 := Nat.pow_le_pow_left hpq 2
  have h₄ : ((p + q) ^ 2 + 1) * (4 * (p + q) + 1) ≤ (B ^ 2 + 1) * (4 * B + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e₁ : B * (3 * B + 5) = 3 * B ^ 2 + 5 * B := by ring
  have e₂ : (B ^ 2 + 1) * (4 * B + 1) = 4 * B ^ 3 + B ^ 2 + 4 * B + 1 := by ring
  have p1 : B ≤ B ^ 3 := by nlinarith [sp_pow_le hB (show 1 ≤ 3 by norm_num)]
  have p2 : B ^ 2 ≤ B ^ 3 := sp_pow_le hB (by norm_num)
  omega

theorem sp_cQArrCost_le {p k N B : ℕ} (hB : 1 ≤ B) (hp : p + k ≤ B) (hN : N ≤ B) :
    cQArrCost p k N ≤ 120 * B ^ 3 := by
  unfold cQArrCost
  have h₀ : N * (24 * p + 49) ≤ B * (24 * B + 49) := Nat.mul_le_mul hN (by omega)
  have h₁ : N * (N * (24 * p + 49) + 5) ≤ B * (B * (24 * B + 49) + 5) :=
    Nat.mul_le_mul hN (by omega)
  have h₂ : 2 * N * N ≤ 2 * B * B := Nat.mul_le_mul (by omega) hN
  have e : B * (B * (24 * B + 49) + 5) = 24 * B ^ 3 + 49 * B ^ 2 + 5 * B := by ring
  have e' : 2 * B * B = 2 * B ^ 2 := by ring
  have p1 : B ≤ B ^ 3 := by nlinarith [sp_pow_le hB (show 1 ≤ 3 by norm_num)]
  have p2 : B ^ 2 ≤ B ^ 3 := sp_pow_le hB (by norm_num)
  omega

theorem sp_skelArrCost_le {k d l B : ℕ} (hB : 1 ≤ B) (hk : k ≤ B) (hd : d ≤ B) (hl : l ≤ B) :
    skelArrCost k d l ≤ 40 * B ^ 3 := by
  unfold skelArrCost
  have h₀ : k * (8 * d + 5) ≤ B * (8 * B + 5) := Nat.mul_le_mul hk (by omega)
  have h₁ : k * (k * (8 * d + 5) + 5) ≤ B * (B * (8 * B + 5) + 5) :=
    Nat.mul_le_mul hk (by omega)
  have h₂ : 2 * k * k ≤ 2 * B * B := Nat.mul_le_mul (by omega) hk
  have e : B * (B * (8 * B + 5) + 5) = 8 * B ^ 3 + 5 * B ^ 2 + 5 * B := by ring
  have e' : 2 * B * B = 2 * B ^ 2 := by ring
  have p1 : B ≤ B ^ 3 := by nlinarith [sp_pow_le hB (show 1 ≤ 3 by norm_num)]
  have p2 : B ^ 2 ≤ B ^ 3 := sp_pow_le hB (by norm_num)
  omega

/-- **`dlI` after a dominant colour, the program.** -/
theorem RunsWithin.sp_dlSkelProg (m t : ℕ) (V₁' : List ℕ) (hV' : ∀ x ∈ V₁', x < m)
    (cs : List (List ℕ)) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * cs.length)
    (a : Array Bool) (d : ℕ) (wl : Array ℕ) (xd D : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hkk : cs.length * cs.length + 1 ≤ B) (hN : m + 2 * cs.length + V₁'.length + 1 ≤ B)
    (hD : D.length ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B) (hd : d ≤ B) (hxd : xd.length ≤ B) :
    RunsWithin X body (SoJTree.sp_dlSkelProg m t cs.length (2 * cs.length / 3) V₁' cs
        cs.toArray a offs wl (Coherent.pwTab d cs.length) (List.range d) (List.range cs.length) D
        xd)
      (splitI (sp_dlSkelI m t V₁' cs a d wl xd D).1)
      (320000 * B ^ 8 * (1 + (sp_dlSkelI m t V₁' cs a d wl xd D).2)) := by
  set k := cs.length with hk
  set W2 := (Coherent.wlA 2 (V₁'.length + k) (sqCodeArr V₁' k a (skelArrD wl d k xd))).1
    with hW2
  set f := fA (offsArr (m + k)) (cQArr m V₁' k W2) with hf
  set col₂ := ((List.range k).map fun j => f (m + j) (m + j)).toArray with hcol₂
  have hkB : k ≤ B := by omega
  have hV : V₁'.length ≤ B := by omega
  have hsk := sp_skelArrCost_le hB hkB hd hxd
  have hsq := sp_sqCodeArrCost_le (p := V₁'.length) (q := k) hB hm (by omega)
  have hwl := sp_wlCost2_le (n := V₁'.length + k) (B := B) (by omega)
  have hcq := sp_cQArrCost_le (p := V₁'.length) (k := k) (N := m + k) hB (by omega) (by omega)
  have p3 : B ^ 3 ≤ B ^ 8 := sp_pow_le hB (by norm_num)
  have p7 : B ^ 7 ≤ B ^ 8 := sp_pow_le hB (by norm_num)
  have p2 : B ^ 2 ≤ B ^ 8 := sp_pow_le hB (by norm_num)
  have p1 : B ≤ B ^ 8 := by nlinarith [sp_pow_le hB (show 1 ≤ 8 by norm_num)]
  have hsm : k * (7 * k + 8) ≤ B * (7 * B + 8) := Nat.mul_le_mul hkB (by omega)
  have esm : B * (7 * B + 8) = 7 * B ^ 2 + 8 * B := by ring
  by_cases hsmall : allSmallL (List.range k) (get col₂) (2 * k / 3) = true
  · have hval : sp_dlSkelI m t V₁' cs a d wl xd D =
        ([shrinkI k V₁' (subCells cs (pickSideD V₁' k a (selThirdL (List.range k) (get col₂))))
          (restrictRel m k a (pickSideD V₁' k a (selThirdL (List.range k) (get col₂))))
          [pieceOp D]], 0) := by
      simp only [sp_dlSkelI, ← hk, ← hW2, ← hf, ← hcol₂, hsmall, ite_true]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.sp_skelArrProg wl d k xd)
      run_step (SoJProg.RunsWithin.cohProg V₁' hV' k a _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sp_cQArrProg m k V₁' W2)
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.csOffsProg (m + k))
      run_step (RunsWithin.sp_diagProg (offsArr (m + k)) (cQArr m V₁' k W2) m k)
      run_step (SoJProg.RunsWithin.allSmallProg (List.range k) col₂ (2 * k / 3))
      apply RunsWithin.ite_pos hsmall
      exact RunsWithin.sp_selCallProg m k V₁' hV' cs hoffs a D col₂ hB hm hkB (by omega) hV
    case hc =>
      simp only [Prim.cost, List.length_range, Nat.add_zero, Nat.mul_one]
      omega
  · have hsmall' : allSmallL (List.range k) (get col₂) (2 * k / 3) = false := by simpa using hsmall
    have hval : sp_dlSkelI m t V₁' cs a d wl xd D = sp_dlBigI m t k V₁' cs a D f := by
      simp only [sp_dlSkelI, ← hk, ← hW2, ← hf, ← hcol₂, hsmall', ite_false, Bool.false_eq_true]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.sp_skelArrProg wl d k xd)
      run_step (SoJProg.RunsWithin.cohProg V₁' hV' k a _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sp_cQArrProg m k V₁' W2)
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.csOffsProg (m + k))
      run_step (RunsWithin.sp_diagProg (offsArr (m + k)) (cQArr m V₁' k W2) m k)
      run_step (SoJProg.RunsWithin.allSmallProg (List.range k) col₂ (2 * k / 3))
      apply RunsWithin.ite_neg hsmall'
      exact RunsWithin.sp_dlBigProg m t k V₁' cs hoffs a D (cQArr m V₁' k W2) hB hm hkk
        (by omega) hD hcs (by omega)
    case hc =>
      simp only [Prim.cost, List.length_range, ← hf]
      have e' : ∀ w : ℕ, 320000 * B ^ 8 * (1 + w) =
          117000 * B ^ 7 * (1 + w) + (320000 * B ^ 8 - 117000 * B ^ 7) * (1 + w) := fun w => by
        rw [← Nat.add_mul, Nat.add_sub_cancel' (by omega)]
      rw [e']
      have : 320000 * B ^ 8 - 117000 * B ^ 7 ≤
          (320000 * B ^ 8 - 117000 * B ^ 7) * (1 + (sp_dlBigI m t k V₁' cs a D f).2) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega

/-- **`dlCont` on data, the program**: `dlI` after the choice `xd`, as a split pair, within
`330000 B^8 (1 + w)` for its work `w`. -/
theorem RunsWithin.sp_dlProg (m t : ℕ) (V₁ V₁' : List ℕ) (hV' : ∀ x ∈ V₁', x < m)
    (cs : List (List ℕ)) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * cs.length)
    (a : Array Bool) (d : ℕ) (wl : Array ℕ) (xd : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hkk : cs.length * cs.length + 1 ≤ B) (hN : m + 2 * cs.length + V₁'.length + 1 ≤ B)
    (hD : (diffD V₁ V₁').length ≤ B) (hcs : ∀ c ∈ cs, c.length ≤ B) (hd : d ≤ B)
    (hxd : xd.length ≤ B) :
    RunsWithin X body (SoJTree.sp_dlProg m t cs.length (2 * cs.length / 3) V₁' cs cs.toArray a
        offs wl (Coherent.pwTab d cs.length) (List.range d) (List.range cs.length) (diffD V₁ V₁')
        xd)
      (splitI (dlI m t V₁ V₁' cs a d wl xd).1)
      (330000 * B ^ 8 * (1 + (dlI m t V₁ V₁' cs a d wl xd).2)) := by
  rw [sp_dlI_eq]
  set k := cs.length with hk
  set col1 := Coherent.col1A wl (Coherent.pwTab d k) d k xd.length xd.toArray with hcol1
  have hl1 : col1.length = k := Coherent.length_col1A _ _ _ _ _ _
  have hkB : k ≤ B := by omega
  have hV : V₁'.length ≤ B := by omega
  have p8 : B ^ 3 ≤ B ^ 8 := sp_pow_le hB (by norm_num)
  have p2 : B ^ 2 ≤ B ^ 8 := sp_pow_le hB (by norm_num)
  have p1 : B ≤ B ^ 8 := by nlinarith [sp_pow_le hB (show 1 ≤ 8 by norm_num)]
  have hc1 : k * (7 * d + 5) ≤ B * (7 * B + 5) := Nat.mul_le_mul hkB (by omega)
  have hdm : col1.length * (6 * col1.length + 9) ≤ B * (6 * B + 9) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e₁ : B * (7 * B + 5) = 7 * B ^ 2 + 5 * B := by ring
  have e₂ : B * (6 * B + 9) = 6 * B ^ 2 + 9 * B := by ring
  rcases hdom : Coherent.domA col1 (2 * k / 3) with _ | u
  · simp only [Nat.add_zero, Nat.mul_one]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (Coherent.RunsWithin.col1Prog wl (Coherent.pwTab d k) d k xd.length xd.toArray)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (Coherent.RunsWithin.domProg col1 (2 * k / 3))
      rw [hdom]
      apply RunsWithin.caseOption_none
      exact RunsWithin.sp_selCallProg m k V₁' hV' cs hoffs a (diffD V₁ V₁') col1.toArray hB hm
        hkB (by omega) hV
    case hc =>
      simp only [Prim.cost, Args.head, Prim.eval, Coherent.length_col1A]
      omega
  · simp only
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (Coherent.RunsWithin.col1Prog wl (Coherent.pwTab d k) d k xd.length xd.toArray)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (Coherent.RunsWithin.domProg col1 (2 * k / 3))
      rw [hdom]
      apply RunsWithin.caseOption_some
      exact RunsWithin.sp_dlSkelProg m t V₁' hV' cs hoffs a d wl xd (diffD V₁ V₁') hB hm hkk hN
        hD hcs hd hxd
    case hc =>
      simp only [Prim.cost, Args.head, Prim.eval, Coherent.length_col1A]
      have e' : ∀ w : ℕ, 330000 * B ^ 8 * (1 + w) =
          320000 * B ^ 8 * (1 + w) + 10000 * B ^ 8 * (1 + w) := fun w => by ring
      rw [e']
      have : 10000 * B ^ 8 ≤ 10000 * B ^ 8 * (1 + (sp_dlSkelI m t V₁' cs a d wl xd
          (diffD V₁ V₁')).2) := Nat.le_mul_of_pos_right _ (by omega)
      omega

/-! #### The exponential parts of the `d`-ary step -/

theorem sp_pow_arity_le (k s n : ℕ) : k ^ arity k s n ≤ (k * n) ^ 6 + 1 := by
  by_cases hk : k ≤ 1
  · have : k ^ arity k s n ≤ 1 ^ arity k s n := Nat.pow_le_pow_left hk _
    simp only [one_pow] at this
    omega
  by_cases hn : n ≤ 1
  · have : arity k s n = 0 := by
      unfold arity
      rw [Nat.clog_of_right_le_one hn]
      simp
    rw [this]
    simp
  have hlt := Nat.pow_pred_clog_lt_self (by omega : 1 < k) (by omega : 1 < n)
  have hpos := Nat.clog_pos (by omega : 1 < k) (by omega : 1 < n)
  have hc : k ^ Nat.clog k n ≤ k * n := by
    have e : k ^ Nat.clog k n = k * k ^ (Nat.clog k n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [e]
    exact Nat.mul_le_mul_left _ (by rw [Nat.pred_eq_sub_one] at hlt; omega)
  calc k ^ arity k s n ≤ k ^ (6 * Nat.clog k n) :=
        Nat.pow_le_pow_right (by omega) (min_le_right _ _)
    _ = (k ^ Nat.clog k n) ^ 6 := by rw [mul_comm, pow_mul]
    _ ≤ (k * n) ^ 6 := Nat.pow_le_pow_left hc 6
    _ ≤ (k * n) ^ 6 + 1 := Nat.le_succ _

/-- **`d^d` is polynomial outside the base case** (`d` the arity, `n ≤ 2t` points). -/
theorem sp_pow_self_arity_le {t k s n : ℕ} (hn : n ≤ 2 * t) (hb : ¬IsBase t k) :
    arity k s n ^ arity k s n ≤ (k * n) ^ 6 + 46656 := by
  by_cases hk : k ≤ 1
  · have : arity k s n = 0 := by
      unfold arity
      rw [Nat.clog_of_left_le_one hk]
      simp
    rw [this]
    simp
  by_cases hn1 : n ≤ 1
  · have : arity k s n = 0 := by
      unfold arity
      rw [Nat.clog_of_right_le_one hn1]
      simp
    rw [this]
    simp
  set L := Nat.clog 2 (2 * t) with hL
  have hc : Nat.clog k n ≤ L :=
    (Nat.clog_anti_left (by norm_num) (by omega)).trans (Nat.clog_mono_right 2 hn)
  have hd : arity k s n ≤ 6 * L := (min_le_right _ _).trans (by omega)
  unfold IsBase at hb
  rw [← hL] at hb
  by_cases h6 : 6 * L ≤ k
  · have h1 : arity k s n ^ arity k s n ≤ k ^ arity k s n :=
      Nat.pow_le_pow_left (hd.trans h6) _
    have h2 := sp_pow_arity_le k s n
    omega
  · have hL1 : L ≤ 1 := by
      by_contra hL2
      have hL2' : 2 ≤ L := by omega
      have : k * k < 36 * (L * L) := by nlinarith
      have : 2 * (L * L) ≤ L * L * L := by nlinarith
      nlinarith
    have hd6 : arity k s n ≤ 6 := by omega
    calc arity k s n ^ arity k s n ≤ 6 ^ arity k s n := Nat.pow_le_pow_left hd6 _
      _ ≤ 6 ^ 6 := Nat.pow_le_pow_right (by norm_num) hd6
      _ ≤ (k * n) ^ 6 + 46656 := by norm_num

theorem sp_sOf_le (v d₁ : ℕ) : sOf v d₁ ≤ v := by
  unfold sOf
  split <;> omega

theorem sp_length_permutations' (k : ℕ) : ((List.range k).permutations').length = k.factorial := by
  rw [(List.permutations_perm_permutations' _).symm.length_eq, List.length_permutations,
    List.length_range]

theorem sp_length_of_mem_permutations' {k : ℕ} {js : List ℕ}
    (h : js ∈ (List.range k).permutations') : js.length = k := by
  rw [List.mem_permutations'] at h
  simpa using h.length_eq

/-- **The base case, the program**: one partition leaf per enumeration. -/
theorem RunsWithin.sp_baseProg (m k : ℕ) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k)
    (a : Array Bool) (V₁ : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hk : k ≤ B)
    (hV : V₁.length ≤ B) :
    RunsWithin X body (SoJTree.sp_baseProg m k offs a V₁)
      (splitI ((List.range k).permutations'.map fun js =>
        .inl (partD (nbrCodeArrD m k a js) (colBlkD m V₁ (nbrCodeArrD m k a js)))))
      (100 * B ^ 3 * (1 + (List.range k).permutations'.length)) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := outTy)
    (xs := (List.range k).permutations') (c := baseLeafCost m V₁.length k + 14)
    (F := fun js => partD (nbrCodeArrD m k a js) (colBlkD m V₁ (nbrCodeArrD m k a js)))
    (f := fun js => .bind (SoJProg.baseLeafProg m offs a V₁ js) fun cb =>
      .bind (.op1 .fst cb) fun col => .bind (.op1 .snd cb) fun blk => SoJTree.partProg col blk)
    fun js hjs => by
      apply RunsWithin.mono
      case h =>
        run_step (SoJProg.RunsWithin.baseLeafProg hoffs a V₁ js)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.partProg _ _
      case hc =>
        simp only [Prim.cost, sp_length_of_mem_permutations' hjs]
        omega
  apply RunsWithin.mono
  case h =>
    run_step (SoJProg.RunsWithin.enumsProg k)
    run_step hmap
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by
      simp only [Prim.eval]
      rw [← splitI_map, List.map_map]
      rfl) le_rfl
  case hc =>
    simp only [Prim.cost, sp_length_permutations', enumsCost, permsCost, insertsCost,
      baseLeafCost, nbrCodeArrCost, nbrCodeCost, colBlkCost]
    set F := k.factorial
    have h1 : k * (F * (k * (4 * k + 9) + k + 7 + 3 * k + 6) + 3) ≤
        F * (B * (B * (4 * B + 9) + B + 7 + 3 * B + 6)) + 3 * B := by
      have h₀ := Nat.mul_le_mul hk (show 4 * k + 9 ≤ 4 * B + 9 by omega)
      have : k * (k * (4 * k + 9) + k + 7 + 3 * k + 6) ≤
          B * (B * (4 * B + 9) + B + 7 + 3 * B + 6) :=
        Nat.mul_le_mul hk (by omega)
      nlinarith
    have h2 : m * (9 * k + 2 + 3) + 2 * m + 4 + (m * (6 * V₁.length + 7) + 2 * m + 4) + 1 + 14 ≤
        B * (15 * B + 16) + 23 := by
      have := Nat.mul_le_mul hm (show 9 * k + 2 + 3 ≤ 9 * B + 5 by omega)
      have := Nat.mul_le_mul hm (show 6 * V₁.length + 7 ≤ 6 * B + 7 by omega)
      nlinarith
    have h3 : F * (m * (9 * k + 2 + 3) + 2 * m + 4 + (m * (6 * V₁.length + 7) + 2 * m + 4) + 1 +
        14 + 3) ≤ F * (B * (15 * B + 16) + 26) := Nat.mul_le_mul_left _ (by omega)
    have e₁ : B * (B * (4 * B + 9) + B + 7 + 3 * B + 6) = 4 * B ^ 3 + 13 * B ^ 2 + 13 * B := by
      ring
    have e₂ : B * (15 * B + 16) = 15 * B ^ 2 + 16 * B := by ring
    have p1 : B ≤ B ^ 3 := by nlinarith [sp_pow_le hB (show 1 ≤ 3 by norm_num)]
    have p2 : B ^ 2 ≤ B ^ 3 := sp_pow_le hB (by norm_num)
    have e₃ : 100 * B ^ 3 * (1 + F) = 100 * B ^ 3 + F * (100 * B ^ 3) := by ring
    have h4 : F * (4 * B ^ 3 + 13 * B ^ 2 + 13 * B) + F * (15 * B ^ 2 + 16 * B + 26) ≤
        F * (100 * B ^ 3) := by
      rw [← Nat.mul_add]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [e₁] at h1
    rw [e₂] at h3
    omega

theorem sp_splitI_length (l : List Item) :
    (splitI l).1.length + (splitI l).2.length = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [show i :: l = [i] ++ l from rfl, splitI_append]
    cases i <;> simp only [splitI_inl, splitI_inr, List.length_append, List.length_cons,
      List.length_nil, List.singleton_append] at ih ⊢ <;> omega

theorem sp_length_cohI (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ C₂ : List ℕ)
    (f : ℕ → ℕ → ℕ) :
    (cohI m t k cs D₁ D₂ C₁ C₂ f).1.length ≤ 1 + (cohI m t k cs D₁ D₂ C₁ C₂ f).2 := by
  unfold cohI
  split <;> simp

theorem sp_length_dlI (m t : ℕ) (V₁ V₁' : List ℕ) (cs : List (List ℕ)) (a : Array Bool)
    (d : ℕ) (wl : Array ℕ) (xd : List ℕ) :
    (dlI m t V₁ V₁' cs a d wl xd).1.length ≤ 1 + (dlI m t V₁ V₁' cs a d wl xd).2 := by
  rw [sp_dlI_eq]
  split
  · simp
  · unfold sp_dlSkelI
    dsimp only
    split
    · simp
    · unfold sp_dlBigI
      dsimp only
      split
      · simp
      · split
        · simp
        · exact sp_length_cohI _ _ _ _ _ _ _ _ _

theorem sp_length_mem_goodList {c : Array ℕ} {k m t : ℕ} {xd : List ℕ}
    (h : xd ∈ goodList c k m t) : xd.length < k := by
  obtain ⟨h₁, -⟩ := List.mem_filter.1 h
  obtain ⟨l, hl, hx⟩ := List.mem_flatMap.1 h₁
  rw [length_of_mem_tupList hx]
  exact List.mem_range.1 hl

theorem sp_length_bigTwinsD (v d : ℕ) (col : Array ℕ) : (bigTwinsD v d col).length ≤ v :=
  (List.length_filter_le _ _).trans (List.length_range).le

/-- The `d`-ary step with a big twin class: a guarded call. -/
theorem RunsWithin.sp_daryRecProg (m k : ℕ) (V₁' : List ℕ) (hV' : ∀ x ∈ V₁', x < m)
    (cs : List (List ℕ)) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * k) (a : Array Bool)
    (D S' : List ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hk : k ≤ B) (hV : V₁'.length ≤ B)
    (hcs : cs.length ≤ B) (hS : S'.length ≤ k) :
    RunsWithin X body (SoJTree.sp_daryRecProg m k offs a V₁' cs D S')
      (splitI [recI k V₁' (subCells cs (pickSideD V₁' k a S'))
        (restrictRel m k a (pickSideD V₁' k a S')) [pieceOp D]]) (150 * B ^ 3) := by
  have hjs := sp_length_pickSideD V₁' k a hS
  apply RunsWithin.mono
  case h =>
    run_step (SoJProg.RunsWithin.pickSideProg V₁' hV' k a S')
    run_step (RunsWithin.sp_subCellsProg cs _)
    run_step (RunsWithin.sp_restrictRelProg hoffs a _)
    run_step (RunsWithin.sp_pieceProg D)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.sp_recIProg _ _ _ _ _
  case hc =>
    simp only [Prim.cost, pickCost, subCells, List.length_map]
    have h1 : V₁'.length * (3 * m + 6) ≤ B * (3 * B + 6) := Nat.mul_le_mul hV (by omega)
    have h2 : V₁'.length * (V₁'.length * (8 * S'.length + 5) + 5) ≤ B * (B * (8 * B + 5) + 5) := by
      have := Nat.mul_le_mul hV (show 8 * S'.length + 5 ≤ 8 * B + 5 by omega)
      exact Nat.mul_le_mul hV (by omega)
    have h3 : m * ((pickSideD V₁' k a S').length * 6 + 5) ≤ B * (B * 6 + 5) :=
      Nat.mul_le_mul hm (by omega)
    have h4 : 2 * m * ((pickSideD V₁' k a S').length + 3) ≤ 2 * B * (B + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : B * (3 * B + 6) + B * (B * (8 * B + 5) + 5) + B * (B * 6 + 5) + 2 * B * (B + 3) =
        8 * B ^ 3 + 16 * B ^ 2 + 22 * B := by ring
    have p1 : B ≤ B ^ 3 := by nlinarith [sp_pow_le hB (show 1 ≤ 3 by norm_num)]
    have p2 : B ^ 2 ≤ B ^ 3 := sp_pow_le hB (by norm_num)
    omega

/-! #### Costs of the `d`-ary step in terms of a bound `Q` on `k + 2`, `d + 2`, `k^d + 2` and
`d^d + 1` -/

theorem sp_daryArrCost_le {k d n Q : ℕ} (hQ : 1 ≤ Q) (hk : k ≤ Q) (hd : d ≤ Q) (hn : n ≤ Q)
    (hK : k ^ d + 1 ≤ Q) : daryArrCost k d n ≤ 63 * Q ^ 3 := by
  have hK' : k ^ d ≤ Q := by omega
  have h : daryArrCost k d n ≤ Q * (8 * Q + 8) + (Q + Q + 5 + Q * (1 + (Q * (4 * Q + 1) + 2))) +
      Q * (Q * (5 * Q + 5) + Q * (3 * Q + 5) + 5 + 4) + 5 := by
    unfold daryArrCost Coherent.tupsCost Coherent.extCost daryEntryCost
    gcongr
  have p1 := sp_pow_le hQ (show 1 ≤ 3 by norm_num)
  have p2 := sp_pow_le hQ (show 2 ≤ 3 by norm_num)
  have p0 := sp_pow_le hQ (show 0 ≤ 3 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

theorem sp_bigTwinsCost_le {k d Q : ℕ} (hQ : 1 ≤ Q) (hk : k ≤ Q) (hd : d ≤ Q)
    (hK : k ^ d + 1 ≤ Q) : bigTwinsCost k d ≤ 100 * Q ^ 4 := by
  have hK' : k ^ d ≤ Q := by omega
  have h : bigTwinsCost k d ≤ 2 * Q + Q + 6 + (Q * (11 * Q + 15) + 6) +
      (Q + Q + 5 + Q * (1 + (Q * (4 * Q + 1) + 2))) +
        Q * (Q * (Q * (21 * Q + 11) + 1 + 4) + 7) := by
    unfold bigTwinsCost Coherent.pwTabCost Coherent.tupsCost Coherent.extCost twinBCost
    gcongr
  have p1 := sp_pow_le hQ (show 1 ≤ 4 by norm_num)
  have p2 := sp_pow_le hQ (show 2 ≤ 4 by norm_num)
  have p3 := sp_pow_le hQ (show 3 ≤ 4 by norm_num)
  have p0 := sp_pow_le hQ (show 0 ≤ 4 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

theorem sp_wlCostQ_le {k d Q : ℕ} (hk : k + 2 ≤ Q) (hd : d + 2 ≤ Q)
    (hK : k ^ d + 1 ≤ Q) (hDd : d ^ d + 1 ≤ Q) : Coherent.wlCost d k ≤ 603 * Q ^ 8 := by
  have h₁ := Coherent.infoCost_le k d
  have h₂ := Coherent.wlRunCost_le k d
  have h₃ : (k ^ d + 1) ^ 3 * ((k + 2) * (d + 2)) ^ 2 * (d ^ d + 1) ≤
      Q ^ 3 * (Q * Q) ^ 2 * Q := by
    gcongr
  have h₄ : (k ^ d + 1) * ((k + 2) * (d + 2)) ^ 2 * (d ^ d + 1) ≤ Q ^ 3 * (Q * Q) ^ 2 * Q := by
    have : k ^ d + 1 ≤ Q ^ 3 := hK.trans (Nat.le_self_pow (by norm_num) _)
    gcongr
  have e : Q ^ 3 * (Q * Q) ^ 2 * Q = Q ^ 8 := by ring
  unfold Coherent.wlCost
  have e₁ : 114 * (k ^ d + 1) * ((k + 2) * (d + 2)) ^ 2 * (d ^ d + 1) =
      114 * ((k ^ d + 1) * ((k + 2) * (d + 2)) ^ 2 * (d ^ d + 1)) := by ring
  have e₂ : 489 * (k ^ d + 1) ^ 3 * ((k + 2) * (d + 2)) ^ 2 * (d ^ d + 1) =
      489 * ((k ^ d + 1) ^ 3 * ((k + 2) * (d + 2)) ^ 2 * (d ^ d + 1)) := by ring
  omega

theorem sp_goodListCost_le {k d Q : ℕ} (hQ : 1 ≤ Q) (hk : k ≤ Q) (hd : d ≤ Q)
    (hK : k ^ d + 2 ≤ Q) : goodListCost d k ≤ 400 * Q ^ 5 := by
  have hK' : k ^ d + 1 ≤ Q := by omega
  have h : goodListCost d k ≤ Q + Q + 4 + (Q * (11 * Q + 15) + 6) + Q * (1 + (Q + Q + 5 +
      Q * (1 + (Q * (4 * Q + 1) + 2))) + Q * (2 * Q + 2 + (Q * (7 * Q + 5) + 2) + (Q + 1) +
      (Q * (6 * Q + 9) + 1) + 5 + (6 * Q + 3) + (Q * (Q * (8 * Q + 6) + 1) + Q * Q + 2) +
      (3 * (Q * Q) + 3) + 3 + 6)) + (Q * Q + 1) := by
    unfold goodListCost Coherent.pwTabCost Coherent.tupsBound Coherent.extCost Coherent.goodCost
    gcongr
  have p1 := sp_pow_le hQ (show 1 ≤ 5 by norm_num)
  have p2 := sp_pow_le hQ (show 2 ≤ 5 by norm_num)
  have p3 := sp_pow_le hQ (show 3 ≤ 5 by norm_num)
  have p4 := sp_pow_le hQ (show 4 ≤ 5 by norm_num)
  have p0 := sp_pow_le hQ (show 0 ≤ 5 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

theorem sp_sum_work {α : Type*} (xs : List α) (w L : α → ℕ) (A : ℕ)
    (hL : ∀ x ∈ xs, L x ≤ 1 + w x) :
    (xs.map fun x => A * (1 + w x) + 2).sum + 15 * xs.length + (xs.map L).sum ≤
      (A + 18) * (xs.length + (xs.map w).sum) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h₁ := hL x List.mem_cons_self
    have h₂ := ih fun y hy => hL y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have e : (A + 18) * (xs.length + 1 + (w x + (xs.map w).sum)) =
        (A + 18) * (xs.length + (xs.map w).sum) + (A * (1 + w x) + 18 + 18 * w x) := by ring
    rw [e]
    omega

/-- **The `d`-ary step without big twin classes, the program**: the Design Lemma options and
`dlI` at each. -/
theorem RunsWithin.sp_daryDLProg (m t : ℕ) (V₁ V₁' : List ℕ) (hV' : ∀ x ∈ V₁', x < m)
    (cs : List (List ℕ)) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * cs.length)
    (a : Array Bool) (d : ℕ) (hs : List (List ℕ)) (hlen : ∀ h ∈ hs, h.length ≤ cs.length)
    {B Q : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hkk : cs.length * cs.length + 1 ≤ B)
    (hN : m + 2 * cs.length + V₁'.length + 1 ≤ B) (hD : (diffD V₁ V₁').length ≤ B)
    (hcs : ∀ c ∈ cs, c.length ≤ B) (hd : d ≤ B) (hQ : 1 ≤ Q) (hkQ : cs.length + 2 ≤ Q)
    (hdQ : d + 2 ≤ Q) (hK : cs.length ^ d + 2 ≤ Q) (hDd : d ^ d + 1 ≤ Q) (hhs : hs.length ≤ Q) :
    RunsWithin X body (SoJTree.sp_daryDLProg m t cs.length d offs a V₁' cs (diffD V₁ V₁') hs)
      (splitI (((goodList (Coherent.wlA d cs.length (daryArr cs.length d hs)).1 d cs.length
        (2 * cs.length / 3)).map (dlI m t V₁ V₁' cs a d
          (Coherent.wlA d cs.length (daryArr cs.length d hs)).1)).flatMap Prod.fst))
      (2000 * Q ^ 8 + 330100 * B ^ 8 *
        ((goodList (Coherent.wlA d cs.length (daryArr cs.length d hs)).1 d cs.length
          (2 * cs.length / 3)).length +
        (((goodList (Coherent.wlA d cs.length (daryArr cs.length d hs)).1 d cs.length
          (2 * cs.length / 3)).map (dlI m t V₁ V₁' cs a d
            (Coherent.wlA d cs.length (daryArr cs.length d hs)).1)).map Prod.snd).sum)) := by
  set k := cs.length with hk
  set wl := (Coherent.wlA d k (daryArr k d hs)).1 with hwl
  set xs := goodList wl d k (2 * k / 3) with hxs
  have hdl : ∀ xd ∈ xs, RunsWithin X body (SoJTree.sp_dlProg m t k (2 * k / 3) V₁' cs
      cs.toArray a offs wl (Coherent.pwTab d k) (List.range d) (List.range k) (diffD V₁ V₁') xd)
      (splitI (dlI m t V₁ V₁' cs a d wl xd).1)
      (330000 * B ^ 8 * (1 + (dlI m t V₁ V₁' cs a d wl xd).2)) := fun xd hxd =>
    RunsWithin.sp_dlProg m t V₁ V₁' hV' cs hoffs a d wl xd hB hm hkk hN hD hcs hd
      ((sp_length_mem_goodList hxd).le.trans hd)
  have hmap := RunsWithin.mapList (X := X) (body := body) (a' := .list .nat)
    (b' := .prod (.list outTy) (.list frameTy)) hdl
  have hcat := RunsWithin.sp_catProg (X := X) (body := body)
    (xs.map fun xd => splitI (dlI m t V₁ V₁' cs a d wl xd).1)
  rw [sp_cat_splitI xs fun xd => (dlI m t V₁ V₁' cs a d wl xd).1] at hcat
  have hdiv := (RunsWithin.sp_div3Prog (X := X) (body := body) (k + k)).of_eq
    (show (k + k) / 3 = 2 * k / 3 by rw [two_mul])
  apply RunsWithin.mono
  case h =>
    run_step (SoJProg.RunsWithin.daryWLProg k d hs hlen)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hdiv
    run_step (SoJProg.RunsWithin.goodListProg wl d k (2 * k / 3))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.pwTabProg d k)
    run_step hmap
    exact hcat.of_eq (by rw [List.flatMap_map])
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map, List.map_map, Function.comp_def,
      sp_splitI_length]
    dsimp only [Ty.denote]
    have hw := sp_sum_work xs (fun x => (dlI m t V₁ V₁' cs a d wl x).2)
      (fun x => (dlI m t V₁ V₁' cs a d wl x).1.length) (330000 * B ^ 8)
      fun x _ => sp_length_dlI m t V₁ V₁' cs a d wl x
    beta_reduce at hw
    have hA : (330000 * B ^ 8 + 18) * (xs.length + (xs.map fun x =>
        (dlI m t V₁ V₁' cs a d wl x).2).sum) ≤ 330100 * B ^ 8 * (xs.length + (xs.map fun x =>
        (dlI m t V₁ V₁' cs a d wl x).2).sum) :=
      Nat.mul_le_mul_right _ (by have : 1 ≤ B ^ 8 := Nat.one_le_pow _ _ hB; omega)
    have h₁ := sp_daryArrCost_le (k := k) (d := d) (n := hs.length) hQ (by omega) (by omega) hhs
      (by omega)
    have h₂ := sp_wlCostQ_le (k := k) (d := d) hkQ hdQ (by omega) hDd
    have h₃ := sp_goodListCost_le (k := k) (d := d) hQ (by omega) (by omega) hK
    have h₄ : Coherent.pwTabCost d k ≤ 26 * Q ^ 2 := by
      unfold Coherent.pwTabCost
      have := Nat.mul_le_mul (show d ≤ Q by omega) (show 11 * k + 15 ≤ 11 * Q + 15 by omega)
      have e : Q * (11 * Q + 15) = 11 * Q ^ 2 + 15 * Q := by ring
      nlinarith
    have p3 := sp_pow_le hQ (show 3 ≤ 8 by norm_num)
    have p5 := sp_pow_le hQ (show 5 ≤ 8 by norm_num)
    have p2 := sp_pow_le hQ (show 2 ≤ 8 by norm_num)
    have p1 : Q ≤ Q ^ 8 := by nlinarith [sp_pow_le hQ (show 1 ≤ 8 by norm_num)]
    omega

theorem sp_length_fOfD (k : ℕ) (a : Array Bool) (d₁ x : ℕ) : (fOfD k a d₁ x).length ≤ k := by
  unfold fOfD nbrD
  split <;> exact (List.length_filter_le _ _).trans (List.length_range).le

/-- **The `d`-ary step, the program**: within `400000 Q^8 (1 + w)` for its work `w`, where
`Q = B^12 + 46658` bounds `k^d` and `d^d` outside the base case. -/
theorem RunsWithin.sp_daryProg (m t : ℕ) (V₁ : List ℕ) (hV₁ : ∀ x ∈ V₁, x < m)
    (cs : List (List ℕ)) {offs : Array ℕ} (hoffs : ∀ x < m, get offs x = x * cs.length)
    (a : Array Bool) (d₁ : ℕ) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hkk : cs.length * cs.length + 1 ≤ B) (hN : m + 2 * cs.length + V₁.length + 1 ≤ B)
    (hcs : ∀ c ∈ cs, c.length ≤ B) (hn2 : V₁.length ≤ 2 * t) (hb : ¬IsBase t cs.length) :
    RunsWithin X body (SoJTree.sp_daryProg m t cs.length offs a V₁ cs d₁)
      (splitI (sp_daryI m t V₁ cs a d₁).1)
      (400000 * (B ^ 12 + 46658) ^ 8 * (1 + (sp_daryI m t V₁ cs a d₁).2)) := by
  set k := cs.length with hk
  set V₁' := tfDegD V₁ k a d₁ with hV₁'
  set d := arity k (sOf k d₁) V₁'.length with hd
  set hs := V₁'.map (fOfD k a d₁) with hhs
  set col := daryArr k d hs with hcol
  set S := bigTwinsD k d col with hS
  set Q := B ^ 12 + 46658 with hQ
  have hsub : ∀ x ∈ V₁', x ∈ V₁ := fun x hx => (List.mem_filter.1 hx).1
  have hV₁'m : ∀ x ∈ V₁', x < m := fun x hx => hV₁ x (hsub x hx)
  have hn : V₁'.length ≤ V₁.length := List.length_filter_le _ _
  have hdk : d ≤ k := (min_le_left _ _).trans (sp_sOf_le k d₁)
  have hkB : k ≤ B := by omega
  have hVB : V₁.length ≤ B := by omega
  have hkn : (k * V₁'.length) ^ 6 ≤ B ^ 12 := by
    have := Nat.pow_le_pow_left (Nat.mul_le_mul hkB (hn.trans hVB)) 6
    rw [← pow_two, ← pow_mul] at this
    simpa using this
  have hK : k ^ d + 2 ≤ Q := by
    have := sp_pow_arity_le k (sOf k d₁) V₁'.length
    rw [← hd] at this
    omega
  have hDd : d ^ d + 1 ≤ Q := by
    have := sp_pow_self_arity_le (s := sOf k d₁) (hn.trans hn2) hb
    rw [← hd] at this
    omega
  have hBQ : B ≤ Q := by
    have := Nat.le_self_pow (show 12 ≠ 0 by norm_num) B
    omega
  have hQ1 : 1 ≤ Q := by omega
  have hV₁'l : (tfDegD V₁ k a d₁).length = V₁'.length := rfl
  have hlen : ∀ h ∈ hs, h.length ≤ k := fun h hh => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hh
    exact sp_length_fOfD k a d₁ x
  have hhsQ : hs.length ≤ Q := by rw [hhs, List.length_map]; omega
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := V₁') (c := fOfCost k) (F := fOfD k a d₁)
    (f := fun x => SoJProg.fOfProg offs a k d₁ x) fun x hx =>
      SoJProg.RunsWithin.fOfProg hoffs a d₁ (hV₁'m x hx)
  have c₁ := sp_daryArrCost_le (k := k) (d := d) (n := hs.length) hQ1 (by omega) (by omega)
    hhsQ (by omega)
  have c₂ := sp_bigTwinsCost_le (k := k) (d := d) hQ1 (by omega) (by omega) (by omega)
  have c₃ : tfDegCost V₁.length k ≤ 50 * Q ^ 3 := by
    have h : tfDegCost V₁.length k ≤
        Q * (Q * (13 * Q + 5) + Q + 4 + Q + 2 + (8 * Q + 2) + 12) + 3 := by
      unfold tfDegCost twCost twinCost degCost
      gcongr <;> omega
    have p1 := sp_pow_le hQ1 (show 1 ≤ 3 by norm_num)
    have p2 := sp_pow_le hQ1 (show 2 ≤ 3 by norm_num)
    have p0 := sp_pow_le hQ1 (show 0 ≤ 3 by norm_num)
    ring_nf at h p1 p0 ⊢
    omega
  have c₄ : clogCost k V₁'.length + 5 + (V₁'.length * (fOfCost k + 3) + 2) +
      (V₁.length * (3 * V₁'.length + 6) + 3) ≤ 60 * Q ^ 2 := by
    unfold clogCost fOfCost
    have h₁ := Nat.mul_le_mul (show V₁'.length ≤ Q by omega) (show 3 * k + 10 ≤ 3 * Q + 10 by omega)
    have h₂ := Nat.mul_le_mul (show V₁'.length ≤ Q by omega)
      (show 9 * k + 7 + 3 ≤ 9 * Q + 10 by omega)
    have h₃ := Nat.mul_le_mul (show V₁.length ≤ Q by omega)
      (show 3 * V₁'.length + 6 ≤ 3 * Q + 6 by omega)
    have e₁ : Q * (3 * Q + 10) = 3 * Q ^ 2 + 10 * Q := by ring
    have e₂ : Q * (9 * Q + 10) = 9 * Q ^ 2 + 10 * Q := by ring
    have e₃ : Q * (3 * Q + 6) = 3 * Q ^ 2 + 6 * Q := by ring
    have p1 : Q ≤ Q ^ 2 := by nlinarith
    omega
  have p3 := sp_pow_le hQ1 (show 3 ≤ 8 by norm_num)
  have p4 := sp_pow_le hQ1 (show 4 ≤ 8 by norm_num)
  have p2 := sp_pow_le hQ1 (show 2 ≤ 8 by norm_num)
  have p1 : Q ≤ Q ^ 8 := by nlinarith [sp_pow_le hQ1 (show 1 ≤ 8 by norm_num)]
  have hB8 : B ^ 8 ≤ Q ^ 8 := Nat.pow_le_pow_left hBQ 8
  have hB3 : B ^ 3 ≤ Q ^ 8 := (Nat.pow_le_pow_left hBQ 3).trans p3
  rcases hSe : S with _ | ⟨j, js⟩
  · have hval : sp_daryI m t V₁ cs a d₁ =
        (((goodList (Coherent.wlA d k col).1 d k (2 * k / 3)).map
          (dlI m t V₁ V₁' cs a d (Coherent.wlA d k col).1)).flatMap Prod.fst,
        (goodList (Coherent.wlA d k col).1 d k (2 * k / 3)).length +
          (((goodList (Coherent.wlA d k col).1 d k (2 * k / 3)).map
            (dlI m t V₁ V₁' cs a d (Coherent.wlA d k col).1)).map Prod.snd).sum) := by
      simp only [sp_daryI, ← hk, ← hV₁', ← hd, ← hhs, ← hcol, ← hS, hSe, ne_eq,
        not_true_eq_false, ite_false]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (SoJProg.RunsWithin.tfDegProg hoffs a hV₁ d₁)
      run_step (SoJProg.RunsWithin.sOfProg k d₁)
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.arityProg k (sOf k d₁) V₁'.length)
      run_step hmap
      run_step (SoJProg.RunsWithin.daryArrProg k d hs hlen)
      run_step (SoJProg.RunsWithin.bigTwinsProg k d col)
      run_step (RunsWithin.sp_diffProg V₁ V₁')
      rw [← hS, hSe]
      apply RunsWithin.caseList_nil
      exact RunsWithin.sp_daryDLProg m t V₁ V₁' hV₁'m cs hoffs a d hs hlen hB hm hkk (by omega)
        ((List.length_filter_le _ _).trans hVB) hcs (by omega) hQ1 (by omega) (by omega) hK hDd
        hhsQ
    case hc =>
      simp only [Prim.cost, Args.head]
      generalize (goodList (Coherent.wlA d k col).1 d k (2 * k / 3)).length +
          (((goodList (Coherent.wlA d k col).1 d k (2 * k / 3)).map
            (dlI m t V₁ V₁' cs a d (Coherent.wlA d k col).1)).map Prod.snd).sum = w
      have h₁ : 330100 * B ^ 8 * w ≤ 400000 * Q ^ 8 * w := Nat.mul_le_mul_right _ (by omega)
      have e : 400000 * Q ^ 8 * (1 + w) = 400000 * Q ^ 8 + 400000 * Q ^ 8 * w := by ring
      omega
  · have hne : S ≠ [] := by rw [hSe]; exact List.cons_ne_nil _ _
    have hval : sp_daryI m t V₁ cs a d₁ =
        ([recI k V₁' (subCells cs (pickSideD V₁' k a S)) (restrictRel m k a (pickSideD V₁' k a S))
          [pieceOp (diffD V₁ V₁')]], 0) := by
      simp only [sp_daryI, ← hk, ← hV₁', ← hd, ← hhs, ← hcol, ← hS, ne_eq, hne,
        not_false_eq_true, ite_true]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (SoJProg.RunsWithin.tfDegProg hoffs a hV₁ d₁)
      run_step (SoJProg.RunsWithin.sOfProg k d₁)
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.arityProg k (sOf k d₁) V₁'.length)
      run_step hmap
      run_step (SoJProg.RunsWithin.daryArrProg k d hs hlen)
      run_step (SoJProg.RunsWithin.bigTwinsProg k d col)
      run_step (RunsWithin.sp_diffProg V₁ V₁')
      rw [← hS, hSe]
      apply RunsWithin.caseList_cons
      rw [← hSe]
      exact RunsWithin.sp_daryRecProg m k V₁' hV₁'m cs hoffs a (diffD V₁ V₁') S hB hm hkB
        (hn.trans hVB) (by omega) (sp_length_bigTwinsD k d col)
    case hc =>
      simp only [Prim.cost, Args.head, Nat.add_zero, Nat.mul_one]
      omega

theorem sp_clog_le (n : ℕ) : Nat.clog 2 n ≤ n := by
  by_cases hn : n ≤ 1
  · rw [Nat.clog_of_right_le_one hn]
    exact Nat.zero_le _
  have h₁ := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < n)
  have h₂ : (Nat.clog 2 n).pred < 2 ^ (Nat.clog 2 n).pred := Nat.lt_two_pow_self
  rw [Nat.pred_eq_sub_one] at h₁ h₂
  omega

theorem sp_tfDegCost_le {n k B : ℕ} (hB : 1 ≤ B) (hn : n ≤ B) (hk : k ≤ B) :
    tfDegCost n k ≤ 60 * B ^ 3 := by
  have h : tfDegCost n k ≤ B * (B * (13 * B + 5) + B + 4 + B + 2 + (8 * B + 2) + 12) + 3 := by
    unfold tfDegCost twCost twinCost degCost
    gcongr
  have p1 := sp_pow_le hB (show 1 ≤ 3 by norm_num)
  have p2 := sp_pow_le hB (show 2 ≤ 3 by norm_num)
  have p0 := sp_pow_le hB (show 0 ≤ 3 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

theorem sp_minBigDegCost_le {n k B : ℕ} (hB : 1 ≤ B) (hn : n ≤ B) (hk : k ≤ B) :
    minBigDegCost n k ≤ 120 * B ^ 4 := by
  have ht := sp_tfDegCost_le hB hn hk
  have h₁ : n * (tfDegCost n k + n + 7) ≤ B * (60 * B ^ 3 + B + 7) :=
    Nat.mul_le_mul hn (by omega)
  have h : minBigDegCost n k ≤ B * (8 * B + 2 + 3) + 2 + (B * (3 * B + 5) + B + 3) +
      B * (60 * B ^ 3 + B + 7) + 3 + 3 * B + 4 := by
    unfold minBigDegCost bigDegsCost degsCost dedupCost degCost
    have h₂ : n * (8 * k + 2 + 3) ≤ B * (8 * B + 2 + 3) := Nat.mul_le_mul hn (by omega)
    have h₃ : n * (3 * n + 5) ≤ B * (3 * B + 5) := Nat.mul_le_mul hn (by omega)
    omega
  have p1 := sp_pow_le hB (show 1 ≤ 4 by norm_num)
  have p2 := sp_pow_le hB (show 2 ≤ 4 by norm_num)
  have p0 := sp_pow_le hB (show 0 ≤ 4 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

theorem sp_twinPartCost_le {m n k B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hn : n ≤ B) (hk : k ≤ B) :
    twinPartCost m n k ≤ 250 * B ^ 4 := by
  have ht := sp_tfDegCost_le hB hn hk
  have h : twinPartCost m n k ≤ 10 * B + 10 + (B * (B * (13 * B + 5) + B + 4 + B + 2 +
      (8 * B + 2) + 3 * (B + B) + 10) + 2 * B + 4) + (B * (B * (13 * B + 5) + B + 4 + B + 2 +
      (8 * B + 2) + 60 * B ^ 3 + (B * (13 * B + 5) + B + 4) + 6) + 2 * B + 4) := by
    unfold twinPartCost twinColCost twinBlkCost
    have e : twCost n k = twinCost n k + n + 2 := rfl
    rw [e]
    unfold twinCost degCost
    gcongr
  have p1 := sp_pow_le hB (show 1 ≤ 4 by norm_num)
  have p2 := sp_pow_le hB (show 2 ≤ 4 by norm_num)
  have p3 := sp_pow_le hB (show 3 ≤ 4 by norm_num)
  have p0 := sp_pow_le hB (show 0 ≤ 4 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

theorem sp_johnsonCost_le {m n k B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B) (hn : n ≤ B) (hk : k ≤ B) :
    johnsonTestCost n k + johnsonLeafCost m n k ≤ 200 * B ^ 3 := by
  have ht := sp_tfDegCost_le hB hn hk
  have h : johnsonTestCost n k + johnsonLeafCost m n k ≤ 60 * B ^ 3 + B +
      (B * (7 * B + 8 + 1) + B + 4 + B + 3) + 6 + (60 * B ^ 3 + (B * (9 * B + 7 + 3) + 2 * B + 4) +
      6) := by
    unfold johnsonTestCost johnsonLeafCost chooseCost pascalCost nextRowCost fArrCost fOfCost
    gcongr
  have p1 := sp_pow_le hB (show 1 ≤ 3 by norm_num)
  have p2 := sp_pow_le hB (show 2 ≤ 3 by norm_num)
  have p0 := sp_pow_le hB (show 0 ≤ 3 by norm_num)
  ring_nf at h p1 p0 ⊢
  omega

/-- **One level of `bsoj` on data, the program**: `bstepI` as a split pair, within
`500000 (B^12 + 46658)^8 (1 + w)` for its work `w`. -/
theorem RunsWithin.sp_bstepProg (m t : ℕ) (V₁ : List ℕ) (hV₁ : ∀ x ∈ V₁, x < m)
    (cs : List (List ℕ)) (a : Array Bool) {B : ℕ} (hB : 1 ≤ B) (hm : m ≤ B)
    (hkk : cs.length * cs.length + 1 ≤ B) (hN : m + 2 * cs.length + V₁.length + 1 ≤ B)
    (hcs : ∀ c ∈ cs, c.length ≤ B) (hn2 : V₁.length ≤ 2 * t) (ht : t + t ≤ B) :
    RunsWithin X body (SoJTree.sp_bstepProg m t V₁ cs a) (splitI (bstepI m t V₁ cs a).1)
      (500000 * (B ^ 12 + 46658) ^ 8 * (1 + (bstepI m t V₁ cs a).2)) := by
  rw [sp_bstepI_eq]
  set k := cs.length with hk
  set Q := B ^ 12 + 46658 with hQ
  have hoffs : ∀ x < m, get ((List.range m).map (· * k)).toArray x = x * k :=
    fun _ hx => get_offsets hx
  have hkB : k ≤ B := by omega
  have hVB : V₁.length ≤ B := by omega
  have hBQ : B ≤ Q := by
    have := Nat.le_self_pow (show 12 ≠ 0 by norm_num) B
    omega
  have hQ1 : 1 ≤ Q := by omega
  have q8 : 1 ≤ Q ^ 8 := Nat.one_le_pow _ _ hQ1
  have hB4 : B ^ 4 ≤ Q ^ 8 := (Nat.pow_le_pow_left hBQ 4).trans (sp_pow_le hQ1 (by norm_num))
  have hB3 : B ^ 3 ≤ B ^ 4 := sp_pow_le hB (by norm_num)
  have hB2 : B ^ 2 ≤ B ^ 4 := sp_pow_le hB (by norm_num)
  have hB1 : B ≤ B ^ 4 := by nlinarith [sp_pow_le hB (show 1 ≤ 4 by norm_num)]
  have c₁ := sp_minBigDegCost_le hB hVB hkB
  have hpre := fun (w : ℕ) => (show 500000 * Q ^ 8 ≤ 500000 * Q ^ 8 * (1 + w) from
    Nat.le_mul_of_pos_right _ (by omega))
  rcases hod : optMin (bigDegsD t V₁ k a) with _ | d₁
  · have c₂ := sp_twinPartCost_le hB hm hVB hkB
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.offsetsProg m k)
      run_step (SoJProg.RunsWithin.minBigDegProg hoffs a hV₁ t)
      rw [hod]
      apply RunsWithin.caseOption_none
      run_step (SoJProg.RunsWithin.twinPartProg m k a hV₁)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.partProg _ _)
      exact RunsWithin.sp_leafPair _
    case hc =>
      simp only [Prim.cost, Args.head, Nat.add_zero, Nat.mul_one]
      omega
  by_cases hj : (tfDegD V₁ k a d₁).length = k.choose (sOf k d₁)
  · have c₂ := sp_johnsonCost_le hB hm hVB hkB
    simp only [hj, ite_true, Nat.add_zero, Nat.mul_one]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.offsetsProg m k)
      run_step (SoJProg.RunsWithin.minBigDegProg hoffs a hV₁ t)
      rw [hod]
      apply RunsWithin.caseOption_some
      run_step (SoJProg.RunsWithin.johnsonTestProg hoffs a hV₁ d₁)
      apply RunsWithin.ite_pos (by simp [hj])
      run_step (SoJProg.RunsWithin.johnsonLeafProg hoffs a hV₁ d₁)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.johnProg _ _ _ _)
      exact RunsWithin.sp_leafPair _
    case hc =>
      simp only [Prim.cost, Args.head]
      omega
  simp only [hj, ite_false]
  have hib₀ := RunsWithin.sp_isBaseProg (X := X) (body := body) t k
  have c₃ : clogCost 2 (t + t) + 3 * Nat.clog 2 (t + t) +
      3 * (Nat.clog 2 (t + t) * Nat.clog 2 (t + t)) + 3 * k + 100 ≤ 200 * B ^ 4 := by
    have hL := sp_clog_le (t + t)
    have h₁ : Nat.clog 2 (t + t) * Nat.clog 2 (t + t) ≤ B * B :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : B * B = B ^ 2 := by ring
    unfold clogCost
    omega
  by_cases hib : IsBase t k
  · simp only [hib, ite_true]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.offsetsProg m k)
      run_step (SoJProg.RunsWithin.minBigDegProg hoffs a hV₁ t)
      rw [hod]
      apply RunsWithin.caseOption_some
      run_step (SoJProg.RunsWithin.johnsonTestProg hoffs a hV₁ d₁)
      apply RunsWithin.ite_neg (by simpa using hj)
      run_step hib₀
      apply RunsWithin.ite_pos (by simpa using hib)
      exact RunsWithin.sp_baseProg m k hoffs a V₁ hB hm hkB hVB
    case hc =>
      have c₂ := sp_johnsonCost_le hB hm hVB hkB
      simp only [Prim.cost, Args.head]
      generalize (List.range k).permutations'.length = w
      have h₁ : 100 * B ^ 3 * (1 + w) ≤ 100 * Q ^ 8 * (1 + w) :=
        Nat.mul_le_mul_right _ (by omega)
      have e : 500000 * Q ^ 8 * (1 + w) = 100 * Q ^ 8 * (1 + w) + 499900 * Q ^ 8 * (1 + w) := by
        ring
      have h₂ : 499900 * Q ^ 8 ≤ 499900 * Q ^ 8 * (1 + w) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  · simp only [hib, ite_false]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.offsetsProg m k)
      run_step (SoJProg.RunsWithin.minBigDegProg hoffs a hV₁ t)
      rw [hod]
      apply RunsWithin.caseOption_some
      run_step (SoJProg.RunsWithin.johnsonTestProg hoffs a hV₁ d₁)
      apply RunsWithin.ite_neg (by simpa using hj)
      run_step hib₀
      apply RunsWithin.ite_neg (by simpa using hib)
      exact RunsWithin.sp_daryProg m t V₁ hV₁ cs hoffs a d₁ hB hm hkk hN hcs hn2 hib
    case hc =>
      have c₂ := sp_johnsonCost_le hB hm hVB hkB
      simp only [Prim.cost, Args.head, ← hQ]
      generalize (sp_daryI m t V₁ cs a d₁).2 = w
      have e : 500000 * Q ^ 8 * (1 + w) = 400000 * Q ^ 8 * (1 + w) + 100000 * Q ^ 8 * (1 + w) := by
        ring
      have h₂ : 100000 * Q ^ 8 ≤ 100000 * Q ^ 8 * (1 + w) := Nat.le_mul_of_pos_right _ (by omega)
      omega

theorem sp_sum_le_add {α : Type*} (xs : List α) (f g : α → ℕ) (h : ∀ x ∈ xs, f x ≤ 1 + g x) :
    (xs.map f).sum ≤ xs.length + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h₁ := h x List.mem_cons_self
    have h₂ := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- **A level has at most `1 + w` items**, for its work `w`. -/
theorem sp_length_bstepI (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a : Array Bool) :
    (bstepI m t V₁ cs a).1.length ≤ 1 + (bstepI m t V₁ cs a).2 := by
  rw [sp_bstepI_eq]
  split
  · simp
  · split_ifs
    · simp
    · simp
    · unfold sp_daryI
      dsimp only
      split
      · simp
      · simp only [List.length_flatMap, List.map_map, Function.comp_def]
        refine le_trans (sp_sum_le_add _ _ _ fun xd _ => sp_length_dlI _ _ _ _ _ _ _ _ _) ?_
        omega

/-! #### The child frames of a level -/

/-- The properties of a child frame used by `FrameD.ValidP`: at most three wrapper operations,
their point lists and the cells bounded, and the points among the parent's. -/
def sp_ChildOK (m L : ℕ) (V₁ : List ℕ) (ch : FrameD) : Prop :=
  ch.wr.length ≤ 3 ∧ (∀ op ∈ ch.wr, op.2.1.length ≤ L) ∧ (∀ c ∈ ch.cs, c.length ≤ m) ∧
    ∀ x ∈ ch.V₁, x ∈ V₁

theorem sp_recI_inr {k : ℕ} {V : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {ops : List WrapOp} {ch : FrameD} (h : Sum.inr ch = recI k V cs a ops) :
    ch = (V, cs, a, ops) := by
  unfold recI at h
  split at h
  · cases h
    rfl
  · cases h

theorem sp_shrinkI_inr {k : ℕ} {V : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {ops : List WrapOp} {ch : FrameD} (h : Sum.inr ch = shrinkI k V cs a ops) :
    ch = (V, cs, a, ops) := by
  unfold shrinkI at h
  split at h
  · cases h
    rfl
  · cases h

theorem sp_subCells_le {m : ℕ} {cs : List (List ℕ)} (hcs : ∀ c ∈ cs, c.length ≤ m)
    (js : List ℕ) : ∀ c ∈ subCells cs js, c.length ≤ m := fun c hc => by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  exact sp_getD_cells_le hcs j

/-- The points `W₁` of a leaf of `cohSojD` lie in `C₁`. -/
def sp_LeafSub (C₁ : List ℕ) : Option SoJProg.LeafD → Prop
  | none => True
  | some (_, _, (W₁, _, _)) => ∀ x ∈ W₁, x ∈ C₁

theorem sp_cohSojD_leafSub (f : ℕ → ℕ → ℕ) (N : ℕ) (C₁ C₂ : List ℕ) :
    (∀ o, cohSojD f N C₁ C₂ = .leaf o → sp_LeafSub C₁ o) ∧
      ∀ opts kk, cohSojD f N C₁ C₂ = .node opts kk → ∀ y, sp_LeafSub C₁ (kk y) := by
  refine ⟨fun o h => ?_, fun opts kk h y => ?_⟩
  · unfold cohSojD imprimTree at h
    repeat' split at h
    all_goals cases h
    all_goals simp [sp_LeafSub, partLeaf, compPart, bipLeaf]
  · unfold cohSojD imprimTree at h
    repeat' split at h
    all_goals cases h
    all_goals try (beta_reduce; unfold primLeaf; repeat' split)
    all_goals simp [sp_LeafSub, partLeaf, bipLeaf, colPartD]
    exact fun x hx _ => hx

theorem sp_contI_child {m t k L : ℕ} {cs : List (List ℕ)} {D₁ D₂ C₁ : List ℕ}
    {f : ℕ → ℕ → ℕ} {o : Option SoJProg.LeafD} (hsub : sp_LeafSub C₁ o) (hC₁ : C₁.length ≤ L)
    (hD₁ : D₁.length ≤ L) (hD₂ : D₂.length ≤ L) {ch : FrameD}
    (h : Sum.inr ch = contI m t k cs D₁ D₂ C₁ f o) : sp_ChildOK m L C₁ ch := by
  rcases o with _ | ⟨tag, cb, ⟨W₁, W₂, g⟩⟩
  · cases h
  simp only [contI] at h
  split at h
  · cases h
  split at h
  · cases h
  have he := sp_shrinkI_inr h
  subst he
  refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
  · intro op hop
    simp only [FrameD.wr, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl | rfl
    · exact (List.length_filter_le _ _).trans hC₁
    · exact hD₂
    · exact hD₁
  · intro c hc
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 (sp_mem_dedupCellsD hc)
    exact sp_length_cellUD m k cs l
  · intro x hx
    exact hsub x (by simpa using (List.mem_filter.1 hx).2)

theorem sp_cohI_child {m t k L : ℕ} {cs : List (List ℕ)} {D₁ D₂ C₁ C₂ : List ℕ}
    {f : ℕ → ℕ → ℕ} (hC₁ : C₁.length ≤ L) (hD₁ : D₁.length ≤ L) (hD₂ : D₂.length ≤ L)
    {ch : FrameD} (h : Sum.inr ch ∈ (cohI m t k cs D₁ D₂ C₁ C₂ f).1) :
    sp_ChildOK m L C₁ ch := by
  have hs := sp_cohSojD_leafSub f (m + k) C₁ (C₂.map (m + ·))
  unfold cohI at h
  split at h
  · rename_i o hD
    simp only [List.mem_singleton] at h
    exact sp_contI_child (hs.1 o hD) hC₁ hD₁ hD₂ h
  · rename_i opts kk hD
    obtain ⟨y, -, hy⟩ := List.mem_map.1 h
    exact sp_contI_child (hs.2 opts kk hD y) hC₁ hD₁ hD₂ hy.symm

theorem sp_ChildOK_mono {m L : ℕ} {C V : List ℕ} {ch : FrameD} (h : sp_ChildOK m L C ch)
    (hC : ∀ x ∈ C, x ∈ V) : sp_ChildOK m L V ch :=
  ⟨h.1, h.2.1, h.2.2.1, fun x hx => hC x (h.2.2.2 x hx)⟩

theorem sp_call_child {m k L : ℕ} {V V' D : List ℕ} {cs : List (List ℕ)} {js : List ℕ}
    {a' : Array Bool} (hsub : ∀ x ∈ V', x ∈ V) (hD : D.length ≤ L)
    (hcs : ∀ c ∈ cs, c.length ≤ m) {ch : FrameD}
    (h : Sum.inr ch ∈ [shrinkI k V' (subCells cs js) a' [pieceOp D]] ∨
      Sum.inr ch ∈ [recI k V' (subCells cs js) a' [pieceOp D]]) :
    sp_ChildOK m L V ch := by
  have he : ch = (V', subCells cs js, a', [pieceOp D]) := by
    rcases h with h | h <;> simp only [List.mem_singleton] at h
    · exact sp_shrinkI_inr h
    · exact sp_recI_inr h
  subst he
  refine ⟨by simp [FrameD.wr], fun op hop => ?_, sp_subCells_le hcs js, hsub⟩
  simp only [FrameD.wr, List.mem_singleton] at hop
  subst hop
  exact hD

/-- The child frames of `dlI`. -/
theorem sp_dlI_child {m t L : ℕ} {V₁ V₁' : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {d : ℕ} {wl : Array ℕ} {xd : List ℕ} (hsub : ∀ x ∈ V₁', x ∈ V₁) (hL : V₁.length ≤ L)
    (hL' : V₁'.length ≤ L) (hcs : ∀ c ∈ cs, c.length ≤ m) {ch : FrameD}
    (h : Sum.inr ch ∈ (dlI m t V₁ V₁' cs a d wl xd).1) : sp_ChildOK m L V₁ ch := by
  have hD : (diffD V₁ V₁').length ≤ L := (List.length_filter_le _ _).trans hL
  rw [sp_dlI_eq] at h
  split at h
  · exact sp_call_child hsub hD hcs (.inl h)
  unfold sp_dlSkelI at h
  dsimp only at h
  split at h
  · exact sp_call_child hsub hD hcs (.inl h)
  unfold sp_dlBigI at h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · exact sp_call_child hsub hD hcs (.inl h)
  refine sp_ChildOK_mono (sp_cohI_child ?_ hD ((List.length_filter_le _ _).trans hL') h)
    fun x hx => hsub x (sp_bigL_sub _ _ _ x hx)
  exact (List.length_filter_le _ _).trans hL'

/-- **The child frames of a level**: at most three wrapper operations on lists of at most
`|V₁|` points, cells of at most `m` points, and points among `V₁`. -/
theorem sp_bstepI_child {m t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    (hcs : ∀ c ∈ cs, c.length ≤ m) {ch : FrameD} (h : Sum.inr ch ∈ (bstepI m t V₁ cs a).1) :
    sp_ChildOK m V₁.length V₁ ch := by
  rw [sp_bstepI_eq] at h
  split at h
  · simp at h
  rename_i _ d₁ _
  split_ifs at h
  · simp at h
  · simp at h
  unfold sp_daryI at h
  dsimp only at h
  have hsub : ∀ x ∈ tfDegD V₁ cs.length a d₁, x ∈ V₁ := fun x hx => (List.mem_filter.1 hx).1
  have hL' : (tfDegD V₁ cs.length a d₁).length ≤ V₁.length := List.length_filter_le _ _
  split at h
  · exact sp_call_child hsub ((List.length_filter_le _ _)) hcs (.inr h)
  obtain ⟨p, hp, hch⟩ := List.mem_flatMap.1 h
  obtain ⟨xd, -, rfl⟩ := List.mem_map.1 hp
  exact sp_dlI_child hsub le_rfl hL' hcs hch

end Specs2

/-! ### The frame invariant and the step -/

section Step

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- **The frame invariant of the costs**: a valid frame with at most `2t` points and at most
`q` cells of at most `m` points each, whose wrapper operations act on at most `m` points, with
`|wr| + 4|cs| ≤ 4q + 1` (each level adds at most three operations and removes a cell). -/
structure FrameD.ValidP (m q t : ℕ) (fr : FrameD) : Prop where
  valid : fr.Valid m
  pts : fr.V₁.length ≤ 2 * t
  cells : fr.cs.length ≤ q
  cellLen : ∀ c ∈ fr.cs, c.length ≤ m
  ops : ∀ op ∈ fr.wr, op.2.1.length ≤ m
  wrap : fr.wr.length + 4 * fr.cs.length ≤ 4 * q + 1

theorem sp_length_le_of_lt {m : ℕ} {V : List ℕ} (hV : V.Nodup) (hlt : ∀ x ∈ V, x < m) :
    V.length ≤ m :=
  (hV.subperm fun x hx => List.mem_range.2 (hlt x hx)).length_le.trans (List.length_range).le

theorem sp_mem_splitI_snd {l : List Item} {ch : FrameD} (h : ch ∈ (splitI l).2) :
    Sum.inr ch ∈ l := by
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.1 h
  cases i with
  | inl o => simp at he
  | inr fr' =>
    simp only [Sum.getRight?_inr, Option.some.injEq] at he
    exact he ▸ hi

/-- **The invariant passes to the child frames.** -/
theorem stepD_validP {m q t : ℕ} {fr : FrameD} (hfr : fr.ValidP m q t) :
    ∀ ch ∈ (stepD m t fr).2, ch.ValidP m q t := by
  intro ch hch
  obtain ⟨hv, hlt⟩ := stepD_children (t := t) hfr.valid ch hch
  rw [stepD_eq] at hch
  obtain ⟨ch₀, hch₀, rfl⟩ := List.mem_map.1 hch
  obtain ⟨hw, hops, hcl, hsub⟩ := sp_bstepI_child hfr.cellLen (sp_mem_splitI_snd hch₀)
  have hVm := sp_length_le_of_lt hfr.valid.nodup hfr.valid.lt
  refine ⟨hv, ?_, ?_, hcl, ?_, ?_⟩
  · exact ((hv.nodup.subperm hsub).length_le).trans hfr.pts
  · exact hlt.le.trans hfr.cells
  · intro op hop
    rcases List.mem_append.1 hop with h | h
    · exact (hops op h).trans hVm
    · exact hfr.ops op h
  · have := hfr.wrap
    simp only [FrameD.wr, FrameD.cs, List.length_append] at hlt this hw ⊢
    omega

/-- **The step cost factor**: `500000 ((M²)^12 + 46658)^8` for the level, with
`M = m + q + t + 2`, plus `(4q + 1)(opCost m m + 1)` for the wrapper of each leaf. -/
def stepK (m q t : ℕ) : ℕ :=
  500000 * (((m + q + t + 2) ^ 2) ^ 12 + 46658) ^ 8 + (4 * q + 1) * (opCost m m + 1) + 30

/-- **One step of a frame, the program**: it computes `stepD m t fr` within
`stepK m q t (1 + w + ℓ)`, for the work `w` and the number `ℓ` of leaves of the step. -/
theorem RunsWithin.stepProg (m t : ℕ) {q : ℕ} (fr : FrameD) (hfr : fr.ValidP m q t) :
    RunsWithin X body (SoJTree.stepProg m t fr) (stepD m t fr)
      (stepK m q t * (1 + stepWork m t fr + (stepD m t fr).1.length)) := by
  obtain ⟨V₁, cs, a', wr⟩ := fr
  have hV₁ : ∀ x ∈ V₁, x < m := hfr.valid.lt
  have hVm : V₁.length ≤ m := sp_length_le_of_lt hfr.valid.nodup hfr.valid.lt
  have hk : cs.length ≤ q := hfr.cells
  have hcs : ∀ c ∈ cs, c.length ≤ m := hfr.cellLen
  have hops : ∀ op ∈ wr, op.2.1.length ≤ m := hfr.ops
  have hwr : wr.length + 4 * cs.length ≤ 4 * q + 1 := hfr.wrap
  have hn2 : V₁.length ≤ 2 * t := hfr.pts
  set M := m + q + t + 2 with hM
  set B := M ^ 2 with hB
  have hM2 : 2 * M ≤ B := by rw [hB, pow_two]; exact Nat.mul_le_mul_right _ (by omega)
  have hkk : cs.length * cs.length + 1 ≤ B := by
    have : cs.length * cs.length ≤ q * q := Nat.mul_le_mul hk hk
    have : q * q + 1 ≤ M * M := by nlinarith
    rw [hB, pow_two]
    omega
  have hbst := RunsWithin.sp_bstepProg (X := X) (body := body) m t V₁ hV₁ cs a' (B := B)
    (by omega) (by omega) hkk (by omega) (fun c hc => (hcs c hc).trans (by omega)) hn2 (by omega)
  set items := (bstepI m t V₁ cs a').1 with hitems
  set L := (splitI items).1 with hL
  set C := (splitI items).2 with hC
  have hwrap := RunsWithin.mapList_le (X := X) (body := body) (a' := outTy) (b' := outTy)
    (xs := L) (c := wr.length * (opCost m m + 1)) (F := wrapD m wr)
    (f := fun o => SoJTree.sp_wrapDProg m wr o) fun o _ => RunsWithin.sp_wrapDProg m wr o hops
  have hre := RunsWithin.mapList_le (X := X) (body := body) (a' := frameTy) (b' := frameTy)
    (xs := C) (c := 13)
    (F := fun ch => (FrameD.V₁ ch, FrameD.cs ch, FrameD.a ch, FrameD.wr ch ++ wr))
    (f := fun ch => SoJTree.sp_rewrapProg wr ch) fun ch hch =>
      (RunsWithin.sp_rewrapProg wr ch).mono
        (by have := (sp_bstepI_child hcs (sp_mem_splitI_snd hch)).1; omega)
  have hval : stepD m t (V₁, cs, a', wr) = (L.map (wrapD m wr),
      C.map fun ch => (ch.V₁, ch.cs, ch.a, ch.wr ++ wr)) := stepD_eq m t _
  have hcnt : L.length + C.length ≤ 1 + (bstepI m t V₁ cs a').2 := by
    rw [hL, hC, sp_splitI_length]
    exact sp_length_bstepI m t V₁ cs a'
  rw [hval]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hbst
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hwrap
    run_step hre
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, List.length_map]
    have hsw : stepWork m t (V₁, cs, a', wr) = (bstepI m t V₁ cs a').2 := rfl
    rw [hsw]
    generalize (bstepI m t V₁ cs a').2 = w at hcnt ⊢
    generalize L.length = l at hcnt ⊢
    generalize C.length = c at hcnt ⊢
    unfold stepK
    rw [← hM]
    generalize 500000 * ((M ^ 2) ^ 12 + 46658) ^ 8 = K₁
    generalize opCost m m + 1 = X₁
    have h₁ : wr.length * X₁ ≤ (4 * q + 1) * X₁ := Nat.mul_le_mul_right _ (by omega)
    have h₂ : l * (wr.length * X₁ + 3) ≤ l * ((4 * q + 1) * X₁) + 3 * l := by
      have := Nat.mul_le_mul_left l h₁
      rw [Nat.mul_add]
      omega
    have e : (K₁ + (4 * q + 1) * X₁ + 30) * (1 + w + l) =
        K₁ * (1 + w) + K₁ * l + (4 * q + 1) * X₁ * (1 + w) + l * ((4 * q + 1) * X₁) + 30 +
          30 * w + 30 * l := by ring
    rw [e]
    omega

end Step

/-! ### The size of the produced leaves -/

section LeafSize

/-- The bound on the size of the leaves produced from frames with at most `q` cells. -/
def outB (m q : ℕ) : ℕ := m * m + m + q + 1

theorem sp_outSize_le {o : OutD} {s : ℕ} (h₁ : ∀ l ∈ o.2.1.2.toList, l.length ≤ s)
    (h₂ : o.2.2.1.length ≤ s) (h₃ : o.2.2.2.1.length ≤ s) (h₄ : ∀ c ∈ o.2.2.2.1, c.length ≤ s)
    (h₅ : ∀ l ∈ o.2.2.2.2.2.toList, l.length ≤ s) : outSize o ≤ s :=
  max_le (ld_maxLen_le h₁) (max_le h₂ (max_le h₃ (max_le (ld_maxLen_le h₄) (ld_maxLen_le h₅))))

theorem sp_arr_le {g : ℕ → List ℕ} {m s : ℕ} (h : ∀ x < m, (g x).length ≤ s) :
    ∀ l ∈ ((List.range m).map g).toArray.toList, l.length ≤ s := fun l hl => by
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨x, hx, rfl⟩ := hl
  exact h x hx

theorem sp_outSize_noneD (s : ℕ) : outSize noneD ≤ s :=
  sp_outSize_le (by simp [noneD]) (by simp [noneD]) (by simp [noneD]) (by simp [noneD])
    (by simp [noneD])

theorem sp_outSize_partD {col : Array ℕ} {blk : Array (List ℕ)} {s : ℕ}
    (h : ∀ l ∈ blk.toList, l.length ≤ s) : outSize (partD col blk) ≤ s :=
  sp_outSize_le h (by simp [partD]) (by simp [partD]) (by simp [partD]) (by simp [partD])

theorem sp_outSize_addPieceD (m : ℕ) {D : List ℕ} {o : OutD} {s : ℕ} (ho : outSize o ≤ s)
    (hD : D.length ≤ s) : outSize (addPieceD m D o) ≤ s := by
  unfold addPieceD
  split
  · refine sp_outSize_partD (sp_arr_le fun x _ => ?_)
    split
    · exact hD
    · exact (outSize_blk o x).trans ho
  · exact ho

theorem sp_outSize_extendD (m : ℕ) (V₁ : List ℕ) (col : ℕ → ℕ) {o : OutD} {s : ℕ}
    (ho : outSize o ≤ s) (hm : m ≤ s) : outSize (extendD m V₁ col o) ≤ s := by
  unfold extendD
  split
  · refine sp_outSize_partD (sp_arr_le fun x _ => ?_)
    split
    · exact (outSize_blk o x).trans ho
    · exact (List.length_filter_le _ _).trans (by simp [hm])
  · exact ho

theorem sp_outSize_wrapD (m : ℕ) {ops : List WrapOp} {s : ℕ} (hops : ∀ op ∈ ops, op.2.1.length ≤ s)
    (hm : m ≤ s) : ∀ {o : OutD}, outSize o ≤ s → outSize (wrapD m ops o) ≤ s := by
  induction ops with
  | nil => exact fun ho => ho
  | cons op ops ih =>
    intro o ho
    simp only [wrapD, List.foldl_cons] at ih ⊢
    refine ih (fun op' h => hops op' (List.mem_cons_of_mem _ h)) ?_
    unfold opD
    split
    · exact sp_outSize_extendD m _ _ ho hm
    · exact sp_outSize_addPieceD m ho (hops op List.mem_cons_self)

theorem sp_colBlkD_le (m : ℕ) (S : List ℕ) (col : Array ℕ) :
    ∀ l ∈ (colBlkD m S col).toList, l.length ≤ S.length :=
  sp_arr_le fun _ _ => List.length_filter_le _ _

/-- The blocks of a leaf of `cohSojD` have at most `L` points. -/
def sp_LeafBlk (L : ℕ) : Option SoJProg.LeafD → Prop
  | none => True
  | some (_, (_, blk), _) => ∀ l ∈ blk.toList, l.length ≤ L

theorem sp_cohSojD_leafBlk (f : ℕ → ℕ → ℕ) (N : ℕ) (C₁ C₂ : List ℕ) :
    (∀ o, cohSojD f N C₁ C₂ = .leaf o → sp_LeafBlk (C₁.length * C₁.length + 1) o) ∧
      ∀ opts kk, cohSojD f N C₁ C₂ = .node opts kk →
        ∀ y, sp_LeafBlk (C₁.length * C₁.length + 1) (kk y) := by
  have hcomp : ∀ r, ∀ l ∈ ((List.range N).map (compD f C₁ r)).toArray.toList,
      l.length ≤ C₁.length * C₁.length + 1 :=
    fun r => sp_arr_le fun x _ => length_compD_le f C₁ r x
  have hcol : ∀ w, ∀ l ∈ ((List.range N).map fun x =>
      C₁.filter fun y => f y w == f x w).toArray.toList, l.length ≤ C₁.length * C₁.length + 1 :=
    fun w => sp_arr_le fun x _ => (List.length_filter_le _ _).trans (by nlinarith)
  refine ⟨fun o h => ?_, fun opts kk h y => ?_⟩
  · unfold cohSojD imprimTree at h
    repeat' split at h
    all_goals cases h
    all_goals simp only [sp_LeafBlk, compPart, partLeaf, bipLeaf]
    all_goals first | exact hcomp _ | trivial | simp
  · unfold cohSojD imprimTree at h
    repeat' split at h
    all_goals cases h
    all_goals try (beta_reduce; unfold primLeaf; repeat' split)
    all_goals simp only [sp_LeafBlk, colPartD, partLeaf, bipLeaf]
    all_goals first | exact hcol _ | trivial | simp

/-- The leaves of `contI` are small. -/
theorem sp_contI_outSize {m t k : ℕ} {cs : List (List ℕ)} {D₁ D₂ C₁ : List ℕ}
    {f : ℕ → ℕ → ℕ} {o : Option SoJProg.LeafD} {s : ℕ} (hblk : sp_LeafBlk s o) (hm : m ≤ s)
    (hC₁ : C₁.length ≤ s) (hD₁ : D₁.length ≤ s) (hD₂ : D₂.length ≤ s) {o' : OutD}
    (h : Sum.inl o' = contI m t k cs D₁ D₂ C₁ f o) : outSize o' ≤ s := by
  rcases o with _ | ⟨tag, ⟨col, blk⟩, ⟨W₁, W₂, g⟩⟩
  · cases h
    exact sp_outSize_noneD s
  simp only [contI] at h
  split at h
  · cases h
    exact sp_outSize_addPieceD m (sp_outSize_addPieceD m (sp_outSize_partD hblk) hD₂) hD₁
  split at h
  · cases h
    refine sp_outSize_addPieceD m (sp_outSize_addPieceD m (sp_outSize_addPieceD m
      (sp_outSize_partD fun l hl => (sp_colBlkD_le m _ _ l hl).trans ?_) ?_) hD₂) hD₁
    · exact (List.length_filter_le _ _).trans (by simp [hm])
    · exact (List.length_filter_le _ _).trans hC₁
  · unfold shrinkI at h
    split at h
    · cases h
    · cases h
      exact sp_outSize_noneD s

theorem sp_LeafBlk_mono {L L' : ℕ} (h : L ≤ L') : ∀ {o : Option SoJProg.LeafD},
    sp_LeafBlk L o → sp_LeafBlk L' o
  | none, _ => trivial
  | some (_, (_, _), _), hb => fun l hl => (hb l hl).trans h

theorem sp_cohI_outSize {m t k : ℕ} {cs : List (List ℕ)} {D₁ D₂ C₁ C₂ : List ℕ}
    {f : ℕ → ℕ → ℕ} {s : ℕ} (hm : m ≤ s) (hC₁ : C₁.length ≤ s)
    (hC₁' : C₁.length * C₁.length + 1 ≤ s) (hD₁ : D₁.length ≤ s) (hD₂ : D₂.length ≤ s)
    {o' : OutD} (h : Sum.inl o' ∈ (cohI m t k cs D₁ D₂ C₁ C₂ f).1) : outSize o' ≤ s := by
  have hb := sp_cohSojD_leafBlk f (m + k) C₁ (C₂.map (m + ·))
  unfold cohI at h
  split at h
  · rename_i o hD
    simp only [List.mem_singleton] at h
    exact sp_contI_outSize (sp_LeafBlk_mono hC₁' (hb.1 o hD)) hm hC₁ hD₁ hD₂ h
  · rename_i opts kk hD
    obtain ⟨y, -, hy⟩ := List.mem_map.1 h
    exact sp_contI_outSize (sp_LeafBlk_mono hC₁' (hb.2 opts kk hD y)) hm hC₁ hD₁ hD₂ hy.symm

theorem sp_shrink_outSize {k : ℕ} {V : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {ops : List WrapOp} {o' : OutD} {s : ℕ}
    (h : Sum.inl o' ∈ [shrinkI k V cs a ops] ∨ Sum.inl o' ∈ [recI k V cs a ops]) :
    outSize o' ≤ s := by
  rcases h with h | h <;> simp only [List.mem_singleton] at h
  · unfold shrinkI at h
    split at h
    · cases h
    · cases h
      exact sp_outSize_noneD s
  · unfold recI at h
    split at h
    · cases h
    · cases h
      exact sp_outSize_noneD s

/-- The leaves of `dlI` are small. -/
theorem sp_dlI_outSize {m t : ℕ} {V₁ V₁' : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {d : ℕ} {wl : Array ℕ} {xd : List ℕ} {s : ℕ} (hV' : V₁'.length ≤ V₁.length) (hm : m ≤ s)
    (hV : V₁.length ≤ s) (hVV : V₁.length * V₁.length + 1 ≤ s) {o' : OutD}
    (h : Sum.inl o' ∈ (dlI m t V₁ V₁' cs a d wl xd).1) : outSize o' ≤ s := by
  have hD : (diffD V₁ V₁').length ≤ s := (List.length_filter_le _ _).trans hV
  rw [sp_dlI_eq] at h
  split at h
  · exact sp_shrink_outSize (.inl h)
  unfold sp_dlSkelI at h
  dsimp only at h
  split at h
  · exact sp_shrink_outSize (.inl h)
  unfold sp_dlBigI at h
  dsimp only at h
  split at h
  · simp only [List.mem_singleton, Sum.inl.injEq] at h
    subst h
    exact sp_outSize_addPieceD m (sp_outSize_partD fun l hl =>
      (sp_colBlkD_le m _ _ l hl).trans (hV'.trans hV)) hD
  split at h
  · exact sp_shrink_outSize (.inl h)
  have hC : (bigL V₁' (get ((List.range m).map fun y => fA (offsArr (m + cs.length))
      (cQArr m V₁' cs.length (Coherent.wlA 2 (V₁'.length + cs.length)
        (sqCodeArr V₁' cs.length a (skelArrD wl d cs.length xd))).1) y y).toArray) t).length ≤
      V₁.length := (sp_length_bigL _ _ _).trans hV'
  refine sp_cohI_outSize hm (hC.trans hV) ?_ hD ((List.length_filter_le _ _).trans (hV'.trans hV)) h
  have := Nat.mul_le_mul hC hC
  omega

/-- **The leaves of a level are small.** -/
theorem sp_bstepI_outSize {m t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a : Array Bool} {s : ℕ}
    (hcs : ∀ c ∈ cs, c.length ≤ s) (hk : cs.length ≤ s) (hm : m ≤ s) (hV : V₁.length ≤ s)
    (hVV : V₁.length * V₁.length + 1 ≤ s) {o : OutD}
    (h : Sum.inl o ∈ (bstepI m t V₁ cs a).1) : outSize o ≤ s := by
  rw [sp_bstepI_eq] at h
  split at h
  · simp only [List.mem_singleton, Sum.inl.injEq] at h
    subst h
    refine sp_outSize_partD (sp_arr_le fun x _ => ?_)
    split
    · exact (List.length_filter_le _ _).trans hV
    · exact (List.length_filter_le _ _).trans hV
  rename_i _ d₁ _
  have hV' : (tfDegD V₁ cs.length a d₁).length ≤ V₁.length := List.length_filter_le _ _
  split_ifs at h
  · simp only [List.mem_singleton, Sum.inl.injEq] at h
    subst h
    exact sp_outSize_le (by simp [johnD]) (by simp only [johnD]; omega) (by simpa [johnD] using hk)
      (by simpa [johnD] using hcs) (sp_arr_le fun x _ => (sp_length_fOfD _ _ _ _).trans hk)
  · obtain ⟨js, -, hjs⟩ := List.mem_map.1 h
    simp only [Sum.inl.injEq] at hjs
    subst hjs
    exact sp_outSize_partD fun l hl => (sp_colBlkD_le m _ _ l hl).trans hV
  unfold sp_daryI at h
  dsimp only at h
  split at h
  · exact sp_shrink_outSize (.inr h)
  obtain ⟨p, hp, hch⟩ := List.mem_flatMap.1 h
  obtain ⟨xd, -, rfl⟩ := List.mem_map.1 hp
  exact sp_dlI_outSize hV' hm hV hVV hch

theorem sp_mem_splitI_fst {l : List Item} {o : OutD} (h : o ∈ (splitI l).1) :
    Sum.inl o ∈ l := by
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.1 h
  cases i with
  | inl o' =>
    simp only [Sum.getLeft?_inl, Option.some.injEq] at he
    exact he ▸ hi
  | inr fr' => simp at he

/-- **The leaves of a step are small**: at most `outB m q` under the invariant. -/
theorem stepD_outSize {m q t : ℕ} {fr : FrameD} (hfr : fr.ValidP m q t) :
    ∀ o ∈ (stepD m t fr).1, outSize o ≤ outB m q := by
  intro o ho
  rw [stepD_eq] at ho
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
  have hVm := sp_length_le_of_lt hfr.valid.nodup hfr.valid.lt
  have hVV : fr.V₁.length * fr.V₁.length + 1 ≤ outB m q := by
    have := Nat.mul_le_mul hVm hVm
    unfold outB
    omega
  have hm : m ≤ outB m q := by unfold outB; omega
  refine sp_outSize_wrapD m (fun op hop => (hfr.ops op hop).trans hm) hm ?_
  exact sp_bstepI_outSize (fun c hc => (hfr.cellLen c hc).trans hm)
    (hfr.cells.trans (by unfold outB; omega)) hm (hVm.trans hm) hVV (sp_mem_splitI_fst ho')

end LeafSize

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_sp_flattenProg {t : Ty} {l₁ : var₁ (.list (.list t))} {l₂ : var₂ (.list (.list t))}
    (hl : ⟨.list (.list t), l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_flattenProg l₁) (sp_flattenProg l₂) := by
  unfold sp_flattenProg
  prog_wf

theorem wf_sp_div3Prog {x₁ : var₁ .nat} {x₂ : var₂ .nat} (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_div3Prog x₁) (sp_div3Prog x₂) := by
  unfold sp_div3Prog sp_div3Step
  prog_wf

theorem wf_sp_diffProg {V₁ V₁' : var₁ (.list .nat)} {V₂ V₂' : var₂ (.list .nat)}
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hV' : ⟨.list .nat, V₁', V₂'⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_diffProg V₁ V₁') (sp_diffProg V₂ V₂') := by
  unfold sp_diffProg Toolkit.filterList SoJProg.memProg anyList
  prog_wf

theorem wf_sp_subCellsProg {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {j₁ : var₁ (.list .nat)} {j₂ : var₂ (.list .nat)} (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ)
    (hj : ⟨.list .nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_subCellsProg c₁ j₁) (sp_subCellsProg c₂ j₂) := by
  unfold sp_subCellsProg mapList
  prog_wf

theorem wf_sp_restrictRelProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {o₁ : var₁ (.array .nat)}
    {o₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    {j₁ : var₁ (.list .nat)} {j₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hj : ⟨.list .nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_restrictRelProg m₁ o₁ a₁ j₁)
      (sp_restrictRelProg m₂ o₂ a₂ j₂) := by
  unfold sp_restrictRelProg mapList relAtProg sp_flattenProg
  prog_wf

theorem wf_sp_pieceProg {D₁ : var₁ (.list .nat)} {D₂ : var₂ (.list .nat)}
    (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_pieceProg D₁) (sp_pieceProg D₂) := by
  unfold sp_pieceProg emptyNatArrProg
  prog_wf

theorem wf_sp_frameProg {V₁ : var₁ (.list .nat)} {V₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))} {a₁ : var₁ (.array .bool)}
    {a₂ : var₂ (.array .bool)} {o₁ : var₁ (.list wrapTy)} {o₂ : var₂ (.list wrapTy)}
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (ho : ⟨.list wrapTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_frameProg V₁ c₁ a₁ o₁) (sp_frameProg V₂ c₂ a₂ o₂) := by
  unfold sp_frameProg
  prog_wf

theorem wf_sp_leafPair {o₁ : var₁ outTy} {o₂ : var₂ outTy} (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_leafPair o₁) (sp_leafPair o₂) := by
  unfold sp_leafPair
  prog_wf

theorem wf_sp_framePair {f₁ : var₁ frameTy} {f₂ : var₂ frameTy} (hf : ⟨frameTy, f₁, f₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_framePair f₁) (sp_framePair f₂) := by
  unfold sp_framePair
  prog_wf

theorem wf_sp_recIProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {V₁ : var₁ (.list .nat)}
    {V₂ : var₂ (.list .nat)} {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} {o₁ : var₁ (.list wrapTy)}
    {o₂ : var₂ (.list wrapTy)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (ho : ⟨.list wrapTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_recIProg k₁ V₁ c₁ a₁ o₁)
      (sp_recIProg k₂ V₂ c₂ a₂ o₂) := by
  unfold sp_recIProg sp_frameProg sp_framePair sp_leafPair noneProg emptyNatArrProg
    emptyLstArrProg mkOutProg
  prog_wf

theorem wf_sp_shrinkIProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {V₁ : var₁ (.list .nat)}
    {V₂ : var₂ (.list .nat)} {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} {o₁ : var₁ (.list wrapTy)}
    {o₂ : var₂ (.list wrapTy)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (ho : ⟨.list wrapTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_shrinkIProg k₁ V₁ c₁ a₁ o₁)
      (sp_shrinkIProg k₂ V₂ c₂ a₂ o₂) := by
  unfold sp_shrinkIProg sp_frameProg sp_framePair sp_leafPair noneProg emptyNatArrProg
    emptyLstArrProg mkOutProg
  prog_wf

theorem wf_sp_opProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    {p₁ : var₁ wrapTy} {p₂ : var₂ wrapTy} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ)
    (hp : ⟨wrapTy, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_opProg m₁ o₁ p₁) (sp_opProg m₂ o₂ p₂) := by
  unfold sp_opProg
  refine .bind (.prim _ (.cons hp .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hp]) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .ite (by simp) ?_ ?_
  · exact wf_extendOutProg (by simp [hm]) (by simp) (by simp) (by simp [ho])
  · exact wf_addPieceProg (by simp [hm]) (by simp) (by simp [ho])

theorem wf_sp_wrapDProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {w₁ : var₁ (.list wrapTy)}
    {w₂ : var₂ (.list wrapTy)} {o₁ : var₁ outTy} {o₂ : var₂ outTy} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hw : ⟨.list wrapTy, w₁, w₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_wrapDProg m₁ w₁ o₁) (sp_wrapDProg m₂ w₂ o₂) := by
  unfold sp_wrapDProg
  exact .foldList hw ho fun _ _ _ _ => wf_sp_opProg (by simp [hm]) (by simp) (by simp)

theorem wf_sp_rewrapProg {w₁ : var₁ (.list wrapTy)} {w₂ : var₂ (.list wrapTy)}
    {f₁ : var₁ frameTy} {f₂ : var₂ frameTy} (hw : ⟨.list wrapTy, w₁, w₂⟩ ∈ Γ)
    (hf : ⟨frameTy, f₁, f₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_rewrapProg w₁ f₁) (sp_rewrapProg w₂ f₂) := by
  unfold sp_rewrapProg sp_frameProg
  prog_wf

theorem wf_sp_idxQProg {m₁ k₁ u₁ : var₁ .nat} {m₂ k₂ u₂ : var₂ .nat} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_idxQProg m₁ k₁ p₁ u₁) (sp_idxQProg m₂ k₂ p₂ u₂) := by
  unfold sp_idxQProg
  refine .bind (.prim _ (.cons hu (.cons hm .nil))) fun _ _ => .ite (by simp) ?_ ?_
  · exact .bind (wf_memProg (by simp [hu]) (by simp [hp])) fun _ _ => .ite (by simp)
      (.bind (Graph.wf_idxOfProg (by simp [hp]) (by simp [hu])) fun _ _ =>
        .prim _ (.cons (by simp) .nil)) (.prim _ .nil)
  · prog_wf

theorem wf_sp_cQdProg {m₁ k₁ u₁ v₁ : var₁ .nat} {m₂ k₂ u₂ v₂ : var₂ .nat}
    {p₁ : var₁ (.list .nat)} {p₂ : var₂ (.list .nat)} {o₁ W₁ : var₁ (.array .nat)}
    {o₂ W₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_cQdProg m₁ k₁ p₁ o₁ W₁ u₁ v₁)
      (sp_cQdProg m₂ k₂ p₂ o₂ W₂ u₂ v₂) := by
  unfold sp_cQdProg
  refine .bind (wf_sp_idxQProg hm hk hp hu) fun _ _ =>
    .bind (wf_sp_idxQProg (by simp [hm]) (by simp [hk]) (by simp [hp]) (by simp [hv]))
    fun _ _ => ?_
  have := ho
  have := hW
  prog_wf

theorem wf_sp_cQArrProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} {W₁ : var₁ (.array .nat)} {W₂ : var₂ (.array .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ)
    (hW : ⟨.array .nat, W₁, W₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_cQArrProg m₁ k₁ p₁ W₁) (sp_cQArrProg m₂ k₂ p₂ W₂) := by
  unfold sp_cQArrProg
  refine .bind (.prim _ (.cons hp .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp [hk]) .nil))) fun _ _ =>
    .bind (wf_offsetsProg (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) (.cons (by simp [hk]) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind ?_ fun _ _ =>
    .bind (wf_sp_flattenProg (by simp)) fun _ _ => .prim _ (.cons (by simp) .nil)
  exact wf_mapList (by simp) fun Γ' hΓ u₁ u₂ hu => wf_mapList (hΓ (by simp)) fun Γ'' hΓ' v₁ v₂ hv =>
    wf_sp_cQdProg (hΓ' (hΓ (by simp [hm]))) (hΓ' (hΓ (by simp [hk])))
      (hΓ' (hΓ (by simp [hp]))) (hΓ' (hΓ (by simp))) (hΓ' (hΓ (by simp [hW]))) (hΓ' hu) hv

theorem wf_sp_skelArrProg {wl₁ : var₁ (.array .nat)} {wl₂ : var₂ (.array .nat)}
    {pw₁ : var₁ (.array (.array .nat))} {pw₂ : var₂ (.array (.array .nat))}
    {rd₁ : var₁ (.list .nat)} {rd₂ : var₂ (.list .nat)} {k₁ : var₁ .nat} {k₂ : var₂ .nat}
    {x₁ : var₁ (.list .nat)} {x₂ : var₂ (.list .nat)} (hwl : ⟨.array .nat, wl₁, wl₂⟩ ∈ Γ)
    (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ) (hrd : ⟨.list .nat, rd₁, rd₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hx : ⟨.list .nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_skelArrProg wl₁ pw₁ rd₁ k₁ x₁)
      (sp_skelArrProg wl₂ pw₂ rd₂ k₂ x₂) := by
  unfold sp_skelArrProg
  refine .bind (.prim _ (.cons hx .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hx]) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp [hk]) .nil)) fun _ _ => .bind ?_ fun _ _ =>
    .bind (wf_sp_flattenProg (by simp)) fun _ _ => .prim _ (.cons (by simp) .nil)
  refine wf_mapList (by simp) fun Γ' hΓ j₁ j₂ hj => wf_mapList (hΓ (by simp))
    fun Γ'' hΓ' i₁ i₂ hi => ?_
  have hwl'' : ⟨.array .nat, wl₁, wl₂⟩ ∈ Γ'' := hΓ' (hΓ (by simp [hwl]))
  exact .bind (Coherent.wf_pad2Prog (hΓ' (hΓ (by simp [hpw]))) (hΓ' (hΓ (by simp [hrd])))
      (hΓ' (hΓ (by simp))) (hΓ' (hΓ (by simp))) hi (hΓ' hj)) fun _ _ =>
    .prim _ (.cons (by simp [hwl'']) (.cons (by simp) .nil))

theorem wf_sp_isBaseProg {t₁ k₁ : var₁ .nat} {t₂ k₂ : var₂ .nat} (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_isBaseProg t₁ k₁) (sp_isBaseProg t₂ k₂) := by
  unfold sp_isBaseProg
  refine .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp [ht])
    (.cons (by simp [ht]) .nil))) fun _ _ => .bind (wf_clogProg (by simp) (by simp)) fun _ _ => ?_
  unfold Coherent.mulNProg
  have := hk
  prog_wf

theorem wf_sp_diagProg {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)}
    {s₁ n₁ : var₁ .nat} {s₂ n₂ : var₂ .nat} (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_diagProg o₁ c₁ s₁ n₁) (sp_diagProg o₂ c₂ s₂ n₂) := by
  unfold sp_diagProg mapList csColProg
  prog_wf

theorem wf_sp_rectProg {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)}
    {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat} (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_rectProg o₁ c₁ m₁ k₁) (sp_rectProg o₂ c₂ m₂ k₂) := by
  unfold sp_rectProg mapList csColProg
  prog_wf

theorem wf_sp_cellUDProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat}
    {c₁ : var₁ (.array (.list .nat))} {c₂ : var₂ (.array (.list .nat))}
    {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hc : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ)
    (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_cellUDProg m₁ k₁ c₁ l₁) (sp_cellUDProg m₂ k₂ c₂ l₂) := by
  unfold sp_cellUDProg Toolkit.filterList mapList sp_flattenProg SoJProg.memProg anyList
  prog_wf

theorem wf_sp_dedupProg {m₁ : var₁ .nat} {m₂ : var₂ .nat} {l₁ : var₁ (.list (.list .nat))}
    {l₂ : var₂ (.list (.list .nat))} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hl : ⟨.list (.list .nat), l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_dedupProg m₁ l₁) (sp_dedupProg m₂ l₂) := by
  unfold sp_dedupProg
  refine .bind (.prim _ .nil) fun _ _ => .foldList (by simp [hl]) (by simp) fun _ _ _ _ =>
    .bind (wf_anyList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_setEqProg (hΓ (by simp [hm])) (hΓ (by simp)) hx) fun _ _ => ?_
  prog_wf

theorem wf_sp_bipRelXProg {m₁ k₁ N₁ g₁ : var₁ .nat} {m₂ k₂ N₂ g₂ : var₂ .nat}
    {c₁ : var₁ (.array (.list .nat))} {c₂ : var₂ (.array (.list .nat))}
    {o₁ q₁ : var₁ (.array .nat)} {o₂ q₂ : var₂ (.array .nat)}
    {W₁ L₁ : var₁ (.list (.list .nat))} {W₂ L₂ : var₂ (.list (.list .nat))}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hg : ⟨.nat, g₁, g₂⟩ ∈ Γ) (hc : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ)
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ)
    (hW : ⟨.list (.list .nat), W₁, W₂⟩ ∈ Γ) (hL : ⟨.list (.list .nat), L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_bipRelXProg m₁ k₁ N₁ g₁ c₁ o₁ q₁ W₁ L₁)
      (sp_bipRelXProg m₂ k₂ N₂ g₂ c₂ o₂ q₂ W₂ L₂) := by
  unfold sp_bipRelXProg
  refine .bind (.prim _ (.cons hm .nil)) fun _ _ => .bind ?_ fun _ _ =>
    .bind (wf_sp_flattenProg (by simp)) fun _ _ => .prim _ (.cons (by simp) .nil)
  refine wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx => wf_mapList (hΓ (by simp [hL]))
    fun Γ'' hΓ' e₁ e₂ he => ?_
  unfold sp_bipEntryProg
  refine wf_anyList (hΓ' (hΓ (by simp [hW]))) fun Γ₃ hΓ₃ l₁ l₂ hl => ?_
  have hm' : ⟨.nat, m₁, m₂⟩ ∈ Γ₃ := hΓ₃ (hΓ' (hΓ (by simp [hm])))
  refine .bind (wf_sp_cellUDProg hm' (hΓ₃ (hΓ' (hΓ (by simp [hk]))))
    (hΓ₃ (hΓ' (hΓ (by simp [hc])))) hl) fun _ _ =>
    .bind (wf_setEqProg (by simp [hm']) (by simp) (by simp [hΓ₃ he])) fun _ _ => ?_
  have hN' : ⟨.nat, N₁, N₂⟩ ∈ Γ₃ := hΓ₃ (hΓ' (hΓ (by simp [hN])))
  have hg' : ⟨.nat, g₁, g₂⟩ ∈ Γ₃ := hΓ₃ (hΓ' (hΓ (by simp [hg])))
  have ho' : ⟨.array .nat, o₁, o₂⟩ ∈ Γ₃ := hΓ₃ (hΓ' (hΓ (by simp [ho])))
  have hq' : ⟨.array .nat, q₁, q₂⟩ ∈ Γ₃ := hΓ₃ (hΓ' (hΓ (by simp [hq])))
  have hx' : ⟨.nat, x₁, x₂⟩ ∈ Γ₃ := hΓ₃ (hΓ' hx)
  unfold anyList csColProg
  prog_wf

theorem wf_sp_catProg {p₁ : var₁ (.list (.prod (.list outTy) (.list frameTy)))}
    {p₂ : var₂ (.list (.prod (.list outTy) (.list frameTy)))}
    (hp : ⟨.list (.prod (.list outTy) (.list frameTy)), p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_catProg p₁) (sp_catProg p₂) := by
  unfold sp_catProg mapList sp_flattenProg
  prog_wf

theorem wf_sp_contBigProg {m₁ k₁ g₁ : var₁ .nat} {m₂ k₂ g₂ : var₂ .nat}
    {c₁ : var₁ (.array (.list .nat))} {c₂ : var₂ (.array (.list .nat))}
    {o₁ q₁ : var₁ (.array .nat)} {o₂ q₂ : var₂ (.array .nat)}
    {W₁ : var₁ (.list (.list .nat))} {W₂ : var₂ (.list (.list .nat))}
    {V₁ DW₁ D₁ E₁ : var₁ (.list .nat)} {V₂ DW₂ D₂ E₂ : var₂ (.list .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hc : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ) (hW : ⟨.list (.list .nat), W₁, W₂⟩ ∈ Γ)
    (hg : ⟨.nat, g₁, g₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hDW : ⟨.list .nat, DW₁, DW₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_contBigProg m₁ k₁ c₁ o₁ q₁ W₁ g₁ V₁ DW₁ D₁ E₁)
      (sp_contBigProg m₂ k₂ c₂ o₂ q₂ W₂ g₂ V₂ DW₂ D₂ E₂) := by
  unfold sp_contBigProg
  refine .bind (wf_mapList hW fun Γ' hΓ x₁ x₂ hx =>
    wf_sp_cellUDProg (hΓ hm) (hΓ hk) (hΓ hc) hx)
    fun _ _ => .bind (wf_sp_dedupProg (by simp [hm]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) (.cons (by simp [hk]) .nil))) fun _ _ =>
    .bind (wf_sp_bipRelXProg (by simp [hm]) (by simp [hk]) (by simp) (by simp [hg])
      (by simp [hc]) (by simp [ho]) (by simp [hq]) (by simp [hW]) (by simp)) fun _ _ =>
    .bind (wf_sp_pieceProg (by simp [hDW])) fun _ _ =>
    .bind (wf_sp_pieceProg (by simp [hE])) fun _ _ =>
    .bind (wf_sp_pieceProg (by simp [hD])) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    wf_sp_shrinkIProg (by simp [hk]) (by simp [hV]) (by simp) (by simp) (by simp)

theorem wf_sp_contSmallProg {m₁ : var₁ .nat} {m₂ : var₂ .nat}
    {V₁ DW₁ D₁ E₁ : var₁ (.list .nat)} {V₂ DW₂ D₂ E₂ : var₂ (.list .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hDW : ⟨.list .nat, DW₁, DW₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_contSmallProg m₁ V₁ DW₁ D₁ E₁)
      (sp_contSmallProg m₂ V₂ DW₂ D₂ E₂) := by
  unfold sp_contSmallProg
  exact .bind wf_emptyNatArrProg fun _ _ =>
    .bind (wf_colBlkProg (by simp [hm]) (by simp [hV]) (by simp)) fun _ _ =>
    .bind (wf_partProg (by simp) (by simp)) fun _ _ =>
    .bind (wf_addPieceProg (by simp [hm]) (by simp [hDW]) (by simp)) fun _ _ =>
    .bind (wf_addPieceProg (by simp [hm]) (by simp [hE]) (by simp)) fun _ _ =>
    .bind (wf_addPieceProg (by simp [hm]) (by simp [hD]) (by simp)) fun _ _ =>
    wf_sp_leafPair (by simp)

theorem wf_sp_contBipProg {m₁ t₁ k₁ g₁ : var₁ .nat} {m₂ t₂ k₂ g₂ : var₂ .nat}
    {c₁ : var₁ (.array (.list .nat))} {c₂ : var₂ (.array (.list .nat))}
    {D₁ E₁ F₁ U₁ : var₁ (.list .nat)} {D₂ E₂ F₂ U₂ : var₂ (.list .nat)}
    {o₁ q₁ : var₁ (.array .nat)} {o₂ q₂ : var₂ (.array .nat)}
    {W₁ : var₁ (.list (.list .nat))} {W₂ : var₂ (.list (.list .nat))}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hc : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) (hF : ⟨.list .nat, F₁, F₂⟩ ∈ Γ)
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ)
    (hU : ⟨.list .nat, U₁, U₂⟩ ∈ Γ) (hW : ⟨.list (.list .nat), W₁, W₂⟩ ∈ Γ)
    (hg : ⟨.nat, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_contBipProg m₁ t₁ k₁ c₁ D₁ E₁ F₁ o₁ q₁ U₁ W₁ g₁)
      (sp_contBipProg m₂ t₂ k₂ c₂ D₂ E₂ F₂ o₂ q₂ U₂ W₂ g₂) := by
  unfold sp_contBipProg
  exact .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (Toolkit.wf_filterList (by simp) fun Γ' hΓ y₁ y₂ hy =>
      wf_memProg hy (hΓ (by simp [hU]))) fun _ _ =>
    .bind (wf_sp_diffProg (by simp [hF]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [ht]) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp)
      (wf_sp_contBigProg (by simp [hm]) (by simp [hk]) (by simp [hc]) (by simp [ho])
        (by simp [hq]) (by simp [hW]) (by simp [hg]) (by simp) (by simp) (by simp [hD])
        (by simp [hE]))
      (wf_sp_contSmallProg (by simp [hm]) (by simp) (by simp) (by simp [hD]) (by simp [hE]))

theorem wf_sp_contProg {m₁ t₁ k₁ : var₁ .nat} {m₂ t₂ k₂ : var₂ .nat}
    {c₁ : var₁ (.array (.list .nat))} {c₂ : var₂ (.array (.list .nat))}
    {D₁ E₁ F₁ : var₁ (.list .nat)} {D₂ E₂ F₂ : var₂ (.list .nat)}
    {o₁ q₁ : var₁ (.array .nat)} {o₂ q₂ : var₂ (.array .nat)}
    {l₁ : var₁ (.option cohLeafTy)} {l₂ : var₂ (.option cohLeafTy)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hc : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) (hF : ⟨.list .nat, F₁, F₂⟩ ∈ Γ)
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ)
    (hl : ⟨.option cohLeafTy, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_contProg m₁ t₁ k₁ c₁ D₁ E₁ F₁ o₁ q₁ l₁)
      (sp_contProg m₂ t₂ k₂ c₂ D₂ E₂ F₂ o₂ q₂ l₂) := by
  unfold sp_contProg
  refine .caseOption hl (.bind wf_noneProg fun _ _ => wf_sp_leafPair (by simp))
    fun lf₁ lf₂ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => .ite (by simp) ?_ ?_
  · refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (wf_partProg (by simp) (by simp)) fun _ _ =>
      .bind (wf_addPieceProg (by simp [hm]) (by simp [hE]) (by simp)) fun _ _ =>
      .bind (wf_addPieceProg (by simp [hm]) (by simp [hD]) (by simp)) fun _ _ =>
      wf_sp_leafPair (by simp)
  · exact .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      wf_sp_contBipProg (by simp [hm]) (by simp [ht]) (by simp [hk]) (by simp [hc])
        (by simp [hD]) (by simp [hE]) (by simp [hF]) (by simp [ho]) (by simp [hq]) (by simp)
        (by simp) (by simp)

theorem wf_sp_cohIProg {m₁ t₁ k₁ : var₁ .nat} {m₂ t₂ k₂ : var₂ .nat}
    {c₁ : var₁ (.array (.list .nat))} {c₂ : var₂ (.array (.list .nat))}
    {D₁ E₁ F₁ G₁ : var₁ (.list .nat)} {D₂ E₂ F₂ G₂ : var₂ (.list .nat)}
    {o₁ q₁ : var₁ (.array .nat)} {o₂ q₂ : var₂ (.array .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hc : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hE : ⟨.list .nat, E₁, E₂⟩ ∈ Γ) (hF : ⟨.list .nat, F₁, F₂⟩ ∈ Γ)
    (hG : ⟨.list .nat, G₁, G₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_cohIProg m₁ t₁ k₁ c₁ D₁ E₁ F₁ G₁ o₁ q₁)
      (sp_cohIProg m₂ t₂ k₂ c₂ D₂ E₂ F₂ G₂ o₂ q₂) := by
  unfold sp_cohIProg
  refine .bind (.prim _ (.cons hm (.cons hk .nil))) fun _ _ =>
    .bind (wf_mapList (by simp [hG]) fun Γ' hΓ j₁ j₂ hj =>
      .prim _ (.cons (hΓ (by simp [hm])) (.cons hj .nil))) fun _ _ =>
    .bind (wf_cohSojProg (by simp) (by simp [hq]) (by simp [hF]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .ite (by simp) ?_ ?_
  · refine .bind (wf_mapList (by simp) fun Γ' hΓ y₁ y₂ hy => ?_) fun _ _ => wf_sp_catProg (by simp)
    have hm' : ⟨.nat, m₁, m₂⟩ ∈ Γ' := hΓ (by simp [hm])
    have ht' : ⟨.nat, t₁, t₂⟩ ∈ Γ' := hΓ (by simp [ht])
    have hk' : ⟨.nat, k₁, k₂⟩ ∈ Γ' := hΓ (by simp [hk])
    have hc' : ⟨.array (.list .nat), c₁, c₂⟩ ∈ Γ' := hΓ (by simp [hc])
    have hD' : ⟨.list .nat, D₁, D₂⟩ ∈ Γ' := hΓ (by simp [hD])
    have hE' : ⟨.list .nat, E₁, E₂⟩ ∈ Γ' := hΓ (by simp [hE])
    have hF' : ⟨.list .nat, F₁, F₂⟩ ∈ Γ' := hΓ (by simp [hF])
    have ho' : ⟨.array .nat, o₁, o₂⟩ ∈ Γ' := hΓ (by simp [ho])
    have hq' : ⟨.array .nat, q₁, q₂⟩ ∈ Γ' := hΓ (by simp [hq])
    exact .bind (.prim _ (.cons (hΓ (by simp)) (.cons hy .nil))) fun _ _ =>
      wf_sp_contProg (by simp [hm']) (by simp [ht']) (by simp [hk']) (by simp [hc'])
        (by simp [hD']) (by simp [hE']) (by simp [hF']) (by simp [ho']) (by simp [hq'])
        (by simp)
  · exact .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp)
      .nil))) fun _ _ => wf_sp_contProg (by simp [hm]) (by simp [ht]) (by simp [hk])
      (by simp [hc]) (by simp [hD]) (by simp [hE]) (by simp [hF]) (by simp [ho])
      (by simp [hq]) (by simp)

theorem wf_sp_callProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat} {V₁ D₁ j₁ : var₁ (.list .nat)}
    {V₂ D₂ j₂ : var₂ (.list .nat)} {c₁ : var₁ (.list (.list .nat))}
    {c₂ : var₂ (.list (.list .nat))} {o₁ : var₁ (.array .nat)} {o₂ : var₂ (.array .nat)}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hj : ⟨.list .nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_callProg m₁ k₁ V₁ c₁ o₁ a₁ D₁ j₁)
      (sp_callProg m₂ k₂ V₂ c₂ o₂ a₂ D₂ j₂) := by
  unfold sp_callProg
  exact .bind (wf_sp_subCellsProg hc hj) fun _ _ =>
    .bind (wf_sp_restrictRelProg (by simp [hm]) (by simp [ho]) (by simp [ha]) (by simp [hj]))
    fun _ _ => .bind (wf_sp_pieceProg (by simp [hD])) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    wf_sp_shrinkIProg (by simp [hk]) (by simp [hV]) (by simp) (by simp) (by simp)

theorem wf_sp_selCallProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat}
    {V₁ D₁ rk₁ : var₁ (.list .nat)} {V₂ D₂ rk₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {o₁ q₁ : var₁ (.array .nat)} {o₂ q₂ : var₂ (.array .nat)}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_selCallProg m₁ k₁ V₁ c₁ o₁ a₁ D₁ rk₁ q₁)
      (sp_selCallProg m₂ k₂ V₂ c₂ o₂ a₂ D₂ rk₂ q₂) := by
  unfold sp_selCallProg
  exact .bind (wf_selThirdProg hrk hq) fun _ _ =>
    .bind (wf_pickSideProg (by simp [hV]) (by simp [hk]) (by simp [ha]) (by simp)) fun _ _ =>
    wf_sp_callProg (by simp [hm]) (by simp [hk]) (by simp [hV]) (by simp [hc]) (by simp [ho])
      (by simp [ha]) (by simp [hD]) (by simp)

theorem wf_sp_dlBigProg {m₁ t₁ k₁ s₁ : var₁ .nat} {m₂ t₂ k₂ s₂ : var₂ .nat}
    {V₁ rk₁ D₁ : var₁ (.list .nat)} {V₂ rk₂ D₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {ca₁ : var₁ (.array (.list .nat))} {ca₂ : var₂ (.array (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    {o₁ n₁ q₁ l₁ : var₁ (.array .nat)} {o₂ n₂ q₂ l₂ : var₂ (.array .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (hca : ⟨.array (.list .nat), ca₁, ca₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hn : ⟨.array .nat, n₁, n₂⟩ ∈ Γ) (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ)
    (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ
      (sp_dlBigProg m₁ t₁ k₁ s₁ V₁ c₁ ca₁ a₁ o₁ rk₁ D₁ n₁ q₁ l₁)
      (sp_dlBigProg m₂ t₂ k₂ s₂ V₂ c₂ ca₂ a₂ o₂ rk₂ D₂ n₂ q₂ l₂) := by
  unfold sp_dlBigProg
  refine .bind (wf_bigProg hrk hl hs) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (wf_sp_diagProg (by simp [hn]) (by simp [hq]) (by simp) (by simp [hm])) fun _ _ =>
    .bind (wf_bigProg (by simp [hV]) (by simp) (by simp [ht])) fun _ _ =>
    .caseList (by simp) ?_ fun _ _ _ _ => ?_
  · exact .bind (wf_colBlkProg (by simp [hm]) (by simp [hV]) (by simp)) fun _ _ =>
      .bind (wf_partProg (by simp) (by simp)) fun _ _ =>
      .bind (wf_addPieceProg (by simp [hm]) (by simp [hD]) (by simp)) fun _ _ =>
      wf_sp_leafPair (by simp)
  refine .bind (wf_sp_rectProg (by simp [hn]) (by simp [hq]) (by simp [hm]) (by simp [hk]))
    fun _ _ => .bind (wf_constRectProg (by simp) (by simp) (by simp)) fun _ _ =>
    .ite (by simp) ?_ ?_
  · exact .bind (Toolkit.wf_filterList (by simp [hrk]) fun Γ' hΓ j₁ j₂ hj =>
        .bind (wf_memProg hj (hΓ (by simp))) fun _ _ => .prim _ (.cons (by simp) .nil))
      fun _ _ => wf_sp_callProg (by simp [hm]) (by simp [hk]) (by simp [hV]) (by simp [hc])
        (by simp [ho]) (by simp [ha]) (by simp [hD]) (by simp)
  · exact .bind (wf_sp_diffProg (by simp [hV]) (by simp)) fun _ _ =>
      wf_sp_cohIProg (by simp [hm]) (by simp [ht]) (by simp [hk]) (by simp [hca]) (by simp [hD])
        (by simp) (by simp) (by simp) (by simp [hn]) (by simp [hq])

theorem wf_sp_dlSkelProg {m₁ t₁ k₁ s₁ : var₁ .nat} {m₂ t₂ k₂ s₂ : var₂ .nat}
    {V₁ rd₁ rk₁ D₁ x₁ : var₁ (.list .nat)} {V₂ rd₂ rk₂ D₂ x₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {ca₁ : var₁ (.array (.list .nat))} {ca₂ : var₂ (.array (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} {o₁ w₁ : var₁ (.array .nat)}
    {o₂ w₂ : var₂ (.array .nat)} {pw₁ : var₁ (.array (.array .nat))}
    {pw₂ : var₂ (.array (.array .nat))} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (hca : ⟨.array (.list .nat), ca₁, ca₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hw : ⟨.array .nat, w₁, w₂⟩ ∈ Γ) (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hrd : ⟨.list .nat, rd₁, rd₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hx : ⟨.list .nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ
      (sp_dlSkelProg m₁ t₁ k₁ s₁ V₁ c₁ ca₁ a₁ o₁ w₁ pw₁ rd₁ rk₁ D₁ x₁)
      (sp_dlSkelProg m₂ t₂ k₂ s₂ V₂ c₂ ca₂ a₂ o₂ w₂ pw₂ rd₂ rk₂ D₂ x₂) := by
  unfold sp_dlSkelProg
  refine .bind (wf_sp_skelArrProg hw hpw hrd hk hx) fun _ _ =>
    .bind (wf_cohProg (by simp [hV]) (by simp [hk]) (by simp [ha]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_sp_cQArrProg (by simp [hm]) (by simp [hk]) (by simp [hV]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) (.cons (by simp [hk]) .nil))) fun _ _ => ?_
  refine .bind (by unfold csOffsProg; prog_wf) fun _ _ =>
    .bind (wf_sp_diagProg (by simp) (by simp) (by simp [hm]) (by simp [hk])) fun _ _ =>
    .bind (wf_allSmallProg (by simp [hrk]) (by simp) (by simp [hs])) fun _ _ =>
    .ite (by simp)
      (wf_sp_selCallProg (by simp [hm]) (by simp [hk]) (by simp [hV]) (by simp [hc])
        (by simp [ho]) (by simp [ha]) (by simp [hD]) (by simp [hrk]) (by simp))
      (wf_sp_dlBigProg (by simp [hm]) (by simp [ht]) (by simp [hk]) (by simp [hs])
        (by simp [hV]) (by simp [hc]) (by simp [hca]) (by simp [ha]) (by simp [ho])
        (by simp [hrk]) (by simp [hD]) (by simp) (by simp) (by simp))

theorem wf_sp_dlProg {m₁ t₁ k₁ s₁ : var₁ .nat} {m₂ t₂ k₂ s₂ : var₂ .nat}
    {V₁ rd₁ rk₁ D₁ x₁ : var₁ (.list .nat)} {V₂ rd₂ rk₂ D₂ x₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {ca₁ : var₁ (.array (.list .nat))} {ca₂ : var₂ (.array (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} {o₁ w₁ : var₁ (.array .nat)}
    {o₂ w₂ : var₂ (.array .nat)} {pw₁ : var₁ (.array (.array .nat))}
    {pw₂ : var₂ (.array (.array .nat))} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hs : ⟨.nat, s₁, s₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (hca : ⟨.array (.list .nat), ca₁, ca₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hw : ⟨.array .nat, w₁, w₂⟩ ∈ Γ) (hpw : ⟨.array (.array .nat), pw₁, pw₂⟩ ∈ Γ)
    (hrd : ⟨.list .nat, rd₁, rd₂⟩ ∈ Γ) (hrk : ⟨.list .nat, rk₁, rk₂⟩ ∈ Γ)
    (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ) (hx : ⟨.list .nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_dlProg m₁ t₁ k₁ s₁ V₁ c₁ ca₁ a₁ o₁ w₁ pw₁ rd₁ rk₁ D₁ x₁)
      (sp_dlProg m₂ t₂ k₂ s₂ V₂ c₂ ca₂ a₂ o₂ w₂ pw₂ rd₂ rk₂ D₂ x₂) := by
  unfold sp_dlProg
  exact .bind (.prim _ (.cons hx .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hx]) .nil))
    fun _ _ => .bind (Coherent.wf_col1Prog (by simp [hw]) (by simp [hpw]) (by simp [hrd])
      (by simp [hrk]) (by simp) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (Coherent.wf_domProg (by simp) (by simp) (by simp) (by simp [hs])) fun _ _ =>
    .caseOption (by simp)
      (wf_sp_selCallProg (by simp [hm]) (by simp [hk]) (by simp [hV]) (by simp [hc])
        (by simp [ho]) (by simp [ha]) (by simp [hD]) (by simp [hrk]) (by simp))
      fun _ _ => wf_sp_dlSkelProg (by simp [hm]) (by simp [ht]) (by simp [hk]) (by simp [hs])
        (by simp [hV]) (by simp [hc]) (by simp [hca]) (by simp [ha]) (by simp [ho])
        (by simp [hw]) (by simp [hpw]) (by simp [hrd]) (by simp [hrk]) (by simp [hD])
        (by simp [hx])

theorem wf_sp_baseProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat} {o₁ : var₁ (.array .nat)}
    {o₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)}
    {V₁ : var₁ (.list .nat)} {V₂ : var₂ (.list .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_baseProg m₁ k₁ o₁ a₁ V₁)
      (sp_baseProg m₂ k₂ o₂ a₂ V₂) := by
  unfold sp_baseProg
  refine .bind (wf_enumsProg hk) fun _ _ => .bind (wf_mapList (by simp) fun Γ' hΓ j₁ j₂ hj =>
    .bind (wf_baseLeafProg (hΓ (by simp [hm])) (hΓ (by simp [ho])) (hΓ (by simp [ha]))
      (hΓ (by simp [hV])) hj) fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => wf_partProg (by simp) (by simp))
    fun _ _ => ?_
  prog_wf

theorem wf_sp_daryRecProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat}
    {o₁ : var₁ (.array .nat)} {o₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)}
    {a₂ : var₂ (.array .bool)} {V₁ D₁ S₁ : var₁ (.list .nat)} {V₂ D₂ S₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hS : ⟨.list .nat, S₁, S₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_daryRecProg m₁ k₁ o₁ a₁ V₁ c₁ D₁ S₁)
      (sp_daryRecProg m₂ k₂ o₂ a₂ V₂ c₂ D₂ S₂) := by
  unfold sp_daryRecProg
  exact .bind (wf_pickSideProg hV hk ha hS) fun _ _ =>
    .bind (wf_sp_subCellsProg (by simp [hc]) (by simp)) fun _ _ =>
    .bind (wf_sp_restrictRelProg (by simp [hm]) (by simp [ho]) (by simp [ha]) (by simp))
    fun _ _ => .bind (wf_sp_pieceProg (by simp [hD])) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    wf_sp_recIProg (by simp [hk]) (by simp [hV]) (by simp) (by simp) (by simp)

theorem wf_sp_daryDLProg {m₁ t₁ k₁ d₁ : var₁ .nat} {m₂ t₂ k₂ d₂ : var₂ .nat}
    {o₁ : var₁ (.array .nat)} {o₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)}
    {a₂ : var₂ (.array .bool)} {V₁ D₁ : var₁ (.list .nat)} {V₂ D₂ : var₂ (.list .nat)}
    {c₁ h₁ : var₁ (.list (.list .nat))} {c₂ h₂ : var₂ (.list (.list .nat))}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (hD : ⟨.list .nat, D₁, D₂⟩ ∈ Γ)
    (hh : ⟨.list (.list .nat), h₁, h₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_daryDLProg m₁ t₁ k₁ d₁ o₁ a₁ V₁ c₁ D₁ h₁)
      (sp_daryDLProg m₂ t₂ k₂ d₂ o₂ a₂ V₂ c₂ D₂ h₂) := by
  unfold sp_daryDLProg
  refine .bind (wf_daryWLProg hk hd hh) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hk]) (.cons (by simp [hk]) .nil))) fun _ _ =>
    .bind (wf_sp_div3Prog (by simp)) fun _ _ =>
    .bind (wf_goodListProg (by simp) (by simp [hd]) (by simp [hk]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hc]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hd]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hk]) .nil)) fun _ _ =>
    .bind (Coherent.wf_pwTabProg (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx => ?_) fun _ _ => wf_sp_catProg (by simp)
  exact wf_sp_dlProg (hΓ (by simp [hm])) (hΓ (by simp [ht])) (hΓ (by simp [hk]))
    (hΓ (by simp)) (hΓ (by simp [hV])) (hΓ (by simp [hc])) (hΓ (by simp)) (hΓ (by simp [ha]))
    (hΓ (by simp [ho])) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp)) (hΓ (by simp))
    (hΓ (by simp [hD])) hx

theorem wf_sp_daryProg {m₁ t₁ k₁ d₁ : var₁ .nat} {m₂ t₂ k₂ d₂ : var₂ .nat}
    {o₁ : var₁ (.array .nat)} {o₂ : var₂ (.array .nat)} {a₁ : var₁ (.array .bool)}
    {a₂ : var₂ (.array .bool)} {V₁ : var₁ (.list .nat)} {V₂ : var₂ (.list .nat)}
    {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ)
    (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ) (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ)
    (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_daryProg m₁ t₁ k₁ o₁ a₁ V₁ c₁ d₁)
      (sp_daryProg m₂ t₂ k₂ o₂ a₂ V₂ c₂ d₂) := by
  unfold sp_daryProg
  exact .bind (wf_tfDegProg ho ha hk hV hd) fun _ _ =>
    .bind (wf_sOfProg (by simp [hk]) (by simp [hd])) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_arityProg (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx => wf_fOfProg (hΓ (by simp [ho]))
      (hΓ (by simp [ha])) (hΓ (by simp [hk])) (hΓ (by simp [hd])) hx) fun _ _ =>
    .bind (wf_daryArrProg (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    .bind (wf_bigTwinsProg (by simp [hk]) (by simp) (by simp)) fun _ _ =>
    .bind (wf_sp_diffProg (by simp [hV]) (by simp)) fun _ _ =>
    .caseList (by simp)
      (wf_sp_daryDLProg (by simp [hm]) (by simp [ht]) (by simp [hk]) (by simp) (by simp [ho])
        (by simp [ha]) (by simp) (by simp [hc]) (by simp) (by simp))
      fun _ _ _ _ => wf_sp_daryRecProg (by simp [hm]) (by simp [hk]) (by simp [ho])
        (by simp [ha]) (by simp) (by simp [hc]) (by simp) (by simp)

theorem wf_sp_bstepProg {m₁ t₁ : var₁ .nat} {m₂ t₂ : var₂ .nat} {V₁ : var₁ (.list .nat)}
    {V₂ : var₂ (.list .nat)} {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sp_bstepProg m₁ t₁ V₁ c₁ a₁)
      (sp_bstepProg m₂ t₂ V₂ c₂ a₂) := by
  unfold sp_bstepProg
  refine .bind (.prim _ (.cons hc .nil)) fun _ _ =>
    .bind (wf_offsetsProg (by simp [hm]) (by simp)) fun _ _ =>
    .bind (wf_minBigDegProg (by simp [ht]) (by simp) (by simp [ha]) (by simp) (by simp [hV]))
    fun _ _ => .caseOption (by simp) ?_ fun _ _ => ?_
  · exact .bind (wf_twinPartProg (by simp [hm]) (by simp) (by simp [ha]) (by simp [hV]))
      fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (wf_partProg (by simp) (by simp)) fun _ _ => wf_sp_leafPair (by simp)
  refine .bind (wf_johnsonTestProg (by simp) (by simp [ha]) (by simp) (by simp [hV]) (by simp))
    fun _ _ => .ite (by simp) ?_ ?_
  · exact .bind (wf_johnsonLeafProg (by simp [hm]) (by simp) (by simp [ha]) (by simp)
      (by simp [hV]) (by simp)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (wf_johnProg (by simp) (by simp [hc]) (by simp) (by simp)) fun _ _ =>
      wf_sp_leafPair (by simp)
  · exact .bind (wf_sp_isBaseProg (by simp [ht]) (by simp)) fun _ _ => .ite (by simp)
      (wf_sp_baseProg (by simp [hm]) (by simp) (by simp) (by simp [ha]) (by simp [hV]))
      (wf_sp_daryProg (by simp [hm]) (by simp [ht]) (by simp) (by simp) (by simp [ha])
        (by simp [hV]) (by simp [hc]) (by simp))

theorem wf_stepProg {m₁ t₁ : var₁ .nat} {m₂ t₂ : var₂ .nat} {f₁ : var₁ frameTy}
    {f₂ : var₂ frameTy} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hf : ⟨frameTy, f₁, f₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (stepProg m₁ t₁ f₁) (stepProg m₂ t₂ f₂) := by
  unfold stepProg
  refine .bind (.prim _ (.cons hf .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hf]) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_sp_bstepProg (by simp [hm]) (by simp [ht]) (by simp) (by simp) (by simp))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ o₁ o₂ ho => wf_sp_wrapDProg (hΓ (by simp [hm]))
      (hΓ (by simp)) ho) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ c₁ c₂ hc => wf_sp_rewrapProg (hΓ (by simp)) hc)
    fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.SoJTree
