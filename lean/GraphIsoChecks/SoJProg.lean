module

public import GraphIso.SoJProg.Twins
meta import GraphIso.SoJProg.Twins
public import GraphIso.SoJProg.Johnson
meta import GraphIso.SoJProg.Johnson
public import GraphIso.SoJProg.BaseCase
meta import GraphIso.SoJProg.BaseCase
public import GraphIso.SoJProg.Dary
meta import GraphIso.SoJProg.Dary
public import GraphIso.SoJProg.WLSets
meta import GraphIso.SoJProg.WLSets
public import GraphIso.SoJProg.DLTest
meta import GraphIso.SoJProg.DLTest
public import GraphIso.SoJProg.Coherent
meta import GraphIso.SoJProg.Coherent
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14c checks: Split-or-Johnson programs, one level

Interpreter runs of the stage 14c programs (no backend calls), each compared with milestone 11's
model function after decoding by `GraphIso/SoJProg/Data.lean` (each `#eval` throws on a
failure):

* **Twins, degrees and the Johnson test** on the Johnson bipartite graphs `J(5, 2)` (the ten
  pairs of `{0, …, 4}` against the five singletons) and `J(6, 3)`: `tfDeg`, the least big
  degree, `twinPart`, the Johnson test (true) and the Johnson leaf; on `J(5, 2)` with one pair
  removed the test is false.
* **The base case**: the enumerations of three cells against `enums`, and `nbrCode`.
* **The `d`-ary structure**: `Nat.clog` and `arity`; `bigTwins` of the `2`-ary colouring of
  four cells with no hyperedge (all twins) and with one (no large twin class); `pickSide`.
* **Weisfeiler–Leman on sets**: the `2`-ary refinement of a family of three cells with one
  hyperedge against `wlOn`, and `cohOn` on three points and three cells against the program on
  the numbered sum.
* **The Design Lemma test**: the good lists of the `5`-cycle (`d = 2`) against the model's
  filter of `tuplesLt` by `DLGood`; `selThird`.
* **Coherent Split-or-Johnson, one level**, against `cohSoj`: equal trees, the leaves compared
  with their relations on all points and cells, and the shape and the kind of every leaf
  asserted. The configurations are certified coherent by a brute-force test of the
  intersection numbers. Every branch is reached:
  - the primitive branch on the `J(5, 2)` incidence configuration: with `C₂` the five points (a
    clique) every leaf is `none`; with `C₂` the ten pairs (the Petersen configuration) every
    leaf is bipartite;
  - the primitive and the imprimitive branch without a majority colour (partition leaves), and
    `X[C₁]` imprimitive (the partition into components), on the pentagon under `D₅ × C_l`;
  - on `J(6, 2) ⊔ ([6] × {0, 1})`, which satisfies all of Helfgott's hypotheses, the
    imprimitive branch twice: with blocks `{i} × {0, 1}` no block is good and the leaf is the
    contraction (bipartite); with blocks `[6] × {j}` every point gives a bipartite leaf;
  - a constant colouring on `C₁ × C₂` with `X[C₂]` imprimitive (excluded by Helfgott's
    hypotheses): no good block and no other colour, the leaf `none`;
  - a configuration that is not coherent (partition leaves).

  The Petersen, pentagon, constant and non-coherent fixtures run the program in the
  interpreter (each in under ten seconds). On `J(6, 2) ⊔ ([6] × {0, 1})` an interpreter run
  takes minutes, and on it and on the clique fixture the data model `cohSojD` is compared
  instead: `RunsWithin.cohSojProg` proves that the program's result is exactly this data model.
* **The Clebsch graph**: its configuration is coherent; milestone 10's `2`-ary refinement
  keeps its partition; its good lists (only `[]`) equal the model's filter; the bipartite graph
  of its adjacency against `tfDeg`, the least big degree, `twinPart` and the Johnson test
  (false); and one level of `cohSoj` on two copies of it (the primitive branch, sixteen
  bipartite leaves, on the data model).
* **The edges of a `bip` leaf**: the materialized relation `bipRelProg` on the `J(5, 2)`
  incidence configuration against `bipEdge` on every point and five cells, for four colours.
* **Kernel-checked runs**: `C(6, 3) = 20` and `⌈log₂ 9⌉ = 4`.
-/

@[expose] public section

namespace GraphIsoChecks.SoJProg

open GraphIso GraphIso.Cost GraphIso.Coherent GraphIso.SoJProg GraphIso.SplitJohnson

/-- Run a program with no backend calls. -/
def run {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

def check (name : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-! ### Bipartite graphs -/

/-- The `s`-subsets of `{0, …, n - 1}`. -/
def subsets : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, s + 1 => (subsets n s).map (· ++ [n]) ++ subsets n (s + 1)

/-- A bipartite graph on data: points `V₁`, cells `cs`, relation array `a` (`x * |cs| + j`). -/
structure Bip where
  m : ℕ
  V₁ : List ℕ
  cs : List (List ℕ)
  a : Array Bool

/-- The Johnson bipartite graph: the points are the `s`-subsets of `{0, …, n - 1}` (the first
`drop` of them omitted), the cells the singletons placed after them, and a point is related to
the cells of its elements. -/
def johnsonBip (n s : ℕ) (drop : ℕ := 0) : Bip :=
  let pts := subsets n s
  let N := pts.length
  { m := N + n, V₁ := (List.range N).drop drop, cs := (List.range n).map fun j => [N + j],
    a := ((List.range (N + n)).flatMap fun x => (List.range n).map fun j =>
      decide (j ∈ pts.getD x [])).toArray }

def Bip.k (B : Bip) : ℕ := B.cs.length

def withOffs {t : Ty} (B : Bip)
    (f : (Ty.array .nat).denote → Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  run (.bind (offsetsProg B.m B.k) f)

/-- Pointwise equality of colored partitions of `Fin m`. -/
def cpartEq {m : ℕ} (p q : CPart (Fin m)) : Bool :=
  (List.finRange m).all fun x => p.col x == q.col x && decide (p.blk x = q.blk x)

/-- Equality of Johnson embeddings of `Fin m`. -/
def jembEq {m : ℕ} (J J' : JEmb (Fin m)) : Bool :=
  decide (J.V0 = J'.V0) && decide (J.Λ = J'.Λ) && J.s == J'.s &&
    (List.finRange m).all fun x => decide (J.f x = J'.f x)

def tfDegOK (B : Bip) (d : ℕ) : Bool :=
  match withOffs B fun offs => tfDegProg offs B.a B.k B.V₁ d with
  | some l => decide (setOf B.m l = tfDeg (setOf B.m B.V₁) (famOf B.m B.cs) (relOf B.m B.cs B.a) d)
  | none => false

def tfDegCard (B : Bip) (d : ℕ) : ℕ :=
  (tfDeg (setOf B.m B.V₁) (famOf B.m B.cs) (relOf B.m B.cs B.a) d).card

def minBigDegOK (B : Bip) (t : ℕ) (expected : Option ℕ) : Bool :=
  let big := bigDegs t (setOf B.m B.V₁) (famOf B.m B.cs) (relOf B.m B.cs B.a)
  let model : Option ℕ := if h : big.Nonempty then some (big.min' h) else none
  withOffs B (fun offs => minBigDegProg t offs B.a B.k B.V₁) == some model && model == expected

def twinPartOK (B : Bip) : Bool :=
  match run (twinPartProg B.m B.k B.a B.V₁) with
  | some (col, blk) =>
    cpartEq (cpartOf B.m col blk) (twinPart (setOf B.m B.V₁) (famOf B.m B.cs) (relOf B.m B.cs B.a))
  | none => false

def johnsonTestOK (B : Bip) (d₁ : ℕ) (expected : Bool) : Bool :=
  let model := decide ((tfDeg (setOf B.m B.V₁) (famOf B.m B.cs) (relOf B.m B.cs B.a) d₁).card =
    (famOf B.m B.cs).card.choose (sOf (famOf B.m B.cs).card d₁))
  withOffs B (fun offs => johnsonTestProg offs B.a B.k B.V₁ d₁) == some model && model == expected

def johnsonLeafOK (B : Bip) (d₁ : ℕ) : Bool :=
  match withOffs B fun offs => johnsonLeafProg B.m offs B.a B.k B.V₁ d₁ with
  | some (V₁', s, fA) =>
    jembEq (jembOf B.m V₁' B.cs s fA)
      ⟨tfDeg (setOf B.m B.V₁) (famOf B.m B.cs) (relOf B.m B.cs B.a) d₁, famOf B.m B.cs,
        sOf (famOf B.m B.cs).card d₁, fOf (famOf B.m B.cs) (relOf B.m B.cs B.a) d₁⟩
  | none => false

def J52 : Bip := johnsonBip 5 2
def J63 : Bip := johnsonBip 6 3
def J52minus : Bip := johnsonBip 5 2 1

#eval check "J(5,2): tfDeg 2 = all ten pairs, as in the model"
  (tfDegOK J52 2 && tfDegCard J52 2 == 10)
#eval check "J(5,2): the least big degree is 2" (minBigDegOK J52 5 (some 2))
#eval check "J(5,2): twinPart agrees with the model" (twinPartOK J52)
#eval check "J(5,2): the Johnson test is true" (johnsonTestOK J52 2 true)
#eval check "J(5,2): the Johnson leaf agrees with the model" (johnsonLeafOK J52 2)
#eval check "J(6,3): tfDeg 3 = all twenty triples" (tfDegOK J63 3 && tfDegCard J63 3 == 20)
#eval check "J(6,3): the Johnson test is true" (johnsonTestOK J63 3 true)
#eval check "J(6,3): the Johnson leaf agrees with the model" (johnsonLeafOK J63 3)
#eval check "J(5,2) minus a pair: the Johnson test is false" (johnsonTestOK J52minus 2 false)
#eval check "J(5,2) minus a pair: twinPart agrees with the model" (twinPartOK J52minus)

/-! ### The base case -/

/-- Three cells `{3}, {4}, {5}` and points `0, 1, 2` related along the diagonal and one more
edge. -/
def B3 : Bip :=
  { m := 6, V₁ := [0, 1, 2], cs := [[3], [4], [5]],
    a := ((List.range 6).flatMap fun x => (List.range 3).map fun j =>
      decide (x = j ∨ (x = 0 ∧ j = 2))).toArray }

def enumsOK : Bool :=
  match run (enumsProg 3) with
  | some ps => ps.length == 6 &&
      decide ((ps.map (choiceOf B3.m B3.cs)).toFinset = enums (famOf B3.m B3.cs))
  | none => false

def nbrCodeOK (js : List ℕ) : Bool :=
  (List.finRange B3.m).all fun x =>
    withOffs B3 (fun offs => nbrCodeProg offs B3.a js x.val) ==
      some (nbrCode (relOf B3.m B3.cs B3.a) (choiceCells (choiceOf B3.m B3.cs js)) x)

#eval check "base case: six enumerations of three cells, equal to enums" enumsOK
#eval check "base case: nbrCode along [2, 0, 1] and [0, 1, 2]"
  (nbrCodeOK [2, 0, 1] && nbrCodeOK [0, 1, 2])

/-! ### The `d`-ary structure -/

#eval check "clog and arity"
  (([(2, 1), (2, 8), (2, 9), (3, 27), (5, 26), (1, 7)].all fun p =>
      run (clogProg p.1 p.2) == some (Nat.clog p.1 p.2)) &&
    ([(10, 3, 45), (16, 8, 100), (4, 2, 6)].all fun p =>
      run (arityProg p.1 p.2.1 p.2.2) == some (arity p.1 p.2.1 p.2.2)))

/-- Four cells `{4}, …, {7}` over eight points. -/
def cells4 : List (List ℕ) := [[4], [5], [6], [7]]

def bigTwinsOK (hs : List (List ℕ)) (expected : ℕ) : Bool :=
  match run (.bind (daryArrProg 4 2 hs) fun col => bigTwinsProg 4 2 col) with
  | some bt =>
    let model := bigTwins (famOf 8 cells4)
      (daryCol (famOf 8 cells4) (hs.map (cellsOf 8 cells4)).toFinset 2)
    decide (cellsOf 8 cells4 bt = model) && model.card == expected
  | none => false

#eval check "bigTwins: no hyperedge makes all four cells twins" (bigTwinsOK [] 4)
#eval check "bigTwins: one hyperedge leaves no large twin class" (bigTwinsOK [[0, 1]] 0)

/-- Points `0, 1, 2, 3` against the four cells, with relation `x ~ j` iff `j ≤ x`. -/
def aPick : Array Bool :=
  ((List.range 8).flatMap fun x => (List.range 4).map fun j => decide (j ≤ x ∧ x < 4)).toArray

def pickOK (T : List ℕ) : Bool :=
  match run (pickSideProg [0, 1, 2, 3] 4 aPick T) with
  | some r => decide (cellsOf 8 cells4 r =
      pickSide (setOf 8 [0, 1, 2, 3]) (famOf 8 cells4) (cellsOf 8 cells4 T) (relOf 8 cells4 aPick))
  | none => false

#eval check "pickSide on two choices of S" (pickOK [0] && pickOK [0, 1, 2])

/-! ### Weisfeiler–Leman on sets -/

/-- Three cells `{3}, {4}, {5}` over six points. -/
def cells3 : List (List ℕ) := [[3], [4], [5]]

/-- The model refinement is recomputed at every tuple, so the family is kept small. -/
def daryWLOK (hs : List (List ℕ)) : Bool :=
  match run (daryWLProg 3 2 hs) with
  | some (arr, _) =>
    decide (∀ y : Fin 2 → Fin 3, get arr (enc y) =
      wlOn 2 (daryCol (famOf 6 cells3) (hs.map (cellsOf 6 cells3)).toFinset 2)
        (cellSub 6 cells3 ∘ y))
  | none => false

#eval check "the 2-ary refinement of a cell family equals wlOn" (daryWLOK [[0, 1]])

/-- Three points `0, 1, 2` and three cells `{3}, {4}, {5}`: `x ~ j` iff `j ≠ x`. -/
def aSum : Array Bool :=
  ((List.range 6).flatMap fun x => (List.range 3).map fun j => decide (j ≠ x ∧ x < 3)).toArray

def cohOnOK : Bool :=
  let ps := [0, 1, 2]
  let cs := [[3], [4], [5]]
  match run (cohProg ps 3 aSum (Array.replicate 9 0)) with
  | some (arr, _) =>
    let hps : ∀ i ∈ ps, i < 6 := by decide
    decide (∀ i j : Fin 6,
      cohOn (sqSet 6 ps cs) (code (relOf 6 cs aSum) (extCells (famOf 6 cs) fun _ _ => 0))
          (sqAt 6 ps cs hps i).val (sqAt 6 ps cs hps j).val = get arr (enc ![i, j]))
  | none => false

#eval check "cohOn on three points and three cells equals the program" cohOnOK

/-! ### The Design Lemma test -/

/-- The `5`-cycle as a `2`-ary colouring: `0` on the diagonal, `1` on edges, `2` otherwise. -/
def cycCol (i j : ℕ) : ℕ := if i = j then 0 else if (i + 5 - j) % 5 ∈ [1, 4] then 1 else 2

def cyc : Array ℕ := ((List.range 25).map fun t => cycCol (t % 5) (t / 5)).toArray

def goodListOK : Bool :=
  (decide (∀ y : Fin 2 → Fin 5, toFun (k := 2) cyc y = cycCol (y 0) (y 1))) &&
  match run (goodListProg cyc 2 5 3) with
  | some gl => decide (((gl.map (decList (Equiv.refl (Fin 5)))).toFinset) =
      (tuplesLt Finset.univ 2).filter (DLGood (fun y => toFun (k := 2) cyc y) 3))
  | none => false

#eval check "the good lists of the 5-cycle equal the model's filter" goodListOK

def selThirdOK (col : List ℕ) : Bool :=
  let S := List.range col.length
  match run (selThirdProg S col.toArray) with
  | some r => r == selThirdL S (get col.toArray) &&
      decide (((r.map fun i => (⟨i % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9))).toFinset =
        selThird ((S.map fun i => (⟨i % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9))).toFinset
          fun x => get col.toArray x.val)
  | none => false

#eval check "selThird: a large class, and a union of classes"
  (selThirdOK [0, 0, 0, 1, 1, 2, 2, 2, 2] && selThirdOK [0, 0, 1, 1, 2, 2, 3, 3, 4])

/-! ### Coherent Split-or-Johnson, one level -/

/-- Equality of two relations on the points of `Fin m` and the cells of `W₂`. The quantifier
over `W₂` is a `Finset.filter`: `decide (∀ B ∈ W₂, …)` elaborates through
`Fintype.decidableForallFintype` on `Finset (Fin m)` and enumerates all `2 ^ m` sets. -/
def relEq {m : ℕ} (W₂ : Finset (Finset (Fin m))) (A A' : Fin m → Finset (Fin m) → Bool) :
    Bool :=
  (List.finRange m).all fun x => (W₂.filter fun B => A x B != A' x B).card == 0

/-- Equality of leaves of `cohSoj` (relations compared on all points and the listed cells). -/
def leafEq {m : ℕ} : Option (CohOut (Fin m)) → Option (CohOut (Fin m)) → Bool
  | none, none => true
  | some (.part p), some (.part q) => cpartEq p q
  | some (.bip W₁ W₂ A), some (.bip W₁' W₂' A') =>
    decide (W₁ = W₁') && decide (W₂ = W₂') && relEq W₂ A A'
  | _, _ => false

/-- Equality of leaf trees. -/
def leafTreeEq {m : ℕ} : CTree (Fin m) (Option (CohOut (Fin m))) →
    CTree (Fin m) (Option (CohOut (Fin m))) → Bool
  | .leaf o, .leaf o' => leafEq o o'
  | _, _ => false

/-- Equality of trees of depth at most one. -/
def treeEq {m : ℕ} : CTree (Fin m) (Option (CohOut (Fin m))) →
    CTree (Fin m) (Option (CohOut (Fin m))) → Bool
  | .leaf o, .leaf o' => leafEq o o'
  | .node S k, .node S' k' =>
    decide (S = S') && decide (∀ y ∈ S, leafTreeEq (k y) (k' y) = true)
  | _, _ => false

/-- The kind of a leaf: `0` none, `1` a colored partition, `2` a bipartite graph. -/
def kind {m : ℕ} : Option (CohOut (Fin m)) → ℕ
  | none => 0
  | some (.part _) => 1
  | some (.bip _ _ _) => 2

def leafKind {m : ℕ} : CTree (Fin m) (Option (CohOut (Fin m))) → ℕ
  | .leaf o => kind o
  | .node _ _ => 3

/-- The shape of a tree of depth at most one: `none` for a leaf, or the number of options; and
the kinds of the leaves reached. -/
def kinds {m : ℕ} : CTree (Fin m) (Option (CohOut (Fin m))) → Option ℕ × List ℕ
  | .leaf o => (none, [kind o])
  | .node S k =>
    (some S.card, ((List.finRange m).filter (· ∈ S)).map fun y => leafKind (k y))

/-- The result `res` decodes to the model's tree (leaves compared with their relations), and
the model's tree has the given shape and every leaf reached the kind `k`. -/
def resOK (m : ℕ) (c : Array ℕ) (C₁ C₂ : List ℕ) (res : ResD) (shape : Option ℕ) (k : ℕ) :
    Bool :=
  let model := cohSoj (setOf m C₁) (setOf m C₂) (colOf m c)
  treeEq (decodeRes m c res) model && (kinds model).1 == shape &&
    (kinds model).2.all (· == k) && !(kinds model).2.isEmpty

/-- An interpreter run of `cohSojProg`, compared with the model. -/
def cohSojOK (m : ℕ) (c : Array ℕ) (C₁ C₂ : List ℕ) (shape : Option ℕ) (k : ℕ) : Bool :=
  match run (cohSojProg m c C₁ C₂) with
  | some res => resOK m c C₁ C₂ res shape k
  | none => false

/-- The data model `cohSojD`, which `RunsWithin.cohSojProg` proves is the program's result,
compared with the model: for the larger fixtures, where an interpreter run takes minutes (the
data model's components cost `O(|S|⁵)` list operations per colour, the interpreter's more). -/
def cohSojDOK (m : ℕ) (c : Array ℕ) (C₁ C₂ : List ℕ) (shape : Option ℕ) (k : ℕ) : Bool :=
  resOK m c C₁ C₂ (toRes m (cohSojD (fA (offsArr m) c) m C₁ C₂)) shape k

/-- The profile of a pair: the sorted counts `(c x z, c z y)` over `z`, encoded. -/
def profile (m : ℕ) (col : ℕ → ℕ → ℕ) (x y : ℕ) : List ℕ :=
  ((List.range m).map fun z => col x z * 1000 + col z y).mergeSort (· ≤ ·)

/-- A brute-force test of `IsCoherent2` for a colouring with colours below `1000`: pairs of one
colour agree on diagonality, on the colours of the reversed pair and of the two diagonal pairs,
and on all intersection numbers. -/
def coherentB (m : ℕ) (col : ℕ → ℕ → ℕ) : Bool :=
  let pairs := (List.range m).flatMap fun x => (List.range m).map fun y => (x, y)
  pairs.all fun p =>
    match pairs.find? (fun q => col q.1 q.2 == col p.1 p.2) with
    | some q =>
      (p.1 == p.2) == (q.1 == q.2) && col p.2 p.1 == col q.2 q.1 &&
        col p.1 p.1 == col q.1 q.1 && col p.2 p.2 == col q.2 q.2 &&
        profile m col p.1 p.2 == profile m col q.1 q.2
    | none => false

/-- The colouring of `m × m` pairs as an array, row-major. -/
def arrOf (m : ℕ) (col : ℕ → ℕ → ℕ) : Array ℕ :=
  ((List.range (m * m)).map fun t => col (t / m) (t % m)).toArray

/-- The incidence configuration of `J(5, 2)`: pairs `0–9`, points `10–14`. Its restriction to
the pairs is the Petersen configuration. -/
def incCol (u v : ℕ) : ℕ :=
  let p := subsets 5 2
  if u < 10 ∧ v < 10 then
    if u = v then 0 else if ((p.getD u []).filter (· ∈ p.getD v [])).isEmpty then 2 else 1
  else if 10 ≤ u ∧ 10 ≤ v then if u = v then 3 else 4
  else if u < 10 then if v - 10 ∈ p.getD u [] then 5 else 6
  else if u - 10 ∈ p.getD v [] then 7 else 8

def incArr : Array ℕ := arrOf 15 incCol

#eval check "the J(5,2) incidence configuration is coherent" (coherentB 15 incCol)
-- `C₁` the pairs, `C₂` the points: `X[C₂]` is a clique (no colour of degree below `|C₂|/2`).
#eval check "cohSoj, primitive branch, C₂ a clique: five options, every leaf none, equal to \
    the model"
  (cohSojDOK 15 incArr (List.range 10) [10, 11, 12, 13, 14] (some 5) 0)
-- `C₁` the points, `C₂` the pairs (Petersen): at a pair `y` the three points outside `y` are a
-- majority, and the pairs disjoint from `y` have degree `3 < 5`.
#eval check "cohSoj, primitive branch, C₂ Petersen: ten options, every leaf bipartite, the \
    program's run equal to the model"
  (cohSojOK 15 incArr [10, 11, 12, 13, 14] (List.range 10) (some 10) 2)

/-- The materialized relation of a `bip` leaf (`bipRelProg`, an interpreter run) against
`bipEdge`, entry by entry, and its size. -/
def bipRelOK (m : ℕ) (c : Array ℕ) (W₂ : List (List ℕ)) (g : ℕ) : Bool :=
  match run (bipRelProg (offsArr m) c m g W₂) with
  | some a =>
    a.size == m * W₂.length &&
      (List.finRange m).all fun x => (List.range W₂.length).all fun j =>
        a.getD (x.val * W₂.length + j) false == bipEdge (colOf m c) g x (setOf m (W₂.getD j []))
  | none => false

#eval check "bipRelProg on the J(5,2) incidence configuration: equal to bipEdge for four colours"
  ([1, 2, 5, 7].all fun g =>
    bipRelOK 15 incArr [[0, 1, 2], [3, 4], [5, 6, 7, 8, 9], [10, 11, 12], [13, 14]] g)

/-- The pentagon under `D₅ × C_l`: its five edges `{i, i + 1}` (points `0–4`) and its vertices
in `l` layers (vertex `j` of layer `k` is point `5 + l j + k`), coloured by the orbitals: cyclic
distances (with equality of layers), and incidence of an edge and a vertex (incident, near or
opposite). -/
def pentCol (l : ℕ) (u v : ℕ) : ℕ :=
  let dist := fun i j : ℕ => min ((i + 5 - j) % 5) ((j + 5 - i) % 5)
  let inc := fun i j : ℕ =>
    if (j + 5 - i) % 5 ≤ 1 then 0 else if (j + 5 - i) % 5 = 3 then 2 else 1
  if u < 5 ∧ v < 5 then dist u v
  else if 5 ≤ u ∧ 5 ≤ v then
    10 + dist ((u - 5) / l) ((v - 5) / l) + if (u - 5) % l = (v - 5) % l then 0 else 3
  else if u < 5 then 20 + inc u ((v - 5) / l)
  else 30 + inc v ((u - 5) / l)

def pentRange (l : ℕ) : List ℕ := (List.range (5 * l)).map (5 + ·)

#eval check "the pentagon configurations (one and two layers) are coherent"
  (coherentB 10 (pentCol 1) && coherentB 15 (pentCol 2))
-- One layer: at a vertex, two edges are incident, two near and one opposite; no majority.
#eval check "cohSoj, primitive branch, no majority colour: five options, partition leaves, \
    the program's run equal to the model"
  (cohSojOK 10 (arrOf 10 (pentCol 1)) (List.range 5) (pentRange 1) (some 5) 1)
-- Two layers: `X[C₂]` is imprimitive (its least disconnected colour joins the vertices of a
-- layer), and again no colour has a majority at any vertex.
#eval check "cohSoj, imprimitive branch, no majority colour: ten options, partition leaves, \
    the program's run equal to the model"
  (cohSojOK 15 (arrOf 15 (pentCol 2)) (List.range 5) (pentRange 2) (some 10) 1)
-- The roles exchanged: `X[C₁]` is imprimitive and its components are the leaf.
#eval check "cohSoj, X[C₁] imprimitive: the partition into layers, the program's run equal to \
    the model"
  (cohSojOK 15 (arrOf 15 (pentCol 2)) (pentRange 2) (List.range 5) none 1)

/-- A configuration that is not coherent (the colour-`4` pairs `(0, 1)` and `(0, 2)` have
different intersection numbers): `C₂ = {4, 5, 6, 7}` with blocks `{4, 5}`, `{6, 7}`. The
procedure is a function of any colouring, and the program equals the model here too. -/
def impCol (u v : ℕ) : ℕ :=
  if u < 4 ∧ v < 4 then (if u = v then 3 else 4)
  else if 4 ≤ u ∧ 4 ≤ v then (if u = v then 0 else if u / 2 = v / 2 then 1 else 2)
  else if u < 4 then (if (u + v) % 2 = 0 then 5 else 6)
  else (if (u + v) % 2 = 0 then 7 else 8)

def impArr : Array ℕ := arrOf 8 impCol

#eval check "a non-coherent configuration: four options, partition leaves, the program's run \
    equal to the model"
  (!coherentB 8 impCol && cohSojOK 8 impArr [0, 1, 2, 3] [4, 5, 6, 7] (some 4) 1)

/-- A clique `C₁ = {0, 1, 2}` and `C₂ = {3, 4, 5, 6}` with blocks `{3, 4}`, `{5, 6}`, and one
colour on `C₁ × C₂` (the orbitals of `Sym(3) × D₈`): the case excluded by Helfgott's hypothesis
that the colouring is not constant on `C₁ × C₂`. -/
def constCol (u v : ℕ) : ℕ :=
  if u < 3 ∧ v < 3 then (if u = v then 0 else 1)
  else if 3 ≤ u ∧ 3 ≤ v then (if u = v then 2 else if (u - 3) / 2 = (v - 3) / 2 then 3 else 4)
  else if u < 3 then 5 else 6

#eval check "a constant colouring on C₁ × C₂, C₂ imprimitive: no good block and no other \
    colour, the leaf none, the program's run equal to the model"
  (coherentB 7 constCol && cohSojOK 7 (arrOf 7 constCol) [0, 1, 2] [3, 4, 5, 6] none 0)

/-- `J(6, 2) ⊔ ([6] × {0, 1})` under `Sym(6) × C₂`: the 2-subsets of `{0, …, 5}` (points
`0–14`) and the pairs `(i, j)` (point `15 + 2i + j`). On `C₂` the colours are the diagonal,
`partner` (same `i`), `copy` (same `j`) and `other`; between the parts, whether `i` lies in the
2-subset. `X[C₂]` is imprimitive with two disconnected colours, and the numbering of `partner`
and `copy` decides which one is the least. Helfgott's hypotheses hold: `|C₁| = 15 > 12`, the
colouring is not constant on `C₁ × C₂`, and `X[C₂]` is not a clique. -/
def wrCol (partnerFirst : Bool) (u v : ℕ) : ℕ :=
  let set := fun w => (subsets 6 2).getD w []
  if u < 15 ∧ v < 15 then ((set u).filter (· ∈ set v)).length
  else if 15 ≤ u ∧ 15 ≤ v then
    let i := (u - 15) / 2
    let j := (u - 15) % 2
    let k := (v - 15) / 2
    let l := (v - 15) % 2
    if u = v then 20
    else if i = k then (if partnerFirst then 21 else 22)
    else if j = l then (if partnerFirst then 22 else 21)
    else 23
  else if u < 15 then (if (v - 15) / 2 ∈ set u then 30 else 31)
  else (if (u - 15) / 2 ∈ set v then 40 else 41)

#eval check "J(6,2) ⊔ ([6] × {0,1}) is a coherent configuration (both numberings)"
  (coherentB 27 (wrCol true) && coherentB 27 (wrCol false))
-- Blocks `{i} × {0, 1}`: the majority colour at `(i, j)` is `i ∉ x`; both points of the block
-- `{i} × {0, 1}` have the pairs avoiding `i` as neighbours, a twin class of ten of the fifteen
-- pairs, so no block is good and the leaf is the contraction.
#eval check "cohSoj, imprimitive branch with blocks {i} × {0,1}: no good block, the \
    contraction leaf (bipartite), equal to the model"
  (cohSojDOK 27 (arrOf 27 (wrCol true)) (List.range 15) ((List.range 12).map (15 + ·)) none 2)
#eval check "cohSoj, imprimitive branch with blocks [6] × {j}: a node over the 12 points of \
    C₂, every leaf bipartite, equal to the model"
  (cohSojDOK 27 (arrOf 27 (wrCol false)) (List.range 15) ((List.range 12).map (15 + ·))
    (some 12) 2)

/-! ### The Clebsch graph -/

/-- The Clebsch graph: `(ℤ/2)⁴`, two vectors adjacent when they differ in one or in all four
coordinates (the folded 5-cube, strongly regular with parameters `(16, 5, 0, 2)`). -/
def clebschAdj (u v : ℕ) : Bool :=
  let d := ((List.range 4).filter fun i => (u ^^^ v).testBit i).length
  d == 1 || d == 4

/-- Its configuration: `0` on the diagonal, `1` on edges, `2` on non-edges. -/
def clebschCol (u v : ℕ) : ℕ := if u = v then 0 else if clebschAdj u v then 1 else 2

/-- The configuration as a `2`-ary array, `enc ![i, j] = i + 16 j`. -/
def clebschArr : Array ℕ := ((List.range 256).map fun t => clebschCol (t % 16) (t / 16)).toArray

#eval check "the Clebsch configuration is coherent (strongly regular)" (coherentB 16 clebschCol)

/-- Weisfeiler–Leman (milestone 10's program, `k = 2`) leaves the Clebsch configuration's
partition unchanged, as a coherent configuration must; the model `wlOn` recomputes the
refinement at every tuple and is too slow on `16` points, so the program is compared with this
independent consequence of coherence instead. -/
def clebschWLOK : Bool :=
  match run (Coherent.wlProg 2 16 clebschArr) with
  | some (out, _) => (List.range 256).all fun t => (List.range 256).all fun t' =>
      (get out t == get out t') == (get clebschArr t == get clebschArr t')
  | none => false

#eval check "Clebsch: the 2-ary refinement keeps the configuration's partition" clebschWLOK

/-- The good lists of the Clebsch configuration (`d = 2`, `t = 8`) against the model's filter of
`tuplesLt` by `DLGood`: only the empty list (the whole set is one dominant class with a
non-clique 2-skeleton; after individualizing a point the class of non-neighbours has `10 > 8`
points). -/
def clebschGoodOK : Bool :=
  (decide (∀ y : Fin 2 → Fin 16, toFun (k := 2) clebschArr y = clebschCol (y 0) (y 1))) &&
  match run (goodListProg clebschArr 2 16 8) with
  | some gl => gl == [[]] && decide (((gl.map (decList (Equiv.refl (Fin 16)))).toFinset) =
      (tuplesLt Finset.univ 2).filter (DLGood (fun y => toFun (k := 2) clebschArr y) 8))
  | none => false

#eval check "Clebsch: the Design Lemma test equals the model's filter (only [])" clebschGoodOK

/-- The bipartite graph of the Clebsch graph: its sixteen vertices against sixteen singleton
cells, a vertex related to the cells of its neighbours. -/
def clebschBip : Bip :=
  { m := 32, V₁ := List.range 16, cs := (List.range 16).map fun w => [16 + w],
    a := ((List.range 32).flatMap fun x => (List.range 16).map fun w =>
      x < 16 && clebschAdj x w).toArray }

#eval check "Clebsch bipartite graph: no twins, tfDeg 5 = all sixteen vertices, as in the model"
  (tfDegOK clebschBip 5 && tfDegCard clebschBip 5 == 16)
#eval check "Clebsch bipartite graph: the least big degree is 5; twinPart agrees"
  (minBigDegOK clebschBip 8 (some 5) && twinPartOK clebschBip)
#eval check "Clebsch bipartite graph: the Johnson test is false (16 ≠ C(16, 5))"
  (johnsonTestOK clebschBip 5 false)

/-- Two copies of the Clebsch configuration (points `0–15` and `16–31`), coloured by the
orbitals of `2⁴ : Sym(5)` acting on both: within a copy and between the copies, equal, adjacent
or not adjacent. -/
def clebsch2Col (u v : ℕ) : ℕ :=
  if u < 16 ∧ v < 16 then clebschCol u v
  else if 16 ≤ u ∧ 16 ≤ v then 10 + clebschCol (u - 16) (v - 16)
  else if u < 16 then 20 + clebschCol u (v - 16)
  else 30 + clebschCol (u - 16) v

#eval check "two copies of the Clebsch configuration form a coherent configuration"
  (coherentB 32 clebsch2Col)
-- At `y` the ten non-neighbours in `C₁` are a majority, and the five neighbours of `y` in `C₂`
-- have degree `5 < 8`; a non-neighbour `x` has two common neighbours with `y` and is related to
-- the other three neighbours of `y`.
#eval check "Clebsch: cohSoj, primitive branch, sixteen options, every leaf bipartite, equal to \
    the model"
  (cohSojDOK 32 (arrOf 32 clebsch2Col) (List.range 16) ((List.range 16).map (16 + ·)) (some 16)
    2)

/-! ### Kernel-checked runs -/

/-- `C(6, 3) = 20` by the Pascal program, evaluated by the kernel. -/
example : run (chooseProg 6 3) = some 20 := by decide +kernel

/-- `⌈log₂ 9⌉ = 4` by the program, evaluated by the kernel. -/
example : run (clogProg 2 9) = some 4 := by decide +kernel

end GraphIsoChecks.SoJProg
