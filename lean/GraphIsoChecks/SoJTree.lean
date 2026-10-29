module

public import GraphIsoChecks.Sims
meta import GraphIsoChecks.Sims
public import GraphIso.SoJTree.Frame
meta import GraphIso.SoJTree.Frame
public import GraphIso.SoJTree.Worklist
meta import GraphIso.SoJTree.Worklist
public import GraphIso.SoJTree.LeafProg
meta import GraphIso.SoJTree.LeafProg
public import GraphIso.SoJTree.LeafStab
meta import GraphIso.SoJTree.LeafStab
public import GraphIso.SoJTree.Trees
meta import GraphIso.SoJTree.Trees
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14d checks: leaves, frames, trees and leaf stabilizers

Each `#eval` throws on a failure. Leaves are compared after decoding with an explicit equality
(`outEqM`: colours and blocks at every point, Johnson embeddings with `f` at every point), and
multisets of leaves by counting (`msEq`), since `Out` has no decidable equality.

* **Leaf data** (six points): `outEqD` and `outEqProg` against the model's equality on equal
  leaves with different data (reordered, repeated and out-of-range entries; different tags of
  `none`) and on unequal leaves (one colour; `f` outside `V0`; different kinds); `actOutD` and
  `actOutProg` against `σ • decodeOut` for two permutations; `addPieceD`/`addPieceProg` and
  `extendD`/`extendOutProg` against `addPieceOut` and `extendOut`.
* **Frame steps** against the model (`stepD_leafMs`'s multiset equation and `stepD_size`'s
  inequality, computed): step 1 (the twin partition), step 2 (the Johnson leaf of `J(5, 2)`),
  step 0 (the base case, 24 leaves), step 3 with large twin classes (a child with a piece), and
  the Design Lemma node with `d = 1` (no dominant class: a third of the cells). The branch
  taken is asserted by `branch`, a copy of the control flow of `bstepI` and `dlI`.
* **The `cohSoj` level, on data only** (frames on the cycles `C₅ + K₁` and `C₆` and a
  pseudo-random frame, with `t = 1` so that six or seven cells are not a base case, and `d = 2`):
  a `cohSoj` node with partition leaves, a `cohSoj` leaf with the partition into components,
  and a bipartite leaf whose `cohCont` gives a child frame with three pieces. Checked: the
  branch taken, the number of produced leaves and children, the produced leaves are colored
  partitions of the frame's points (by brute force on `Fin m`, without the bound on block
  sizes, which needs Helfgott's hypotheses), the children are valid with fewer cells, and every
  child's step against the model. The step itself and `stepD_size` are not compared with the
  model here: see below.
* **Whole trees**: the worklist on data (`worklistD` of `stepD`) against the model's
  `(bsoj …).leafMs` and count on the five frames above, and from `sojAtD`'s leaves and frames
  against `(soj (colOf m c) t).leafMs` and count on the Petersen configuration (`t = 6`), the
  complete graph `K₅` (every leaf `none`) and two pseudo-random symmetric colourings (frames
  with the extension wrapper, and `none` leaves).
* **The tree programs** (interpreter runs): `bsojProg` equals the worklist on data on the five
  model-checked frames, whose leaves are the model's with the count as length (24 for the base
  case); `sojProg` likewise on the Petersen configuration, `K₅` and the two symmetric
  colourings; `sojAtProg` at three points of the Petersen configuration and four points of a
  symmetric colouring (leaves and frames) against `(sojAt …).leafMs` and the count; `stepProg`
  equals `stepD` on all eight frames and on their children (wrappers of one and three
  pieces); `bsojProg` equals the worklist on data on the three `cohSoj`-level frames (the model
  is too slow there; `RunsWithin.bsojProg` proves the program's value is that data model); and
  every leaf of the `bsojProg` and `sojProg` runs has size at most `outB`
  (`bsojProg_outSize`, `sojProg_outSize`).
* **Direct continuation coverage** (local, not reachability): `dlI` and `contI` on hand-built
  inputs, which need not arise from a valid frame, for every branch of `dlCont` (no dominant
  class; every class of the refinement small, `allSmall`; empty `C₁`; constant rectangle; the
  `cohSoj` level) and of `cohCont` (partition leaf; bipartite leaf with `|W| ≤ t`; bipartite
  recursion, here on a cell merged from two; the failed shrink guard; `none`). Each asserts the
  branch taken, compares an interpreter run of `sp_dlProg` / `sp_contProg` with the data model,
  and compares the decoded items with the model's `dlCont` / `cohCont` (with the guarded
  recursion `recB`, and `shrink`). The `dlCont` fixtures have two cells and `d = 1`, so that
  the model's Weisfeiler–Leman, which recomputes earlier rounds at every evaluation, stays
  within seconds (the `allSmall` one takes about twelve seconds).
* **Leaf orbits and stabilizers**: `orbitD` against brute-force orbits (sizes, distinctness,
  index maps) for the Petersen leaf under `S₅` and `D₅`, a partition under `S₅` and the
  Johnson embedding of the pairs in the points under `S₅`; `leafStabProg` with the
  Schreier–Sims backend: the stabilizer's order (12, 2, 24, 120) equals the brute-force count,
  its generators fix the leaf, and the representatives move the leaf to distinct leaves,
  number `|G| / |stabilizer|` and equal the orbit size; the index bound of macro-step M4 on
  the Petersen configuration (the leaf is reachable, `S₅` and `D₅` preserve the colouring, and
  the orbits 10 and 5 are at most the count 10).

**Model-compared and data-checked.** The leaf data, the five frame steps of steps 0–3 and the
Design Lemma node with `d = 1`, the whole trees, the tree programs on those frames and
configurations, and the leaf orbits and stabilizers are compared with the model or with brute
force; the `cohSoj` level of whole frames only on data, and every continuation branch locally
by the direct fixtures. Through whole valid frames, the `allSmall` branch of `dlCont` is
neither reached nor excluded (see below). The model is too slow at the `cohSoj` level of
whole frames: milestone 11's `wlOn` and `cohOn` recompute Weisfeiler–Leman at every
evaluation, and the model evaluates them thousands of times in a Design Lemma node with
`d ≥ 2` and in the dominant-class branch of `dlCont` (a frame with six cells and `d = 2` did not
finish in five minutes). With `d = 1` the
dominant-class branch is never taken: a good option `x` has no class of more than `t₂` cells
unless `|x| + 2 ≤ d` (`DLGood`).

**Branches of `dlCont` and `cohCont` not reached through whole valid frames, and why.** (All
of them are covered locally by the direct fixtures.) In the dominant-class branch, `C₂`
is one class `Q` of the classical refinement on `V₁' ⊔ V₂` (two classes of more than `2k/3` of
the `k` cells cannot coexist), and that refinement is coherent.

* *Empty `C₁`* and *constant `C₁ × C₂`* are unreachable for `t = 1`. Every point of `V₁'` is
  then related to all of `Q` or to none of it: for the points of `C₁` this is the constancy, and
  a point outside `C₁` is alone in its class, so by coherence every cell of `Q` is related to it
  or none is. So every hyperedge (a neighbourhood, or its complement when `d₁ > k/2`) contains
  `Q` or misses it, and it cannot contain `Q`, having `s ≤ k/2 < |Q|` cells. The cells of `Q`
  are then pairwise twins of the `d`-ary colouring, a twin class of more than `k/2` cells, and
  step 3 takes the large-twins branch instead. For `t ≥ 2` the same counting over a class of at
  most `t` points forces a hyperedge to meet `Q` in at least `|Q|/t` cells, and leaving the base
  case needs `k ≥ 15` (for `t = 2`), so `s ≥ 6` and the arity is `6`: at least `15⁶` tuples,
  beyond these checks.
* The *small-`W`* outcome of `cohCont` is unreachable for `t = 1`: a bipartite leaf of `cohSoj`
  has `W = C₁` or `|W| > |C₁|/2`, and `C₁` contains a class of more than `t` points, so
  `|W| ≥ 2 > t`. For `t ≥ 2` it needs at least 15 cells.
* The *failed guard* of `cohCont` (`3 |V₂''| > 2 |V₂|`) is unreachable for every `t`: the new
  cells number fewer than `|C₂|/2` in the primitive case (the blue colour) and at most `|C₂|/2`
  in the imprimitive cases (the components of a colour of the coherent refinement on `Q` have
  equal sizes and are at least two), so `3 |V₂''| ≤ 3k/2 ≤ 2k`.
* *All classes small* (`allSmall`) was not reached and is not excluded. Since the cells'
  diagonal in the code is the individualized vertex colouring, it needs the classical
  refinement on points and cells to split a class of more than `2k/3` cells that the `d`-ary
  refinement leaves whole. Automorphisms never split a class, so the candidates are graphs of
  hyperedges whose vertex classes are not orbits, such as strongly regular graphs without
  transitive automorphism groups. A data-level step on a frame of the size of the smallest such
  graphs we know (the Latin square graph of the cyclic group of order 5: 25 cells, 150 points)
  did not finish in fifteen minutes.
-/

@[expose] public section

namespace GraphIsoChecks.SoJTree

open Equiv GraphIso GraphIso.Cost GraphIso.SoJTree GraphIso.SoJProg GraphIso.SplitJohnson
  GraphIso.Coherent GraphIso.Sims GraphIsoChecks.Sims

/-- Run a program with no backend calls. -/
def run {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

def check (name : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-! ### Equality of decoded leaves, and of multisets of leaves -/

/-- Equality of colored partitions of `Fin m`, at every point. -/
def cpartEq {m : ℕ} (p q : CPart (Fin m)) : Bool :=
  (List.finRange m).all fun x => p.col x == q.col x && decide (p.blk x = q.blk x)

/-- Equality of Johnson embeddings of `Fin m`, with `f` at every point. -/
def jembEq {m : ℕ} (J J' : JEmb (Fin m)) : Bool :=
  decide (J.V0 = J'.V0) && decide (J.Λ = J'.Λ) && J.s == J'.s &&
    (List.finRange m).all fun x => decide (J.f x = J'.f x)

/-- Equality of decoded leaves. -/
def outEqM {m : ℕ} : Option (Out (Fin m)) → Option (Out (Fin m)) → Bool
  | none, none => true
  | some (.inl p), some (.inl q) => cpartEq p q
  | some (.inr J), some (.inr J') => jembEq J J'
  | _, _ => false

/-- Equality of multisets of leaves: equal cardinalities, and every leaf of `M` occurs as
often in `M` as in `M'`. -/
def msEq {m : ℕ} (M M' : Multiset (Option (Out (Fin m)))) : Bool :=
  Multiset.card M == Multiset.card M' &&
    decide (∀ x ∈ M, Multiset.countP (fun y => outEqM x y = true) M =
      Multiset.countP (fun y => outEqM x y = true) M')

/-- The kind of a leaf: `0` none, `1` a colored partition, `2` a Johnson embedding. -/
def kindOf {m : ℕ} : Option (Out (Fin m)) → ℕ
  | none => 0
  | some (.inl _) => 1
  | some (.inr _) => 2

/-- The numbers of leaves of each kind in a multiset: `(none, colored partitions, Johnson)`. -/
def kindsMs {m : ℕ} (M : Multiset (Option (Out (Fin m)))) : ℕ × ℕ × ℕ :=
  (Multiset.countP (fun o => kindOf o = 0) M, Multiset.countP (fun o => kindOf o = 1) M,
    Multiset.countP (fun o => kindOf o = 2) M)

/-! ### Frames -/

/-- The branch taken by one level of `bsoj` on data (a copy of the control flow of `bstepI`
and `dlI`), for asserting which branches the checks reach. -/
def contTag (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ : List ℕ) (f : ℕ → ℕ → ℕ) :
    Option SoJProg.LeafD → String
  | none => "none"
  | some (tag, _, (W₁, W₂, g)) =>
    if tag = 0 then "part"
    else
      let W := (List.range m).filter fun y => y ∈ W₁
      if W.length ≤ t then "bipSmall"
      else match contI m t k cs D₁ D₂ C₁ f (some (tag, (#[], #[]), (W₁, W₂, g))) with
        | .inl _ => "bipNone"
        | .inr _ => "bipRec"

def cohTag (m t k : ℕ) (cs : List (List ℕ)) (D₁ D₂ C₁ C₂ : List ℕ) (f : ℕ → ℕ → ℕ) :
    String :=
  match cohSojD f (m + k) C₁ (C₂.map (m + ·)) with
  | .leaf o => "cohLeaf:" ++ contTag m t k cs D₁ D₂ C₁ f o
  | .node opts kk =>
    s!"cohNode{opts.length}:" ++
      ",".intercalate (opts.map fun y => contTag m t k cs D₁ D₂ C₁ f (kk y))

def dlTag (m t : ℕ) (V₁ V₁' : List ℕ) (cs : List (List ℕ)) (a : Array Bool) (d : ℕ)
    (wl : Array ℕ) (xd : List ℕ) : String :=
  let k := cs.length
  let t₂ := 2 * k / 3
  let col1 := col1A wl (pwTab d k) d k xd.length xd.toArray
  match domA col1 t₂ with
  | none => "noDom"
  | some _ =>
    let W2 := (wlA 2 (V₁'.length + k) (sqCodeArr V₁' k a (skelArrD wl d k xd))).1
    let f := fA (offsArr (m + k)) (cQArr m V₁' k W2)
    let col₂ := ((List.range k).map fun j => f (m + j) (m + j)).toArray
    if allSmallL (List.range k) (get col₂) t₂ then "allSmall"
    else
      let C₂ := bigL (List.range k) (get col₂) t₂
      let colP := ((List.range m).map fun y => f y y).toArray
      let C₁ := bigL V₁' (get colP) t
      if C₁ = [] then "C1empty"
      else if constRectL C₁ C₂ (get2 (rectArr m k f)) then "constRect"
      else cohTag m t k cs (diffD V₁ V₁') (diffD V₁' C₁) C₁ C₂ f

def branch (m t : ℕ) (fr : FrameD) : String :=
  let V₁ := fr.V₁
  let cs := fr.cs
  let a := fr.a
  let k := cs.length
  match optMin (bigDegsD t V₁ k a) with
  | none => "twins"
  | some d₁ =>
    let V₁' := tfDegD V₁ k a d₁
    let s := sOf k d₁
    if V₁'.length = k.choose s then "johnson"
    else if IsBase t k then "base"
    else
      let d := arity k s V₁'.length
      let col := daryArr k d (V₁'.map (fOfD k a d₁))
      let S := bigTwinsD k d col
      if S ≠ [] then "bigTwins"
      else
        let wl := (wlA d k col).1
        let xs := goodList wl d k (2 * k / 3)
        s!"dl{xs.length}[" ++ ";".intercalate (xs.map (dlTag m t V₁ V₁' cs a d wl)) ++ "]"

/-- A frame of points `0, …, p - 1` and singleton cells `[p], …, [p + v - 1]`, with the
relation given by a function on all points. -/
def frameOf (p v : ℕ) (rel : ℕ → ℕ → Bool) : ℕ × FrameD :=
  (p + v, (List.range p, (List.range v).map (fun j => [p + j]),
    ((List.range (p + v)).flatMap fun x => (List.range v).map fun j => rel x j).toArray, []))

/-- The `s`-subsets of `{0, …, n - 1}`. -/
def subsets : ℕ → ℕ → List (List ℕ)
  | _, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, s + 1 => (subsets n s).map (· ++ [n]) ++ subsets n (s + 1)

/-- A linear congruential generator. -/
def lcg (s : ℕ) : ℕ := (s * 1103515245 + 12345) % 2147483648

/-- `n` pseudo-random bits, each `true` with probability `pct %`. -/
def randBits (seed n pct : ℕ) : List Bool :=
  ((List.range n).foldl (fun (acc : ℕ × List Bool) _ =>
    let s := lcg acc.1; (s, decide ((s / 65536) % 100 < pct) :: acc.2)) (seed, [])).2

/-- A pseudo-random frame on `p` points and `v` singleton cells. -/
def randFrame (p v seed pct : ℕ) : ℕ × FrameD :=
  let bits := (randBits seed ((p + v) * v) pct).toArray
  frameOf p v fun x j => bits.getD (x * v + j) false

/-- The Johnson frame: the `s`-subsets of `{0, …, n - 1}` (the first `drop` omitted) against
the `n` singletons. -/
def johnsonFrame (n s : ℕ) (drop : ℕ := 0) : ℕ × FrameD :=
  let pts := (subsets n s).drop drop
  frameOf pts.length n fun x j => decide (j ∈ pts.getD x [])

/-- The frame of a graph `H` on `v` cells: its edges as points, related to their ends. -/
def graphFrame (v : ℕ) (es : List (ℕ × ℕ)) : ℕ × FrameD :=
  frameOf es.length v fun x j => decide ((es.getD x (0, 0)).1 = j ∨ (es.getD x (0, 0)).2 = j)

/-- **One step of a frame against the model**: the frame tree's leaves are the produced leaves
plus the children's leaves, and the work, the produced leaves and the children's sizes fit in
the frame tree's size. -/
def stepOK (m t : ℕ) (fr : FrameD) : Bool :=
  let r := stepD m t fr
  let T := fr.tree m t
  msEq T.leafMs
      ((r.1.map (decodeOut m) : Multiset _) + (r.2.map fun ch => (ch.tree m t).leafMs).sum)
    && decide (stepWork m t fr + r.1.length + (r.2.map fun ch => (ch.tree m t).size).sum ≤ T.size)

/-- **A whole tree on data against the model**: the worklist from one frame (with no wrapper)
enumerates exactly the leaves of `bsoj`, as a multiset, and their number is the count. -/
def bsojOK (m t : ℕ) (fr : FrameD) : Bool :=
  let out := worklistD (stepD m t) (fun fr => fr.cs.length) (fun _ => 100000) [fr] []
  let T := bsoj t (setOf m fr.V₁) (famOf m fr.cs) (relOf m fr.cs fr.a)
  msEq (out.map (decodeOut m) : Multiset _) T.leafMs && out.length == T.count

/-- **Split-or-Johnson on data against the model**: the leaves of `sojAtD` at every point,
and the worklist from its frames, enumerate exactly the leaves of `soj`, with the count. -/
def sojOK (m t : ℕ) (c : Array ℕ) : Bool :=
  let items := (List.range m).map (sojAtD m t c)
  let out := worklistD (stepD m t) (fun fr => fr.cs.length) (fun _ => 100000)
    (items.filterMap Sum.getRight?) (items.filterMap Sum.getLeft?)
  let T := soj (colOf m c) t
  msEq (out.map (decodeOut m) : Multiset _) T.leafMs && out.length == T.count

/-- The child frames of a step are valid and have fewer cells (on data). -/
def childrenOK (m t : ℕ) (fr : FrameD) : Bool :=
  (stepD m t fr).2.all fun ch =>
    decide (ch.cs.length < fr.cs.length) && decide ch.V₁.Nodup && ch.V₁.all (· < m) &&
      decide ((ch.cs.map (setOf m)).Nodup)

/-- `n × n` colourings from functions. -/
def arrOf (n : ℕ) (col : ℕ → ℕ → ℕ) : Array ℕ :=
  ((List.range (n * n)).map fun u => col (u / n) (u % n)).toArray

/-- A pseudo-random symmetric colouring with `q` colours off the diagonal (`0` on it). -/
def randCol (n q seed : ℕ) : Array ℕ :=
  let bits := ((List.range (n * n)).foldl (fun (acc : ℕ × List ℕ) _ =>
    let s := lcg acc.1; (s, (s / 65536) % q :: acc.2)) (seed, [])).2.toArray
  arrOf n fun x y => if x = y then 0 else 1 + bits.getD (min x y * n + max x y) 0

/-! ### Leaf data -/

/-- A colored partition of six points. -/
def pA : OutD := partD #[0, 0, 1, 1, 2, 2] #[[0, 1], [0, 1], [2, 3], [2, 3], [4, 5], [4, 5]]

/-- The same partition, with an extra colour entry, repeated and out-of-range block entries
and reordered blocks. -/
def pA' : OutD :=
  partD #[0, 0, 1, 1, 2, 2, 9] #[[1, 0, 0], [0, 1, 7], [3, 2], [2, 3], [5, 4], [4, 5]]

/-- `pA` with another colour at point `5`. -/
def pB : OutD := partD #[0, 0, 1, 1, 2, 3] #[[0, 1], [0, 1], [2, 3], [2, 3], [4, 5], [4, 5]]

/-- A Johnson embedding with `V0 = {0, 1, 2}`, the cells `{3}, {4}, {5}` and `s = 1`. -/
def jA : OutD := johnD [0, 1, 2] [[3], [4], [5]] 1 #[[0], [1], [2], [], [], []]

/-- The same embedding, with reordered cells and indices and a repeated point. -/
def jA' : OutD := johnD [2, 0, 1, 1] [[5], [3], [4]] 1 #[[1], [2], [0], [], [], []]

/-- `jA` with another value of `f` at the point `4`, outside `V0`. -/
def jB : OutD := johnD [0, 1, 2] [[3], [4], [5]] 1 #[[0], [1], [2], [], [0], []]

/-- Leaves `none` with different tags. -/
def nA : OutD := noneD
def nA' : OutD := (7, (#[1], #[]), ([], ([], (0, #[]))))

/-- `outEqD` and `outEqProg` against the model's equality, and the expected answer. -/
def eqOK (o o' : OutD) (expected : Bool) : Bool :=
  outEqD 6 o o' == expected && outEqM (decodeOut 6 o) (decodeOut 6 o') == expected &&
    run (outEqProg 6 o o') == some expected

#eval check "outEqD/outEqProg: equal leaves with different data (partition, Johnson, none)"
  (eqOK pA pA' true && eqOK jA jA' true && eqOK nA nA' true && eqOK pA pA true)
#eval check "outEqD/outEqProg: unequal leaves (a colour; f outside V0; different kinds)"
  (eqOK pA pB false && eqOK jA jB false && eqOK pA jA false && eqOK pA nA false &&
    eqOK jA nA false && eqOK nA pB false)

def leaves6 : List OutD := [pA, pA', pB, jA, jA', jB, nA, nA']

def perms6 : List PermData := [ofCycles 6 [[0, 1, 2], [3, 4]], ofCycles 6 [[0, 5], [1, 4, 2]]]

#eval check "actOutD/actOutProg: the action of two permutations equals σ • decodeOut"
  (perms6.all fun σ => leaves6.all fun o =>
    outEqM (decodeOut 6 (actOutD 6 σ o)) (PermData.denote 6 σ • decodeOut 6 o) &&
      run (actOutProg 6 σ o) == some (actOutD 6 σ o))

#eval check "addPieceD/addPieceProg against addPieceOut"
  (leaves6.all fun o =>
    outEqM (decodeOut 6 (addPieceD 6 [1, 4] o)) (addPieceOut (setOf 6 [1, 4]) (decodeOut 6 o)) &&
      run (addPieceProg 6 [1, 4] o) == some (addPieceD 6 [1, 4] o))

def row6 : Array ℕ := #[5, 5, 6, 6, 7, 8]

#eval check "extendD/extendOutProg against extendOut"
  (leaves6.all fun o =>
    outEqM (decodeOut 6 (extendD 6 [0, 1, 2, 3] (get row6) o))
        (extendOut (setOf 6 [0, 1, 2, 3]) (fun y => get row6 y.val) (decodeOut 6 o)) &&
      run (extendOutProg 6 [0, 1, 2, 3] row6 o) == some (extendD 6 [0, 1, 2, 3] (get row6) o))

/-! ### Frame steps -/

def fTwins : ℕ × FrameD := johnsonFrame 5 2
def fBase : ℕ × FrameD := johnsonFrame 4 2 1
def fBigTwins : ℕ × FrameD := randFrame 9 6 69 60
def fNoDom : ℕ × FrameD := randFrame 8 6 38 30
def fCohNode : ℕ × FrameD := graphFrame 6 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
def fCohLeaf : ℕ × FrameD := graphFrame 6 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)]
def fCohBip : ℕ × FrameD := randFrame 8 7 277 35

#eval check "stepD, step 1: the twin partition (J(5,2), t = 20), equal to the model"
  (branch fTwins.1 20 fTwins.2 == "twins" && stepOK fTwins.1 20 fTwins.2)
#eval check "stepD, step 2: the Johnson leaf (J(5,2), t = 6), equal to the model"
  (branch fTwins.1 6 fTwins.2 == "johnson" && stepOK fTwins.1 6 fTwins.2)
#eval check "stepD, step 0: the base case (J(4,2) minus a pair, t = 3, 24 leaves), equal to the \
    model"
  (branch fBase.1 3 fBase.2 == "base" && (stepD fBase.1 3 fBase.2).1.length == 24 &&
    stepOK fBase.1 3 fBase.2)
#eval check "stepD, step 3: large twin classes, one child frame with a piece, equal to the model"
  (branch fBigTwins.1 1 fBigTwins.2 == "bigTwins" &&
    (stepD fBigTwins.1 1 fBigTwins.2).2.length == 1 && stepOK fBigTwins.1 1 fBigTwins.2)
#eval check "stepD, the Design Lemma node (d = 1): no dominant class, a third of the cells, \
    equal to the model"
  (branch fNoDom.1 1 fNoDom.2 == "dl1[noDom]" && stepOK fNoDom.1 1 fNoDom.2)

/-- A colored partition of `V` (brute force, without the bound on block sizes): every point of
`V` lies in its block, blocks lie in `V` and are constant along themselves, colours are constant
on blocks, points of one colour have blocks of one size, and a singleton block has a colour of
its own. -/
def colPartB {m : ℕ} (V : List ℕ) (p : CPart (Fin m)) : Bool :=
  let pts := (List.finRange m).filter fun v => v.val ∈ V
  pts.all fun v =>
    decide (v ∈ p.blk v) &&
      (List.finRange m).all (fun w => !decide (w ∈ p.blk v) || decide (w.val ∈ V)) &&
      pts.all fun w =>
        (!decide (w ∈ p.blk v) || (decide (p.blk w = p.blk v) && p.col w == p.col v)) &&
        (p.col v != p.col w || (p.blk v).card == (p.blk w).card) &&
        ((p.blk v).card != 1 || p.col w != p.col v || w == v)

/-- Every produced leaf is a colored partition of the frame's points. -/
def leavesPartOK (mf : ℕ × FrameD) : Bool :=
  (stepD mf.1 1 mf.2).1.all fun o =>
    match decodeOut mf.1 o with
    | some (.inl p) => colPartB mf.2.V₁ p
    | _ => false

/-- The `cohSoj` level on data, where the model is too slow: the branch, the produced leaves
(colored partitions of the frame's points) and children (valid, with fewer cells), and every
child step against the model. -/
def cohLevelOK (mf : ℕ × FrameD) (tag : String) (leaves children : ℕ) : Bool :=
  let r := stepD mf.1 1 mf.2
  branch mf.1 1 mf.2 == tag && r.1.length == leaves && r.2.length == children &&
    leavesPartOK mf && childrenOK mf.1 1 mf.2 && r.2.all fun ch => stepOK mf.1 1 ch

#eval check "dlCont, the cohSoj node (C₅ + K₁): five partition leaves, every child step equal to \
    the model"
  (cohLevelOK fCohNode "dl6[cohNode5:part,part,part,part,part;noDom;noDom;noDom;noDom;noDom]" 5 5)
#eval check "dlCont, a cohSoj leaf (C₆): the partition into components, every child step equal \
    to the model"
  (cohLevelOK fCohLeaf "dl7[cohLeaf:part;noDom;noDom;noDom;noDom;noDom;noDom]" 1 6)
#eval check "cohCont, a bipartite cohSoj leaf: a child frame with three pieces, every child step \
    equal to the model"
  (cohLevelOK fCohBip "dl7[cohLeaf:bipRec;noDom;noDom;noDom;noDom;noDom;noDom]" 0 7 &&
    (stepD fCohBip.1 1 fCohBip.2).2.any fun ch => ch.wr.length == 3)

/-! ### Whole trees -/

#eval check "bsoj on data (worklist) equals the model's leaves and count: twins, Johnson, base \
    case, large twins, the Design Lemma"
  (bsojOK fTwins.1 20 fTwins.2 && bsojOK fTwins.1 6 fTwins.2 && bsojOK fBase.1 3 fBase.2 &&
    bsojOK fBigTwins.1 1 fBigTwins.2 && bsojOK fNoDom.1 1 fNoDom.2)

/-- The ten pairs `{a, b}`, `a < b`, of `{0, …, 4}`. -/
def pairs5 : List (ℕ × ℕ) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (a < ·)).map fun b => (a, b)

/-- The orbital colouring of the Petersen graph on the pairs: `0` equal, `1` disjoint,
`2` meeting. -/
def petCol (u v : ℕ) : ℕ :=
  let p := pairs5.getD u (0, 0)
  let q := pairs5.getD v (0, 0)
  if u = v then 0 else if p.1 != q.1 && p.1 != q.2 && p.2 != q.1 && p.2 != q.2 then 1 else 2

def petArr : Array ℕ := arrOf 10 petCol

#eval check "soj on data equals the model: the Petersen configuration (t = 6, ten leaves)"
  (sojOK 10 6 petArr && (soj (colOf 10 petArr) 6).count == 10)
#eval check "soj on data equals the model: the complete graph K₅ (t = 3, every leaf none)"
  (sojOK 5 3 (arrOf 5 fun x y => if x = y then 0 else 1) &&
    kindsMs (soj (colOf 5 (arrOf 5 fun x y => if x = y then 0 else 1)) 3).leafMs == (5, 0, 0))
#eval check "soj on data equals the model: two symmetric colourings with frames (extensions) \
    and none leaves"
  (sojOK 8 5 (randCol 8 2 1) && sojOK 9 5 (randCol 9 2 7))

/-! ### Leaf orbits and stabilizers -/

/-- Run a program with the Schreier–Sims backend substituted. -/
def runSS {t : Ty} (p : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 100000000 (p.subst ssImpl)).map Prod.fst

/-- The index of a pair. -/
def pairIdx (a b : ℕ) : ℕ := pairs5.idxOf (min a b, max a b)

/-- A permutation `σ` of `{0, …, 4}` acting on the pairs (positions `0–9`) and, if `pts`, on
the points (positions `10–14`). -/
def onPairs (pts : Bool) (σ : PermData) : PermData :=
  let fp := pairs5.map fun p => pairIdx (get σ.1 p.1) (get σ.1 p.2)
  let ip := pairs5.map fun p => pairIdx (get σ.2 p.1) (get σ.2 p.2)
  if pts then
    ((fp ++ (List.range 5).map fun a => 10 + get σ.1 a).toArray,
      (ip ++ (List.range 5).map fun a => 10 + get σ.2 a).toArray)
  else (fp.toArray, ip.toArray)

/-- The product `g h` (first `h`) of permutations of `{0, …, n - 1}`. -/
def compose (n : ℕ) (g h : PermData) : PermData :=
  (((List.range n).map fun i => get g.1 (get h.1 i)).toArray,
    ((List.range n).map fun i => get h.2 (get g.2 i)).toArray)

/-- One round of the closure: multiply every element by every generator. -/
def closeStep (n : ℕ) (gs : GensData) (acc : List PermData) : List PermData :=
  acc.foldl (fun acc g => gs.foldl (fun acc s =>
    let h := compose n s g
    if acc.any (·.1 == h.1) then acc else acc ++ [h]) acc) acc

/-- The elements of `⟨gs⟩ ≤ Sym(n)`, by `r` rounds of closure. -/
def elems (n r : ℕ) (gs : GensData) : List PermData :=
  Nat.iterate (closeStep n gs) r [(Array.range n, Array.range n)]

def sym5 : GensData := symGens 5
def dih5 : GensData := [cycleOf 5, ofCycles 5 [[1, 4], [2, 3]]]

/-- `S₅` and `D₅` on the ten pairs, and `S₅` on the pairs and the points, by brute force. -/
def sym5Pairs : List PermData := (elems 5 20 sym5).map (onPairs false)
def dih5Pairs : List PermData := (elems 5 20 dih5).map (onPairs false)
def sym5Both : List PermData := (elems 5 20 sym5).map (onPairs true)

/-- The leaves of `xs` up to equality of decoded leaves. -/
def distinctLeaves (k : ℕ) (xs : List OutD) : List OutD :=
  xs.foldl (fun acc o => if acc.any (outEqD k o) then acc else acc ++ [o]) []

/-- The leaf of `sojAt` at the pair `0` on the Petersen configuration (`t = 6`): the colored
partition of the row. -/
def petLeaf : OutD :=
  match sojAtD 10 6 petArr 0 with
  | .inl o => o
  | .inr _ => noneD

/-- A colored partition of the pairs: whether a pair contains the point `0`. -/
def zeroLeaf : OutD :=
  let col := (List.range 10).map fun x => if (pairs5.getD x (0, 0)).1 = 0 then 1 else 0
  partD col.toArray ((List.range 10).map fun x =>
    (List.range 10).filter fun y => col.getD y 0 == col.getD x 0).toArray

/-- The Johnson embedding of the pairs (positions `0–9`) in the points (`10–14`). -/
def johnLeaf : OutD :=
  johnD (List.range 10) ((List.range 5).map fun j => [10 + j]) 2
    ((List.range 15).map fun x =>
      if x < 10 then [(pairs5.getD x (0, 0)).1, (pairs5.getD x (0, 0)).2] else []).toArray

/-- **The orbit closure against brute force**: the orbit of `o₀` under the generators `gd`
(degree `k`) has the size of the brute-force orbit under the group's elements `G`, its leaves
are distinct and contain every image, and the index maps are correct. -/
def orbitOK (k : ℕ) (gd : GensData) (G : List PermData) (o₀ : OutD) : Bool :=
  let (orb, imgs) := orbitD (τ := outTy) (actOutD k) (outEqD k) k gd o₀
  let brute := distinctLeaves k (G.map fun g => actOutD k g o₀)
  orb.length == brute.length && (distinctLeaves k orb).length == orb.length &&
    brute.all (fun o => orb.any (outEqD k o)) && imgs.length == gd.length &&
    (List.range gd.length).all fun i => (List.range orb.length).all fun j =>
      outEqD k (orb.getD ((imgs.getD i []).getD j 0) noneD)
        (actOutD k (gd.getD i (#[], #[])) (orb.getD j noneD))

#eval check "orbitD against brute force: the Petersen leaf under S₅ (10) and D₅ (5), a partition \
    under S₅ (5), the Johnson embedding under S₅ (1)"
  (orbitOK 10 (sym5.map (onPairs false)) sym5Pairs petLeaf &&
    orbitOK 10 (dih5.map (onPairs false)) dih5Pairs petLeaf &&
    orbitOK 10 (sym5.map (onPairs false)) sym5Pairs zeroLeaf &&
    orbitOK 15 (sym5.map (onPairs true)) sym5Both johnLeaf &&
    (orbitD (τ := outTy) (actOutD 10) (outEqD 10) 10 (sym5.map (onPairs false)) petLeaf).1.length
      == 10)

/-- **The leaf stabilizer against brute force** (Schreier–Sims backend, degree `N`, all
positions forming the configuration): the result group's order is the number of elements
fixing the leaf, its generators fix the leaf, the representatives move the leaf to distinct
leaves, and there are `|G| / |stabilizer|` of them. -/
def leafStabOK (N : ℕ) (gs : GensData) (G : List PermData) (o₀ : OutD) : Bool :=
  match runSS (leafStabProg N N (Array.range N) (List.range N) gs o₀) with
  | none => false
  | some (H, reps) =>
    let stab := (G.filter fun g => outEqD N (actOutD N g o₀) o₀).length
    order N (build N (Array.range N) H.2.1).1 == stab &&
      H.2.1.all (fun g => outEqD N (actOutD N g o₀) o₀) &&
      (distinctLeaves N (reps.map fun r => actOutD N r o₀)).length == reps.length &&
      reps.length * stab == G.length &&
      reps.length == leafR N (Array.range N) (List.range N) gs o₀

#eval check "leafStabProg: the Petersen leaf under S₅ (stabilizer of order 12, 10 coset \
    representatives) and under D₅ (order 2, 5 representatives)"
  (leafStabOK 10 (sym5.map (onPairs false)) sym5Pairs petLeaf &&
    leafStabOK 10 (dih5.map (onPairs false)) dih5Pairs petLeaf &&
    sym5Pairs.length == 120 && dih5Pairs.length == 10 &&
    (sym5Pairs.filter fun g => outEqD 10 (actOutD 10 g petLeaf) petLeaf).length == 12 &&
    (dih5Pairs.filter fun g => outEqD 10 (actOutD 10 g petLeaf) petLeaf).length == 2)
#eval check "leafStabProg: a partition under S₅ (order 24, 5 representatives), the Johnson \
    embedding under S₅ on pairs and points (order 120, one representative)"
  (leafStabOK 10 (sym5.map (onPairs false)) sym5Pairs zeroLeaf &&
    leafStabOK 15 (sym5.map (onPairs true)) sym5Both johnLeaf &&
    sym5Both.length == 120 &&
    (sym5Pairs.filter fun g => outEqD 10 (actOutD 10 g zeroLeaf) zeroLeaf).length == 24 &&
    (sym5Both.filter fun g => outEqD 15 (actOutD 15 g johnLeaf) johnLeaf).length == 120)

/-- **The index bound of macro-step M4**: the leaf is a reachable leaf of `soj` on the
configuration (which `S₅` and `D₅` preserve), and its orbit is at most the count. -/
def indexOK (gs : GensData) (G : List PermData) : Bool :=
  let T := soj (colOf 10 petArr) 6
  G.all (fun g => (List.range 10).all fun u => (List.range 10).all fun v =>
      petCol (get g.1 u) (get g.1 v) == petCol u v) &&
    decide (0 < Multiset.countP (fun o => outEqM (decodeOut 10 petLeaf) o = true) T.leafMs) &&
    decide (leafR 10 (Array.range 10) (List.range 10) gs petLeaf ≤ T.count)

#eval check "the index bound: the Petersen leaf is reachable, S₅ and D₅ preserve the \
    configuration, and the orbits (10 and 5) are at most the count (10)"
  (indexOK (sym5.map (onPairs false)) sym5Pairs && indexOK (dih5.map (onPairs false)) dih5Pairs &&
    leafR 10 (Array.range 10) (List.range 10) (sym5.map (onPairs false)) petLeaf == 10 &&
    leafR 10 (Array.range 10) (List.range 10) (dih5.map (onPairs false)) petLeaf == 5 &&
    (soj (colOf 10 petArr) 6).count == 10)

/-! ### The tree programs -/

/-- The worklist on data from a stack and outputs (fuel to spare). -/
def wlD (m t : ℕ) (stack : List FrameD) (out : List OutD) : List OutD :=
  worklistD (stepD m t) (fun fr => fr.cs.length) (fun _ => 100000) stack out

/-- **`bsojProg` against the model**: an interpreter run equals the worklist on data, whose
leaves decode to the model's `(bsoj …).leafMs` with the count as length. -/
def bsojProgOK (m t : ℕ) (fr : FrameD) : Bool :=
  let out := wlD m t [fr] []
  let T := bsoj t (setOf m fr.V₁) (famOf m fr.cs) (relOf m fr.cs fr.a)
  run (bsojProg m t fr.V₁ fr.cs fr.a) == some out &&
    msEq (out.map (decodeOut m) : Multiset _) T.leafMs && out.length == T.count

/-- **`sojProg` against the model**: an interpreter run equals the worklist on data from
`sojAtD`'s leaves and frames, whose leaves decode to `(soj …).leafMs` with the count as
length. -/
def sojProgOK (m t : ℕ) (c : Array ℕ) : Bool :=
  let items := (List.range m).map (sojAtD m t c)
  let out := wlD m t (items.filterMap Sum.getRight?) (items.filterMap Sum.getLeft?)
  let T := soj (colOf m c) t
  run (sojProg m t c) == some out &&
    msEq (out.map (decodeOut m) : Multiset _) T.leafMs && out.length == T.count

/-- `stepProg` equals `stepD` on a frame and on its children. -/
def stepProgOK (m t : ℕ) (fr : FrameD) : Bool :=
  run (stepProg m t fr) == some (stepD m t fr) &&
    (stepD m t fr).2.all fun ch => run (stepProg m t ch) == some (stepD m t ch)

#eval check "bsojProg (interpreter) equals the worklist on data, the model's leaves and the \
    count: twins, Johnson, base case (24 leaves), large twins, the Design Lemma (d = 1)"
  (bsojProgOK fTwins.1 20 fTwins.2 && bsojProgOK fTwins.1 6 fTwins.2 &&
    bsojProgOK fBase.1 3 fBase.2 && bsojProgOK fBigTwins.1 1 fBigTwins.2 &&
    bsojProgOK fNoDom.1 1 fNoDom.2 && (wlD fBase.1 3 [fBase.2] []).length == 24)
#eval check "sojProg (interpreter) equals the worklist on data, the model's leaves and the count: \
    Petersen (t = 6), K₅ (t = 3), two symmetric colourings"
  (sojProgOK 10 6 petArr && sojProgOK 5 3 (arrOf 5 fun x y => if x = y then 0 else 1) &&
    sojProgOK 8 5 (randCol 8 2 1) && sojProgOK 9 5 (randCol 9 2 7))
#eval check "stepProg (interpreter) equals stepD on the model-checked frames and their children \
    (wrappers with one piece)"
  (stepProgOK fTwins.1 20 fTwins.2 && stepProgOK fTwins.1 6 fTwins.2 &&
    stepProgOK fBase.1 3 fBase.2 && stepProgOK fBigTwins.1 1 fBigTwins.2 &&
    stepProgOK fNoDom.1 1 fNoDom.2)
#eval check "stepProg (interpreter) equals stepD at the cohSoj level (C₅ + K₁, C₆, a bipartite \
    leaf) and on the children (three pieces)"
  (stepProgOK fCohNode.1 1 fCohNode.2 && stepProgOK fCohLeaf.1 1 fCohLeaf.2 &&
    stepProgOK fCohBip.1 1 fCohBip.2)
/-- **`sojAtProg` against the model**: an interpreter run at `x` equals the worklist on data
from `sojAtD`'s leaf or frame, whose leaves decode to `(sojAt …).leafMs` with the count as
length. -/
def sojAtProgOK (m t : ℕ) (c : Array ℕ) (x : Fin m) : Bool :=
  let out := wlD m t (splitI [sojAtD m t c x.val]).2 (splitI [sojAtD m t c x.val]).1
  let T := sojAt (colOf m c) t x
  run (sojAtProg m t c x.val) == some out &&
    msEq (out.map (decodeOut m) : Multiset _) T.leafMs && out.length == T.count

#eval check "sojAtProg (interpreter) equals the worklist on data, the model's leaves and the \
    count: Petersen (t = 6) at three points, a symmetric colouring (t = 5) at four points \
    (leaves and frames)"
  (sojAtProgOK 10 6 petArr 0 && sojAtProgOK 10 6 petArr 3 && sojAtProgOK 10 6 petArr 7 &&
    sojAtProgOK 9 5 (randCol 9 2 7) 0 && sojAtProgOK 9 5 (randCol 9 2 7) 1 &&
    sojAtProgOK 9 5 (randCol 9 2 7) 3 && sojAtProgOK 9 5 (randCol 9 2 7) 7)

/-- Every leaf of a run has size at most `outB m q` (`bsojProg_outSize`, `sojProg_outSize`). -/
def outSizeOK (m q : ℕ) (out : Option (List OutD)) : Bool :=
  match out with
  | some l => l.all fun o => decide (outSize o ≤ outB m q)
  | none => false

#eval check "the leaves of the bsojProg and sojProg runs have size at most outB"
  (outSizeOK 15 5 (run (bsojProg 15 20 fTwins.2.V₁ fTwins.2.cs fTwins.2.a)) &&
    outSizeOK 15 5 (run (bsojProg 15 6 fTwins.2.V₁ fTwins.2.cs fTwins.2.a)) &&
    outSizeOK fBase.1 4 (run (bsojProg fBase.1 3 fBase.2.V₁ fBase.2.cs fBase.2.a)) &&
    outSizeOK fBigTwins.1 6
      (run (bsojProg fBigTwins.1 1 fBigTwins.2.V₁ fBigTwins.2.cs fBigTwins.2.a)) &&
    outSizeOK fNoDom.1 6 (run (bsojProg fNoDom.1 1 fNoDom.2.V₁ fNoDom.2.cs fNoDom.2.a)) &&
    outSizeOK 10 6 (run (sojProg 10 6 petArr)) &&
    outSizeOK 5 3 (run (sojProg 5 3 (arrOf 5 fun x y => if x = y then 0 else 1))) &&
    outSizeOK 8 5 (run (sojProg 8 5 (randCol 8 2 1))) &&
    outSizeOK 9 5 (run (sojProg 9 5 (randCol 9 2 7))))

/-- An interpreter run of `bsojProg` equals the worklist on data. -/
def bsojDataOK (mf : ℕ × FrameD) : Bool :=
  run (bsojProg mf.1 1 mf.2.V₁ mf.2.cs mf.2.a) == some (wlD mf.1 1 [mf.2] [])

#eval check "bsojProg (interpreter) equals the worklist on data at the cohSoj level (C₅ + K₁, \
    C₆, a bipartite leaf; the model is too slow there)"
  (bsojDataOK fCohNode && bsojDataOK fCohLeaf && bsojDataOK fCohBip)

/-! ### Direct continuation coverage

`dlI` and `contI` on hand-built inputs (not necessarily reached from a valid frame): the branch
taken, an interpreter run of `sp_dlProg` / `sp_contProg` equal to the data model, and the
decoded items equal to the model's `dlCont` / `cohCont` (with the model's guarded recursion
`recB`, and `shrink` for `cohCont`). -/

/-- A direct `dlCont` fixture with `d = 1` and no individualized cells: `m` points, the
points `V₁ ⊇ V₁'`, the cells `cs`, the relation `rel` and the `1`-ary colours `wl` of the
cells. -/
structure DLFix where
  m : ℕ
  V₁ : List ℕ
  V₁' : List ℕ
  cs : List (List ℕ)
  rel : ℕ → ℕ → Bool
  wl : Array ℕ

def DLFix.a (F : DLFix) : Array Bool :=
  ((List.range F.m).flatMap fun x => (List.range F.cs.length).map fun j => F.rel x j).toArray

/-- The data model of the continuation. -/
def DLFix.items (F : DLFix) : List SoJTree.Item := (dlI F.m 1 F.V₁ F.V₁' F.cs F.a 1 F.wl []).1

/-- The branch taken. -/
def DLFix.tag (F : DLFix) : String := dlTag F.m 1 F.V₁ F.V₁' F.cs F.a 1 F.wl []

/-- The interpreter run of `sp_dlProg` equals the data model. -/
def DLFix.progOK (F : DLFix) : Bool :=
  let k := F.cs.length
  run (sp_dlProg F.m 1 k (2 * k / 3) F.V₁' F.cs F.cs.toArray F.a
      ((List.range F.m).map (· * k)).toArray F.wl (pwTab 1 k) [0] (List.range k)
      (diffD F.V₁ F.V₁') []) == some (splitI F.items)

/-- The decoded items equal the model's `dlCont`, with the `1`-ary colouring read from `wl`. -/
def DLFix.modelOK (F : DLFix) : Bool :=
  let V₂ := famOf F.m F.cs
  let W : (Fin 1 → ↥V₂) → ℕ := fun y => get F.wl (cellIdx F.m F.cs (y 0).val)
  msEq (dlCont 1 (setOf F.m F.V₁) (setOf F.m F.V₁') V₂ (relOf F.m F.cs F.a) W (recB 1 V₂)
      []).leafMs (F.items.map (itemMs F.m 1)).sum

def DLFix.ok (F : DLFix) (tag : String) : Bool := F.tag == tag && F.progOK && F.modelOK

/-- Two cells with distinct colours: no dominant class. -/
def dlNoDom : DLFix := ⟨3, [0], [0], [[1], [2]], fun x j => x == 0 && j == 0, #[0, 1]⟩
/-- One colour, one point related to one of the two cells: the refinement splits the cells
(Codex's fixture of round 1, with two cells instead of three to keep the model fast). -/
def dlAllSmall : DLFix := ⟨3, [0], [0], [[1], [2]], fun x j => x == 0 && j == 0, #[0, 0]⟩
/-- One point related to both cells, and a point outside `V₁'`: no class of points of more
than `t = 1` points. -/
def dlC1Empty : DLFix := ⟨4, [0, 3], [0], [[1], [2]], fun x _ => x == 0, #[0, 0]⟩
/-- Two points related to both cells: a constant rectangle (recursion on no cells). -/
def dlRect : DLFix := ⟨4, [0, 1], [0, 1], [[2], [3]], fun x _ => x < 2, #[0, 0]⟩
/-- Two points matched to two cells: the `cohSoj` level, a node with partition leaves. -/
def dlCoh : DLFix := ⟨4, [0, 1], [0, 1], [[2], [3]], fun x j => x == j, #[0, 0]⟩

#eval check "direct dlCont, no dominant class: interpreter = data = model"
  (dlNoDom.ok "noDom")
#eval check "direct dlCont, every class of the refinement small (allSmall): interpreter = data \
    = model"
  (dlAllSmall.ok "allSmall")
#eval check "direct dlCont, no large class of points (empty C₁): interpreter = data = model"
  (dlC1Empty.ok "C1empty")
#eval check "direct dlCont, a constant rectangle: interpreter = data = model"
  (dlRect.ok "constRect")
#eval check "direct dlCont, the cohSoj level: interpreter = data = model"
  (dlCoh.ok "cohNode2:part,part")

/-- A direct `cohCont` fixture: `m = 8` points, the points `V₁ = [0, …, 4]`, `V₁' = [0, …, 3]`,
`C₁ = [0, 1, 2]`, three cells `{5}, {6}, {7}` numbered `8, 9, 10`, a colouring of the eleven
numbered points and cells, and `t = 1`. -/
def ctM : ℕ := 8
def ctCs : List (List ℕ) := [[5], [6], [7]]
def ctV₁ : List ℕ := [0, 1, 2, 3, 4]
def ctV₁' : List ℕ := [0, 1, 2, 3]
def ctC₁ : List ℕ := [0, 1, 2]
def ctCol (u v : ℕ) : ℕ := (u + 2 * v) % 3
def ctArr : Array ℕ := arrOf 11 ctCol

/-- The index of a point or cell of the model in the numbering. -/
def idxQ' (m : ℕ) (cs : List (List ℕ)) : Fin m ⊕ Finset (Fin m) → ℕ
  | .inl x => x.val
  | .inr s => m + cellIdx m cs s

/-- A data leaf on the numbered points and cells, as a leaf of the model. -/
def decodeQ (m : ℕ) (cs : List (List ℕ)) (f : ℕ → ℕ → ℕ) :
    Option SoJProg.LeafD → Option (CohOut (Fin m ⊕ Finset (Fin m)))
  | none => none
  | some (tag, (col, blk), (W₁, W₂, g)) =>
    let N := m + cs.length
    let ptsOf := fun l : List ℕ => ((l.filter (· < N)).map (eQf m cs)).toFinset
    if tag = 0 then
      some (.part ⟨fun q => get col (idxQ' m cs q), fun q => ptsOf (blk.getD (idxQ' m cs q) [])⟩)
    else
      some (.bip (ptsOf W₁) ((W₂.map ptsOf).toFinset)
        (bipEdge (fun q q' => f (idxQ' m cs q) (idxQ' m cs q')) g))

/-- The branch of `cohCont` taken. -/
def ctTag (o : Option SoJProg.LeafD) : String :=
  contTag ctM 1 ctCs.length ctCs (diffD ctV₁ ctV₁') (diffD ctV₁' ctC₁) ctC₁ (fA (offsArr 11) ctArr)
    o

/-- The interpreter, the data model and the model of `cohCont` agree on the leaf `o`. -/
def ctOK (o : Option SoJProg.LeafD) (tag : String) : Bool :=
  let f := fA (offsArr 11) ctArr
  let D₁ := diffD ctV₁ ctV₁'
  let D₂ := diffD ctV₁' ctC₁
  let it := contI ctM 1 ctCs.length ctCs D₁ D₂ ctC₁ f o
  let V₂ := famOf ctM ctCs
  ctTag o == tag &&
    run (sp_contProg ctM 1 ctCs.length ctCs.toArray D₁ D₂ ctC₁ (offsArr 11) ctArr o) ==
      some (splitI [it]) &&
    msEq (cohCont 1 (setOf ctM ctV₁) (setOf ctM ctV₁') (setOf ctM ctC₁) (shrink V₂ (recB 1 V₂))
      (decodeQ ctM ctCs f o)).leafMs (itemMs ctM 1 it)

#eval check "direct cohCont, a partition leaf (two pieces added): interpreter = data = model"
  (ctOK (some (0, (#[1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    #[[0, 1], [0, 1], [2], [], [], [], [], [], [], [], []]), ([], ([], 0)))) "part")
#eval check "direct cohCont, a bipartite leaf with |W| ≤ t: interpreter = data = model"
  (ctOK (some (1, (#[], #[]), ([0], ([[8]], 1)))) "bipSmall")
#eval check "direct cohCont, a bipartite leaf, recursion on one merged cell: interpreter = data \
    = model"
  (ctOK (some (1, (#[], #[]), ([0, 1], ([[8, 9]], 1)))) "bipRec")
#eval check "direct cohCont, a bipartite leaf failing the shrink guard: interpreter = data = model"
  (ctOK (some (1, (#[], #[]), ([0, 1, 2], ([[8], [9], [10]], 2)))) "bipNone")
#eval check "direct cohCont, the leaf none: interpreter = data = model"
  (ctOK none "none")

end GraphIsoChecks.SoJTree
