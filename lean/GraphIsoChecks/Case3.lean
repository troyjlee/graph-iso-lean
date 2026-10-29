module

public import GraphIsoChecks.Case2b
meta import GraphIsoChecks.Case2b
public import GraphIsoChecks.CertProg
meta import GraphIsoChecks.CertProg
public import GraphIso.Case3.Link
meta import GraphIso.Case3.Link
public import GraphIso.Case3.PipelineProg
meta import GraphIso.Case3.PipelineProg
public import GraphIso.Case3.Colouring
meta import GraphIso.Case3.Colouring
public import GraphIso.Case3.Case3Prog
meta import GraphIso.Case3.Case3Prog
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14i checks: Case 3

Checks of the stage 14i programs and data models (`GraphIso/Case3/`), each comparing a result
with brute force computed in the same term. Colourings of pairs (`k = 2`) are arrays in
milestone 10's code order (`u + m v`). Backend programs run with the Schreier–Sims backend inside
the solver procedure (`runR`, so the sub-solver `fun J => .recur J` is milestone 1's solver), or
with the verified oracle answering the backend calls directly and the solver as the recursive
procedure (`runDirectS`, for the kernel). Certificates use stage 14e's fixtures
(`GraphIsoChecks.CertProg`: `S₃`, `S₅` acting on the points, strings coloured on the points) and
its brute-force `certIso`.

**Kernel-checked examples** (`decide +kernel`, about three minutes in all):
* **The colourings on data** (`colXD`, `colYD` with comparisons by a key of the base pairs): the
  colour classes are exactly the key classes of the repetition-free pairs (repetitions colour
  `0`); names are consistent, `c_y (π ∘ T) = c_x T`, for the path `0–1–2–3` and its image by
  `(0 1)`; a class absent from `x` gets the fresh name `1 + 16 +` the index of its first pair.
* **The pipeline** (`pipeOK`, interpreter runs of `wlCProg`, `goodListProg`, `allStructsProg`,
  `firstStructProg`, `twinsFlagProg`, against brute force on the computed refinement):
  - the refinement has the partition of the classical refinement with the equality type
    (iterated; for the stable `C₅` colouring one round);
  - the good lists are exactly the candidates where milestone 10's `DesignGood` holds;
  - every structure, good list by good list: the extended vertex colouring (colour + 1 on `V`,
    classes as blocks, the rest one block of colour `0`); on the dominant class at `[]`, the
    restricted 2-skeleton's components of the least disconnected colour (`2K₂`) or the leaves of
    `soj` (`C₅`: the colouring from each point, five leaves); all valid colored partitions;
  - the first structure is the first of the list, and the flag `twinsD` is set exactly when
    there is no good list (the constant colouring). No good list implies a class of more than
    `t` pairwise twins (`twinsD_spec`); the converse fails (below, the empty window).

  Fixtures: `C₅` (10 structures), `C₄` with the diagonal by parity (5), `2K₂` (5), the constant
  colouring (no good list, no structure).
* **Canonicity of the complete structure lists**: for a relabelled colouring the structures are
  the images of the structures, as multisets of decoded leaves with multiplicity (`C₄`, `2K₂`,
  `C₅` under a rotation).
* **`case3Prog` end to end** (`runDirectS`): `S₃` acting on the points of `[3]`, `k = 1`, the
  window all string positions: with one distinguished point (`V = [0]` for `x`, `[1]` for
  `y`) the answer is the brute-force isomorphism coset (two isomorphisms); a non-isomorphic
  pair gives `some none` (Align finds the structures isomorphic, the sub-solver rejects); with
  `V = [0, 1, 2]` every point has an equivalent certificate (for `k ≤ 2`, `Alt(A)` is trivial,
  the beard's window is empty and every injective tuple is equivalent), so for `k = 1` the
  only candidate `[]` has a class of three points, more than `t = 2`: no good list exists and
  the program returns the fallback `none`.
* **`case3Prog` on an empty window** (from the round 1 audit): `S₃`, equal constant strings,
  `k = 2`, the complements listed as `[0, 1, 2]` and `[2, 0, 1]`; the colourings are computed by
  `tupleColProg` (one non-gray colour for the injective pairs), the three points are pairwise
  twins (a class of three, more than `t = 2`), yet good lists exist, so there is no fallback;
  three Align candidates, and the returned coset is the whole group (every element is an
  isomorphism on the empty window). The fallback happens when no good list exists, which
  implies large twins (`twinsD_spec`); large twins alone need not trigger it.

**Interpreter runs** (`#eval`, each throwing on a failure), supplementary:
* the same colouring, pipeline and canonicity checks (also `C₅` under a reflection);
* the data models (`allStructsD`, `firstStructD`, `twinsD`) equal the programs;
* **`tupleColProg`** (with `certIsoProg`) on `S₅` acting on the points, `k = 2`, a colouring and
  its image by `(0 1)`: equal to the colourings by the brute-force `certIso`, with consistent
  names;
* **`case3Prog`** with the PHOAS Schreier–Sims backend on the three `S₃` cases above, and on `S₅`
  with `k = 3`, `V = [0, 1, 2]` coloured by three distinct colours (nontrivial certificates:
  the beard's window is `V`, the six orderings of `V` are pairwise inequivalent, no twins): the
  answer is the brute-force isomorphism coset (two isomorphisms).

**Not checked in the kernel, and why.** Milestone 10's array Weisfeiler–Leman (`wlA`) does not
reduce in the kernel, so the data models containing it are compared with the programs by
`#eval` only; the kernel checks use interpreter runs of the programs, which reduce. The
iterated classical refinement on the 25 pairs of `C₅` exceeds the kernel's recursion depth, so
`C₅` is checked against one round (its colouring is stable). `tupleColProg` makes a
`certIsoProg` call per comparison; in the kernel only the `k = 1` runs inside `case3Prog` are
feasible, so `tupleColProg` on `S₅` and `case3Prog` with `k = 3` are interpreter runs (the latter
takes about a minute). Nontrivial certificates need `k ≥ 3`, hence a base of at least five
points. The `soj` leaves of these fixtures are colored partitions; Johnson leaves need a big
colour class, which small fixtures do not have (stage 14h's checks cover Johnson dispatch).
Note: `case3Prog`'s answer is correct only when every isomorphism maps `Vx` onto `Vy` (as the
supports' complements do); with `V = [0, 1, 2]` and only two distinguished points, a trial run
returned exactly the isomorphisms preserving `V`, as expected — the fixtures above choose `V`
canonical.

The whole file compiles in about six minutes (the empty-window kernel check about 80 s).
-/

@[expose] public section

namespace GraphIsoChecks.Case3

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims
  GraphIso.SoJTree GraphIso.SoJProg GraphIso.SplitJohnson GraphIso.Case3
  GraphIsoChecks.Sims GraphIsoChecks.Sweep GraphIsoChecks.SoJTree GraphIsoChecks.Case2b

/-! ### Pairs of `[m]` (`k = 2`) -/

/-- The code of the pair `(u, v)` in milestone 10's order (`u + m v`). -/
def code2 (m u v : ℕ) : ℕ := u + m * v

/-- A colouring of the pairs of `[m]`, as an array in code order. -/
def colArr (m : ℕ) (f : ℕ → ℕ → ℕ) : Array ℕ :=
  ((List.range (m * m)).map fun c => f (c % m) (c / m)).toArray

/-- The row-major list (index `u m + v`) of an array in code order. -/
def rowMajor (m : ℕ) (W : Array ℕ) : List ℕ :=
  (List.range m).flatMap fun u => (List.range m).map fun v => get W (code2 m u v)

/-- The row-major list of a colouring with the equality type added (the diagonal apart). -/
def rowMajorEq (m : ℕ) (W : Array ℕ) : List ℕ :=
  (List.range m).flatMap fun u => (List.range m).map fun v =>
    2 * get W (code2 m u v) + if u == v then 1 else 0

/-! ### The colouring of the tuples (data, with given comparisons) -/

/-- The class of a pair of base points in a graph: `1` an edge, `2` a non-edge (`0` otherwise). -/
def keyG (es : List (ℕ × ℕ)) (b : List ℕ) : ℕ :=
  match b with
  | [a, c] => if es.any (fun e => (e.1 == a && e.2 == c) || (e.1 == c && e.2 == a)) then 1 else 2
  | _ => 0

/-- A comparison of two digit lists through keys of their base tuples. -/
def cmpK (kx ky : List ℕ → ℕ) (vx vy : List ℕ) (di dt : List ℕ) : Bool :=
  kx (tupD vx di) == ky (tupD vy dt)

/-- The pairs of `[m]` as digit lists, in code order. -/
def digits2 (m : ℕ) : List (List ℕ) :=
  (List.range m).flatMap fun v => (List.range m).map fun u => [u, v]

/-- **Consistent names**: `c_y (π ∘ T) = c_x T` for every pair `T`. -/
def consistentOK (m : ℕ) (cX cY : Array ℕ) (π : List ℕ) : Bool :=
  (List.range m).all fun u => (List.range m).all fun v =>
    get cY (code2 m (π.getD u 0) (π.getD v 0)) == get cX (code2 m u v)

/-- **The colouring is the equivalence**: two pairs have the same colour exactly when both
repeat a point, or neither does and their keys agree. -/
def classOK (m : ℕ) (c : Array ℕ) (key : List ℕ → ℕ) (v : List ℕ) : Bool :=
  (digits2 m).all fun d => (digits2 m).all fun d' =>
    (get c (code2 m (d.getD 0 0) (d.getD 1 0)) == get c (code2 m (d'.getD 0 0) (d'.getD 1 0))) ==
      ((!d.Nodup && !d'.Nodup) || (d.Nodup && d'.Nodup && key (tupD v d) == key (tupD v d')))

/-- The path `0–1–2–3` and its image under `(0 1)`: `1–0–2–3`. -/
def pathX : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3)]
def pathY : List (ℕ × ℕ) := [(1, 0), (0, 2), (2, 3)]
def v4 : List ℕ := [0, 1, 2, 3]

def colX4 : Array ℕ := colXD (cmpK (keyG pathX) (keyG pathX) v4 v4) 2 4
def colY4 : Array ℕ := colYD (cmpK (keyG pathX) (keyG pathY) v4 v4)
  (cmpK (keyG pathY) (keyG pathY) v4 v4) 2 4

/-- A key with a third class (the pair `{0, 3}`), absent from `x`. -/
def keyZ (b : List ℕ) : ℕ := if b == [0, 3] || b == [3, 0] then 3 else keyG pathX b

def colZ4 : Array ℕ := colYD (cmpK (keyG pathX) keyZ v4 v4) (cmpK keyZ keyZ v4 v4) 2 4

/-- The colouring of `x`, consistent names for the relabelled `y`, and fresh names for a class
absent from `x` (`1 + |tuples| +` the index of the first equivalent pair of `y`). -/
def colourOK : Bool :=
  colX4.size == 16 && colY4.size == 16 &&
  classOK 4 colX4 (keyG pathX) v4 && classOK 4 colY4 (keyG pathY) v4 &&
  consistentOK 4 colX4 colY4 [1, 0, 2, 3] &&
  get colZ4 (code2 4 0 3) == 1 + 16 + code2 4 3 0 && get colZ4 (code2 4 3 0) == 1 + 16 + 3 &&
  get colZ4 (code2 4 1 2) == get colX4 (code2 4 1 2)

#eval check "colouring data: classes, consistent names, fresh names" fun _ => colourOK

/-! ### The pipeline against brute force (`k = 2`) -/

/-- The `2`-ary refinement, by an interpreter run of `wlCProg`. -/
def wlRun (m : ℕ) (col : Array ℕ) : Option (Array ℕ) := runP (wlCProg 2 m col)

/-- The vertex colouring at `x` (`x = []` or a point): `W (u, u)` or `W (a, u)`. -/
def sk1 (m : ℕ) (W : Array ℕ) (x : List ℕ) (u : ℕ) : ℕ :=
  match x with
  | [] => get W (code2 m u u)
  | a :: _ => get W (code2 m a u)

/-- The class of `u` in the vertex colouring at `x`. -/
def clsB (m : ℕ) (W : Array ℕ) (x : List ℕ) (u : ℕ) : List ℕ :=
  (List.range m).filter fun w => sk1 m W x w == sk1 m W x u

/-- The 2-skeleton at `[]` is a clique on `C`: all pairs of distinct points have one colour. -/
def cliqueB (m : ℕ) (W : Array ℕ) (C : List ℕ) : Bool :=
  (C.flatMap fun u => (C.filter (· != u)).map fun v => get W (code2 m u v)).dedup.length ≤ 1

/-- Milestone 10's `DesignGood` at `x`, for `k = 2`. -/
def goodB (m t : ℕ) (W : Array ℕ) (x : List ℕ) : Bool :=
  (List.range m).all (fun u => (clsB m W x u).length ≤ t) ||
    (x.length + 2 ≤ 2 && (List.range m).any fun u =>
      t < (clsB m W x u).length && !cliqueB m W (clsB m W x u))

/-- The candidates for `k = 2`: `[]` and the points. -/
def candsB (m : ℕ) : List (List ℕ) := [] :: (List.range m).map ([·])

/-- The good lists, brute force. -/
def goodsB (m : ℕ) (W : Array ℕ) : List (List ℕ) := (candsB m).filter (goodB m (tOf m) W)

/-- The expected key of the structure at `x` when every class is small: the vertex colouring
(shifted by one) on `V`, its classes as blocks, and the rest one block of colour `0`. -/
def smallKey (M : ℕ) (V : List ℕ) (W : Array ℕ) (x : List ℕ) : List (ℕ × List ℕ) :=
  let m := V.length
  (List.range M).map fun v =>
    if v ∈ V then
      (sk1 m W x (V.idxOf v) + 1, (List.range M).filter fun w =>
        w ∈ V && sk1 m W x (V.idxOf w) == sk1 m W x (V.idxOf v))
    else (0, (List.range M).filter (· ∉ V))

/-- The dominant class at `[]`: the class of the first point with more than `t` points. -/
def domClsB (m : ℕ) (W : Array ℕ) : Option (List ℕ) :=
  ((List.range m).find? fun u => tOf m < (clsB m W [] u).length).map (clsB m W [])

/-- The 2-skeleton at `[]` restricted to `C`, row-major. -/
def skelB (m : ℕ) (W : Array ℕ) (C : List ℕ) : List ℕ :=
  C.flatMap fun u => C.map fun v => get W (code2 m u v)

/-- The number of structures at a good list. -/
def segLen (m : ℕ) (W : Array ℕ) (x : List ℕ) : ℕ :=
  if (List.range m).all (fun u => (clsB m W x u).length ≤ tOf m) then 1
  else match domClsB m W with
    | some C => if (disconnB C.length (skelB m W C)).isEmpty then C.length else 1
    | none => 0

/-- The structures at a good list against brute force: the extended vertex colouring, or, on the
dominant class, the components of the least disconnected colour or the leaves of `soj` (each the
colouring from one point, when no class from a point is big), extended along the class. -/
def segOK (M : ℕ) (V : List ℕ) (W : Array ℕ) (x : List ℕ) (seg : List OutD) : Bool :=
  let m := V.length
  validB M seg &&
  if (List.range m).all (fun u => (clsB m W x u).length ≤ tOf m) then
    seg.length == 1 && seg.all fun o => o.1 == 1 && keyOf M o == smallKey M V W x
  else match domClsB m W with
    | some C =>
      let s := C.length
      let sk := skelB m W C
      let CB := C.map (V.getD · 0)
      match disconnB s sk with
      | r :: rs => seg.length == 1 && seg.all fun o =>
          o.1 == 1 && keyOf M o == compKey M CB sk ((r :: rs).foldl min r)
      | [] => noBig s ((s + 3) / 2) sk && seg.all (fun o => o.1 == 1) &&
          msEqL (seg.map (keyOf M)) ((List.range s).map (colPartKey M CB sk))
    | none => false

/-- Split a list into segments of the given lengths. -/
def segments {α : Type} (L : List α) : List ℕ → List (List α)
  | [] => []
  | n :: ns => L.take n :: segments (L.drop n) ns

/-- The refinement `W` against the classical refinement with the equality type (same partition
of the pairs). For a `stable` input, one round leaves the partition unchanged and `W` has the
input's partition (cheaper in the kernel than iterating). -/
def wlCheck (m : ℕ) (col W : Array ℕ) (stable : Bool) : Bool :=
  if stable then
    samePart m (rowMajor m W) (rowMajorEq m col) &&
      samePart m (rowMajorEq m col) (wlRound m (rowMajorEq m col))
  else samePart m (rowMajor m W) (wlB m (rowMajorEq m col))

/-- **The pipeline against brute force**: the refinement against the classical refinement
(same partition), the good lists (`goodListProg`), all structures (`allStructsProg`) segment by
segment, the first structure (`firstStructProg`) and the twins flag (`twinsFlagProg`). -/
def pipeOK (M : ℕ) (V : List ℕ) (col : Array ℕ) (count : ℕ) (twins stable : Bool) : Bool :=
  let m := V.length
  match wlRun m col, runP (allStructsProg M 2 V col), runP (firstStructProg M 2 V col),
      runP (twinsFlagProg 2 m col) with
  | some W, some L, some fst, some tw =>
    W.size == m * m && wlCheck m col W stable &&
    runP (SoJProg.goodListProg W 2 m (tOf m)) == some (goodsB m W) &&
    tw == twins && tw == (goodsB m W).isEmpty && L.length == count &&
    L.length == ((goodsB m W).map (segLen m W)).sum &&
    ((goodsB m W).zip (segments L ((goodsB m W).map (segLen m W)))).all
      (fun p => segOK M V W p.1 p.2) &&
    fst == L.head?
  | _, _, _, _ => false

/-- The cycle `C₅` on `[5]`: `0` on the diagonal, `1` on the edges, `2` on the non-edges. -/
def c5col : Array ℕ := colArr 5 fun u v =>
  if u == v then 0 else if (u + 5 - v) % 5 == 1 || (v + 5 - u) % 5 == 1 then 1 else 2

/-- The cycle `C₄` on `[4]` with the diagonal coloured by parity. -/
def c4col : Array ℕ := colArr 4 fun u v =>
  if u == v then 10 + u % 2 else if (u + 4 - v) % 4 == 1 || (v + 4 - u) % 4 == 1 then 1 else 2

/-- Two disjoint edges `{0, 1}`, `{2, 3}` on `[4]`. -/
def k22col : Array ℕ := colArr 4 fun u v =>
  if u == v then 0 else if u / 2 == v / 2 then 1 else 2

/-- The constant colouring of `[4]`: all points pairwise twins, and no good list. -/
def constCol : Array ℕ := colArr 4 fun _ _ => 0

#eval check "pipeline: C5 (soj at [], small at the points), C4 (small), 2K2 (components), \
    constant (no good list)" fun _ =>
  pipeOK 6 [0, 1, 2, 3, 4] c5col 10 false false && pipeOK 5 [1, 2, 3, 4] c4col 5 false false &&
    pipeOK 5 [0, 2, 3, 4] k22col 5 false false && pipeOK 4 [0, 1, 2, 3] constCol 0 true false


/-! ### Canonicity of the complete structure lists -/

/-- The colouring relabelled by a permutation `π` of `[m]`: `c' (π u, π v) = c (u, v)`. -/
def relabelCol (m : ℕ) (π : List ℕ) (col : Array ℕ) : Array ℕ :=
  colArr m fun u' v' => get col (code2 m (π.idxOf u') (π.idxOf v'))

/-- The permutation of the base `[M]` induced by `π` on the indices of `V` (identity off `V`). -/
def baseSigma (M : ℕ) (V π : List ℕ) : List ℕ :=
  (List.range M).map fun b => if b ∈ V then V.getD (π.getD (V.idxOf b) 0) 0 else b

/-- **Canonicity**: the structures of the relabelled colouring are the images of the
structures, as multisets of decoded leaves (complete lists, with multiplicity). -/
def canonOK3 (M : ℕ) (V : List ℕ) (π : List ℕ) (col : Array ℕ) : Bool :=
  match runP (allStructsProg M 2 V col),
      runP (allStructsProg M 2 V (relabelCol V.length π col)) with
  | some L, some L' =>
    L.length == L'.length && msEq (Multiset.ofList (L'.map (decodeOut M)))
      (Multiset.ofList (L.map fun o =>
        PermData.denote M (ofList (baseSigma M V π)) • decodeOut M o))
  | _, _ => false

#eval check "canonicity of the complete structure lists: C5 (a rotation and a reflection), C4, \
    2K2" fun _ =>
  canonOK3 6 [0, 1, 2, 3, 4] [1, 2, 3, 4, 0] c5col &&
    canonOK3 6 [0, 1, 2, 3, 4] [0, 4, 3, 2, 1] c5col &&
    canonOK3 5 [1, 2, 3, 4] [2, 3, 0, 1] c4col && canonOK3 5 [0, 2, 3, 4] [2, 0, 1, 3] k22col

/-- The data models (`allStructsD`, `firstStructD`, `twinsD`; supplementary, `#eval` only, since
milestone 10's `wlA` does not reduce in the kernel) equal the interpreter runs. -/
def dataOK (M : ℕ) (V : List ℕ) (col : Array ℕ) : Bool :=
  runP (allStructsProg M 2 V col) == some (allStructsD M 2 V col) &&
    runP (firstStructProg M 2 V col) == some (firstStructD M 2 V col) &&
    runP (twinsFlagProg 2 V.length col) == some (twinsD 2 V.length col)

#eval check "the data models equal the programs: C5, C4, 2K2, constant" fun _ =>
  dataOK 6 [0, 1, 2, 3, 4] c5col && dataOK 5 [1, 2, 3, 4] c4col &&
    dataOK 5 [0, 2, 3, 4] k22col && dataOK 4 [0, 1, 2, 3] constCol

/-! ### The colouring by certificate equivalence (`tupleColProg`) -/

/-- `tupleColProg` (an interpreter run, `certIsoProg` with milestone 1's solver as the
sub-solver) against the colourings by the brute-force equivalence of certificates, and the
consistent names for `y` the image of `x` (renumbering `π`). -/
def tupleColOK (F : GraphIsoChecks.CertProg.Fix) (G gs : List (List ℕ)) (x y : StrData)
    (vx vy π : List ℕ) : Bool :=
  let m := vx.length
  let cXX := fun di dt => F.certIso G x x (tupD vx di) (tupD vx dt)
  let cXY := fun di dt => F.certIso G x y (tupD vx di) (tupD vy dt)
  let cYY := fun di dt => F.certIso G y y (tupD vy di) (tupD vy dt)
  match runR (tupleColProg sub F.n F.N 2 vx vy x y (F.grp gs)) with
  | some (cx, cy) => cx == colXD cXX 2 m && cy == colYD cXY cYY 2 m && consistentOK m cx cy π
  | none => false

#eval check "tupleColProg: S5 on the points, k = 2, a colouring and its image by (0 1)" fun _ =>
  tupleColOK GraphIsoChecks.CertProg.pts5 GraphIsoChecks.CertProg.S5 GraphIsoChecks.CertProg.sym5
    (GraphIsoChecks.CertProg.col5 [1, 2, 0, 0, 2]) (GraphIsoChecks.CertProg.col5 [2, 1, 0, 0, 2])
    [0, 1, 2] [0, 1, 2] [1, 0, 2]

/-! ### `case3Prog` end to end -/

/-- Run with the verified Schreier–Sims oracle answering the backend calls directly, and
milestone 1's solver (`solveBody`) as the recursive procedure, so `sub := .recur` is the
solver. -/
def runDirectS {t : Ty} (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval ssOracle (Solver.solveBody Ty.unit Ty.denote) 10000000 p).map Prod.fst

/-- The brute-force isomorphisms on the window `W` (elements of `G` as permutations of the
points, which act on the string positions as on the base). -/
def isoB (G : List (List ℕ)) (x y : StrData) (W : List ℕ) : List (List ℕ) :=
  G.filter fun g => W.all fun j => get y (g.getD j 0) == get x j

/-- `case3Prog` on `S₃` acting on the points of `[3]` (string positions `0–2`, base `3–5`),
`k = 1`, the window all string positions, run by `run` (the direct oracle, or the PHOAS
Schreier–Sims backend): `expect = 0` asserts the fallback (`none`), `1` no isomorphism
(`some none`), `2` the brute-force isomorphism coset. -/
def case3OK (run : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote
      (.option (Ty.answer Ty.unit)) → Option (Option (Option (CosetData Ty.unit))))
    (x y : StrData) (Vx Vy : List ℕ) (expect : ℕ) : Bool :=
  let F := GraphIsoChecks.CertProg.pts3
  let C := isoB GraphIsoChecks.CertProg.S3 x y [0, 1, 2]
  match run (case3Prog sub 3 1 (x, y) (WinData.ofPoints 6 [0, 1, 2])
      (F.grp GraphIsoChecks.CertProg.sym3) Vx Vy) with
  | some none => expect == 0
  | some (some none) => expect == 1 && C.isEmpty
  | some (some (some (σ, K))) =>
    expect == 2 && sameSet ((F.closed K).map (compose (F.baseOf σ))) C
  | none => false

def col3 (l : List ℕ) : StrData := GraphIsoChecks.CertProg.col3 l

#eval check "case3Prog (PHOAS Schreier-Sims, solver as sub-solver): one distinguished point \
    (2 isomorphisms), a non-isomorphic pair (none), the fallback (V = [3], k = 1)" fun _ =>
  case3OK runR (col3 [1, 0, 0]) (col3 [0, 1, 0]) [0] [1] 2 &&
    case3OK runR (col3 [1, 0, 0]) (col3 [0, 0, 0]) [0] [1] 1 &&
    case3OK runR (col3 [1, 0, 0]) (col3 [0, 1, 0]) [0, 1, 2] [0, 1, 2] 0

/-- `case3Prog` on `S₅` acting on the points of `[5]` (string positions `0–4`, base `5–9`),
`k = 3`, `V = [0, 1, 2]`, the window all string positions, against the brute-force isomorphisms
(`expect` as in `case3OK`). -/
def case3OK5 (x y : StrData) (Vx Vy : List ℕ) (expect : ℕ) : Bool :=
  let F := GraphIsoChecks.CertProg.pts5
  let C := isoB GraphIsoChecks.CertProg.S5 x y [0, 1, 2, 3, 4]
  match runR (case3Prog sub 5 3 (x, y) (WinData.ofPoints 10 [0, 1, 2, 3, 4])
      (F.grp GraphIsoChecks.CertProg.sym5) Vx Vy) with
  | some none => expect == 0
  | some (some none) => expect == 1 && C.isEmpty
  | some (some (some (σ, K))) =>
    expect == 2 && sameSet ((F.closed K).map (compose (F.baseOf σ))) C
  | none => false

#eval check "case3Prog, S5, k = 3, V = [3] canonical (three distinct colours): the two \
    isomorphisms" fun _ =>
  case3OK5 (GraphIsoChecks.CertProg.col5 [1, 2, 3, 0, 0])
    (GraphIsoChecks.CertProg.col5 [2, 1, 3, 0, 0]) [0, 1, 2] [0, 1, 2] 2

/-! ### Kernel-checked examples -/

/-- The colourings on data: classes, consistent names, fresh names. -/
example : colourOK = true := by decide +kernel
/-- The pipeline on `C₄` (every good list small). -/
example : pipeOK 5 [1, 2, 3, 4] c4col 5 false false = true := by decide +kernel
/-- The pipeline on `2K₂` (the components leaf at `[]`). -/
example : pipeOK 5 [0, 2, 3, 4] k22col 5 false false = true := by decide +kernel
/-- The pipeline on the constant colouring (no good list, no structure, the flag set). -/
example : pipeOK 4 [0, 1, 2, 3] constCol 0 true false = true := by decide +kernel
/-- The pipeline on `C₅` (five `soj` leaves at `[]`, small at the points); its colouring is
stable, so the refinement is checked against one round of the classical refinement. -/
example : pipeOK 6 [0, 1, 2, 3, 4] c5col 10 false true = true := by decide +kernel
/-- Canonicity of the complete structure lists: `C₄` and `2K₂`. -/
example : (canonOK3 5 [1, 2, 3, 4] [2, 3, 0, 1] c4col &&
    canonOK3 5 [0, 2, 3, 4] [2, 0, 1, 3] k22col) = true := by decide +kernel
/-- Canonicity of the complete structure lists: `C₅` under a rotation. -/
example : canonOK3 6 [0, 1, 2, 3, 4] [1, 2, 3, 4, 0] c5col = true := by decide +kernel
/-- **`case3Prog` end to end** (the direct oracle, milestone 1's solver as the sub-solver):
one distinguished point, against the brute-force isomorphism coset (two isomorphisms). -/
example : case3OK runDirectS (col3 [1, 0, 0]) (col3 [0, 1, 0]) [0] [1] 2 = true := by
  decide +kernel
/-- `case3Prog` end to end: a non-isomorphic pair (`some none`) and the fallback (`none`: for
`k = 1` and `V = [0, 1, 2]` no good list exists). -/
example : (case3OK runDirectS (col3 [1, 0, 0]) (col3 [0, 0, 0]) [0] [1] 1 &&
    case3OK runDirectS (col3 [1, 0, 0]) (col3 [0, 1, 0]) [0, 1, 2] [0, 1, 2] 0) = true := by
  decide +kernel

/-! ### `case3Prog` on an empty window (from the round 1 audit) -/

/-- `case3Prog` on `S₃` acting on the points of `[3]`, equal constant strings, `k = 2`, the
empty window, and the complements listed as `[0, 1, 2]` and `[2, 0, 1]`. -/
def emptyWinResult : Option (Option (AnswerData Ty.unit)) :=
  let F := GraphIsoChecks.CertProg.pts3
  let x := col3 [0, 0, 0]
  runDirectS (case3Prog sub 3 2 (x, x) (WinData.ofPoints 6 [])
    (F.grp GraphIsoChecks.CertProg.sym3) [0, 1, 2] [2, 0, 1])

/-- The returned coset is the whole group (every element is an isomorphism on the empty
window); three good lists on each side give three Align candidates. -/
def emptyWinOK : Bool :=
  let F := GraphIsoChecks.CertProg.pts3
  match emptyWinResult with
  | some (some (some (σ, H))) =>
    sameSet ((F.closed H).map (compose (F.baseOf σ))) GraphIsoChecks.CertProg.S3
  | _ => false

/-- The colouring the certificate program computes: one non-gray colour for the injective
pairs. -/
def emptyWinCol : Array ℕ := colXD (fun _ _ => true) 2 3

/-- The colourings of `x` and `y` by `tupleColProg` (the direct oracle). -/
def emptyWinColours : Option (Array ℕ × Array ℕ) :=
  let F := GraphIsoChecks.CertProg.pts3
  let x := col3 [0, 0, 0]
  runDirectS (tupleColProg sub 3 6 2 [0, 1, 2] [2, 0, 1] x x
    (F.grp GraphIsoChecks.CertProg.sym3))

/-- The three points are pairwise twins of that colouring, a class of more than `t = 2`
points; yet the program does not fall back (good lists exist). -/
theorem emptyWin_large_twins : ∃ T : Finset (Fin 3), tOf 3 < T.card ∧
    ∀ u ∈ T, ∀ v ∈ T, Coherent.IsTwin (Coherent.toFun (k := 2) emptyWinCol) u v := by
  refine ⟨Finset.univ, by decide, ?_⟩
  intro u _ v _ T
  unfold emptyWinCol
  rw [toFun_colXD, toFun_colXD]
  have hnd : (Coherent.digits (⇑(Equiv.swap u v) ∘ T)).Nodup ↔ (Coherent.digits T).Nodup := by
    rw [Case3.nodup_digits_iff, Case3.nodup_digits_iff]
    exact (Equiv.swap u v).injective.of_comp_iff T
  simp only [colXVal, hnd]

/-- **`case3Prog` on an empty window**: the whole group. -/
example : emptyWinOK = true := by decide +kernel
#eval check "the colourings on the empty-window fixture: one non-gray colour" fun _ =>
  emptyWinColours == some (emptyWinCol, emptyWinCol)

end GraphIsoChecks.Case3
