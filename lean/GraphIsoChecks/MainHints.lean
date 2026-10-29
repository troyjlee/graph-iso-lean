module

public import GraphIsoChecks.Align
meta import GraphIsoChecks.Align
public import GraphIso.Main.Derive
meta import GraphIso.Main.Derive
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-1 checks: derived hints

Checks of the stage 14j-1 programs (`GraphIso/Main/`), each comparing a program's result with
brute force computed in the same term. The backend programs run with the verified Schreier–Sims
oracle answering their backend calls directly (`runDirect`); the brute force enumerates group
elements (`closure`, on image lists) and all permutations (`perms`, structural recursion).

The **hint check** (`hintOK`) is the content of stage 14b's `HintValid` on data, tested over
every element of the re-based group: its degree is `n + k`; restricted to the string positions
`[0, n)` it is the old group restricted to them (`sameRes`, the same action on the strings);
every element `g` carries the label of `i` to the label of `g i` through its action on the new
base (equivariance); the labels are not constant on the window; their entries are below `k`.

**Kernel-checked examples** (`decide +kernel`):
* **M0** (`m0Prog`): `D₄` on four string positions (the maximal blocks `{0, 2}, {1, 3}`, two
  new base points) and `S₄` (primitive: four singleton blocks). The hint check, and maximality:
  the group's action on the new base (the action on the blocks) is primitive (`primitive`, every
  pair generates the whole set as a block).
* **M1** (`m1Prog`): an intransitive base action with two fixed base points; the chosen orbit
  is the only one with non-constant labels (two new base points), the new labels are its
  intersections with the old ones, and the hint check.
* **M2a** (`m2aProg`): `C₄` on the strings and the base alike with the blocks `{0, 2}, {1, 3}`
  of the base and labels `{i}` (not equidistributed): each new label is the block met.
* **M2b** (`m2bProg`): the same group with labels `{i, i + 1}` (equidistributed): the block
  stabilizer equals the brute-force setwise stabilizer (order 2), the representatives cover the
  group (at most two of them), the re-based stabilizer is exactly the stabilizer acting on the
  strings and on the block's points (`rebaseOK`), and the new labels are the intersections with
  the block, renumbered.
* **The Johnson fallback** (`jfallbackProg`): `S₂ × S₂` on `[4]` with the union cells `{2, 3}`
  (which it preserves): the pointwise stabilizer of their positions against brute force (order
  2), a cover by at most `2! = 2` representatives.
* **Coloured Johnson** (`cjohnOps`): `V₀ = {0, 1}`, cells `{2}, {3}`, `s = 1`, the rest `{4, 5}`
  in two colourings (equal colours: stabilizer of order 4; different: order 2); the generated
  group equals the brute-force stabilizer over `Sym(6)` (the embedding and the colours of the
  rest preserved), and the isomorphism search against brute force (a relabelling found; a
  different colour profile rejected); programs equal the data functions.
* **Derived hints** (`deriveProg`, `deriveOK`): a parent hint `(G, w, L)`, a reduced group `K`
  and a `K`-orbit `O` (`DFix`). Each fixture checks the setting (`DSetting` on data:
  `settingOK`), that the program's output equals `deriveModel`'s (run with the same
  verified oracle; all fixtures, free and coloured Johnson), its tag, and the outcome
  promised for it (`outcomeOK`), with the child's window `O` at the child's degree and its
  action on the string positions equal to that of the group it comes from. Tag 0 (no hint,
  `2|O| ≤ |w|`): `C₄` with labels `{i, i + 2}`, `K = ⟨(0 2)(1 3)⟩`. Tag 1 (M1,
  `4(N' − n) ≤ 3m`): the same with labels `{i}`. Tag 2 (M2a, `2(N' − n) ≤ m`): `K = C₄`, labels
  `{i}`. Tag 3 (M2b: `R ≤ P`, a cover of `P` by at most `m` cosets, the hint check on every
  `R`-orbit in `O`): `K = C₄`, labels `{i, i + 1}`. Tags 4 and 5 on a Johnson structure `j12`
  (`m = 12`: cells `A, B` of two points and `C, D` of one, `s = 2`, `V₀` the six pairs; proved
  `IsJohnson`, `JValid`, and the colour bound of `deriveCJ_ne_stuck`), preserved by
  `K = C₂ ≀ C₂`, which also permutes the points inside `A` and `B`: the Johnson union re-based
  onto the cells (tag 4, unions `{A, C} ≠ {B, C}`: the child is `K` acting on the cells, the
  labels the unions), and the fallback (tag 5, one union `{A, B, C, D}`: `P` is `K` re-based
  onto the cells, `R` the pointwise stabilizer in `P` of the four cells, two representatives,
  `R`-orbits in `O` of half of `O`).
* **The negative control** (tag 6, `stuckOK`): `C₃` with no structure, a primitive base action.
* **Progress with a preserved colored partition** (`derivePart_ne_stuck`): `C₆` preserves two
  partitions with `4t ≤ 3m` (`partPres`), and its tag is `2`, not `6`.

**Interpreter runs** (`#eval`, each throwing on a failure), supplementary: M0 on `D₆` (either
maximal block system accepted: the check is primitivity of the action on the blocks), M1 with a
larger base, M2b on `C₈` with blocks of size four, and coloured Johnson with a rest of three
points.
-/

@[expose] public section

namespace GraphIsoChecks.MainHints

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Align
  GraphIso.SoJTree GraphIsoChecks.Sweep

/-- Run a program with the verified Schreier–Sims oracle answering its backend calls. -/
def runDirect {t : Ty} (p : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval ssOracle (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-- Run a program with no backend calls. -/
def runP {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-! ### Brute force -/

def gD (gs : List (List ℕ)) : GensData := gs.map ofList

def setEq (u v : List ℕ) : Bool := u.all (· ∈ v) && v.all (· ∈ u)

def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

/-- The image of `v` under the image list `p`. -/
def ap (p : List ℕ) (v : ℕ) : ℕ := p.getD v v

/-- The elements of two groups agree on the string positions `[0, n)`. -/
def sameRes (n : ℕ) (A B : List (List ℕ)) : Bool :=
  sameSet (A.map (·.take n)) (B.map (·.take n))

/-- **The hint check** (`HintValid` on data, over every element of the new group `H'` of
degree `n + k`): same action on the strings as the old group `G` (elements given as image
lists), equivariant labels, labels not constant on the window `pts`, entries below `k`. -/
def hintOK (n k : ℕ) (G H' : List (List ℕ)) (pts : List ℕ) (L : Array (List ℕ)) : Bool :=
  H'.all (fun g => g.length == n + k) && sameRes n G H' &&
    H'.all (fun g => pts.all fun i =>
      setEq (L.getD (ap g i) []) ((L.getD i []).map fun t => ap g (n + t) - n)) &&
    pts.any (fun i => pts.any fun j => !setEq (L.getD i []) (L.getD j [])) &&
    pts.all (fun i => (L.getD i []).all (· < k))

/-- The smallest block containing `B` for the group `H` on `[0, k)` (at most `k` rounds). -/
def blockGen (H : List (List ℕ)) : ℕ → List ℕ → List ℕ
  | 0, B => B
  | r + 1, B =>
    let B' := H.foldl (fun acc g =>
      let gB := acc.map (ap g)
      if gB.any (· ∈ acc) then acc ++ gB.filter (· ∉ acc) else acc) B
    if B'.length == B.length then B else blockGen H r B'

/-- The group `H` (image lists on `[0, k)`) is primitive: every pair generates the whole set as
a block. -/
def primitive (k : ℕ) (H : List (List ℕ)) : Bool :=
  (List.range k).all fun a => (List.range k).all fun b =>
    a == b || (blockGen H k [a, b]).length == k

/-- The action of `H'` (degree `n + k`) on the new base `[n, n + k)`, as image lists on `[0, k)`. -/
def baseAct (n k : ℕ) (H' : List (List ℕ)) : List (List ℕ) :=
  H'.map fun g => (List.range k).map fun t => ap g (n + t) - n

/-! ### M0 -/

/-- **M0** against brute force: the hint check, `k` new base points, and the action on the
blocks primitive (the blocks are maximal). -/
def m0OK (n : ℕ) (gs : List (List ℕ)) (k : ℕ) : Bool :=
  match runDirect (m0Prog (D := Ty.unit) n n (gD gs) (WinData.ofPoints n (List.range n))) with
  | some (G', (w', L')) =>
    let H' := closure (n + k) (G'.2.1.map img)
    G'.1 == n + k && w'.1 == List.range n && L'.size == n &&
      hintOK n k (closure n gs) H' (List.range n) L' &&
      (List.range n).all (fun i => (L'.getD i []).length == 1) &&
      primitive k (baseAct n k H')
  | none => false

def d4 : List (List ℕ) := [[1, 2, 3, 0], [0, 3, 2, 1]]
def s4 : List (List ℕ) := [[1, 0, 2, 3], [1, 2, 3, 0]]
def d6 : List (List ℕ) := [[1, 2, 3, 4, 5, 0], [0, 5, 4, 3, 2, 1]]

/-! ### M1 -/

/-- The orbits of `G` (image lists on `[0, N)`) on the base `[n, N)`, as base indices. -/
def baseOrbits (n N : ℕ) (G : List (List ℕ)) : List (List ℕ) :=
  ((List.range (N - n)).map fun j => (G.map fun g => ap g (n + j) - n).dedup).dedup.map
    fun o => (List.range (N - n)).filter (· ∈ o)

/-- The labels restricted to the orbit `o` are not constant on `pts`. -/
def ncB (o : List ℕ) (pts : List ℕ) (L : Array (List ℕ)) : Bool :=
  pts.any fun i => pts.any fun j =>
    !setEq ((L.getD i []).filter (· ∈ o)) ((L.getD j []).filter (· ∈ o))

/-- **M1** against brute force: the hint check, and the new labels are the old ones restricted
to a base orbit with non-constant labels (renumbered by the new group's action). -/
def m1OK (n N : ℕ) (gs : List (List ℕ)) (pts : List ℕ) (L : Array (List ℕ)) : Bool :=
  let G := closure N gs
  let cands := (baseOrbits n N G).filter fun o => ncB o pts L
  match runDirect (m1Prog (D := Ty.unit) n N (N, gD gs, ()) (WinData.ofPoints N pts) L) with
  | some (G', (_, L')) =>
    let k := G'.1 - n
    let H' := closure (n + k) (G'.2.1.map img)
    hintOK n k G H' pts L' &&
      cands.any (fun o => o.length == k &&
        pts.all fun i => (L'.getD i []).length == ((L.getD i []).filter (· ∈ o)).length)
  | none => false

/-! ### M2a -/

/-- **M2a** against brute force: the hint check, and each new label is the set of blocks met
(the fixture's labels meet one block each). -/
def m2aOK (n N : ℕ) (gs : List (List ℕ)) (pts : List ℕ) (L : Array (List ℕ))
    (bs : List (List ℕ)) : Bool :=
  match runDirect (m2aProg (D := Ty.unit) n N (gD gs) (WinData.ofPoints N pts) L bs) with
  | some (G', (_, L')) =>
    let k := bs.length
    let H' := closure (n + k) (G'.2.1.map img)
    G'.1 == n + k && hintOK n k (closure N gs) H' pts L' &&
      pts.all fun i => setEq (L'.getD i [])
        ((List.range k).filter fun t => (L.getD i []).any fun j => n + j ∈ bs.getD t [])
  | none => false

/-! ### M2b -/

/-- `h` is in the coset `r H`: `r⁻¹ h ∈ H`, tested as `h = r ∘ e` for some `e ∈ H`. -/
def inCoset (H : List (List ℕ)) (r h : List ℕ) : Bool := H.any fun e => compose r e == h

/-- The re-based group is exactly `H` acting on the strings and on the block's points (in
order): the same set of pairs (strings, base action). -/
def rebaseOK (n : ℕ) (B₀ : List ℕ) (H H' : List (List ℕ)) : Bool :=
  let k := B₀.length
  let exp := H.map fun h =>
    h.take n ++ (List.range k).map fun t => n + B₀.idxOf (ap h (B₀.getD t 0))
  sameSet exp (H'.map (·.take (n + k)))

/-- **M2b** against brute force: the stabilizer of block `t`, the cover, the re-based
stabilizer, and the labels intersected with the block. -/
def m2bOK (n N : ℕ) (gs : List (List ℕ)) (bs : List (List ℕ)) (t : ℕ) (L : Array (List ℕ))
    (pts : List ℕ) : Bool :=
  let G := closure N gs
  let B₀ := bs.getD t []
  let stab := G.filter fun g => setEq (B₀.map (ap g)) B₀
  match runDirect (m2bProg (D := Ty.unit) n N (gD gs) bs t L pts) with
  | some ((H, reps), (H', L')) =>
    let Hc := closure N (H.2.1.map img)
    let k := B₀.length
    sameSet Hc stab && reps.length ≤ bs.length &&
      G.all (fun g => (reps.map img).any fun r => inCoset Hc r g) &&
      H'.1 == n + k && rebaseOK n B₀ Hc (closure (n + k) (H'.2.1.map img)) &&
      pts.all fun i => setEq (L'.getD i [])
        ((List.range k).filter fun s => B₀.getD s 0 - n ∈ L.getD i [])
  | none => false

def c4b : List (List ℕ) := [[1, 2, 3, 0, 5, 6, 7, 4]]
def c8b : List (List ℕ) := [[1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8]]

/-! ### The Johnson fallback -/

/-- **The Johnson fallback** against brute force: for a group at degree `n + m` (re-based onto
the cells) and the union cells `cl`, the pointwise stabilizer of their positions `n + c`, a
cover by at most `|cl|!` representatives. -/
def fallbackOK (n m : ℕ) (gs : List (List ℕ)) (cl : List ℕ) : Bool :=
  let G := closure (n + m) gs
  let stab := G.filter fun g => cl.all fun c => ap g (n + c) == n + c
  match runDirect (jfallbackProg (D := Ty.unit) n (n + m, gD gs, ()) cl) with
  | some (H, reps) =>
    let Hc := closure (n + m) (H.2.1.map img)
    sameSet Hc stab && reps.length ≤ cl.length.factorial &&
      G.all (fun g => (reps.map img).any fun r => inCoset Hc r g)
  | none => false

/-! ### Coloured Johnson -/

/-- The decoded colour at `u` (`cjcol`, on data). -/
def colB (m : ℕ) (e : CJData) (u : ℕ) : ℕ :=
  if u ∈ jrest m e.1 then get e.2 u + 1 else 0

/-- `σ` carries the coloured structure `e` to `e'`: the embedding (stage 14d's leaf data) and
the colours of the rest. -/
def cjMaps (m : ℕ) (σ : List ℕ) (e e' : CJData) : Bool :=
  GraphIsoChecks.Align.outMaps m (ofList σ) (GraphIsoChecks.Align.johnOut e.1)
    (GraphIsoChecks.Align.johnOut e'.1) &&
    (List.range m).all fun u => colB m e' (ap σ u) == colB m e u

/-- **Coloured Johnson** against brute force over `Sym(m)`: the generated group is the
stabilizer of order `order`, the search finds an isomorphism exactly when brute force does,
and the programs equal the data functions. -/
def cjOK (m : ℕ) (e e' : CJData) (order : ℕ) : Bool :=
  let gs := cjohnGensD m e
  let H := closure m (gs.map img)
  let P := GraphIsoChecks.Align.perms m
  H.length == order && sameSet H (P.filter fun σ => cjMaps m σ e e) &&
    GraphIsoChecks.Align.gsEq (runP (cjohnGensProg m e)) gs &&
    GraphIsoChecks.Align.optEq (runP (cjohnIsoProg m e e')) (cjohnIsoD m e e') &&
    match cjohnIsoD m e e' with
    | some σ => P.any (fun τ => cjMaps m τ e e') && cjMaps m (img σ) e e'
    | none => !P.any fun τ => cjMaps m τ e e'

/-- `V₀ = {0, 1}`, cells `{2}, {3}`, `s = 1`, the rest `{4, 5}`. -/
def jc6 : JData := ([0, 1], [[2], [3]], 1, #[[0], [1], [], [], [], []])
/-- A relabelling: `V₀ = {2, 3}`, cells `{0}, {1}`, the rest `{4, 5}`. -/
def jc6' : JData := ([2, 3], [[0], [1]], 1, #[[], [], [0], [1], [], []])

/-! ### Kernel-checked examples -/

example : m0OK 4 d4 2 = true := by decide +kernel
example : m0OK 4 s4 4 = true := by decide +kernel
example : m1OK 4 8 [[1, 0, 2, 3, 5, 4, 6, 7]] [0, 1] #[[0, 2], [1, 2], [], []] = true := by
  decide +kernel
example : m2aOK 4 8 c4b [0, 1, 2, 3] #[[0], [1], [2], [3]] [[4, 6], [5, 7]] = true := by
  decide +kernel
example : m2bOK 4 8 c4b [[4, 6], [5, 7]] 0 #[[0, 1], [1, 2], [2, 3], [3, 0]] [0, 1, 2, 3] =
    true := by decide +kernel
example : fallbackOK 0 4 [[1, 0, 2, 3], [0, 1, 3, 2]] [2, 3] = true := by decide +kernel
/-- Equal colours on the rest: stabilizer of order 4; a relabelling is isomorphic. -/
example : cjOK 6 (jc6, #[0, 0, 0, 0, 0, 0]) (jc6', #[0, 0, 0, 0, 0, 0]) 4 = true := by
  decide +kernel
/-- Different colours on the rest: stabilizer of order 2; the relabelling with equal colours is
not isomorphic (a different colour profile). -/
example : cjOK 6 (jc6, #[0, 0, 0, 0, 0, 1]) (jc6', #[0, 0, 0, 0, 0, 0]) 2 = true := by
  decide +kernel

/-! ### Derived hints (`deriveProg`) -/

/-- A group on `[m]` acting on the string positions `[0, m)` and the base `[m, 2m)` alike. -/
def alike (gs : List (List ℕ)) : List (List ℕ) := gs.map fun p => p ++ p.map (· + p.length)

/-- No structure (any tag but `2`). -/
def noSt : ℕ × CJData := (0, (([], [], 0, #[]), #[]))

/-- **A derived-hint fixture**: the parent hint `(G, w, L)` at degree `N` with string positions
`[0, n)`, the reduced group `K ≤ G`, a `K`-orbit `O` of the window, and the structure. -/
structure DFix where
  n : ℕ
  N : ℕ
  G : List (List ℕ)
  w : List ℕ
  L : Array (List ℕ)
  K : List (List ℕ)
  O : List ℕ
  st : ℕ × CJData

/-- `deriveProg` run with the verified oracle. -/
def runD (f : DFix) : Option (DOut Ty.unit) :=
  runDirect (deriveProg (D := Ty.unit) f.n f.N (f.N, gD f.K, ()) f.O f.L f.st)

/-- `deriveModel` with the verified oracle. -/
def modelD (f : DFix) : DOut Ty.unit := deriveModel ssOracle f.n f.N (f.N, gD f.K, ()) f.O f.L f.st

/-- Group data with lists in place of arrays (the kernel does not reduce equality of arrays). -/
def gdL (G : GroupData Ty.unit.denote) : ℕ × List (List ℕ × List ℕ) :=
  (G.1, G.2.1.map GraphIsoChecks.Align.pdL)

/-- An output with lists in place of arrays. -/
def outL (o : DOut Ty.unit) :=
  (o.1, (gdL o.2.1.1, gdL o.2.1.2.1, o.2.1.2.2.map GraphIsoChecks.Align.pdL),
    (gdL o.2.2.1, (o.2.2.2.1.1, o.2.2.2.1.2.toList), o.2.2.2.2.toList))

/-- The orbit of `u` under the elements `H` (image lists). -/
def orbitB (H : List (List ℕ)) (u : ℕ) : List ℕ := (H.map fun g => ap g u).dedup

/-- The orbits of `H` meeting `O` (with repetitions). -/
def orbitsIn (H : List (List ℕ)) (O : List ℕ) : List (List ℕ) := O.map (orbitB H)

/-- The cosets `r R` of the representatives cover `P`. -/
def coverB (P R reps : List (List ℕ)) : Bool := P.all fun g => reps.any fun r => inCoset R r g

/-- **The setting** (`DSetting` on data, by brute force): the parent hint is valid at degree
`N` (`hintOK`), `G` is transitive on `w`, preserves the base and is faithful on the string
positions, `K ≤ G`, and `O` is a `K`-orbit inside `w`. -/
def settingOK (f : DFix) : Bool :=
  let G := closure f.N f.G
  let K := closure f.N f.K
  let m := f.N - f.n
  hintOK f.n m G G f.w f.L && f.w.all (fun u => setEq (orbitB G u) f.w) &&
    G.all (fun g => (List.range m).all fun j => f.n ≤ ap g (f.n + j)) &&
    G.all (fun g => g.take f.n != List.range f.n || g == List.range f.N) &&
    K.all (· ∈ G) && f.O.dedup.length == f.O.length && f.O.all (· ∈ f.w) &&
    setEq (orbitB K (f.O.headD 0)) f.O

/-- The Johnson union (cell indices) of the label of the point `i`, by brute force: the cells of
its points in `V₀`. -/
def unionAt (f : DFix) (i : ℕ) : List ℕ :=
  let jd := f.st.2.1
  (List.range jd.2.1.length).filter fun c =>
    ((f.L.getD i []).filter (· ∈ jd.1)).any fun v => c ∈ jd.2.2.2.getD v []

/-- `K` re-based onto the cells, by brute force: every element acting on the strings and on the
cells (positions `n + c`). -/
def cellRebase (f : DFix) : List (List ℕ) :=
  let cs := f.st.2.1.2.1
  ((closure f.N f.K).map fun g => g.take f.n ++ (List.range cs.length).map fun c =>
    f.n + ((List.range cs.length).find? (fun c' =>
      setEq ((cs.getD c []).map fun j => ap g (f.n + j) - f.n) (cs.getD c' [])) |>.getD c)).dedup

/-- **The outcome** of the tag (`DOutcome` on data, by brute force), with the child's window `O`
(at the child's degree) and its action on the string positions that of the group it comes from
(`sameRes`, inside `hintOK`):
* `0`: the labels are constant on `O`, `2|O| ≤ |w|`, the child is `K`;
* `1`: the hint check of the child, `4(N' − n) ≤ 3m`;
* `2`: the same with `2(N' − n) ≤ m`;
* `3`: `P` acts on the strings as `K`, `R ≤ P`, the `reps` cover `P` by cosets of `R`, at most
  `m` of them, `2(N' − n) ≤ m`, and the hint check of the child (`R` re-based) on every
  `R`-orbit in `O`;
* `4`: the child is `K` re-based onto the cells (`cellRebase`), at most `3m/4` of them, with the
  Johnson unions as labels, and the hint check;
* `5`: `P` is `K` re-based onto the cells, `R` the pointwise stabilizer in `P` of the positions
  of the union cells `U` of the first point of `O`, the `reps` cover `P`, at most `|U|!` of
  them, the child is `R`, and every `R`-orbit in `O` has at most `|O|/2` points. -/
def outcomeOK (f : DFix) (o : DOut Ty.unit) : Bool :=
  let n := f.n
  let m := f.N - n
  let K := closure f.N f.K
  let P := closure o.2.1.1.1 (o.2.1.1.2.1.map img)
  let R := closure o.2.1.1.1 (o.2.1.2.1.2.1.map img)
  let reps := o.2.1.2.2.map img
  let N' := o.2.2.1.1
  let H' := closure N' (o.2.2.1.2.1.map img)
  let L' := o.2.2.2.2
  let U := (unionAt f (f.O.headD 0)).map (n + ·)
  o.2.2.2.1.1 == f.O && o.2.2.2.1.2.size == N' &&
  match o.1 with
  | 0 => 2 * f.O.length ≤ f.w.length && N' == f.N && sameSet H' K &&
    f.O.all fun i => setEq (f.L.getD i []) (f.L.getD (f.O.headD 0) [])
  | 1 => 4 * (N' - n) ≤ 3 * m && hintOK n (N' - n) K H' f.O L'
  | 2 => 2 * (N' - n) ≤ m && hintOK n (N' - n) K H' f.O L'
  | 3 => sameRes n K P && R.all (· ∈ P) && coverB P R reps && reps.length ≤ m &&
    2 * (N' - n) ≤ m && (orbitsIn R f.O).all fun O' => hintOK n (N' - n) R H' O' L'
  | 4 => 4 * (N' - n) ≤ 3 * m && sameSet H' (cellRebase f) &&
    f.O.all (fun i => setEq (L'.getD i []) (unionAt f i)) && hintOK n (N' - n) K H' f.O L'
  | 5 => sameRes n K P && sameSet P (cellRebase f) &&
    sameSet R (P.filter fun g => U.all fun u => ap g u == u) && coverB P R reps &&
    reps.length ≤ U.length.factorial && N' == o.2.1.1.1 && sameSet H' R &&
    (orbitsIn R f.O).all fun O' => 2 * O'.length ≤ f.O.length
  | _ => false

/-- **A derived hint against brute force**: the setting holds, and the program's output equals
`deriveModel`'s, has the tag `tag`, satisfies its outcome and the test `extra`. -/
def deriveWith (f : DFix) (tag : ℕ) (extra : DOut Ty.unit → Bool) : Bool :=
  settingOK f &&
  match runD f with
  | some o => outL o == outL (modelD f) && o.1 == tag && outcomeOK f o && extra o
  | none => false

/-- `deriveWith` without an extra test. -/
def deriveOK (f : DFix) (tag : ℕ) : Bool := deriveWith f tag fun _ => true

/-- **The stuck control**: the setting holds, the program's output equals the model's and has
tag `6`, and `K`'s base action is transitive and primitive (so `K` preserves no colored
partition of blocks of at most `3m/4` points). -/
def stuckOK (f : DFix) : Bool :=
  let m := f.N - f.n
  let B := baseAct f.n m (closure f.N f.K)
  settingOK f && setEq (orbitB B 0) (List.range m) && primitive m B &&
  match runD f with
  | some o => outL o == outL (modelD f) && o.1 == 6
  | none => false

/-- `K` preserves the partition `p` of the base into blocks of `t` points (one colour), with
`2 ≤ t` and `4t ≤ 3m`. -/
def partPres (f : DFix) (p : List (List ℕ)) (t : ℕ) : Bool :=
  let m := f.N - f.n
  setEq p.flatten (List.range m) && p.flatten.length == m && p.all (·.length == t) && 2 ≤ t &&
    4 * t ≤ 3 * m &&
    (closure f.N f.K).all fun g => p.all fun B => p.any fun B' =>
      setEq (B.map fun j => ap g (f.n + j) - f.n) B'

def c4 : List (List ℕ) := [[1, 2, 3, 0]]
def r2 : List (List ℕ) := [[2, 3, 0, 1]]

/-- Tag 0: `C₄` with labels `{i, i + 2}`; `K = ⟨(0 2)(1 3)⟩`, `O = {0, 2}`. -/
def fx0 : DFix := ⟨4, 8, alike c4, [0, 1, 2, 3], #[[0, 2], [1, 3], [0, 2], [1, 3]], alike r2,
  [0, 2], noSt⟩
/-- Tag 1: `C₄` with labels `{i}`; `K = ⟨(0 2)(1 3)⟩`, `O = {0, 2}` (a base orbit of 2 points). -/
def fx1 : DFix := ⟨4, 8, alike c4, [0, 1, 2, 3], #[[0], [1], [2], [3]], alike r2, [0, 2], noSt⟩
/-- Tag 2: `K = G = C₄` with labels `{i}` (blocks `{0, 2}, {1, 3}`, not equidistributed). -/
def fx2 : DFix := ⟨4, 8, alike c4, [0, 1, 2, 3], #[[0], [1], [2], [3]], alike c4, [0, 1, 2, 3],
  noSt⟩
/-- Tag 3: `K = G = C₄` with labels `{i, i + 1}` (equidistributed over the blocks). -/
def fx3 : DFix := ⟨4, 8, alike c4, [0, 1, 2, 3], #[[0, 1], [1, 2], [2, 3], [3, 0]], alike c4,
  [0, 1, 2, 3], noSt⟩

/-- **A Johnson structure** on a base of `m = 12` points (the audit's family `4, 4, 1, 1` with
`r = 2`): the cells `A = {6, 7}`, `B = {8, 9}`, `C = {10}`, `D = {11}`, `s = 2`, and `V₀` the six
pairs `AB, AC, AD, BC, BD, CD` (points `0, …, 5`); no rest. -/
def j12 : JData :=
  ([0, 1, 2, 3, 4, 5], [[6, 7], [8, 9], [10], [11]], 2,
    #[[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]])
def cj12 : CJData := (j12, #[])

theorem j12_cells : (jdec 12 j12).Λ = {{6, 7}, {8, 9}, {10}, {11}} := by decide +kernel

/-- **`IsJohnson`** (`5 < |V₀| = 6`, `s = 2`, `2s ≤ |Λ| = 4`), field by field (three fields by
cases: decided whole, they exceed the kernel's recursion depth). -/
theorem j12_johnson : SplitJohnson.IsJohnson Finset.univ 5 (jdec 12 j12) := by
  constructor
  case cells_ne =>
    intro a ha
    rw [j12_cells] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel
  case cells_disj =>
    intro a ha b hb hne
    rw [j12_cells] at ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  case surj =>
    have hp : (jdec 12 j12).Λ.powersetCard 2 = {(jdec 12 j12).f 0, (jdec 12 j12).f 1,
        (jdec 12 j12).f 2, (jdec 12 j12).f 3, (jdec 12 j12).f 4, (jdec 12 j12).f 5} := by
      decide +kernel
    intro T hT
    change T ∈ (jdec 12 j12).Λ.powersetCard 2 at hT
    rw [hp] at hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide +kernel, rfl⟩
    · exact ⟨1, by decide +kernel, rfl⟩
    · exact ⟨2, by decide +kernel, rfl⟩
    · exact ⟨3, by decide +kernel, rfl⟩
    · exact ⟨4, by decide +kernel, rfl⟩
    · exact ⟨5, by decide +kernel, rfl⟩
  all_goals decide +kernel

theorem j12_shape : JShape 12 j12 := by
  constructor
  case trim =>
    intro v hv
    have hv6 : 6 ≤ v := by simp [j12] at hv; omega
    simp [jfl, j12, Array.getD, show ¬ v < 6 by omega]
  all_goals decide +kernel

/-- **`JValid`**, from the shape and `IsJohnson`. -/
theorem j12_valid : JValid 12 j12 := jvalid_of_isJohnson j12_shape j12_johnson

/-- **The colour bound of `deriveCJ_ne_stuck`** (with `m = 12 ≥ 5`): outside `V₀` every colour
class has at most `m/2` points (the six cell points have colour `0`; there is no rest). -/
theorem j12_colours : ∀ c, 2 * (Finset.univ.filter fun x : Fin 12 =>
    x ∉ (jdec 12 j12).V0 ∧ cjcol 12 cj12 x = c).card ≤ 12 := by
  intro c
  by_cases hc : c = 0
  · subst hc; decide +kernel
  · have he : (Finset.univ.filter fun x : Fin 12 =>
        x ∉ (jdec 12 j12).V0 ∧ cjcol 12 cj12 x = c) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      have h0 : ∀ x : Fin 12, cjcol 12 cj12 x = 0 := by decide +kernel
      exact hc ((Finset.mem_filter.mp hx).2.2 ▸ h0 x)
    rw [he]
    decide

/-- `K = C₂ ≀ C₂` (order 8) at degree `4 + 12`, mirrored on four string positions (fibres
`{0, 1}`, `{2, 3}`): the swap inside `A` with `(0 1)`, the swap inside `B` with `(2 3)`, and
`A ↔ B` (`AC ↔ BC`, `AD ↔ BD`) with `(0 2)(1 3)`. -/
def k12 : List (List ℕ) :=
  [[1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10, 12, 13, 14, 15],
    [0, 1, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 14, 15],
    [2, 3, 0, 1, 4, 7, 8, 5, 6, 9, 12, 13, 10, 11, 14, 15]]

/-- Tag 4: the labels `{AC}` and `{BC}`, inside `V₀`, with Johnson unions `{A, C} ≠ {B, C}`. -/
def fxU : DFix := ⟨4, 16, k12, [0, 1, 2, 3], #[[1], [1], [3], [3]], k12, [0, 1, 2, 3], (2, cj12)⟩
/-- Tag 5: the labels `{AC, BD}` and `{AD, BC}`, inside `V₀`, with one Johnson union
`{A, B, C, D}`; in `K` re-based onto the cells (`A ↔ B` with `(0 2)(1 3)`, order 8) its
pointwise stabilizer is the kernel of the cell action (order 4: the swaps inside `A` and `B`,
with orbits `{0, 1}`, `{2, 3}` in `O`), of index 2. -/
def fxF : DFix := ⟨4, 16, k12, [0, 1, 2, 3], #[[1, 4], [1, 4], [2, 3], [2, 3]], k12, [0, 1, 2, 3],
  (2, cj12)⟩

/-- Tag 6: `K = G = C₃` with labels `{i}` (a primitive base action, no structure). -/
def fx6 : DFix := ⟨3, 6, alike [[1, 2, 0]], [0, 1, 2], #[[0], [1], [2]], alike [[1, 2, 0]],
  [0, 1, 2], noSt⟩

/-- A preserved colored partition: `K = G = C₆` with labels `{i}`. -/
def fxP : DFix := ⟨6, 12, alike [[1, 2, 3, 4, 5, 0]], List.range 6,
  #[[0], [1], [2], [3], [4], [5]], alike [[1, 2, 3, 4, 5, 0]], List.range 6, noSt⟩

/-- The Johnson structure is preserved by `K` (brute force, `cjMaps`). -/
def cjPres (f : DFix) : Bool :=
  let m := f.N - f.n
  (baseAct f.n m (closure f.N f.K)).all fun σ => cjMaps m σ f.st.2 f.st.2

example : deriveOK fx0 0 = true := by decide +kernel
example : deriveOK fx1 1 = true := by decide +kernel
example : deriveOK fx2 2 = true := by decide +kernel
example : deriveOK fx3 3 = true := by decide +kernel
example : (cjPres fxU && deriveOK fxU 4) = true := by decide +kernel
/-- The fallback: two representatives (the index of the cell-action kernel), not the `8` of the
pointwise stabilizer of the union's points. -/
example : (cjPres fxF && deriveWith fxF 5 fun o => o.2.1.2.2.length == 2) = true := by
  decide +kernel
/-- **The negative control**: with no structure and a primitive base action, `deriveProg` is
stuck; the progress theorems' hypotheses (a preserved structure) are needed. -/
example : stuckOK fx6 = true := by decide +kernel
/-- **Progress with a preserved colored partition** (`derivePart_ne_stuck`): `C₆` preserves
`{0, 2, 4}, {1, 3, 5}` (`t = 3`) and `{0, 3}, {1, 4}, {2, 5}` (`t = 2`), with `4t ≤ 3m`, and the
tag is `2` (block labels), not `6`; `C₄` (fixtures 2 and 3, tags 2 and 3) preserves
`{0, 2}, {1, 3}`. -/
example : (partPres fxP [[0, 2, 4], [1, 3, 5]] 3 && partPres fxP [[0, 3], [1, 4], [2, 5]] 2 &&
    deriveOK fxP 2 && partPres fx2 [[0, 2], [1, 3]] 2 && partPres fx3 [[0, 2], [1, 3]] 2) =
    true := by decide +kernel

/-! ### Interpreter runs (supplementary) -/

#eval check "M0 on D₆ (six string positions): maximal blocks, the hint check" fun _ =>
  m0OK 6 d6 2 || m0OK 6 d6 3
#eval check "M1 with a base of six points (orbits {0, 1}, {2, 3}, {4}, {5}; two candidates)"
    fun _ => m1OK 3 9 [[1, 0, 2, 4, 3, 6, 5, 7, 8]] [0, 1] #[[0, 2], [1, 3], []]
#eval check "M2b on C₈ (strings and base alike) with blocks of four points" fun _ =>
  m2bOK 8 16 c8b [[8, 10, 12, 14], [9, 11, 13, 15]] 0
    #[[0, 1], [1, 2], [2, 3], [3, 4], [4, 5], [5, 6], [6, 7], [7, 0]] (List.range 8)
#eval check "coloured Johnson with a rest of three points (colours 0, 0, 1)" fun _ =>
  cjOK 7 (([0, 1], [[2], [3]], 1, #[[0], [1], [], [], [], [], []]), #[0, 0, 0, 0, 0, 0, 1])
    (([2, 3], [[0], [1]], 1, #[[], [], [0], [1], [], [], []]), #[0, 0, 0, 0, 1, 0, 0]) 4

end GraphIsoChecks.MainHints
