module

public import GraphIsoChecks.Sims
meta import GraphIsoChecks.Sims
public import GraphIsoChecks.SoJTree
meta import GraphIsoChecks.SoJTree
public import GraphIsoChecks.Align
meta import GraphIsoChecks.Align
public import GraphIso.Case2b.Case2bProg
meta import GraphIso.Case2b.Case2bProg
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14h checks: Case 2b

Checks of the stage 14h programs and data models (`GraphIso/Case2b/`), each comparing a result
with brute force (or with milestone 11's model) computed in the same term. Backend programs run
with the Schreier–Sims backend inside the solver procedure, so the sub-solver
`fun J => .recur J` is milestone 1's solver; the data models use the Schreier–Sims oracle
`ssOracle`. The fixtures are permutation groups `F` of a base `[m]`, given at degree `2m`
(acting on the string positions `[0, m)` and the base `[m, 2m)` alike), with the large orbit
`Φ` the whole base: `C₄`, `D₄`, `C₅`, `D₅` (degree of transitivity `d = 1`), `AGL(1, 5)` and
`PSL(2, 5)` on the projective line (`d = 2`, so one point is individualized), and `S₅` on the
ten pairs of `[5]` (the Petersen graph's vertices, `d = 1`). The brute force enumerates group
elements (`closure`), orbitals, a classical 2-dimensional Weisfeiler–Leman refinement written
here (`wlRound`, compared by the partition of the pairs it induces, since colour names differ),
components of colour graphs, and isomorphisms.

**Kernel-checked examples** (`decide +kernel`):
* **The enumerations**: `tuplesD`, `pairsD`, `phiSD` and their programs against structural brute
  force.
* **The orbital colouring** (data model: `F_(S)` by the backend, restricted to `Φ ∖ S`, the
  orbital array): `C₄` with `S = ∅` and `AGL(1, 5)` with `S = {2}`, against brute-force orbitals;
  and a control: `C₄`'s colouring is not `D₄`'s.
* **The degree of transitivity** (`degD`, `degProg`) of `C₄`.
* **One choice of `C₄`** (`choiceProg`, `colProg`, interpreter runs): the WL colouring against
  the brute-force refinement, the components leaf of the least disconnected colour against
  brute-force components, and the validity of the leaf (a colored partition of the base).
* **The leaves on a colouring against milestone 11's model** (`leavesMatch`): `leavesOfD` on
  `C₄`'s colouring is exactly the partition into the components of the least disconnected
  colour, and on `C₅`'s colouring the trimmed leaves of `soj` as a multiset; controls: `[none]`
  and the components of a wrong colour are rejected.
* **`case2bProg` end to end** with the verified Schreier–Sims oracle answering the backend calls
  (`runDirect`), on the empty window with `F(x) = F(y)` the Klein group on `[4]` (`d = 1`) and
  `G = S₄`, the large orbit listed in two orders, and the correct sub-solver of the empty window:
  the degrees, the first leaf, all twelve leaves, Align over every aligned coset and the
  combination; the answer is all of `S₄` (the 24 permutations), so the aligned cosets cover the
  group.
* **The complete leaf lists and their canonicity**: all twelve leaves of the Klein group, with
  multiplicity, for `Φ` listed in two orders, equal as multisets, and equal to the images by
  `σ = (0 1 3 2)` (which normalizes the group and preserves `Φ`).
* **`outOps` on Johnson leaves** (`s = 2`, stage 14f's `j10`): an isomorphism found, program
  and data generators equal, and both cross-kind searches rejected.
* **Trimming and extension**: a Johnson leaf whose cell lists reach outside `V₀` and a colored
  partition, extended from `Fin 3` along `[0, 2, 4]`, against `pipeExt ∘ trimOut`; a components
  leaf extended with a nonempty rest; and a control: without trimming the Johnson leaf differs.
* **Canonicity of one choice**: the choice `(σ 0, σ 1)` for `σ C₄ σ⁻¹` has the images by `σ` of
  the leaves of the choice `(0, 1)` for `C₄`.
* **The isomorphism search of `outOps`** between components leaves (isomorphic and not).

**Interpreter runs** (`#eval`, each throwing on a failure), supplementary:
* the degree of transitivity of `D₄`, `C₅`, `D₅` (1), `AGL(1, 5)`, `PSL(2, 5)` (2) and `S₅` on
  the pairs (1), data model and program against brute force;
* one choice for `D₄` (components), `C₅`, `D₅` (`soj`), `AGL(1, 5)` with `S = {2}`
  (components, a nonempty rest), `PSL(2, 5)` with `S = {5}` (`soj`), and `S₅` on the pairs
  (`soj`, two pairs);
* the `soj` step against milestone 11's `soj` on the computed colourings of `C₅`, `PSL(2, 5)`
  and `S₅` on the pairs;
* all choices (`allLeavesD`, `allLeavesProg`, `firstLeafProg`): the program equals the data
  model, the data model is the concatenation over the brute-force tuples and pairs, with 12,
  12, 100 and 60 leaves for `C₄`, `D₄`, `C₅`, `AGL(1, 5)`, all valid;
* **canonicity of the structure lists** over all choices: the leaves for `σ F σ⁻¹`, `σ Φ` are
  the images by `σ` of the leaves for `F`, `Φ` (`C₄`, `C₅`, `AGL(1, 5)`), and for one choice
  with an individualized point (`AGL(1, 5)`);
* **`case2bProg`** in `S₄` acting on graphs with four vertices (the six pairs as string
  positions, the four vertices as the base), with `F(x) = Aut(x)`, `F(y) = Aut(y)` (canonical)
  and `Φ` the four vertices: two 4-cycles (8 isomorphisms), a 4-cycle and two disjoint edges
  (none, after Align finds isomorphic structures), two copies of two disjoint edges (8), and a
  4-cycle and `K₄` (the degrees of transitivity differ: none), against the brute-force
  isomorphism coset.

**Not kernel-checked, and why.** Milestone 10's array Weisfeiler–Leman (`wlA`) does not reduce
in the kernel, so the data models that contain it (`wlColOf`, `choiceLeavesD`, `allLeavesD`,
`firstLeafD`) are checked through interpreter runs of the programs (`colProg`, `choiceProg`,
which do reduce) or by `#eval`. The tree model `case2bTree` itself is not evaluated: its
colouring is milestone 11's `wlRel`, which reruns Weisfeiler–Leman at every query (a comparison
on `C₄` did not finish in ten minutes); its pieces are checked instead (the orbitals, the
refinement's partition, the leaves on the computed colouring against milestone 11's `soj`, the
extension against `pipeExt`). `case2bProg` is kernel-checked end to end with the verified
oracle on the empty window (above); with a nonempty window and milestone 1's solver as the
sub-solver, run through the PHOAS Schreier–Sims implementation, a kernel run did not finish in
fifteen minutes, so the graph instances are interpreter runs; one choice of `AGL(1, 5)` takes
about 90 s in the kernel, also an interpreter run. The tree's leaves are colored partitions in
all fixtures: Johnson leaves need a big colour class, which small fixtures do not have;
trimming and extending a Johnson leaf, and `outOps` on Johnson leaves, are checked directly.

The whole file compiles in about four minutes.
-/

@[expose] public section

namespace GraphIsoChecks.Case2b

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims
  GraphIso.Case2b GraphIso.SoJTree GraphIso.SoJProg GraphIso.SplitJohnson GraphIsoChecks.Sims
  GraphIsoChecks.Sweep GraphIsoChecks.SoJTree

/-- Run a program with no backend calls. -/
def runP {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-- Run a program with the Schreier–Sims backend, inside the solver as recursive procedure. -/
def runR {t : Ty} (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (simsSolver.proc Ty.denote) 100000000 (p.subst ssImpl)).map Prod.fst

def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

def sub : InstData Ty.unit → Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  fun J => Prog.recur J

def setEq (u v : List ℕ) : Bool := u.all (· ∈ v) && v.all (· ∈ u)

def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

/-! ### Fixtures: a group on the base, also acting on as many string positions -/

/-- The group data of permutations `gs` of `[m]` acting on the string positions `[0, m)` and the
base `[m, 2m)` alike. -/
def grpOf (m : ℕ) (gs : List (List ℕ)) : GroupData Ty.unit.denote :=
  (m + m, gs.map (fun p => ofList (p ++ p.map (· + m))), ())

def c4 : List (List ℕ) := [[1, 2, 3, 0]]
def d4 : List (List ℕ) := [[1, 2, 3, 0], [0, 3, 2, 1]]
def c5 : List (List ℕ) := [[1, 2, 3, 4, 0]]
def d5 : List (List ℕ) := [[1, 2, 3, 4, 0], [0, 4, 3, 2, 1]]
/-- `AGL(1, 5)`: `x ↦ x + 1` and `x ↦ 2x`. -/
def agl5 : List (List ℕ) := [[1, 2, 3, 4, 0], [0, 2, 4, 1, 3]]
/-- `PSL(2, 5)` on the projective line `{0, …, 4, ∞ = 5}`: `x ↦ x + 1` and `x ↦ −1/x`. -/
def psl25 : List (List ℕ) := [[1, 2, 3, 4, 0, 5], [5, 4, 2, 3, 1, 0]]

/-! ### Brute force -/

/-- The `j`-tuples of distinct entries of `l`, by structural recursion. -/
def tuplesB (l : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | j + 1 => (tuplesB l j).flatMap fun T => (l.filter (· ∉ T)).map (· :: T)

/-- The points of `Φ ∖ S` below `m`, in increasing order. -/
def phiSB (m : ℕ) (Φ S : List ℕ) : List ℕ := (List.range m).filter fun v => v ∈ Φ && v ∉ S

/-- The orbital of `(a, b)` (indices of `ΦS`) under the elements of `E` fixing `S`, as pairs of
indices of `ΦS`. -/
def orbitalB (E : List (List ℕ)) (S ΦS : List ℕ) (a b : ℕ) : List (ℕ × ℕ) :=
  ((E.filter fun g => S.all fun s => g.getD s 0 == s).map fun g =>
    (ΦS.idxOf (g.getD (ΦS.getD a 0) 0), ΦS.idxOf (g.getD (ΦS.getD b 0) 0))).dedup

/-- `relCol` of the orbital: `0` on the diagonal, `1` on the orbital, `2` elsewhere. -/
def relColB (R : List (ℕ × ℕ)) (u v : ℕ) : ℕ := if u == v then 0 else if (u, v) ∈ R then 1 else 2

/-- The orbital colouring as `tcolD` writes it (transposed). -/
def tcolOK (E : List (List ℕ)) (m : ℕ) (Φ S : List ℕ) (a b : ℕ) (T : Array ℕ) : Bool :=
  let ΦS := phiSB m Φ S
  let R := orbitalB E S ΦS a b
  let k := ΦS.length
  T.size == k * k &&
    (List.range k).all fun i => (List.range k).all fun j => T.getD (i * k + j) 0 == relColB R j i

/-- One round of the classical Weisfeiler–Leman refinement of a colouring `c` of the pairs of
`[k]` (row-major list): the new colour of `(u, v)` is the index of its signature, the old
colour and the numbers of `w` with each pair of colours `(c(u, w), c(w, v))`. -/
def wlRound (k : ℕ) (c : List ℕ) : List ℕ :=
  let cols := c.dedup
  let sig := fun u v => (c.getD (u * k + v) 0) ::
    (cols.flatMap fun c1 => cols.map fun c2 =>
      ((List.range k).filter fun w => c.getD (u * k + w) 0 == c1 &&
        c.getD (w * k + v) 0 == c2).length)
  let sigs := (List.range k).flatMap fun u => (List.range k).map fun v => sig u v
  let ds := sigs.dedup
  sigs.map ds.idxOf

/-- The stable refinement: refine until the number of colours stops growing (at most `k * k`
rounds). -/
def wlB (k : ℕ) (c : List ℕ) : List ℕ :=
  (List.range (k * k)).foldl (fun c _ =>
    let c' := wlRound k c
    if c'.dedup.length == c.dedup.length then c else c') c

/-- Two colourings of the pairs of `[k]` induce the same partition. -/
def samePart (k : ℕ) (c c' : List ℕ) : Bool :=
  (List.range (k * k)).all fun p => (List.range (k * k)).all fun q =>
    (c.getD p 0 == c.getD q 0) == (c'.getD p 0 == c'.getD q 0)

/-- The WL colouring of a choice (row-major, as `wlColD`) against the brute-force refinement of
the orbital colouring. -/
def wlOK (E : List (List ℕ)) (m : ℕ) (Φ S : List ℕ) (a b : ℕ) (W : List ℕ) : Bool :=
  let ΦS := phiSB m Φ S
  let R := orbitalB E S ΦS a b
  let k := ΦS.length
  let c0 := (List.range k).flatMap fun u => (List.range k).map fun v => relColB R u v
  W.length == k * k && samePart k W (wlB k c0)


/-! ### Leaves -/

/-- The component of `x` in the undirected graph of colour `r` of a row-major colouring `W` of
`[k]` (`k` rounds of growth). -/
def compB (k : ℕ) (W : List ℕ) (r x : ℕ) : List ℕ :=
  (List.range k).foldl (fun T _ => (List.range k).filter fun y =>
    y ∈ T || T.any fun z => W.getD (z * k + y) 0 == r || W.getD (y * k + z) 0 == r) [x]

/-- The disconnected off-diagonal colours of `W`. -/
def disconnB (k : ℕ) (W : List ℕ) : List ℕ :=
  (((List.range k).flatMap fun u => ((List.range k).filter (· != u)).map fun v =>
    W.getD (u * k + v) 0).dedup).filter fun r =>
    (List.range k).any fun x => (compB k W r x).length != k

/-- A colored-partition datum as a key: for each base point its colour and its block as an
increasing list (entries below `m` only). -/
def keyOf (m : ℕ) (o : OutD) : List (ℕ × List ℕ) :=
  (List.range m).map fun v =>
    (get o.2.1.1 v, (List.range m).filter fun w => w ∈ o.2.1.2.getD v [])

/-- The expected key of the components leaf of `W` on `ΦS`, extended to `[m]`. -/
def compKey (m : ℕ) (ΦS : List ℕ) (W : List ℕ) (r : ℕ) : List (ℕ × List ℕ) :=
  let k := ΦS.length
  (List.range m).map fun v =>
    if v ∈ ΦS then
      (1, (List.range m).filter fun w => w ∈ (compB k W r (ΦS.idxOf v)).map (ΦS.getD · 0))
    else (0, (List.range m).filter (· ∉ ΦS))


/-- The expected key of the leaf of `soj` at the point `x` (index of `ΦS`) when no colour class
from `x` is big: the colouring `y ↦ W(x, y)` with its classes as blocks, extended to `[m]`. -/
def colPartKey (m : ℕ) (ΦS : List ℕ) (W : List ℕ) (x : ℕ) : List (ℕ × List ℕ) :=
  let k := ΦS.length
  (List.range m).map fun v =>
    if v ∈ ΦS then
      (W.getD (x * k + ΦS.idxOf v) 0 + 1, (List.range m).filter fun w =>
        w ∈ ΦS && W.getD (x * k + ΦS.idxOf w) 0 == W.getD (x * k + ΦS.idxOf v) 0)
    else (0, (List.range m).filter (· ∉ ΦS))

/-- No colour class from any point has more than `t` points (then every leaf of `soj` is the
colouring from a point). -/
def noBig (k t : ℕ) (W : List ℕ) : Bool :=
  (List.range k).all fun x => (List.range k).all fun y =>
    ((List.range k).filter fun z => W.getD (x * k + z) 0 == W.getD (x * k + y) 0).length ≤ t

/-- Equality of lists as multisets. -/
def msEqL {α : Type} [DecidableEq α] (A B : List α) : Bool :=
  A.length == B.length && A.all fun a => A.count a == B.count a

/-- Every leaf decodes to a colored partition of `[m]` (brute force, stage 14d's `colPartB`). -/
def validB (m : ℕ) (ls : List OutD) : Bool :=
  ls.all fun o => match decodeOut m o with
    | some (.inl p) => colPartB (List.range m) p
    | _ => false

/-- **One choice `(S, (a, b))`** against brute force: the orbital colouring (data model), the
WL colouring (an interpreter run of `colProg`) against the brute-force refinement, and the
leaves (an interpreter run of `choiceProg`): the components leaf of the least disconnected
colour, or the leaves of `soj` (each the colouring from one point, when no class is big). -/
def choiceOK (m : ℕ) (gs : List (List ℕ)) (Φ S : List ℕ) (a b : ℕ) : Bool :=
  let F := grpOf m gs
  let E := closure m gs
  let ΦS := phiSB m Φ S
  let k := ΦS.length
  let G' := resModel ssOracle (m + m) m F Φ S
  tcolOK E m Φ S a b (tcolD (orbArrD ssOracle (m + m) m F Φ S) k a b) &&
  match runR (colProg G' k a b), runR (choiceProg (m + m) m F Φ S a b) with
  | some Wa, some ls =>
    let W := Wa.toList
    wlOK E m Φ S a b W && validB m ls &&
      match disconnB k W with
      | r :: rs => ls.length == 1 && ls.all (fun o => o.1 == 1 &&
          keyOf m o == compKey m ΦS W ((r :: rs).foldl min r))
      | [] => noBig k ((k + 3) / 2) W && ls.all (fun o => o.1 == 1) &&
          msEqL (ls.map (keyOf m)) ((List.range k).map (colPartKey m ΦS W))
  | _, _ => false

/-! ### The degree of transitivity -/

/-- The elements `E` act `d`-transitively on `Φ`. -/
def transB (E : List (List ℕ)) (Φ : List ℕ) (d : ℕ) : Bool :=
  (tuplesB Φ d).all fun T => E.any fun g => ((tuplesB Φ d).headD []).map (g.getD · 0) == T

/-- The largest `d ≤ |Φ|` such that the elements `E` act `d`-transitively on `Φ` (transitivity
is inherited downwards, so the count stops at the first failure). -/
def degB (E : List (List ℕ)) (Φ : List ℕ) : ℕ :=
  ((List.range Φ.length).foldl (fun st d =>
    if st.2 && transB E Φ (d + 1) then (d + 1, true) else (st.1, false)) (0, true)).1

/-- `degD` (the data model) and `degProg` (an interpreter run) against brute force. -/
def degOK (m : ℕ) (gs : List (List ℕ)) (Φ : List ℕ) : Bool :=
  let d := degB (closure m gs) Φ
  degD ssOracle (m + m) m (grpOf m gs) Φ == d && runR (degProg (m + m) m (grpOf m gs) Φ) == some d


/-! ### The `soj` step against milestone 11's model -/

/-- A list of decoded leaves against the model on the colouring `C`: if a colour is
disconnected, exactly the partition into the components of the least disconnected colour
(milestone 11's `⟨fun _ => 0, comp univ (colOf k C) r⟩`, compared by `outEqM`); otherwise the
trimmed leaves of `soj (colOf k C) ((k + 3) / 2)` as a multiset. -/
def leavesMatch (k : ℕ) (C : Array ℕ) (ls : List (Option (Out (Fin k)))) : Bool :=
  if h : (disconn Finset.univ (colOf k C)).Nonempty then
    match ls with
    | [o] => outEqM o (some (.inl ⟨fun _ => 0,
        Coherent.comp Finset.univ (colOf k C) ((disconn Finset.univ (colOf k C)).min' h)⟩))
    | _ => false
  else msEq (Multiset.ofList ls) ((soj (colOf k C) ((k + 3) / 2)).leafMs.map Align.trimOut)

/-- The leaves of `leavesOfD` on the colouring `C` against the model (`decodeOut_compLeafD`,
`disconn_wlCol`, `sojD_leafMs`, `leavesOfD_decode_soj`); `C` is a WL colouring computed by
`colProg`, so the model's colour function is an array lookup. -/
def leavesModelOK (k : ℕ) (C : Array ℕ) : Bool :=
  leavesMatch k C ((leavesOfD k C).map (decodeOut k))

/-! ### Canonicity -/

/-- The conjugate `σ g σ⁻¹` of a permutation `g` of `[m]` (image lists). -/
def conjB (m : ℕ) (σ g : List ℕ) : List ℕ :=
  (List.range m).map fun i => σ.getD (g.getD (σ.idxOf i) 0) 0

/-- **Canonicity of the structure lists**: the leaves for `σ F σ⁻¹` and `σ Φ` are the images by
`σ` of the leaves for `F` and `Φ`, as multisets of decoded leaves. -/
def canonOK (m : ℕ) (gs : List (List ℕ)) (Φ : List ℕ) (j : ℕ) (σ : List ℕ) : Bool :=
  let L := (allLeavesD ssOracle (m + m) m (grpOf m gs) Φ j).map (decodeOut m)
  let L' := (allLeavesD ssOracle (m + m) m (grpOf m (gs.map (conjB m σ))) (Φ.map (σ.getD · 0))
    j).map (decodeOut m)
  msEq (Multiset.ofList L') (Multiset.ofList (L.map (PermData.denote m (ofList σ) • ·)))

/-- **One choice and its image**: the choice `(σS, (σa, σb))` for `σ F σ⁻¹`, `σ Φ` has the
images by `σ` of the leaves of the choice `(S, (a, b))` for `F`, `Φ` (interpreter runs). -/
def canonChoiceOK (m : ℕ) (gs : List (List ℕ)) (Φ S : List ℕ) (a b : ℕ) (σ : List ℕ) : Bool :=
  let ΦS := phiSB m Φ S
  let Φ' := Φ.map (σ.getD · 0)
  let S' := S.map (σ.getD · 0)
  let ΦS' := phiSB m Φ' S'
  let a' := ΦS'.idxOf (σ.getD (ΦS.getD a 0) 0)
  let b' := ΦS'.idxOf (σ.getD (ΦS.getD b 0) 0)
  match runR (choiceProg (m + m) m (grpOf m gs) Φ S a b),
      runR (choiceProg (m + m) m (grpOf m (gs.map (conjB m σ))) Φ' S' a' b') with
  | some ls, some ls' =>
    msEq (Multiset.ofList (ls'.map (decodeOut m)))
      (Multiset.ofList (ls.map fun o => PermData.denote m (ofList σ) • decodeOut m o))
  | _, _ => false

/-! ### All choices -/

/-- `allLeavesProg` (an interpreter run) equals the data model, and the data model is the
concatenation over the brute-force tuples and pairs, with `count` leaves; every leaf is valid;
`firstLeafProg` equals its data model. -/
def allOK (m : ℕ) (gs : List (List ℕ)) (Φ : List ℕ) (j count : ℕ) : Bool :=
  let F := grpOf m gs
  let L := allLeavesD ssOracle (m + m) m F Φ j
  L.length == count && L == (tuplesB Φ j).flatMap (fun S =>
    let k := (phiSB m Φ S).length
    ((List.range k).flatMap fun a => ((List.range k).filter (· != a)).map (a, ·)).flatMap
      fun ab => choiceLeavesD ssOracle (m + m) m F Φ S ab.1 ab.2) &&
  validB m L && runR (allLeavesProg (m + m) m F Φ j) == some L &&
  runR (firstLeafProg (m + m) m F Φ j) == some (firstLeafD ssOracle (m + m) m F Φ j)


/-! ### Case 2b on graphs with four vertices -/

/-- The six pairs of `[4]`: the string positions. -/
def P4 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- The permutation of the pairs induced by a permutation `p` of `[4]`. -/
def pairPerm (p : List ℕ) : List ℕ :=
  P4.map fun ab =>
    P4.idxOf (min (p.getD ab.1 0) (p.getD ab.2 0), max (p.getD ab.1 0) (p.getD ab.2 0))

/-- Group data at degree `10`: the pairs `[0, 6)` and the base `[6, 10)` (the vertices). -/
def gGrp (gs : List (List ℕ)) : GroupData Ty.unit.denote :=
  (10, gs.map fun p => ofList (pairPerm p ++ p.map (· + 6)), ())

/-- A graph as a string on the pairs (the base positions read `0`). -/
def gStr (x : List ℕ) : StrData := (x ++ [0, 0, 0, 0]).toArray

def gWin : WinData := WinData.ofPoints 10 (List.range 6)

def sym4 : List (List ℕ) := [[1, 0, 2, 3], [1, 2, 3, 0]]

def S4 : List (List ℕ) := closure 4 sym4

/-- The permutation of the vertices read off the base positions. -/
def baseOfG (g : PermData) : List ℕ := (List.range 4).map fun a => get g.1 (6 + a) - 6

/-- The isomorphisms of graphs in `S₄`: `x u = y (g u)` on the pairs. -/
def isoG (x y : List ℕ) : List (List ℕ) :=
  S4.filter fun p => (List.range 6).all fun u => x.getD u 0 == y.getD ((pairPerm p).getD u 0) 0

/-- **`case2bProg`** (an interpreter run, milestone 1's solver as the sub-solver) with
`F(x) = Aut(x)`, `F(y) = Aut(y)` (canonical) and the large orbits `Φx = Φy = [4]`, against the
brute-force isomorphism coset in `S₄`. -/
def case2bOK (x y : List ℕ) : Bool :=
  let B := isoG x y
  match runR (case2bProg sub 6 (gStr x, gStr y) gWin (gGrp sym4) (gGrp (isoG x x))
      (gGrp (isoG y y)) [0, 1, 2, 3] [0, 1, 2, 3]) with
  | some (some (σ, (_, hs, _))) =>
    sameSet ((closure 4 (hs.map baseOfG)).map (compose (baseOfG σ))) B
  | some none => B.isEmpty
  | none => false


/-- `leavesModelOK` on the WL colouring of a choice, computed by `colProg`. -/
def leavesModelFor (m : ℕ) (gs : List (List ℕ)) (Φ S : List ℕ) (a b : ℕ) : Bool :=
  match runR (colProg (resModel ssOracle (m + m) m (grpOf m gs) Φ S) (phiSB m Φ S).length a b)
  with
  | some C => leavesModelOK (phiSB m Φ S).length C
  | none => false

/-- The isomorphism search of `outOps` between two leaves of one tree (data and program agree,
and a found permutation carries one decoded leaf to the other). -/
def outIsoOK (m : ℕ) (o o' : OutD) : Bool :=
  runP (outIsoProg m o o') == some (outIsoD m o o') &&
    match outIsoD m o o' with
    | some σ => outEqM (PermData.denote m σ • decodeOut m o) (decodeOut m o')
    | none => true

/-- The ten pairs of `[5]`, and the action of `S₅` on them (the Petersen graph's vertices). -/
def P5 : List (ℕ × ℕ) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (a < ·)).map (a, ·)

def pairPerm5 (p : List ℕ) : List ℕ :=
  P5.map fun ab =>
    P5.idxOf (min (p.getD ab.1 0) (p.getD ab.2 0), max (p.getD ab.1 0) (p.getD ab.2 0))

/-- `S₅` acting on the ten pairs: rank 3, transitive and not doubly transitive (`d = 1`). -/
def petersen : List (List ℕ) := [pairPerm5 [1, 0, 2, 3, 4], pairPerm5 [1, 2, 3, 4, 0]]


/-! ### Trimming and extension of a Johnson leaf -/

/-- A Johnson leaf on `Fin 3`: `V₀ = {0}`, cells `{1}`, `{2}`, `s = 1`, with cell lists also off
`V₀` (which trimming removes). -/
def jLeaf : OutD := johnD [0] [[1], [2]] 1 #[[0], [1], [0]]

/-- Trimming then extending along `ΦS` decodes to the model's `pipeExt ∘ trimOut`. -/
def extTrimOK (m : ℕ) (ΦS : List ℕ) (h : ∀ v ∈ ΦS, v < m) (o : OutD) : Bool :=
  outEqM (decodeOut m (extD m ΦS (trimD ΦS.length o)))
    (pipeExt (eFin ΦS h) (eInv ΦS) (Align.trimOut (decodeOut ΦS.length o)))


/-! ### End-to-end runs with the verified oracle (from the round 1 audit) -/

/-- Run a program with the verified Schreier–Sims oracle directly: the PHOAS program is
executed, its backend calls answered by `ssOracle` (not expanded into PHOAS). -/
def runDirect {t : Ty} (p : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval ssOracle (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-- The correct sub-solver for an empty window: the whole input coset is the answer. -/
def emptySub (I : InstData Ty.unit) :
    Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  .bind (.op1 (.snd (a := Ty.strs) (b := .prod Ty.win (Ty.coset Ty.unit))) I) fun wC =>
    .bind (.op1 (.snd (a := Ty.win) (b := Ty.coset Ty.unit)) wC) fun C => .op1 .some C

/-- The Klein four-group on `[4]`: transitive, not doubly transitive (`d = 1`). -/
def klein : List (List ℕ) := [[1, 0, 3, 2], [2, 3, 0, 1]]

/-- `S₄` and the Klein group on the base `[4]` alone (no string positions). -/
def g4 : GroupData Ty.unit.denote := (4, sym4.map ofList, ())
def f4 : GroupData Ty.unit.denote := (4, klein.map ofList, ())

/-- `case2bProg` on the empty window with `F(x) = F(y)` the Klein group and `Φ` the base listed
in two orders: the degrees, the first leaf, all twelve leaves, Align over every aligned coset,
and the combination. -/
def emptyCase : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  case2bProg emptySub 0 (#[], #[]) (WinData.ofPoints 4 []) g4 f4 f4 [0, 1, 2, 3] [3, 1, 0, 2]

/-- The answer is all of `S₄` (every permutation is an isomorphism on the empty window), so the
aligned cosets cover the group. -/
def answerIsS4 : Bool :=
  match runDirect emptyCase with
  | some (some (σ, (_, hs, _))) =>
    sameSet ((closure 4 (hs.map fun g => g.1.toList)).map (compose σ.1.toList))
      (GraphIsoChecks.Align.perms 4)
  | _ => false

/-- **The complete leaf lists and their canonicity**: all twelve leaves (with multiplicity) for
`Φ` listed in two orders agree, and equal the images by `σ = (0 1 3 2)` of each other's
(`σ` normalizes the Klein group and preserves `Φ`). -/
def allLeavesDirect : Bool :=
  match runDirect (allLeavesProg 4 0 f4 [0, 1, 2, 3] 0),
      runDirect (allLeavesProg 4 0 f4 [3, 1, 0, 2] 0) with
  | some L, some L' =>
    L.length == 12 && L'.length == 12 &&
      msEq (Multiset.ofList (L.map (decodeOut 4))) (Multiset.ofList (L'.map (decodeOut 4))) &&
      msEq (Multiset.ofList (L'.map (decodeOut 4)))
        (Multiset.ofList (L.map fun o => PermData.denote 4 (ofList [1, 3, 0, 2]) • decodeOut 4 o))
  | _, _ => false

def johnsonOut : OutD := GraphIsoChecks.Align.johnOut GraphIsoChecks.Align.j10
def johnsonOut' : OutD := GraphIsoChecks.Align.johnOut GraphIsoChecks.Align.j10'

/-- **`outOps` on Johnson leaves** (`s = 2`, stage 14f's `j10`): the isomorphism search finds
an isomorphism, program and data agree on the generators, and both cross-kind searches fail. -/
def johnsonDispatch : Bool :=
  outIsoOK 10 johnsonOut johnsonOut' && (outIsoD 10 johnsonOut johnsonOut').isSome &&
    runP (outGensProg 10 johnsonOut) == some (outGensD 10 johnsonOut) &&
    (outIsoD 10 johnsonOut (partD #[] #[])).isNone && (outIsoD 10 (partD #[] #[]) johnsonOut).isNone

/-! ### Fixture constants -/

/-- The WL colouring of the choice `(0, 1)` of `C₄` on `[4]` (as `colProg` computes it): the
diagonal, the two directions of the cycle and the opposite pairs. -/
def wC4 : List ℕ := [0, 1, 3, 2, 2, 0, 1, 3, 3, 2, 0, 1, 1, 3, 2, 0]

/-- The WL colouring of the choice `(0, 1)` of `C₅` on `[5]`: the five differences. -/
def wC5 : List ℕ := [0, 1, 3, 4, 2, 2, 0, 1, 3, 4, 4, 2, 0, 1, 3, 3, 4, 2, 0, 1, 1, 3, 4, 2, 0]

def full4 : List ℕ := [0, 1, 2, 3]
def full5 : List ℕ := [0, 1, 2, 3, 4]
def full6 : List ℕ := [0, 1, 2, 3, 4, 5]

/-- Graphs on `[4]` as strings on the pairs `01, 02, 03, 12, 13, 23`. -/
def cyc4 : List ℕ := [1, 0, 1, 1, 0, 1]
def cyc4' : List ℕ := [0, 1, 1, 1, 1, 0]
def twoK2 : List ℕ := [1, 0, 0, 0, 0, 1]
def twoK2' : List ℕ := [0, 1, 0, 0, 1, 0]
def k4 : List ℕ := [1, 1, 1, 1, 1, 1]

/-! ### Interpreter runs (supplementary) -/

#eval check "the degree of transitivity: D4, C5, D5 (1), AGL(1,5), PSL(2,5) (2), S5 on pairs (1)"
  fun _ => degOK 4 d4 full4 && degOK 5 c5 full5 && degOK 5 d5 full5 && degOK 5 agl5 full5 &&
    degOK 6 psl25 full6 && degOK 10 petersen (List.range 10)
#eval check "one choice: D4 (components), C5, D5 (soj), AGL(1,5) with S = {2} (components), \
    PSL(2,5) with S = {5} (soj), S5 on the ten pairs (soj, two pairs)" fun _ =>
  choiceOK 4 d4 full4 [] 0 1 && choiceOK 5 c5 full5 [] 0 1 && choiceOK 5 d5 full5 [] 0 2 &&
    choiceOK 5 agl5 full5 [2] 0 1 && choiceOK 6 psl25 full6 [5] 0 1 &&
    choiceOK 10 petersen (List.range 10) [] 0 1 && choiceOK 10 petersen (List.range 10) [] 0 9
#eval check "the soj step against milestone 11's model on computed colourings: C5, PSL(2,5) \
    with S = {5}, S5 on the ten pairs" fun _ =>
  leavesModelFor 5 c5 full5 [] 0 1 && leavesModelFor 6 psl25 full6 [5] 0 1 &&
    leavesModelFor 10 petersen (List.range 10) [] 0 1
#eval check "all choices: the program, the data model and the brute-force enumeration agree, \
    every leaf valid (C4: 12, D4: 12, C5: 100, AGL(1,5): 60 leaves)" fun _ =>
  allOK 4 c4 full4 0 12 && allOK 4 d4 full4 0 12 && allOK 5 c5 full5 0 100 &&
    allOK 5 agl5 full5 1 60
#eval check "canonicity of the structure lists (all choices): C4, C5, AGL(1,5)" fun _ =>
  canonOK 4 c4 full4 0 [1, 3, 0, 2] && canonOK 5 c5 full5 0 [2, 0, 4, 1, 3] &&
    canonOK 5 agl5 full5 1 [2, 0, 4, 1, 3]
#eval check "canonicity of one choice with an individualized point: AGL(1,5)" fun _ =>
  canonChoiceOK 5 agl5 full5 [2] 0 1 [2, 0, 4, 1, 3]
#eval check "case2bProg in S4 on graphs with four vertices: two 4-cycles (8 isomorphisms), a \
    4-cycle and 2K2 (none), two 2K2 (8), a 4-cycle and K4 (degrees differ, none)" fun _ =>
  (isoG cyc4 cyc4').length == 8 && case2bOK cyc4 cyc4' && (isoG cyc4 twoK2).isEmpty &&
    case2bOK cyc4 twoK2 && (isoG twoK2 twoK2').length == 8 && case2bOK twoK2 twoK2' &&
    (isoG cyc4 k4).isEmpty && case2bOK cyc4 k4

/-! ### Kernel-checked examples -/

/-- The enumerations: the 2-tuples of distinct points of `[5]`, the pairs below `4`, `Φ ∖ S`;
data and programs against structural brute force. -/
example : (sameSet (tuplesD full5 2) (tuplesB full5 2) && (tuplesD full5 2).length == 20 &&
    runP (tuplesProg full5 2) == some (tuplesD full5 2) &&
    sameSet ((pairsD 4).map fun ab => [ab.1, ab.2])
      ((tuplesB full4 2).map fun T => [T.getD 1 0, T.getD 0 0]) &&
    runP (pairsProg 4) == some (pairsD 4) &&
    phiSD 6 [0, 2, 3, 5] [3] == phiSB 6 [0, 2, 3, 5] [3] &&
    runP (phiSProg 6 [0, 2, 3, 5] [3]) == some [0, 2, 5]) = true := by
  decide +kernel

/-- The orbital colouring (data model: the pointwise stabilizer, the restriction to `Φ ∖ S`,
the backend's orbital array): `C₄` with `S = ∅`, and `AGL(1, 5)` with `S = {2}` (whose
stabilizer acts on the other four points as `C₄`), against brute-force orbitals. -/
example : (tcolOK (closure 4 c4) 4 full4 [] 0 1
      (tcolD (orbArrD ssOracle 8 4 (grpOf 4 c4) full4 []) 4 0 1) &&
    tcolOK (closure 5 agl5) 5 full5 [2] 0 1
      (tcolD (orbArrD ssOracle 10 5 (grpOf 5 agl5) full5 [2]) 4 0 1)) = true := by
  decide +kernel

/-- The check discriminates: the orbital colouring of `C₄` is not that of `D₄`. -/
example : tcolOK (closure 4 d4) 4 full4 [] 0 1
    (tcolD (orbArrD ssOracle 8 4 (grpOf 4 c4) full4 []) 4 0 1) = false := by
  decide +kernel

/-- The degree of transitivity: `degD` and `degProg` against brute force, `C₄` on `[4]`. -/
example : degOK 4 c4 full4 = true := by decide +kernel

/-- **One choice of `C₄`**: the WL colouring (`colProg`) against the brute-force refinement, and
the leaf (`choiceProg`): the components of the opposite pairs, a valid colored partition. -/
example : choiceOK 4 c4 full4 [] 0 1 = true := by decide +kernel

/-- The leaves on a colouring against milestone 11's model: the components leaf (`C₄`'s
colouring) and the trimmed leaves of `soj` as a multiset (`C₅`'s colouring). -/
example : (leavesModelOK 4 wC4.toArray && leavesModelOK 5 wC5.toArray) = true := by
  decide +kernel

/-- The disconnected branch discriminates: `[none]` and the partition into the components of
the wrong colour (`1`, a 4-cycle, so one block) are rejected. -/
example : (leavesMatch 4 wC4.toArray [none] || leavesMatch 4 wC4.toArray
    [decodeOut 4 (compLeafD 4 wC4.toArray 1)]) = false := by
  decide +kernel

/-- **`case2bProg` end to end** (the verified oracle, the empty window, the Klein group): the
answer is all of `S₄`. -/
example : answerIsS4 = true := by decide +kernel

/-- **The complete leaf lists** of the Klein group: twelve leaves, independent of the listing
of `Φ`, and canonical under relabelling. -/
example : allLeavesDirect = true := by decide +kernel

/-- `outOps` on Johnson leaves, and across kinds. -/
example : johnsonDispatch = true := by decide +kernel

/-- Trimming and extension: a Johnson leaf with cell lists off `V₀` and a colored partition,
extended from `Fin 3` along `[0, 2, 4]`, against `pipeExt ∘ trimOut`; the components leaf of
`C₄`'s colouring extended along `[0, 1, 3, 4]` (the rest `{2}` one block of colour `0`). -/
example : (extTrimOK 5 [0, 2, 4] (by decide) jLeaf &&
    extTrimOK 5 [0, 2, 4] (by decide) (partD #[0, 1, 0] #[[0, 2], [1], [0, 2]]) &&
    keyOf 5 (extD 5 [0, 1, 3, 4] (compLeafD 4 wC4.toArray 3)) ==
      compKey 5 [0, 1, 3, 4] wC4 3) = true := by
  decide +kernel

/-- Without trimming, the Johnson leaf's extension differs from the model's. -/
example : outEqM (decodeOut 5 (extD 5 [0, 2, 4] jLeaf))
    (pipeExt (eFin [0, 2, 4] (by decide)) (eInv [0, 2, 4]) (Align.trimOut (decodeOut 3 jLeaf)))
    = false := by
  decide +kernel

/-- **Canonicity of one choice**: the choice `(σ 0, σ 1)` for `σ C₄ σ⁻¹` has the images by `σ` of
the leaves of the choice `(0, 1)` for `C₄`. -/
example : canonChoiceOK 4 c4 full4 [] 0 1 [1, 3, 0, 2] = true := by decide +kernel

/-- The isomorphism search of `outOps` between leaves: two components partitions of `[4]` into
pairs (isomorphic), and one with two colours (not). -/
example : (outIsoOK 4 (partD #[1, 1, 1, 1] #[[0, 2], [1, 3], [2, 0], [3, 1]])
      (partD #[1, 1, 1, 1] #[[0, 1], [0, 1], [2, 3], [2, 3]]) &&
    (outIsoD 4 (partD #[1, 1, 1, 1] #[[0, 2], [1, 3], [2, 0], [3, 1]])
      (partD #[1, 1, 1, 1] #[[0, 1], [0, 1], [2, 3], [2, 3]])).isSome &&
    outIsoOK 4 (partD #[1, 1, 1, 1] #[[0, 2], [1, 3], [2, 0], [3, 1]])
      (partD #[1, 1, 0, 0] #[[0, 1], [0, 1], [2, 3], [2, 3]]) &&
    (outIsoD 4 (partD #[1, 1, 1, 1] #[[0, 2], [1, 3], [2, 0], [3, 1]])
      (partD #[1, 1, 0, 0] #[[0, 1], [0, 1], [2, 3], [2, 3]])).isNone) = true := by
  decide +kernel

end GraphIsoChecks.Case2b
