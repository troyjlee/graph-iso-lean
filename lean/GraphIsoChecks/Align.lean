module

public import GraphIsoChecks.Sims
meta import GraphIsoChecks.Sims
public import GraphIso.Align.SetOps
meta import GraphIso.Align.SetOps
public import GraphIso.Align.JohnOps
meta import GraphIso.Align.JohnOps
public import GraphIso.Align.AlignProg
meta import GraphIso.Align.AlignProg
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14f checks: structures on the base and Align

Checks of the stage 14f programs (`GraphIso/Align/`), each comparing a program's result with a
brute-force value computed in the same term.

**Kernel-checked examples** (`decide +kernel`), on bases of three and four points:
* **Structures**, for each kind:
  - sets (`setOps`): `{0, 2}` in `[4]`;
  - colored partitions (`partOps`): two blocks of two colours in `[4]`, and two blocks of one
    colour;
  - trimmed Johnson embeddings (`johnOps`): `V₀ = {0, 1}`, cells `{2}`, `{3}`, `s = 1`.

  Each kind is checked as follows:
  - the generator program equals the data function, and every generator stabilizes the
    structure;
  - the group they generate is exactly the brute-force stabilizer, over all of `Sym(4)`;
  - the isomorphism program equals the search, and its `some σ` carries the structure to the
    target;
  - `none` occurs exactly when brute force finds no isomorphism.

  Structures are compared through stage 14d's `actOutD` and `outEqD`, which decide equality of
  the decoded structures (`decodeOut_actOutD`, `outEqD_iff`).
* **Parity inside `P`** (`stabInPProg`, `isoInPProg`):
  - flags from membership in `Alt(4)` or `Sym(4)`;
  - the generated group is exactly the brute-force `Stab(X) ∩ P`;
  - the isomorphism inside `P` is correct;
  - `none` when every isomorphism is odd and the stabilizer is even (a partition of `[4]` into
    singletons of distinct colours, against its image under a transposition).
* **Align** (`alignProg`):
  - the fixture: `S₃` and `A₃` acting on the points of `[3]` (string positions `0–2`) and on
    the base `3–5`;
  - strings: colourings of `[3]`; the structure: the set of base points coloured `1`;
  - backend and sub-solver: Schreier–Sims, with milestone 1's solver as the sub-solver
    (`sub := .recur` inside `simsSolver`);
  - the answer equals the brute-force isomorphism coset.

**Interpreter runs** (`#eval`, each throwing on a failure), supplementary, on larger bases:
* **Sets** in `[5]`.
* **Colored partitions** in `[5]` and `[6]`; the stabilizer `S₂ ≀ S₃` has order 48.
* **Trimmed Johnson embeddings:**
  - `V₀ = {0, 1}`, cells `{2, 3}`, `{4, 5}`, the rest `{6, 7}`, `s = 1`: order 16, compared
    with brute force over `Sym(8)`;
  - `V₀` the six pairs of four singleton cells, `s = 2`: order 24 = `|Sym(4)|`, since an
    element is determined by its action on the cells. Every element of the generated group
    stabilizes the structure; no brute force over `Sym(10)`.
  - Each with isomorphisms to relabelled copies and a `none` against a different profile.
* **Parity inside `Alt(5)`** and **`Sym(5)`**.
* **Align with `S₃` and `A₃`:**
  - a non-isomorphic pair (no isomorphism);
  - a candidate list with an extra structure that no isomorphism reaches;
  - a pair whose structure isomorphism is odd and is corrected inside `A₃`.

The whole file (kernel checks and interpreter runs) compiles in about a minute.
-/

@[expose] public section

namespace GraphIsoChecks.Align

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims GraphIso.Align
  GraphIso.SoJTree GraphIsoChecks.Sims GraphIsoChecks.Sweep Pointwise

/-- Run a program with no backend calls. -/
def runP {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-- Run a program with the Schreier–Sims backend, inside the solver as recursive procedure (the
sub-solver `fun J => .recur J` is milestone 1's solver). -/
def runR {t : Ty} (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (simsSolver.proc Ty.denote) 100000000 (p.subst ssImpl)).map Prod.fst

def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-! ### Brute force -/

/-- Insert `a` at every position of a list. -/
def insAll (a : ℕ) : List ℕ → List (List ℕ)
  | [] => [[a]]
  | x :: xs => (a :: x :: xs) :: (insAll a xs).map (x :: ·)

/-- All permutations of `[m]`, as image lists, by structural recursion (the kernel does not
reduce `List.permutations`, which is defined by well-founded recursion). -/
def perms : ℕ → List (List ℕ)
  | 0 => [[]]
  | m + 1 => (perms m).flatMap (insAll m)

/-- Two lists of permutations are equal as sets. -/
def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

/-- The parity of an image list. -/
def isEven (m : ℕ) (p : List ℕ) : Bool :=
  ((List.range m).flatMap fun i => ((List.range m).filter (i < ·)).map fun j => (i, j)).countP
    (fun q => p.getD q.1 0 > p.getD q.2 0) % 2 == 0

/-- A list of permutations as image lists. -/
def imgs (gs : List PermData) : List (List ℕ) := gs.map img

/-- Permutation data as two lists (the kernel does not reduce equality of arrays). -/
def pdL (g : PermData) : List ℕ × List ℕ := (g.1.toList, g.2.toList)

/-- A program's list of permutations equals `gs`. -/
def gsEq (o : Option (List PermData)) (gs : List PermData) : Bool :=
  match o with
  | some l => l.map pdL == gs.map pdL
  | none => false

/-- A program's optional permutation equals `r`. -/
def optEq (o : Option (Option PermData)) (r : Option PermData) : Bool :=
  match o, r with
  | some (some a), some b => pdL a == pdL b
  | some none, none => true
  | _, _ => false

/-! ### Structures: sets -/

/-- `σ` maps the set `l` onto `l'`. -/
def setMaps (m : ℕ) (σ : PermData) (l l' : List ℕ) : Bool :=
  setEqD m (l.filter (· < m) |>.map (get σ.1)) l'

/-- Generators of the stabilizer of a set against brute force. -/
def setGensOK (m : ℕ) (l : List ℕ) : Bool :=
  let gs := (setOps m).gens l
  gsEq (runP (setGensProg m l)) gs && gs.all (fun g => setMaps m g l l) &&
    sameSet (closure m (imgs gs)) ((perms m).filter fun p => setMaps m (ofList p) l l)

/-- The isomorphism search for sets against brute force. -/
def setIsoOK (m : ℕ) (l l' : List ℕ) : Bool :=
  let r := (setOps m).iso l l'
  optEq (runP (setIsoProg m l l')) r &&
    match r with
    | some σ => PermData.validB m σ && setMaps m σ l l'
    | none => !(perms m).any fun p => setMaps m (ofList p) l l'

/-! ### Structures: colored partitions and trimmed Johnson embeddings, through leaf data -/

/-- `σ` carries the leaf `o` to `o'` (decoded: `outEqD_iff`, `decodeOut_actOutD`). -/
def outMaps (m : ℕ) (σ : PermData) (o o' : OutD) : Bool := outEqD m (actOutD m σ o) o'

def partOut (x : Array ℕ × Array (List ℕ)) : OutD := partD x.1 x.2

/-- Generators of the stabilizer of a colored partition against brute force. -/
def partGensOK (m : ℕ) (x : Array ℕ × Array (List ℕ)) : Bool :=
  let gs := (partOps m).gens x
  gsEq (runP (partGensProg m x)) gs && gs.all (fun g => outMaps m g (partOut x) (partOut x)) &&
    sameSet (closure m (imgs gs))
      ((perms m).filter fun p => outMaps m (ofList p) (partOut x) (partOut x))

/-- The isomorphism search for colored partitions against brute force. -/
def partIsoOK (m : ℕ) (x y : Array ℕ × Array (List ℕ)) : Bool :=
  let r := (partOps m).iso x y
  optEq (runP (partIsoProg m x y)) r &&
    match r with
    | some σ => PermData.validB m σ && outMaps m σ (partOut x) (partOut y)
    | none => !(perms m).any fun p => outMaps m (ofList p) (partOut x) (partOut y)

def johnOut (d : JData) : OutD := johnD d.1 d.2.1 d.2.2.1 d.2.2.2

/-- Generators of the stabilizer of a trimmed Johnson embedding against brute force (`full`:
over all of `Sym(m)`; otherwise only that the generators stabilize, and the group's order). -/
def johnGensOK (m : ℕ) (d : JData) (full : Bool) (order : ℕ) : Bool :=
  let gs := (johnOps m).gens d
  let H := closure m (imgs gs)
  gsEq (runP (johnGensProg m d)) gs &&
    gs.all (fun g => outMaps m g (johnOut d) (johnOut d)) &&
    H.length == order &&
    (if full then sameSet H ((perms m).filter fun p => outMaps m (ofList p) (johnOut d) (johnOut d))
      else H.all fun p => outMaps m (ofList p) (johnOut d) (johnOut d))

/-- The isomorphism search for trimmed Johnson embeddings; `expect` is the brute-force answer
asserted (brute force over `Sym(m)` when `full`). -/
def johnIsoOK (m : ℕ) (d d' : JData) (full expect : Bool) : Bool :=
  let r := (johnOps m).iso d d'
  optEq (runP (johnIsoProg m d d')) r &&
    (!full || (perms m).any (fun p => outMaps m (ofList p) (johnOut d) (johnOut d')) == expect) &&
    match r with
    | some σ => expect && PermData.validB m σ && outMaps m σ (johnOut d) (johnOut d')
    | none => !expect

/-! ### Parity inside `P` -/

/-- Flag the stabilizer's generators by membership in `Alt(m)` (`alt`) or `Sym(m)`. -/
def flags (m : ℕ) (alt : Bool) (gs : List PermData) : List (PermData × Bool) :=
  gs.map fun g => (g, !alt || isEven m (img g))

/-- `Stab(X) ∩ P` and the isomorphism inside `P`, for colored partitions, against brute force. -/
def inPOK (m : ℕ) (alt : Bool) (x y : Array ℕ × Array (List ℕ)) : Bool :=
  let inP := fun p => !alt || isEven m p
  let gfs := flags m alt ((partOps m).gens x)
  let Ls := stabInPL gfs
  let exists_ := (perms m).any fun p => inP p && outMaps m (ofList p) (partOut x) (partOut y)
  gsEq (runP (stabInPProg gfs)) Ls &&
    sameSet (closure m (imgs Ls))
      ((perms m).filter fun p => inP p && outMaps m (ofList p) (partOut x) (partOut x)) &&
    match (partOps m).iso x y with
    | some σ =>
      let r := isoInPL gfs σ (inP (img σ))
      optEq (runP (isoInPProg gfs σ (inP (img σ)))) r &&
        match r with
        | some π => exists_ && inP (img π) && outMaps m π (partOut x) (partOut y)
        | none => !exists_
    | none => !exists_

/-! ### Align -/

/-- The group of the fixture: permutations `p` of `[3]` acting on the string positions `0–2` and
on the base `3–5` alike. -/
def both3 (p : List ℕ) : List ℕ := p ++ p.map (· + 3)

def grp3 (gs : List (List ℕ)) : GroupData Ty.unit.denote := (6, gs.map (ofList ∘ both3), ())

/-- The permutation of `[3]` read off the base positions. -/
def baseOf3 (g : PermData) : List ℕ := (List.range 3).map fun a => get g.1 (3 + a) - 3

def S3 : List (List ℕ) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
def A3 : List (List ℕ) := [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
def sym3 : List (List ℕ) := [[1, 0, 2], [1, 2, 0]]
def alt3 : List (List ℕ) := [[1, 2, 0]]

/-- A colouring of `[3]` as a string of degree 6. -/
def col3 (l : List ℕ) : StrData := (l ++ [0, 0, 0]).toArray

/-- The canonical structure of a colouring: the base points coloured `1`. -/
def ones (l : List ℕ) : List ℕ := (List.range 3).filter fun i => l.getD i 0 == 1

def win3 : WinData := WinData.ofPoints 6 [0, 1, 2]

def sub : InstData Ty.unit → Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  fun J => Prog.recur J

/-- The brute-force isomorphisms in `G`: `x u = y (g u)` on the window. -/
def isoB (G : List (List ℕ)) (x y : List ℕ) : List (List ℕ) :=
  G.filter fun g => (List.range 3).all fun u => x.getD u 0 == y.getD (g.getD u 0) 0

/-- `alignProg` on sets, against the brute-force isomorphism coset. -/
def alignOK (G gs : List (List ℕ)) (x y : List ℕ) (Ys : List (List ℕ)) : Bool :=
  let B := isoB G x y
  match runR (alignProg sub (fun l => setGensProg 3 l) (fun l l' => setIsoProg 3 l l') 3
      (col3 x, col3 y) win3 (grp3 gs) (ones x) Ys) with
  | some (some (σ, (_, hs, _))) =>
    sameSet ((closure 3 (hs.map baseOf3)).map (compose (baseOf3 σ))) B
  | some none => B.isEmpty
  | none => false

/-! ### Interpreter runs (supplementary) -/

/-- A partition of `[5]`: colour `0` on `{0, 1}`, `1` on `{2, 3}`, `2` on `{4}`. -/
def p5 : Array ℕ × Array (List ℕ) := (#[0, 0, 1, 1, 2], #[[0, 1], [0, 1], [2, 3], [2, 3], [4]])
/-- Its relabelling by `(0 4)(1 3)`-like moves: colour `0` on `{3, 4}`, `1` on `{0, 2}`. -/
def p5' : Array ℕ × Array (List ℕ) := (#[1, 2, 1, 0, 0], #[[0, 2], [1], [0, 2], [3, 4], [3, 4]])
/-- Three blocks of one colour in `[6]` (stabilizer `S₂ ≀ S₃`, order 48). -/
def p6 : Array ℕ × Array (List ℕ) :=
  (#[0, 0, 0, 0, 0, 0], #[[0, 1], [0, 1], [2, 3], [2, 3], [4, 5], [4, 5]])
/-- Two blocks of size three in `[6]`: not isomorphic to `p6`. -/
def q6 : Array ℕ × Array (List ℕ) :=
  (#[0, 0, 0, 0, 0, 0], #[[0, 1, 2], [0, 1, 2], [0, 1, 2], [3, 4, 5], [3, 4, 5], [3, 4, 5]])

/-- `V₀ = {0, 1}`, cells `{2, 3}`, `{4, 5}`, the rest `{6, 7}`, `s = 1`. -/
def j8 : JData := ([0, 1], [[2, 3], [4, 5]], 1, #[[0], [1], [], [], [], [], [], []])
/-- A relabelling of `j8`. -/
def j8' : JData := ([6, 7], [[0, 1], [2, 3]], 1, #[[], [], [], [], [], [], [1], [0]])
/-- A different profile: cells `{2}`, `{3, 4, 5}`. -/
def j8'' : JData := ([0, 1], [[2], [3, 4, 5]], 1, #[[0], [1], [], [], [], [], [], []])

/-- The six pairs of four singleton cells `{6}, …, {9}`, `s = 2`. -/
def j10 : JData :=
  ([0, 1, 2, 3, 4, 5], [[6], [7], [8], [9]], 2,
    #[[0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3], [], [], [], []])
/-- A relabelling of `j10`: cells listed in another order. -/
def j10' : JData :=
  ([4, 5, 6, 7, 8, 9], [[3], [2], [1], [0]], 2,
    #[[], [], [], [], [0, 1], [0, 2], [0, 3], [1, 2], [1, 3], [2, 3]])

#eval check "sets in [5]: stabilizer of {0, 2} (order 12); {0, 2} ≅ {1, 4}; ≇ {0, 1, 2}" fun _ =>
  (setGensOK 5 [0, 2] && setIsoOK 5 [0, 2] [1, 4] && setIsoOK 5 [0, 2] [0, 1, 2])
#eval check "partitions: [5] three colours (order 4), [6] S₂ ≀ S₃ (order 48), isomorphisms"
    fun _ =>
  (partGensOK 5 p5 && partGensOK 6 p6 && (closure 6 (imgs ((partOps 6).gens p6))).length == 48 &&
    partIsoOK 5 p5 p5' && partIsoOK 6 p6 q6)
#eval check "Johnson j8: stabilizer of order 16 over Sym(8); ≅ a relabelling; ≇ another profile"
    fun _ =>
  (johnGensOK 8 j8 true 16 && johnIsoOK 8 j8 j8' true true && johnIsoOK 8 j8 j8'' true false)
#eval check "Johnson j10 (s = 2, four cells): stabilizer of order 24; ≅ a relabelling" fun _ =>
  (johnGensOK 10 j10 false 24 && johnIsoOK 10 j10 j10' false true &&
    johnIsoOK 10 j10 j8 false false)
#eval check "parity inside Alt(5) and Sym(5): Stab(X) ∩ P, isomorphisms inside P" fun _ =>
  (inPOK 5 true p5 p5' && inPOK 5 false p5 p5' &&
    inPOK 5 true (#[0, 1, 2, 3, 4], #[[0], [1], [2], [3], [4]])
      (#[1, 0, 2, 3, 4], #[[0], [1], [2], [3], [4]]))
#eval check "alignProg in S3 and A3: no isomorphism; an extra candidate; parity corrected"
    fun _ =>
  (alignOK S3 sym3 [0, 0, 1] [1, 1, 0] [ones [1, 1, 0]] &&
    alignOK S3 sym3 [0, 0, 1] [1, 0, 0] [[1], ones [1, 0, 0]] &&
    alignOK A3 alt3 [0, 0, 1] [0, 1, 0] [ones [0, 1, 0]] &&
    alignOK A3 alt3 [1, 0, 0] [0, 1, 0] [[2], ones [0, 1, 0]])

/-! ### Kernel-checked examples -/

/-- A partition of `[4]`: colour `0` on `{0, 1}`, colour `1` on `{2, 3}`. -/
def p4 : Array ℕ × Array (List ℕ) := (#[0, 0, 1, 1], #[[0, 1], [0, 1], [2, 3], [2, 3]])
/-- A relabelling: colour `0` on `{1, 3}`, colour `1` on `{0, 2}`. -/
def p4' : Array ℕ × Array (List ℕ) := (#[1, 0, 1, 0], #[[0, 2], [1, 3], [0, 2], [1, 3]])
/-- Two blocks of one colour (stabilizer `S₂ ≀ S₂`, order 8): not isomorphic to `p4`. -/
def r4 : Array ℕ × Array (List ℕ) := (#[0, 0, 0, 0], #[[0, 1], [0, 1], [2, 3], [2, 3]])
/-- Singletons of distinct colours, and their image under the transposition `(0 1)`. -/
def s4 : Array ℕ × Array (List ℕ) := (#[0, 1, 2, 3], #[[0], [1], [2], [3]])
def s4' : Array ℕ × Array (List ℕ) := (#[1, 0, 2, 3], #[[0], [1], [2], [3]])

/-- `V₀ = {0, 1}`, cells `{2}`, `{3}`, `s = 1`, and a relabelling. -/
def j4 : JData := ([0, 1], [[2], [3]], 1, #[[0], [1], [], []])
def j4' : JData := ([2, 3], [[0], [1]], 1, #[[], [], [1], [0]])
/-- One cell of two points: a different profile. -/
def j4'' : JData := ([0, 1], [[2, 3]], 1, #[[0], [0], [], []])

/-- Sets: the stabilizer of `{0, 2}` in `Sym(4)`; `{0, 2} ≅ {1, 3}`; `≇ {0}`. -/
example : (setGensOK 4 [0, 2] && setIsoOK 4 [0, 2] [1, 3] && setIsoOK 4 [0, 2] [0]) = true := by
  decide +kernel
/-- Colored partitions: stabilizers of `p4` and `r4`; `p4 ≅ p4'`; `p4 ≇ r4`. -/
example : (partGensOK 4 p4 && partGensOK 4 r4 && partIsoOK 4 p4 p4' && partIsoOK 4 p4 r4) = true :=
  by decide +kernel
/-- Trimmed Johnson embeddings: the stabilizer of `j4` (order 2); `j4 ≅ j4'`; `j4 ≇ j4''`. -/
example : (johnGensOK 4 j4 true 2 && johnIsoOK 4 j4 j4' true true &&
    johnIsoOK 4 j4 j4'' true false) = true := by decide +kernel
/-- Parity inside `Alt(4)` and `Sym(4)`; with `s4`, every isomorphism to `s4'` is odd and the
stabilizer is trivial, so there is none inside `Alt(4)`. -/
example : (inPOK 4 true p4 p4' && inPOK 4 false p4 p4' && inPOK 4 true s4 s4' &&
    inPOK 4 false s4 s4') = true := by decide +kernel
/-- Align in `S₃`: the structure isomorphism and the solver on the aligned coset. -/
example : alignOK S3 sym3 [0, 0, 1] [1, 0, 0] [ones [1, 0, 0]] = true := by decide +kernel
/-- Align in `A₃`: the structure isomorphism is corrected to an even one. -/
example : alignOK A3 alt3 [0, 0, 1] [0, 1, 0] [ones [0, 1, 0]] = true := by decide +kernel

end GraphIsoChecks.Align
