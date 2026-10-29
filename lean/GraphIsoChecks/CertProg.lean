module

public import GraphIsoChecks.Sims
meta import GraphIsoChecks.Sims
public import GraphIso.CertProg.CertIso
meta import GraphIso.CertProg.CertIso
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14e checks: local certificates as programs

Runs of the stage 14e programs (`GraphIso/CertProg/`) with the Schreier–Sims backend, compared
with brute force over all group elements. The sub-solver is milestone 1's solver: the programs
run inside the procedure `simsSolver`, with `sub := fun J => .recur J`.

**Kernel-checked runs** (the end of the file; `decide +kernel`, each comparing the program's
result with a brute-force value computed in the same term), on `S₃` and `A₃` acting on the
points of `[3]` (string positions `0–2`) and on the base `3–5`:
* `stabSetProg` (`G_A` of a point), `moveProg` (in `S₃` and `A₃`), `giantAProg` (`S₃` a giant on
  `A = [3]`, `⟨(0 1)⟩` not), `affProg` (every point affected), `kerAProg` and `kerOrbitsProg` (the
  trivial kernel, six representatives covering `S₃`), `tupleTransProg` (found and not found);
* `beardStepProg` for `A = [3]` (`k = 3`): six branches, each calling the solver on the kernel's
  orbits, against the brute-force affected points and `H₁`;
* `pairLoopProg` for two different colourings, against the brute-force paired coset;
* `certProg` and `certIsoProg` for a point (`k = 1`; they need two base points outside `A`, so
  with `m = 3` only `k = 1`). With `k = 1`, `Alt(A)` is trivial, every group is a giant on `A`, no
  point is affected and the windows stay empty: these two runs exercise the programs' control
  flow, `G_A`, the move, the loop, `K(A)`, the fullness test and the tuple transporter, but not
  affected points (which the `k = 3` runs above cover). Larger `k` needs `m ≥ 5`, beyond kernel
  evaluation.

The kernel checks take about four minutes in all (the four whole-procedure runs 35–55 s each).

**Interpreter runs** (`#eval`, each throwing on a failure), supplementary, on larger fixtures:

Fixtures: a permutation group of `[m]` acting on `n` string positions and on the base
`[n, n + m)` as on `[m]`:
* `S₅` and `A₅` on the ten pairs of `[5]` (degree 15), strings graphs on `[5]` (a path with an
  extra edge, its relabelling, `C₅`), test sets of size `k = 3`;
* `S₅` and `A₅` on the points of `[5]` (degree 10), strings colourings of the points, `k = 3`;
* `S₇` on the points of `[7]` (degree 14), test set `{0, …, 4}` (`k = 5`).

Checks:
* **Item 1.** `stabSetProg` (`G_A` as a set: orders 12, 6 and 240); `moveProg` (an even
  permutation of the base mapping `T` to `T'` pointwise, in `S₅` and `A₅`, lifted to the
  degree); `giantAProg` on four subgroups (`ψ_A(H) ⊇ Alt(A)` decided by the order of the image);
  `affProg` (the pairs meeting `A`; the points of `A` for `k = 5`); `kerAProg` (the kernel
  `G_A ∩ ker ψ_A`, at most `k!` representatives, which with the kernel give `G_A`) and
  `kerOrbitsProg` (the kernel's orbits on the affected points; `k · |o| ≤ n` for `k = 5`);
  `tupleTransProg` in `G_A` (found and not found, on base and string positions).
* **Item 2.** `beardStepProg` from `G_A` (the affected points and the coset `H₁`, in `S₅` and
  `A₅`); `pairLoopProg` from `τ • G_A` for `x' ≠ x`: the final coset equals the brute-force
  paired coset (`pairCoset`: `ψ(g) A = A'`, every window `W_j` onto `W'_j`, `x` to `x'` on the
  last), nonempty for a relabelled graph and empty for a non-isomorphic one, and the window list
  is `x`'s beard window. The case `x' = x` runs inside `certProg`.
* **Item 3.** `certProg`: `W(A)`, `H(A)`, `K(A) = H(A)_(Ω ∖ W(A))` and the fullness test
  against the brute-force beard (`W_{i+1} = W_i ∪ aff(H_i)` while `ψ_A(H_i)` is a giant,
  `H_{i+1}` the elements of `H_i` preserving `W_{i+1}` and `x` on it), on the path (not full) and
  on colourings constant on `A` (full, in `S₅` and `A₅`) and not constant (not full);
  `certIsoProg` against brute-force `CertIso` (an element mapping `T` to `T'` pointwise, `W(T)`
  onto `W(T')` and `x` to `x'` on `W(T)`): equivalent for a relabelled graph and for colourings
  agreeing along the tuples, not equivalent for `path`/`C₅` and for colourings differing on `T`.

Not covered: whole certificates with `k = 5` (`S₇` on the points) take about 40 s each (the
kernel of `G_A` has 120 cosets, each branch running the solver), and steps on `S₇` acting on
the 21 pairs of `[7]` (degree 28) take minutes; so whole certificates use `k = 3`, and `k = 5` is
checked through its ingredients (`G_A`, the affected points, the kernel and its orbits). The
programs do not depend on `k ≥ 5`; only the window bound in the sub-solver hypothesis
`StepSubP` (from `kernel_orbit`) does. The interpreter runs take about 70 s.
-/

@[expose] public section

namespace GraphIsoChecks.CertProg

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Sims
  GraphIso.CertProg GraphIsoChecks.Sims GraphIsoChecks.Sweep

/-- Run a program with the Schreier–Sims backend, inside the solver as recursive procedure (the
sub-solver `fun J => .recur J` is milestone 1's solver). -/
def runR {t : Ty} (p : Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (simsSolver.proc Ty.denote) 100000000 (p.subst ssImpl)).map Prod.fst

def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-! ### Fixtures -/

/-- A fixture: `S_m` (or a subgroup) acting on `n` string positions through `str` and on the
base `[n, n + m)` as on `[m]`. -/
structure Fix where
  n : ℕ
  m : ℕ
  str : List ℕ → ℕ → ℕ

namespace Fix

variable (F : Fix)

def N : ℕ := F.n + F.m

/-- The image list of degree `n + m` of a permutation `p` of `[m]`. -/
def both (p : List ℕ) : List ℕ :=
  (List.range F.n).map (F.str p) ++ (List.range F.m).map fun a => F.n + p.getD a 0

def grp (gs : List (List ℕ)) : GroupData Ty.unit.denote := (F.N, gs.map (ofList ∘ F.both), ())

/-- The permutation of `[m]` read off the base positions. -/
def baseOf (g : PermData) : List ℕ := (List.range F.m).map fun a => get g.1 (F.n + a) - F.n

def closed (g : GroupData Ty.unit.denote) : List (List ℕ) := closure F.m (g.2.1.map F.baseOf)

def posW (al : List ℕ) : Array ℕ := WinData.pos F.N (winA F.N F.n al)
def pA (al : List ℕ) : List ℕ := (winA F.N F.n al).1
def one : PermData := ofList (List.range F.N)

end Fix

/-- `S₇` on the points: string positions `0–6`, base `7–13`. -/
def pts7 : Fix := ⟨7, 7, fun p j => p.getD j 0⟩

/-- `S₅` on the points: string positions `0–4`, base `5–9`. -/
def pts5 : Fix := ⟨5, 5, fun p j => p.getD j 0⟩

/-- The 10 pairs of `[5]`. -/
def pairs5 : List (ℕ × ℕ) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (a < ·)).map fun b => (a, b)

def pairIdx5 (a b : ℕ) : ℕ := pairs5.idxOf (min a b, max a b)

/-- `S₅` on the pairs: string positions `0–9`, base `10–14`. -/
def prs5 : Fix := ⟨10, 5, fun p j =>
  let q := pairs5.getD j (0, 0)
  pairIdx5 (p.getD q.1 0) (p.getD q.2 0)⟩

def sym7 : List (List ℕ) := [[1, 0, 2, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 0]]
def alt7 : List (List ℕ) := [[1, 2, 0, 3, 4, 5, 6], [1, 2, 3, 4, 5, 6, 0]]
def sym5 : List (List ℕ) := [[1, 0, 2, 3, 4], [1, 2, 3, 4, 0]]

def sub : InstData Ty.unit → Prog (groupSig Ty.unit) (Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  fun J => Prog.recur J

def strOf (F : Fix) (l : List ℕ) : StrData := (l ++ List.replicate F.m 0).toArray

/-! ### Brute force -/

/-- `ψ_A(H)` contains `Alt(A)`: it has at least `k!/2` elements (the subgroups of `Sym(k)` of
that order are `Alt(k)` and `Sym(k)`). -/
def giant (H : List (List ℕ)) (al : List ℕ) : Bool :=
  2 * (H.map fun p => al.map (p.getD · 0)).dedup.length ≥ al.length.factorial

def setEq (u v : List ℕ) : Bool := u.all (· ∈ v) && v.all (· ∈ u)

/-- The elements of `G_A`. -/
def stabSet (G : List (List ℕ)) (al : List ℕ) : List (List ℕ) :=
  G.filter fun p => al.all fun a => p.getD a 0 ∈ al

namespace Fix

variable (F : Fix)

/-- The image of a string position under a permutation of `[m]`. -/
def act (p : List ℕ) (j : ℕ) : ℕ := F.str p j

/-- The affected string positions. -/
def aff (H : List (List ℕ)) (al : List ℕ) : List ℕ :=
  (List.range F.n).filter fun j => !giant (H.filter fun p => F.act p j == j) al

/-- One step of the beard of `x` at `A`. -/
def bstep (x : StrData) (al : List ℕ) (st : List ℕ × List (List ℕ)) :
    List ℕ × List (List ℕ) :=
  if giant st.2 al then
    let W := (st.1 ++ aff F st.2 al).dedup
    (W, st.2.filter fun p => W.all fun u => F.act p u ∈ W && get x (F.act p u) == get x u)
  else st

/-- The beard's states after `0, …, n` steps. -/
def beards (G : List (List ℕ)) (x : StrData) (al : List ℕ) : List (List ℕ × List (List ℕ)) :=
  (List.range (F.n + 1)).foldl (fun acc _ => acc ++ [bstep F x al (acc.getLastD ([], []))])
    [([], stabSet G al)] |>.take (F.n + 1)

def beardW (G : List (List ℕ)) (x : StrData) (al : List ℕ) : List ℕ :=
  (beards F G x al).getLastD ([], []) |>.1

def beardH (G : List (List ℕ)) (x : StrData) (al : List ℕ) : List (List ℕ) :=
  (beards F G x al).getLastD ([], []) |>.2

/-- `K(A)`: the elements of `H(A)` fixing every string position outside `W(A)`. -/
def certK (G : List (List ℕ)) (x : StrData) (al : List ℕ) : List (List ℕ) :=
  (beardH F G x al).filter fun p =>
    (List.range F.n).all fun u => u ∈ beardW F G x al || F.act p u == u

/-- The paired coset after `n` steps. -/
def pairCoset (G : List (List ℕ)) (x x' : StrData) (al al' : List ℕ) : List (List ℕ) :=
  let B := beards F G x al
  let B' := beards F G x' al'
  G.filter fun g => setEq (al.map (g.getD · 0)) al' &&
    (List.range (F.n + 1)).all (fun j =>
      setEq ((B.getD j ([], [])).1.map (F.act g)) (B'.getD j ([], [])).1) &&
    (B.getLastD ([], [])).1.all fun u => get x' (F.act g u) == get x u

/-- Milestone 13's equivalence of certificates of the tuples `T`, `T'`. -/
def certIso (G : List (List ℕ)) (x x' : StrData) (T T' : List ℕ) : Bool :=
  let W := beardW F G x T
  let W' := beardW F G x' T'
  G.any fun g => (List.range T.length).all (fun i => g.getD (T.getD i 0) 0 == T'.getD i 0) &&
    setEq (W.map (F.act g)) W' && W.all fun u => get x' (F.act g u) == get x u

end Fix

/-- Two lists of permutations are equal as sets. -/
def sameSet (A B : List (List ℕ)) : Bool := A.all (· ∈ B) && B.all (· ∈ A)

def allPerms (m : ℕ) : List (List ℕ) := (List.range m).permutations

def isEven (m : ℕ) (p : List ℕ) : Bool :=
  ((List.range m).flatMap fun i => ((List.range m).filter (i < ·)).map fun j => (i, j)).countP
    (fun q => p.getD q.1 0 > p.getD q.2 0) % 2 == 0

def S5 : List (List ℕ) := allPerms 5
def A5 : List (List ℕ) := S5.filter (isEven 5)
def alt5 : List (List ℕ) := [[1, 2, 0, 3, 4], [1, 2, 3, 4, 0]]

/-- A graph on `[5]` as a string on the pairs. -/
def gr (es : List (ℕ × ℕ)) : StrData :=
  strOf prs5 ((List.range 10).map fun j => if es.any (fun e => pairIdx5 e.1 e.2 == j) then 1 else 0)

def pathG : StrData := gr [(0, 1), (1, 2), (3, 4)]
def c5G : StrData := gr [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]
/-- `pathG` relabelled by `(0 3)(1 4)`. -/
def pathG' : StrData := gr [(3, 4), (4, 2), (0, 1)]

/-! ### Item 1: test sets, `ψ_A`, affected points, kernels, transporters -/

/-- The setwise stabilizer `G_A` as computed. -/
def gaD (F : Fix) (gs : List (List ℕ)) (al : List ℕ) : GroupData Ty.unit.denote :=
  (runR (stabSetProg F.n (F.grp gs) al)).getD (F.grp [])

def stabSetOK (F : Fix) (G gs : List (List ℕ)) (al : List ℕ) : Bool :=
  sameSet (F.closed (gaD F gs al)) (stabSet G al)

/-- `moveProg` maps `T` onto `T'` pointwise by an even permutation of the base. -/
def moveOK (F : Fix) (gs : List (List ℕ)) (T T' : List ℕ) : Bool :=
  match runR (moveProg F.n (F.grp gs) T T') with
  | some τ => let p := F.baseOf τ
    (List.range T.length).all (fun i => p.getD (T.getD i 0) 0 == T'.getD i 0) && isEven F.m p &&
      PermData.validB F.N τ && τ.1.toList == F.both p
  | none => false

/-- `giantAProg` on the group generated by `hs` (permutations of `[m]`) against brute force. -/
def giantOK (F : Fix) (hs : List (List ℕ)) (al : List ℕ) : Bool :=
  runR (giantAProg (D := Ty.unit) (F.posW al) (F.pA al) (F.grp hs).2.1) ==
    some (giant (closure F.m hs) al)

/-- `affProg` on `G_A` against brute force. -/
def affOK (F : Fix) (G gs : List (List ℕ)) (al : List ℕ) : Bool :=
  match runR (affProg F.n (F.posW al) (F.pA al) (gaD F gs al)) with
  | some af => af == F.aff (stabSet G al) al
  | none => false

/-- `kerAProg` on `G_A`: the kernel `G_A ∩ ker ψ_A`, at most `k!` representatives covering `G_A`;
and `kerOrbitsProg` on the affected points: the kernel's orbits, with `k · |o| ≤ n` if `bound`. -/
def kerOK (F : Fix) (G gs : List (List ℕ)) (al : List ℕ) (bound : Bool) : Bool :=
  let H := stabSet G al
  let Kb := H.filter fun p => al.all fun a => p.getD a 0 == a
  match runR (kerAProg (gaD F gs al) (F.pA al)) with
  | some (K, rs) =>
    let reps := rs.map F.baseOf
    let af := F.aff H al
    let orbsB := (af.map fun u => (af.filter fun v => Kb.any fun p => F.act p u == v)).dedup
    sameSet (F.closed K) Kb && reps.length ≤ al.length.factorial &&
      sameSet ((reps.flatMap fun r => Kb.map (compose r))) H &&
      match runR (kerOrbitsProg K (WinData.ofPoints F.N af)) with
      | some os => os.length == orbsB.length && os.all (fun o => orbsB.any (setEq o)) &&
          (!bound || os.all fun o => al.length * o.length ≤ F.n)
      | none => false
  | none => false

/-- `tupleTransProg` in `G_A` against brute force (positions of degree `n + m`). -/
def transOK (F : Fix) (G gs : List (List ℕ)) (al ps qs : List ℕ) : Bool :=
  let H := stabSet G al
  let ex := H.any fun p => (List.range ps.length).all fun i =>
    (F.both p).getD (ps.getD i 0) 0 == qs.getD i 0
  match runR (tupleTransProg (gaD F gs al) ps qs) with
  | some (some h) => ex && (List.range ps.length).all fun i => get h.1 (ps.getD i 0) == qs.getD i 0
  | some none => !ex
  | none => false

#eval check "S5 on pairs: G_A for A = {0,1,2} (order 12)" fun _ =>
  (stabSetOK prs5 S5 sym5 [0, 1, 2])
#eval check "A5 on pairs: G_A for A = {0,1,2} (order 6)" fun _ =>
  (stabSetOK prs5 A5 alt5 [0, 1, 2])
#eval check "S7 on points: G_A for A = {0,…,4} (order 240)" fun _ =>
  (stabSetOK pts7 (allPerms 7) sym7 [0, 1, 2, 3, 4])
#eval check "moveProg: (0,1,2) to (2,4,0) in S5 and A5, even and lifted" fun _ =>
  (moveOK prs5 sym5 [0, 1, 2] [2, 4, 0] && moveOK prs5 alt5 [0, 1, 2] [2, 4, 0] &&
    moveOK prs5 alt5 [0, 1, 2] [1, 0, 2])
#eval check "giantAProg: S3 x S2 and A3 are giants on A, S2 x S2 and C2 are not" fun _ =>
  (giantOK prs5 [[1, 0, 2, 3, 4], [1, 2, 0, 3, 4], [0, 1, 2, 4, 3]] [0, 1, 2] &&
    giantOK prs5 [[1, 2, 0, 3, 4]] [0, 1, 2] &&
    giantOK prs5 [[1, 0, 2, 3, 4], [0, 1, 2, 4, 3]] [0, 1, 2] &&
    giantOK prs5 [[2, 1, 0, 3, 4]] [0, 1, 2])
#eval check "affProg: the pairs meeting A (S5), the points of A (S7, k = 5)" fun _ =>
  (affOK prs5 S5 sym5 [0, 1, 2] && affOK pts7 (allPerms 7) sym7 [0, 1, 2, 3, 4])
#eval check "kerAProg and kerOrbitsProg on G_A (S5, A5; S7 with k = 5 and k |o| ≤ n)" fun _ =>
  (kerOK prs5 S5 sym5 [0, 1, 2] false && kerOK prs5 A5 alt5 [0, 1, 2] false &&
    kerOK pts7 (allPerms 7) sym7 [0, 1, 2, 3, 4] true)
#eval check "tupleTransProg in G_A: a 3-cycle of A (found), a point outside A (none), pairs"
    fun _ =>
  (transOK prs5 S5 sym5 [0, 1, 2] [10, 11, 12] [11, 12, 10] &&
    transOK prs5 S5 sym5 [0, 1, 2] [10, 11, 12] [10, 11, 13] &&
    transOK prs5 S5 sym5 [0, 1, 2] [0, 9] [4, 9] && transOK prs5 S5 sym5 [0, 1, 2] [0, 9] [9, 0])

/-! ### Item 2: the beard step and the paired beard -/

/-- One step from `G_A` (`x' = x`): the affected points and the coset `H_1`. -/
def stepOK (F : Fix) (G gs : List (List ℕ)) (x : StrData) (al : List ℕ) : Bool :=
  let H := stabSet G al
  match runR (beardStepProg sub F.n (F.posW al) (F.pA al) (x, x) F.one (gaD F gs al)) with
  | some (some (af, some (σ, K))) =>
    giant H al && af == F.aff H al &&
      sameSet ((F.closed K).map (compose (F.baseOf σ))) (F.bstep x al ([], H)).2
  | some none => !giant H al
  | _ => false

/-- The paired beard from `τ • G_A` with `ψ(τ) A = A'`: the final coset and window. -/
def pairOK (F : Fix) (G gs : List (List ℕ)) (x x' : StrData) (al al' : List ℕ) : Bool :=
  let C := F.pairCoset G x x' al al'
  match runR (moveProg F.n (F.grp gs) al al') with
  | some τ =>
    match runR (pairLoopProg sub F.n (F.posW al) (F.pA al) (x, x') τ (gaD F gs al)) with
    | some (Wl, some (σ, K)) =>
      setEq Wl (F.beardW G x al) && sameSet ((F.closed K).map (compose (F.baseOf σ))) C
    | some (_, none) => C.isEmpty
    | none => false
  | none => false

#eval check "beardStepProg from G_A: path (S5), path (A5)" fun _ =>
  (stepOK prs5 S5 sym5 pathG [0, 1, 2] && stepOK prs5 A5 alt5 pathG [0, 1, 2])
#eval check "pairLoopProg, x' ≠ x: path to its relabelling (nonempty), path to C5 (empty)" fun _ =>
  (pairOK prs5 S5 sym5 pathG pathG' [0, 1, 2] [3, 4, 2] &&
    pairOK prs5 S5 sym5 pathG c5G [0, 1, 2] [0, 1, 2])

/-! ### Item 3: certificates and their comparison -/

/-- The certificate against brute force. -/
def certOK (F : Fix) (G : List (List ℕ)) (gs : List (List ℕ)) (x : StrData) (al : List ℕ) :
    Bool :=
  match runR (certProg sub F.n (F.posW al) (F.pA al) (x, x) (F.grp gs) al) with
  | some (some (Wl, K, KA, full)) =>
    setEq Wl (F.beardW G x al) && sameSet (F.closed K) (F.beardH G x al) &&
      sameSet (F.closed KA) (F.certK G x al) && full == giant (F.certK G x al) al
  | _ => false

/-- The comparison against brute force; `expect` is the brute-force answer asserted. -/
def certIsoOK (F : Fix) (G gs : List (List ℕ)) (x x' : StrData) (T T' : List ℕ) (expect : Bool) :
    Bool :=
  F.certIso G x x' T T' == expect &&
    runR (certIsoProg sub F.n (F.posW T) (F.pA T) (x, x') (F.grp gs) T T') == some expect

/-- A colouring of `[5]` as a string on the points. -/
def col5 (l : List ℕ) : StrData := strOf pts5 l

#eval check "certProg: path on the pairs, A = {0,1,2} (not full)" fun _ =>
  (certOK prs5 S5 sym5 pathG [0, 1, 2])
#eval check "certProg: colourings of the points, constant on A (full) and not (not full)" fun _ =>
  (certOK pts5 S5 sym5 (col5 [1, 1, 1, 0, 2]) [0, 1, 2] &&
    certOK pts5 S5 sym5 (col5 [1, 2, 1, 0, 0]) [0, 1, 2] &&
    certOK pts5 A5 alt5 (col5 [3, 3, 3, 0, 0]) [0, 1, 2])
#eval check "certIsoProg: path and its relabelling (equivalent), path and C5 (not)" fun _ =>
  (certIsoOK prs5 S5 sym5 pathG pathG' [0, 1, 2] [3, 4, 2] true &&
    certIsoOK prs5 S5 sym5 pathG c5G [0, 1, 2] [0, 1, 2] false)
#eval check "certIsoProg on colourings: equal colours on the tuples (equivalent), not" fun _ =>
  (certIsoOK pts5 S5 sym5 (col5 [1, 1, 1, 0, 2]) (col5 [0, 2, 1, 1, 1]) [0, 1, 2] [4, 2, 3] true &&
    certIsoOK pts5 S5 sym5 (col5 [1, 2, 1, 0, 0]) (col5 [1, 1, 2, 0, 0]) [0, 1, 2] [0, 1, 2] false)
/-! ### Kernel-checked runs

The same comparisons with brute force, evaluated by the kernel (`decide +kernel`), on `S₃` and
`A₃` acting on the points of `[3]` (string positions `0–2`) and on the base `3–5`. -/

/-- `S₃` on the points: string positions `0–2`, base `3–5`. -/
def pts3 : Fix := ⟨3, 3, fun p j => p.getD j 0⟩

def S3 : List (List ℕ) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
def A3 : List (List ℕ) := [[0, 1, 2], [1, 2, 0], [2, 0, 1]]
def sym3 : List (List ℕ) := [[1, 0, 2], [1, 2, 0]]
def alt3 : List (List ℕ) := [[1, 2, 0]]

/-- A colouring of `[3]` as a string on the points. -/
def col3 (l : List ℕ) : StrData := strOf pts3 l

/-- The paired beard from `1 • G_A` (`A' = A`) against the brute-force paired coset. -/
def pairOneOK (F : Fix) (G gs : List (List ℕ)) (x x' : StrData) (al : List ℕ) : Bool :=
  let C := F.pairCoset G x x' al al
  match runR (pairLoopProg sub F.n (F.posW al) (F.pA al) (x, x') F.one (gaD F gs al)) with
  | some (Wl, some (σ, K)) =>
    setEq Wl (F.beardW G x al) && sameSet ((F.closed K).map (compose (F.baseOf σ))) C
  | some (_, none) => C.isEmpty
  | none => false

/-- `G_A` of a point (`k = 1`, `m = 3`). -/
example : stabSetOK pts3 S3 sym3 [0] = true := by decide +kernel
/-- Moving a point, in `S₃` and `A₃`. -/
example : (moveOK pts3 sym3 [0] [2] && moveOK pts3 alt3 [0] [1]) = true := by decide +kernel
/-- The giant test on `A = [3]` (`k = 3`): `S₃` is a giant, `⟨(0 1)⟩` is not. -/
example : (giantOK pts3 sym3 [0, 1, 2] && giantOK pts3 [[1, 0, 2]] [0, 1, 2]) = true := by
  decide +kernel
/-- The affected points of `S₃` for `A = [3]`: every point. -/
example : affOK pts3 S3 sym3 [0, 1, 2] = true := by decide +kernel
/-- The kernel of `S₃` on `A = [3]`, its six representatives and its orbits. -/
example : kerOK pts3 S3 sym3 [0, 1, 2] false = true := by decide +kernel
/-- The tuple transporter: found, and not found. -/
example : (transOK pts3 S3 sym3 [0, 1, 2] [0, 3] [1, 4] &&
    transOK pts3 S3 sym3 [0, 1, 2] [0, 3] [1, 5]) = true := by decide +kernel
/-- One beard step for `A = [3]`: six branches, each calling the solver on the orbits. -/
example : stepOK pts3 S3 sym3 (col3 [0, 0, 1]) [0, 1, 2] = true := by decide +kernel
/-- The paired beard of two colourings. -/
example : pairOneOK pts3 S3 sym3 (col3 [0, 0, 1]) (col3 [0, 1, 0]) [0, 1, 2] = true := by
  decide +kernel
/-- The certificate of a point (`k = 1`). -/
example : certOK pts3 S3 sym3 (col3 [0, 0, 1]) [0] = true := by decide +kernel
/-- The comparison of the certificates of two points (`k = 1`). -/
example : certIsoOK pts3 S3 sym3 (col3 [0, 0, 1]) (col3 [1, 0, 0]) [0] [1] true = true := by
  decide +kernel

end GraphIsoChecks.CertProg
