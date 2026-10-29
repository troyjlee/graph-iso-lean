module

public import GraphIsoChecks.MainSteps
meta import GraphIsoChecks.MainSteps
public import GraphIso.Main.SimsM5
meta import GraphIso.Main.SimsM5
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-5c checks: the Schreier–Sims steps

Checks of the Schreier–Sims step corollaries (`GraphIso/Main/SimsSteps.lean`, `SimsM4.lean`,
`SimsM5.lean`) on executed runs. Each step runs with the verified Schreier–Sims oracle, the
instrumented sub-solver `spySub` of stage 14j-2 and milestone 1's solver for the children
(`MainSteps.runT`).

* **The step's own work** (`ownCost`): `spySub` brackets every sub-call between two marker calls
  (`SENT`, `SENT2`), so the step's own events are those outside the brackets (`own`). Their cost
  under `ssB` is compared with the corollary's explicit work. The corollaries bound a run by the
  children's costs plus that work, so this is the part the work must cover.
* **The charges, per call site** (`sitesOK`). Each charge lemma is a *site*: the set of calls it
  bounds, and its bound. A lemma about one specific call (the re-basing of M1, the leaf
  stabilizer's `generate` of M4, the restriction's kernel of M5, …) is a site that matches
  exactly that input, computed here by the same model functions its statement names. A lemma
  quantified over inputs (`BackendBounds`, `RDBounds`, the transfer's `generate` on at most `s`
  generators, …) is a site that matches the degree, window and size conditions of its statement.
  The semantic conditions (validity, a subgroup of `G`, `M5Full`) are not tested, so such a site
  can match more calls than its lemma covers, which only makes the check stricter. Every own call
  of the step must match some site and be within the bound of *every* site it matches.
* **Negative controls**: with the bound of one exact site set to `0` (M1's re-basing, M2b's block
  stabilizer, M4's leaf stabilizer, M5's restriction), the check fails, so each exact site is
  tested on its own call.

Kernel-checked (`decide +kernel`): M1 (`m1WorkSS`), M2a (`m2aWorkSS`) and M2b (`m2bWorkSS`, with
and without hinted children) on stage 14j-2's fixtures `fM1`, `fM2a`, `fM2b`, `fM2b'`.

By interpreter runs (`#eval` through `check`, which fails the build on a false result; the runs
are too large for one kernel check):
* M4 on stage 14j-3's `AGL(1, 5)` fixture: the own work against `m4CostSS` at the run's
  individualization depth (the function the envelope `m4WorkSS` bounds from above; the envelope
  itself ranges over every smaller size and is not evaluated), and the charges per site, with
  the parameters of `m4_params`;
* M5 on stage 14j-4's `S₄` fixtures `fA`, `fB` and on the `S₅` fixtures (`x` constant, an
  isomorphic and a non-isomorphic pair), with `k = 3`: the charges per site, with
  `sIn = ssSIn NP s |gsP|`, `uB = m` and `Lg = ssLgM5 m k sIn`. These fixtures are outside M5's
  numeric conditions (`5 ≤ k`, `12 ≤ m`), so the step corollary itself is not checked on them.
-/

@[expose] public section

namespace GraphIsoChecks.MainSimsSteps

open GraphIso GraphIso.Cost GraphIso.Main GraphIso.Sims GraphIso.Toolkit GraphIso.SoJTree
open GraphIsoChecks.MainSteps

/-! ### The step's own events -/

/-- A marker call of `spySub`, with first entry `k`. -/
def isMark (k : ℕ) (e : Event (groupSig Ty.unit)) : Bool :=
  match e with
  | .call .generate x _ => x.1 == 0 && (x.2.headD (#[], #[])).1.getD 0 0 == k
  | _ => false

/-- **The step's own events**: outside the sub-solver's runs (between the markers `SENT` and
`SENT2`), the markers excluded. -/
def own : List (Event (groupSig Ty.unit)) → ℕ → List (Event (groupSig Ty.unit))
  | [], _ => []
  | e :: t, d =>
    if isMark SENT e then own t (d + 1)
    else if isMark SENT2 e then own t (d - 1)
    else if d == 0 then e :: own t d else own t d

/-- The cost of the step's own events under the Schreier–Sims schedule. -/
def ownCost (tr : Trace (groupSig Ty.unit)) : ℕ := Trace.cost ssB (own tr 0)

/-- The number of the step's own backend calls (that the run made some). -/
def ownCalls (tr : Trace (groupSig Ty.unit)) : ℕ :=
  (own tr 0).countP fun e => match e with | .call _ _ _ => true | _ => false

/-! ### Charge sites -/

/-- **A charge site**: on a call in the input set of one charge lemma, `some` of the lemma's
bound; `none` otherwise. -/
abbrev Site := Event (groupSig Ty.unit) → Option ℕ

/-- **The per-site check**: every own backend call of the step matches some site, and is within
the bound of every site it matches. -/
def sitesOK (sites : List Site) (tr : Trace (groupSig Ty.unit)) : Bool :=
  (own tr 0).all fun e => match e with
    | .call op x y =>
      let bs := sites.filterMap (· e)
      !bs.isEmpty && bs.all fun b => decide (ssB.call op x y ≤ b)
    | _ => true

/-- `some b` when `c` holds. -/
def ifB (c : Bool) (b : ℕ) : Option ℕ := if c then some b else none

def onGen (f : ℕ × GensData → Option ℕ) : Site := fun e => match e with
  | .call .generate x _ => f x
  | _ => none
def onOrb (f : GroupData Unit × WinData → Option ℕ) : Site := fun e => match e with
  | .call .orbits x _ => f x
  | _ => none
def onStab (f : GroupData Unit × ℕ → Option ℕ) : Site := fun e => match e with
  | .call .stabilizer x _ => f x
  | _ => none
def onTrans (f : GroupData Unit × ℕ → Option ℕ) : Site := fun e => match e with
  | .call .orbitTransversal x _ => f x
  | _ => none
def onKer (f : GroupData Unit × WinData → Option ℕ) : Site := fun e => match e with
  | .call .kernel x _ => f x
  | _ => none
def onLift (f : GroupData Unit × (WinData × PermData) → Option ℕ) : Site := fun e => match e with
  | .call .lift x _ => f x
  | _ => none
def onMem (f : GroupData Unit × PermData → Option ℕ) : Site := fun e => match e with
  | .call .mem x _ => f x
  | _ => none
def onReps (f : GroupData Unit × GroupData Unit → Option ℕ) : Site := fun e => match e with
  | .call .cosetReps x _ => f x
  | _ => none

/-- `generate` on exactly the input `x`. -/
def genEq (x : ℕ × GensData) (b : ℕ) : Site := onGen fun y => ifB (decide (y = x)) b
/-- `generate` at a degree in `[lo, hi]` on at most `L` generators. -/
def genSz (lo hi L b : ℕ) : Site :=
  onGen fun y => ifB (decide (lo ≤ y.1) && decide (y.1 ≤ hi) && decide (y.2.length ≤ L)) b

/-- **`BackendBounds` with Schreier–Sims at degree `M`** (`ssBoundsS M s`): `orbits`,
`stabilizer` and `orbitTransversal` on at most `s` generators, `generate` on at most
`M (s + 1)`. -/
def bbSites (M s : ℕ) : List Site :=
  [onOrb fun x => ifB (x.1.1 == M && decide (x.1.2.1.length ≤ s)) (orbitsCost M s M + 5),
   onStab fun x => ifB (x.1.1 == M && decide (x.1.2.1.length ≤ s)) (stabCost M s + 5),
   onTrans fun x => ifB (x.1.1 == M && decide (x.1.2.1.length ≤ s)) (transCost M s + 5),
   genSz M M (M * (s + 1)) (genCost M (M * (s + 1)) + 2)]

/-- **`ssBm`**: `BackendBounds` at every degree `M` with `M²` generators. -/
def bmSites : List Site :=
  [onOrb fun x => ifB (decide (x.1.2.1.length ≤ x.1.1 * x.1.1))
     (orbitsCost x.1.1 (x.1.1 * x.1.1) x.1.1 + 5),
   onStab fun x => ifB (decide (x.1.2.1.length ≤ x.1.1 * x.1.1))
     (stabCost x.1.1 (x.1.1 * x.1.1) + 5),
   onTrans fun x => ifB (decide (x.1.2.1.length ≤ x.1.1 * x.1.1))
     (transCost x.1.1 (x.1.1 * x.1.1) + 5),
   onGen fun x => ifB (decide (x.2.length ≤ x.1 * (x.1 * x.1 + 1)))
     (genCost x.1 (x.1 * (x.1 * x.1 + 1)) + 2)]

/-- **`RDBounds` with Schreier–Sims** (`rd_ss_boundsS n N sIn Lg`): the lifts at degrees
`M ≤ N` on the strings, `generate` on at most `Lg` generators, `orbits` (also of the kernel), the
kernel and the coset representatives on groups of at most `sIn` generators. -/
def rdSites (n N sIn Lg : ℕ) : List Site :=
  [onLift fun x => ifB (decide (x.1.1 ≤ N) && decide (x.1.2.1.length ≤ sIn) &&
     decide (x.2.1 = strWin x.1.1 n)) (Sims.liftCost N sIn n + 7),
   genSz 0 N Lg (genCost N Lg + 2),
   onOrb fun x => ifB (decide (x.1.1 ≤ N) && decide (x.1.2.1.length ≤ sIn))
     (orbitsCost N sIn N + 5),
   onKer fun x => ifB (x.1.1 == N && decide (x.1.2.1.length ≤ sIn) &&
     decide (x.2 = baseWin n N)) (kerCost N sIn N + 5),
   onReps fun x => ifB (x.1.1 == N && decide (x.1.2.1.length ≤ sIn) &&
     decide (x.2 = kerModel ssOracle n x.1)) (Sims.repsCost N sIn (N * N) (N - n).factorial + 7)]

/-- **The derived hints' charges** in reduce-and-derive's `RDOrbit` (`rd_orbit_free_ssU`,
`rd_orbit_cj_ssU`, at `S` generators): M1's base orbits and re-basing (`ss_m1Charges`), the
block step at the extended degree `2N` (`ss_blkCharges_of`) and the cells' re-basing. -/
def rdOrbitSites (n N S : ℕ) : List Site :=
  [onOrb fun x => ifB (decide (x.1.1 ≤ N) && decide (x.1.2.1.length ≤ S) &&
     decide (x.2 = baseWin n x.1.1)) (orbitsCost N S (N - n) + 5),
   genSz 0 N S (genCost N S + 2),
   genSz 0 N (N * N) (genCost N (N * N) + 2),
   genSz 0 (2 * N) (N * N) (genCost (2 * N) (N * N) + 2),
   onStab fun x => ifB (decide (x.1.1 ≤ 2 * N) && decide (x.1.2.1.length ≤ 2 * N * (2 * N)))
     (stabCost (2 * N) (2 * N * (2 * N)) + 5),
   onTrans fun x => ifB (decide (x.1.1 ≤ 2 * N) && decide (x.1.2.1.length ≤ 2 * N * (2 * N)))
     (transCost (2 * N) (2 * N * (2 * N)) + 5),
   genSz 0 N (2 * N * (2 * N)) (genCost N (2 * N * (2 * N)) + 2)]

/-! ### M1, M2a, M2b -/

/-- **M1's sites** (`RunsWithin.m1StepProg_ss`), with the re-basing's bound `Bgen₁`: the base
orbits (`ss_hint_hBo`), the re-basing onto the orbit, an exact site (`ss_hint_hB`), the
transfer's lifts (`ss_hint_hBlift`) and `generate` on at most `s` generators
(`ss_hint_hBgen`). -/
def m1Sites (f : SFix) (L : Array (List ℕ)) (Bgen₁ : ℕ) : List Site :=
  let G : GroupData Unit := (f.N, gD f.gs, ())
  let O := singD (m1O ssOracle f.n f.N G (WinData.ofPoints f.N f.w) L)
  let g := f.gs.length
  let s := f.N * f.N
  [onOrb fun x => ifB (decide (x = (G, baseWin f.n f.N))) (orbitsCost f.N g (f.N - f.n) + 5),
   genEq (f.n + O.length, rebaseGens f.n f.N O (gD f.gs)) Bgen₁,
   onLift fun x => ifB (decide (x.1 = G) && decide (x.2.1 = strWin f.N f.n))
     (Sims.liftCost f.N g f.n + 7),
   genSz f.N f.N s (genCost f.N s + 2)]

/-- **M1 with Schreier–Sims** on a fixture: the own work within `m1WorkSS n m |W| |gs| N²` and
every call within its site's bound, the re-basing's bound being `Bgen₁`. -/
def m1With (f : SFix) (L : Array (List ℕ)) (Bgen₁ : ℕ) : Bool :=
  match runT (m1StepProg spySub f.hinst L) with
  | some (_, tr) =>
    decide (ownCost tr ≤ m1WorkSS f.n (f.N - f.n) f.w.length f.gs.length (f.N * f.N)) &&
      decide (0 < ownCalls tr) && sitesOK (m1Sites f L Bgen₁) tr
  | none => false

/-- M1 with the bound of `ss_hint_hB`. -/
def m1SS (f : SFix) (L : Array (List ℕ)) : Bool := m1With f L (genCost f.N f.gs.length + 2)

/-- **M2a's sites** (`RunsWithin.m2aStepProg_ss`): the re-basing onto the blocks `mbD`, an exact
site (`ss_hint_hB`), and the transfer's lifts and `generate`. -/
def m2aSites (f : SFix) : List Site :=
  let G : GroupData Unit := (f.N, gD f.gs, ())
  let bs := mbD f.n f.N (gD f.gs)
  let g := f.gs.length
  let s := f.N * f.N
  [genEq (f.n + bs.length, rebaseGens f.n f.N bs (gD f.gs)) (genCost f.N g + 2),
   onLift fun x => ifB (decide (x.1 = G) && decide (x.2.1 = strWin f.N f.n))
     (Sims.liftCost f.N g f.n + 7),
   genSz f.N f.N s (genCost f.N s + 2)]

/-- **M2a with Schreier–Sims** on a fixture. -/
def m2aSS (f : SFix) (L : Array (List ℕ)) : Bool :=
  match runT (m2aStepProg spySub f.hinst L (mbD f.n f.N (gD f.gs))) with
  | some (_, tr) =>
    decide (ownCost tr ≤ m2aWorkSS f.n (f.N - f.n) f.w.length f.gs.length (f.N * f.N) L.size) &&
      decide (0 < ownCalls tr) && sitesOK (m2aSites f) tr
  | none => false

/-- **M2b's sites** (`RunsWithin.m2bStepProg_ss`, with `sIn = N²`), at the extended degree
`E = n + 2m`, the block stabilizer's `generate` bounded by `Bge`: the five exact sites of
`ss_m2bCharges` (the extended group, the stabilizer and transversal of block `0`, the stabilizer
at degree `N`, its re-basing onto the block), the lifts from the block stabilizer
(`ss_m2b_hBlift`), `generate` on the branches' answers (`ss_m2b_hBgen`), the orbits of the
re-based block stabilizer's subgroups (`ss_m2b_hBo`) and `generate` on the combined branches
(`ss_m2b_hBgen₂`). -/
def m2bSites (f : SFix) (bs : List (List ℕ)) (Bge : ℕ) : List Site :=
  let n := f.n
  let N := f.N
  let gs := gD f.gs
  let sIn := N * N
  let E := n + 2 * (N - n)
  let b0 := (bs.toArray.getD 0 []).map fun p => [p]
  let H := (blockStabModel ssOracle N bs gs 0).1.2.1
  let Rb := rebaseModel ssOracle n N b0 H
  [genEq (N + bs.length, Programs.extendGens N bs gs) Bge,
   onStab fun x => ifB (decide (x = (Programs.extGroup ssOracle N bs gs, N + 0))) (stabCost E (E * E) + 5),
   onTrans fun x => ifB (decide (x = (Programs.extGroup ssOracle N bs gs, N + 0)))
     (transCost E (E * E) + 5),
   genEq (N, (bsStab ssOracle N bs gs 0).2.1.map (PermData.truncTo N)) (genCost N (E * E) + 2),
   genEq (n + b0.length, rebaseGens n N b0 H) (genCost N (N * N) + 2),
   onLift fun x => ifB (decide (x.1 = m2bRg ssOracle N gs bs) && decide (x.2.1 = strWin N n))
     (Sims.liftCost N (N * N) n + 7),
   genSz N N sIn (genCost N sIn + 2),
   onOrb fun x => ifB (x.1.1 == Rb.1 && decide (x.1.2.1.length ≤ sIn)) (orbitsCost N sIn N + 5),
   genSz N N ((blockStabModel ssOracle N bs gs 0).2.length * (N * N + 1))
     (genCost N ((N - n) * (N * N + 1)) + 2)]

/-- **M2b with Schreier–Sims** on a fixture, the extended group's `generate` bounded by
`Bge`. -/
def m2bWith (f : SFix) (L : Array (List ℕ)) (bs : List (List ℕ)) (Bge : ℕ) : Bool :=
  match runT (m2bStepProg spySub f.hinst bs) with
  | some (_, tr) =>
    decide (ownCost tr ≤ m2bWorkSS f.n (f.N - f.n) f.w.length f.gs.length L.size (f.N * f.N)) &&
      decide (0 < ownCalls tr) && sitesOK (m2bSites f bs Bge) tr
  | none => false

/-- M2b with the bound of `ss_m2bCharges`. -/
def m2bSS (f : SFix) (L : Array (List ℕ)) (bs : List (List ℕ)) : Bool :=
  m2bWith f L bs (genCost (f.n + 2 * (f.N - f.n)) f.gs.length + 2)

example : m1SS fM1 lM1 = true := by decide +kernel
example : m2aSS fM2a lM2a = true := by decide +kernel
example : m2bSS fM2b lM2b (mbD fM2b.n fM2b.N (gD fM2b.gs)) = true := by decide +kernel
example : m2bSS fM2b' lM2b (mbD fM2b'.n fM2b'.N (gD fM2b'.gs)) = true := by decide +kernel

/-- **Negative controls**: with the bound of the exact site of M1's re-basing, or of M2b's
extended group, set to `0`, the check fails. -/
example : m1With fM1 lM1 0 = false := by decide +kernel
example : m2bWith fM2b lM2b (mbD fM2b.n fM2b.N (gD fM2b.gs)) 0 = false := by decide +kernel

/-! ### M4 and M5 (interpreter runs) -/

/-- **A check that fails the build**: `#eval check name b` throws when `b` is false. -/
def check (name : String) (b : Unit → Bool) : IO Unit := do
  unless b () do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

/-- The fixtures of stages 14j-3 and 14j-4 (`MainM4.fM4AGL`, `MainM5.fA`, `MainM5.fB`,
`MainM5.mkD`), restated here so that this module does not depend on those check modules. A group
on `[k]` acting on `k` strings and on the base alike. -/
def alike (gs : List (List ℕ)) : List (List ℕ) := gs.map fun p => p ++ p.map (· + p.length)

/-- `AGL(1, 5)` on five strings and the base alike, labels `{i}`, `x = y` symmetric under the
reflection fixing `0`: degree `2`, one individualized point (`MainM4.fM4AGL`). -/
def fM4AGL : SFix := ⟨5, 10, alike [[1, 2, 3, 4, 0], [0, 2, 4, 1, 3]], [0, 1, 2, 3, 4],
  List.range 10, [0, 1, 2, 2, 1, 0, 0, 0, 0, 0], [0, 1, 2, 2, 1, 0, 0, 0, 0, 0],
  some #[[0], [1], [2], [3], [4]]⟩

/-- Labels `{i}` on four strings. -/
def l4 : Array (List ℕ) := #[[0], [1], [2], [3]]

/-- `S₄` on four strings and the base alike (`MainM5.mk4`). -/
def mk4 (x y : List ℕ) : SFix := ⟨4, 8, alike [[1, 0, 2, 3], [1, 2, 3, 0]], List.range 4,
  List.range 8, x ++ [0, 0, 0, 0], y ++ [0, 0, 0, 0], some l4⟩

/-- `x = 0 0 0 1`, `y = 0 1 0 0`: four isomorphisms (`MainM5.fA`). -/
def fA : SFix := mk4 [0, 0, 0, 1] [0, 1, 0, 0]
/-- `x = 0 0 0 1`, `y = 0 0 1 1`: none (`MainM5.fB`). -/
def fB : SFix := mk4 [0, 0, 0, 1] [0, 0, 1, 1]

/-- Labels `{i}` on five strings. -/
def l5 : Array (List ℕ) := #[[0], [1], [2], [3], [4]]

/-- `S₅` on five strings and the base alike (`MainM5.mkD`). -/
def mk5 (x y : List ℕ) : SFix := ⟨5, 10, alike [[1, 0, 2, 3, 4], [1, 2, 3, 4, 0]],
  List.range 5, List.range 10, x ++ [0, 0, 0, 0, 0], y ++ [0, 0, 0, 0, 0], some l5⟩

/-- No structure (`MainM5.noSt`). -/
def noSt : ℕ × CJData := (0, (([], [], 0, #[]), #[]))

/-- **M4's sites** (`RunsWithin.m4StepProg_ss`, with `sIn = s = N²` and the parameters of
`m4_params`), the leaf stabilizer's extended `generate` bounded by `Bge`: `BackendBounds` at `N`
(`ssBoundsS`: the degree, the individualization, the orbital configuration); the four exact
sites of the leaf stabilizer (`ss_m4Charges`, with `R = msCount (m − j)`); reduce-and-derive's
`RDBounds` (`rd_ss_boundsS`) and the derived hints' charges (`ss_m4_hD`). -/
def m4Sites (f : SFix) (Bge : ℕ) : List Site :=
  let n := f.n
  let N := f.N
  let m := N - n
  let G : GroupData Unit := (N, gD f.gs, ())
  let sIn := N * N
  let j := m4J ssOracle n G
  let Lg := ssLgM4 m j sIn
  let R := msCount (m - j)
  let gsH := (m4PS ssOracle n G).1.2.1
  let o := msLeaf ssOracle (n + j) (m4PS ssOracle n G).1
  let r := msR (n + j) N gsH o
  let imgs := msImgs (n + j) N gsH o
  let OG := osGroup ssOracle N r gsH imgs
  bbSites N sIn ++
  [genEq (N + r, os_extGens N r gsH imgs) Bge,
   onStab fun x => ifB (decide (x = (OG, N))) (stabCost (N + R) ((N + R) * (N + R)) + 5),
   onTrans fun x => ifB (decide (x = (OG, N))) (transCost (N + R) ((N + R) * (N + R)) + 5),
   genEq (N, (osStab ssOracle N r gsH imgs).2.1.map (PermData.truncTo N))
     (genCost N ((N + R) * (N + R)) + 2)] ++
  rdSites n N sIn Lg ++ rdOrbitSites n N sIn

/-- **M4 with Schreier–Sims** on a fixture: the own work within `m4CostSS` at the run's depth
`j`, and every call within its site's bound. -/
def m4With (f : SFix) (Bge : ℕ) : Bool :=
  let m := f.N - f.n
  let sIn := f.N * f.N
  let j := m4J ssOracle f.n (f.N, gD f.gs, ())
  let Lg := ssLgM4 m j sIn
  let L := f.L.getD #[]
  match runT (m4StepProg spySub f.hinst) with
  | some (_, tr) =>
    decide (ownCost tr ≤ m4CostSS f.n m j f.w.length sIn Lg
      (m4WhSS f.n m f.w.length sIn L.size sIn Lg m.factorial
        (m4W6SS f.n m f.w.length sIn sIn Lg))) && decide (0 < ownCalls tr) &&
      sitesOK (m4Sites f Bge) tr
  | none => false

/-- M4 with the bound of `ss_m4Charges`. -/
def m4SS (f : SFix) : Bool :=
  let j := m4J ssOracle f.n (f.N, gD f.gs, ())
  m4With f (genCost (f.N + msCount (f.N - f.n - j)) (f.N * f.N) + 2)

/-- **M5's sites** (`RunsWithin.m5StepCJProg_ss`, `ss_m5_*`) on a fixture with certificate size
`k`, the restriction's `generate` bounded by `BgmR`.
* The restriction (`rbCost`): the exact sites of `ss_m5_hBgmR`, `ss_m5_hBliftR`, `ss_m5_hBkerR`,
  and `generate` on the parent's answer (`ss_m5_hBgnR`).
* On the restricted group `G = (N, gs)`: the exact sites of the base action's `generate`
  (`ss_m5_hBgP`), `mem` (`ss_m5_hBmem`), the kernel (`hBkA`, `hBk3`), the lifts from the base
  (`ss_m5_hBlA`), the kernel's orbits (`hBo3`) and coset representatives (`hBcr3`); `generate`
  at the base's degrees (`ss_m5_hBg`); `BackendBounds` at `N`, at `k` (`Bk'`) and at every degree
  (`ssBm`).
* `generate` at degree `N` on at most: `k! (sIn + 1)` (`ss_m5_hBgk`), `k + sIn` (the giant set
  stabilizers, `ss_m5_hBgs` through `ss_giantGens_le`), `2 sIn` (`ss_m5_hBF`),
  `|kerReps| (max s |ker| + 1)` (`ss_m5_hB3`), `2(m² + m) + N²` (the aligned groups of Cases 1,
  2a, 2b and 3, `ss_m5_hBg1₁` …), `6m² + N²` (the coloured Johnson routes, `ss_m5_hBg1J₂`, `₃`),
  `sIn + 1` and `(sIn + 1)² + 2 sIn` (Case 2a, `ss_m5_hBgen₂ₐ`, `ss_m5_hBpb`), `N² + s`
  (`ss_m5_hBgn`), `c2bRU m (sIn + 1)` (`ss_m5_hBgen₂ᵦ`), `c3R k m Z (sIn + 1)`
  (`ss_m5_hBgen₃`).
* Case 1's full groups' base orbits (`ss_m5_hBox`, `hBoy`); Case 2a's sub-instances
  (`ss_m5_hBgm`, `hBlift`, `hBker`); reduce-and-derive (`rd_ss_boundsS`) and its derived hints
  (`ss_m5_hD₁` …, `ss_m5_hDJ₂` …). -/
def m5Sites (f : SFix) (k BgmR : ℕ) : List Site :=
  let NP := f.N
  let nP := f.n
  let wP := WinData.ofPoints f.N f.w
  let gsP := gD f.gs
  let n := f.w.length
  let m := NP - nP
  let N := (rbPts nP NP wP).length
  let sIn := ssSIn NP (NP * NP) gsP.length
  let s := sIn
  let Lg := ssLgM5 m k sIn
  let β := ssM5β N m k sIn s
  let G : GroupData Unit := ssOracle.run .generate (N, rbGens nP NP wP gsP)
  let gs := G.2.1
  let w := WinData.ofPoints N (List.range n)
  let K := kerModel ssOracle n G
  [genEq (N, rbGens nP NP wP gsP) BgmR,
   onLift fun x => ifB (decide (x.1 = (NP, gsP, ())) && decide (x.2.1 = rbU nP NP wP))
     (Sims.liftCost NP sIn NP + 7),
   onKer fun x => ifB (decide (x = ((NP, gsP, ()), rbU nP NP wP))) (kerCost NP sIn NP + 5),
   genSz NP NP (NP * NP + sIn) (genCost NP (NP * NP + sIn) + 2),
   genEq (N - n, gs.map (Align.baseD n N)) β.BgP,
   onMem fun x => ifB (decide (x.1 = Align.pModel ssOracle n G)) β.Bmem,
   onKer fun x => ifB (decide (x = (G, baseWin n N))) β.BkA,
   onLift fun x => ifB (decide (x.1 = G) && decide (x.2.1 = baseWin n N)) β.BlA,
   onOrb fun x => ifB (decide (x = (K, w))) β.Bo3,
   onReps fun x => ifB (decide (x = (G, K))) β.Bcr3,
   genSz 0 m sIn β.Bg,
   genSz N N (k.factorial * (sIn + 1)) β.Bgk,
   genSz N N (k + sIn) β.Bgs,
   genSz N N (2 * sIn) β.BF,
   genSz N N ((kerReps ssOracle n G).length * (max s K.2.1.length + 1)) β.Bgen3,
   genSz N N (2 * (m * m + m) + N * N) β.Bg1₁,
   genSz N N (2 * (3 * (m * m)) + N * N) (ssBg1J N m),
   genSz N N (sIn + 1) β.Bgen₂ₐ,
   genSz N N ((sIn + 1) * (sIn + 1) + sIn + sIn) β.Bpb,
   genSz N N (β.sK + s) β.Bgn,
   genSz N N (c2bRU m * (sIn + 1)) β.Bgen₂ᵦ,
   genSz N N (Case3.c3R k m (Case2b.sojZ m) * (sIn + 1)) β.Bgen₃,
   onOrb fun x => ifB (x.1.1 == N && decide (x.1.2.1.length ≤ sIn) &&
     decide (x.2 = baseWin n N)) β.Box,
   genSz 0 N sIn β.Bgm,
   onLift fun x => ifB (x.1.1 == N && decide (x.1.2.1.length ≤ sIn) &&
     decide (x.2.1.1.length ≤ N)) β.Blift,
   onKer fun x => ifB (x.1.1 == N && decide (x.1.2.1.length ≤ sIn)) β.Bker] ++
  bbSites N sIn ++ bbSites k sIn ++ bmSites ++ rdSites n N sIn Lg ++ rdOrbitSites n N sIn

/-- **M5's charges with Schreier–Sims** on a fixture with certificate size `k`: every own call
of the step (`m5StepCJProg`) within the bound of every site it matches, the restriction's
`generate` bounded by `BgmR`. -/
def m5With (f : SFix) (L : Array (List ℕ)) (k BgmR : ℕ) : Bool :=
  match runT (m5StepCJProg spySub f.hinst L k noSt) with
  | some (_, tr) => decide (0 < ownCalls tr) && sitesOK (m5Sites f k BgmR) tr
  | none => false

/-- M5 with the bound of `ss_m5_hBgmR`. -/
def m5SS (f : SFix) (L : Array (List ℕ)) (k : ℕ) : Bool :=
  let wP := WinData.ofPoints f.N f.w
  m5With f L k (genCost (rbPts f.n f.N wP).length (ssSIn f.N (f.N * f.N) f.gs.length) + 2)

#eval check "M4 on AGL(1, 5): the own work and every call per site" fun _ => m4SS fM4AGL
#eval check "M4: the negative control (the leaf stabilizer's generate bounded by 0)" fun _ =>
  !m4With fM4AGL 0

#eval check "M5 on S₄ (k = 3), an isomorphic and a non-isomorphic pair: every call per site"
  fun _ => m5SS fA l4 3 && m5SS fB l4 3
#eval check "M5 on S₅ (k = 3), x constant, an isomorphic and a non-isomorphic pair: every call \
    per site" fun _ =>
  m5SS (mk5 [0, 0, 0, 0, 0] [0, 0, 0, 0, 0]) l5 3 &&
    m5SS (mk5 [0, 0, 0, 0, 1] [0, 1, 0, 0, 0]) l5 3 &&
    m5SS (mk5 [0, 0, 0, 0, 1] [0, 0, 0, 1, 1]) l5 3
#eval check "M5: the negative control (the restriction's generate bounded by 0)" fun _ =>
  !m5With fA l4 3 0

end GraphIsoChecks.MainSimsSteps
