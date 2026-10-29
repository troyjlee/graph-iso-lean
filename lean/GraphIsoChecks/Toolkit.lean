module

public import GraphIsoChecks.Sims
meta import GraphIsoChecks.Sims
public import GraphIso.Toolkit.Extend
meta import GraphIso.Toolkit.Extend
public import GraphIso.Toolkit.Labels
meta import GraphIso.Toolkit.Labels
public import GraphIso.Toolkit.Orbital
meta import GraphIso.Toolkit.Orbital
public import GraphIso.Toolkit.Reduce
meta import GraphIso.Toolkit.Reduce

/-!
# Milestone 14, stage 14b checks: the group toolkit

Interpreter runs of the toolkit programs over the Schreier–Sims backend (each `#eval` throws on
a failure):

* `Sym(5)`, `Alt(5)` and the dihedral group `D₅`, acting on the ten pairs of `{0, …, 4}`
  (string positions `0–9`) and on `{0, …, 4}` itself (base positions `10–14`). Their degrees
  of transitivity on the base are `3` (capped at `m − 2`), `3` and `1`, and the giant test
  separates `Sym(5)` and `Alt(5)` from `D₅`;
* the base of `Sym(5)` is primitive (singleton maximal blocks), and `D₅`'s too;
* the orbital configuration of `Sym(5)` on the pairs (as a base) has three colours, the
  Petersen graph being the disjoint pairs;
* the kernel of `Sym(5)` on the base is trivial, with `120` coset representatives;
* the Johnson labels of the pairs satisfy `HintValid`'s generator condition;
* `C₂ ≀ C₂` re-based onto its two blocks acts on the two block points.
-/

@[expose] public section

namespace GraphIsoChecks.Toolkit

open Equiv GraphIso GraphIso.Cost GraphIso.Toolkit GraphIso.Sims GraphIsoChecks.Sims

/-- Run a toolkit program with the Schreier–Sims backend substituted. -/
def run {t : Ty} (p : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote t) :
    Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 1000000 (p.subst ssImpl)).map Prod.fst

/-- The ten pairs `{a, b}`, `a < b`, of `{0, …, 4}`. -/
def pairs5 : List (ℕ × ℕ) :=
  (List.range 5).flatMap fun a => ((List.range 5).filter (a < ·)).map fun b => (a, b)

/-- The index of a pair. -/
def pairIdx (a b : ℕ) : ℕ := pairs5.idxOf (min a b, max a b)

/-- A permutation `σ` of `{0, …, 4}` acting on pairs (positions `0–9`) and, if `base`, on the
points (positions `10–14`). -/
def onPairs (base : Bool) (σ : PermData) : PermData :=
  let fp := pairs5.map fun p => pairIdx (get σ.1 p.1) (get σ.1 p.2)
  let ip := pairs5.map fun p => pairIdx (get σ.2 p.1) (get σ.2 p.2)
  if base then
    ((fp ++ (List.range 5).map fun a => 10 + get σ.1 a).toArray,
      (ip ++ (List.range 5).map fun a => 10 + get σ.2 a).toArray)
  else (fp.toArray, ip.toArray)

def sym5 : GensData := symGens 5
def alt5 : GensData := altGens 5
def dih5 : GensData := [cycleOf 5, ofCycles 5 [[1, 4], [2, 3]]]

/-- The group `⟨gs⟩` on pairs and points, at degree 15. -/
def onBoth (gs : GensData) : GroupData Ty.unit.denote := (15, gs.map (onPairs true), ())

/-- The group `⟨gs⟩` on pairs only, at degree 10, all positions forming the base. -/
def onPairsOnly (gs : GensData) : GroupData Ty.unit.denote := (10, gs.map (onPairs false), ())

def check (name : String) (b : Bool) : IO Unit := do
  unless b do throw <| IO.userError s!"{name}: failed"
  IO.println s!"{name}: ok"

#eval check "degree of Sym(5) on the base = 3 (cap 3)"
  (run (degreeProg 10 3 (onBoth sym5)) == some 3)
#eval check "degree of Alt(5) on the base = 3"
  (run (degreeProg 10 3 (onBoth alt5)) == some 3)
#eval check "degree of D5 on the base = 1"
  (run (degreeProg 10 3 (onBoth dih5)) == some 1)
#eval check "Sym(5) is a giant on the base" (run (giantProg 10 (onBoth sym5)) == some true)
#eval check "Alt(5) is a giant on the base" (run (giantProg 10 (onBoth alt5)) == some true)
#eval check "D5 is not a giant on the base" (run (giantProg 10 (onBoth dih5)) == some false)
#eval check "Sym(5) on the base is primitive"
  ((run (baseBlocksProg 10 (onBoth sym5))).map (·.all (·.length == 1)) == some true)
#eval check "D5 on the base is primitive"
  ((run (baseBlocksProg 10 (onBoth dih5))).map (·.all (·.length == 1)) == some true)

/-- The orbital colours of `Sym(5)` on the pairs: three colours, and two pairs have the colour of
`({0, 1}, {2, 3})` exactly when they are disjoint (the Petersen graph). -/
def petersenOK : Bool :=
  match run (orbitalProg 0 (onPairsOnly sym5)) with
  | none => false
  | some c =>
    let col := fun i j => get c (i * 10 + j)
    let disj := col (pairIdx 0 1) (pairIdx 2 3)
    ((List.range 100).map (get c)).dedup.length == 3 &&
      (List.range 10).all fun i => (List.range 10).all fun j =>
        let p := pairs5.getD i (0, 0)
        let q := pairs5.getD j (0, 0)
        (col i j == disj) == (p.1 != q.1 && p.1 != q.2 && p.2 != q.1 && p.2 != q.2)

#eval check "orbital configuration of Sym(5) on pairs: the Petersen graph" petersenOK

#eval check "the kernel of Sym(5) on the base is trivial, with 120 coset representatives"
  ((run (kerProg 10 (onBoth sym5))).map (fun r => r.2.length) == some 120)

/-- The Johnson labels of the pairs: pair `{a, b}` is labelled `[a, b]` (base indices). -/
def johnsonLabels : LabelData :=
  (pairs5.map (fun p : ℕ × ℕ => [p.1, p.2]) ++ (List.range 5).map fun _ => ([] : List ℕ)).toArray

/-- The generator condition of `HintValid` for the Johnson labels of `Sym(5)`: the label of
`g i` is the image of the label of `i`. -/
def johnsonEquivarOK : Bool :=
  (onBoth sym5).2.1.all fun g => (List.range 10).all fun i =>
    let lhs := johnsonLabels.getD (get g.1 i) []
    let rhs := (johnsonLabels.getD i []).map fun j => get g.1 (10 + j) - 10
    lhs.all rhs.contains && rhs.all lhs.contains

#eval check "Sym(5): the Johnson labels are equivariant on the generators" johnsonEquivarOK

/-- `C₂ ≀ C₂` on four base points (no string positions), re-based onto its two blocks: the new
group has degree `2` and moves the two block points. -/
def rebaseOK : Bool :=
  let gs : GensData := [ofCycles 4 [[0, 1]], ofCycles 4 [[0, 2], [1, 3]]]
  match run (rebaseProg 0 4 gs [[0, 1], [2, 3]]) with
  | none => false
  | some G => G.1 == 2 && G.2.1.any fun g => get g.1 0 == 1

#eval check "C2 wr C2 re-based onto its blocks acts on two block points" rebaseOK

end GraphIsoChecks.Toolkit
