module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The Palomar statement: its definitions

`PLAN-19.md` §5–§6 and Appendices A and B. The single-tape graph-isomorphism theorems are stated
with these definitions and Mathlib's, nothing else, so that what they claim can be read without
the library. This file imports Mathlib only. `GraphIso.Palomar.Bridge` relates the definitions
to the library's encodings and proves the statements (`gi_singleTape_proof`,
`gi_coset_singleTape_proof`, `cosetWord_injective_proof`). For the Palomar submission,
`scripts/palomar-snapshot.sh` writes the challenge file `Challenge.lean`: this text followed by
the statements, with their proofs left open (`PLAN-19.md` §7).

**The words.** The machines' inputs and outputs are words over `Sym`, which fixed injective maps
take into a machine's tape alphabet:
* a natural number is its binary digits, least significant first, without trailing zeros
  (Mathlib's `Nat.bits`), then `endNum`;
* a list is each element after `cons`, then `nil`;
* a simple graph on `Fin n` is the list of the neighbour lists (each in increasing order) of the
  vertices `n - 1`, …, `0`, in that order, which is the order in which the library serializes
  its adjacency arrays;
* a permutation `σ` of `Fin n` is the list of the images `σ (n - 1)`, …, `σ 0`, then the list
  of the inverse images in the same order (the library's forward and inverse arrays);
* the input of graphs `G`, `H` on `Fin n` is `n`, `G`, `H` between the marks `lmark` and
  `rmark`; the decision machine's output is `yes` or `no` between the marks; the coset
  machine's output is `no`, or `yes`, a permutation and a list of permutations, between the
  marks.
-/

@[expose] public section

namespace GraphIsoPalomar

/-- The symbols of the input and output words. -/
inductive Sym where
  /-- A binary digit. -/
  | digit (b : Bool)
  /-- The end of a number. -/
  | endNum
  /-- Before each element of a list. -/
  | cons
  /-- The end of a list. -/
  | nil
  /-- The left end of a word on the tape. -/
  | lmark
  /-- The right end of a word on the tape. -/
  | rmark
  /-- The answer "isomorphic". -/
  | yes
  /-- The answer "not isomorphic". -/
  | no

/-- A natural number: its binary digits, least significant first, without trailing zeros
(`Nat.bits`), then `endNum`. -/
def natWord (k : ℕ) : List Sym :=
  (Nat.bits k).map Sym.digit ++ [Sym.endNum]

/-- A list of words: each after `cons`, then `nil`. -/
def listWord (ws : List (List Sym)) : List Sym :=
  (ws.map (Sym.cons :: ·)).flatten ++ [Sym.nil]

/-- The neighbours of `u` in `G`, in increasing order. -/
def nbrs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) : List ℕ :=
  ((List.finRange n).filter fun v => G.Adj u v).map (·.val)

/-- A graph on `Fin n`: the list, from the last vertex `n - 1` down to `0`, of the neighbour
lists. -/
def graphWord {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List Sym :=
  listWord ((List.finRange n).reverse.map fun u => listWord ((nbrs G u).map natWord))

/-- **The input**: `n`, then `G`, then `H`, between the marks. -/
def input {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    List Sym :=
  Sym.lmark :: (natWord n ++ graphWord G ++ graphWord H) ++ [Sym.rmark]

/-- **The output**: the answer between the marks. -/
def output (b : Bool) : List Sym :=
  [Sym.lmark, if b then Sym.yes else Sym.no, Sym.rmark]

/-- A permutation `σ` of `Fin n`: the images `σ i`, then the inverse images `σ⁻¹ i`, each as a
list of numbers, for `i` from `n - 1` down to `0`. -/
def permWord {n : ℕ} (σ : Equiv.Perm (Fin n)) : List Sym :=
  listWord ((List.finRange n).reverse.map fun i => natWord (σ i)) ++
    listWord ((List.finRange n).reverse.map fun i => natWord (σ.symm i))

/-- **The output of the coset machine**, between the marks: `no` when there is no isomorphism;
otherwise `yes`, an isomorphism `τ`, and the list of generators `gs`. -/
def cosetWord {n : ℕ} : Option (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n))) → List Sym
  | none => [Sym.lmark, Sym.no, Sym.rmark]
  | some (τ, gs) =>
    Sym.lmark :: Sym.yes :: (permWord τ ++ listWord (gs.map permWord)) ++ [Sym.rmark]

end GraphIsoPalomar
