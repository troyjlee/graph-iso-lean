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

/-- **Graph isomorphism is decided by a single-tape Turing machine in quasipolynomial time.**
There are a Turing machine `M` of mathlib's single-tape model `Turing.TM0`, with a finite tape
alphabet `Γ` and finitely many states, an injective map `ι` of the symbols above into `Γ`, none of
them blank, and a constant `c`, such that for all `n` and all simple graphs `G`, `H` on `Fin n`:
started (in its start state `default`, head on the first symbol, blanks elsewhere) on the tape
`ι (input G H)`, `M` makes at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions and halts (`step`
returns `none`) with the tape `ι (output b)`, head on its first symbol and blanks elsewhere, where
`b = true` exactly when `G` and `H` are isomorphic. -/
theorem gi_singleTape :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ), Finite Γ ∧ Finite Λ ∧
      ∃ (M : Turing.TM0.Machine Γ Λ) (ι : Sym ↪ Γ) (c : ℕ), (∀ s, ι s ≠ default) ∧
        ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
          ∃ b : Bool, (b = true ↔ Nonempty (G ≃g H)) ∧
            ∃ k ≤ 2 ^ (c * (Nat.log 2 n + 1) ^ 8), ∃ q : Λ,
              (flip bind (Turing.TM0.step M))^[k]
                  (some (Turing.TM0.init ((input G H).map ι))) =
                some ⟨q, Turing.Tape.mk₁ ((output b).map ι)⟩ ∧
              Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((output b).map ι)⟩ = none := by
  sorry

/-- **The coset machine's output determines its answer**: `cosetWord` is injective. -/
theorem cosetWord_injective (n : ℕ) : Function.Injective (cosetWord (n := n)) := by
  sorry

/-- **All isomorphisms of two graphs, by a single-tape Turing machine in quasipolynomial time.**
There are a Turing machine `M` of mathlib's single-tape model `Turing.TM0`, with a finite tape
alphabet `Γ` and finitely many states, injective maps `ιin`, `ιout` of the symbols into `Γ`, none
of them blank, and a constant `c`, such that for all `n` and all simple graphs `G`, `H` on
`Fin n` there is an answer `r` with:
* `r = none` exactly when `G` and `H` are not isomorphic;
* if `r = some (τ, gs)`, a permutation `φ` of `Fin n` underlies an isomorphism `G ≃g H` exactly
  when `τ⁻¹ * φ` lies in the subgroup generated by `gs`: the isomorphisms form the left coset of
  that subgroup by `τ`;
* started (in its start state `default`, head on the first symbol, blanks elsewhere) on the tape
  `ιin (input G H)`, `M` makes at most `2 ^ (c (⌊log₂ n⌋ + 1) ^ 8)` transitions and halts with
  the tape `ιout (cosetWord r)`, head on its first symbol and blanks elsewhere. -/
theorem gi_coset_singleTape :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ), Finite Γ ∧ Finite Λ ∧
      ∃ (M : Turing.TM0.Machine Γ Λ) (ιin ιout : Sym ↪ Γ) (c : ℕ),
        (∀ s, ιin s ≠ default) ∧ (∀ s, ιout s ≠ default) ∧
        ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
          ∃ r : Option (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n))),
            (r = none ↔ IsEmpty (G ≃g H)) ∧
            (∀ τ gs, r = some (τ, gs) → ∀ φ : Equiv.Perm (Fin n),
              (∃ e : G ≃g H, e.toEquiv = φ) ↔ τ⁻¹ * φ ∈ Subgroup.closure {g | g ∈ gs}) ∧
            ∃ k ≤ 2 ^ (c * (Nat.log 2 n + 1) ^ 8), ∃ q : Λ,
              (flip bind (Turing.TM0.step M))^[k]
                  (some (Turing.TM0.init ((input G H).map ιin))) =
                some ⟨q, Turing.Tape.mk₁ ((cosetWord r).map ιout)⟩ ∧
              Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((cosetWord r).map ιout)⟩ = none := by
  sorry

end GraphIsoPalomar
