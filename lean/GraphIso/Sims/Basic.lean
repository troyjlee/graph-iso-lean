module

public import GraphIso.Representation.Group

/-!
# Sims tables: functional models

A **base order** of degree `n` is an array `b` listing all `n` points without repetition. A
**Sims table** `T` for it has `n` rows of `n` slots: slot `(k, j)` is either empty or holds an
element fixing `b₀, …, b_{k−1}` and mapping `b_k` to `j`, and slot `(k, b_k)` holds the identity.
Reads are total (`slot`), as array reads in the cost model are.

* `sift n b T k x`: from row `k`, repeatedly look up the slot of `x b_k` and continue from the
  next row with `σ⁻¹ x`. It stops past the last row (success) or at an empty slot, and returns
  the row where it stopped and the residue.
* `build n b gs`: the worklist construction. Its state is the table, the list of entries
  `(row, element)` and the pending items `(row, element)` still to be sifted. Processing an
  item that does not sift inserts the residue into its empty slot and queues the products the
  closure criterion needs: `(l, h σ)` for every entry `σ` at row `l ≤ k` and `(k, τ h)` for
  every entry `τ` at a row `≥ k`, where `h` is the new entry at row `k`.

These are the functions the programs of the cost language compute; the theory of
`GraphIso/Sims/Table.lean` and `GraphIso/Sims/Construct.lean` proves what they compute.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv

/-- A Sims table: `T[k][j]` is slot `(k, j)`. -/
abbrev Table := Array (Array (Option PermData))

/-- Slot `(k, j)`; empty out of bounds. -/
def slot (T : Table) (k j : ℕ) : Option PermData := (T.getD k #[]).getD j none

/-- Fill slot `(k, j)` with `h`. -/
def fill (T : Table) (k j : ℕ) (h : PermData) : Table :=
  T.setIfInBounds k ((T.getD k #[]).setIfInBounds j (some h))

/-- Iterate a step function at most `fuel` times, stopping when it returns `none`. -/
def iter {α : Type} (f : α → Option α) : ℕ → α → α
  | 0, a => a
  | k + 1, a =>
    match f a with
    | none => a
    | some a' => iter f k a'

/-! ### Sifting -/

/-- One sifting step from row `k` with element `x`; `none` past the last row or at an empty
slot. -/
def siftStep (n : ℕ) (b : Array ℕ) (T : Table) (st : ℕ × PermData) : Option (ℕ × PermData) :=
  if st.1 < n then
    match slot T st.1 (get st.2.1 (get b st.1)) with
    | none => none
    | some σ => some (st.1 + 1, σ.inv.mul st.2)
  else none

/-- Sift `x` from row `k`: the row where sifting stops and the residue. It succeeds when the
row is `n`. -/
def sift (n : ℕ) (b : Array ℕ) (T : Table) (k : ℕ) (x : PermData) : ℕ × PermData :=
  iter (siftStep n b T) n (k, x)

/-! ### The construction -/

/-- An entry or a pending item: a row and an element. -/
abbrev Item := ℕ × PermData

/-- The state of the construction: table, entries, pending items. -/
abbrev State := Table × List Item × List Item

/-- Queue the items of one entry `e = (l, σ)` for a new entry `h` at row `k`: `(l, h σ)` if
`l ≤ k`, and `(k, σ h)` if `k ≤ l`. -/
def newItemsStep (k : ℕ) (h : PermData) (acc : List Item) (e : Item) : List Item :=
  let acc₁ := if k < e.1 then acc else (e.1, h.mul e.2) :: acc
  if e.1 < k then acc₁ else (k, e.2.mul h) :: acc₁

/-- The items queued for a new entry `h` at row `k`, given all entries `ent` (including the
new one): `(l, h σ)` for each entry `(l, σ)` with `l ≤ k`, and `(k, τ h)` for each entry
`(l, τ)` with `k ≤ l`. -/
def newItems (k : ℕ) (h : PermData) (ent : List Item) : List Item :=
  ent.foldl (newItemsStep k h) []

/-- One iteration: sift the first pending item; if it does not sift, insert the residue and
queue the new products. `none` when nothing is pending. -/
def step (n : ℕ) (b : Array ℕ) (st : State) : Option State :=
  match st.2.2 with
  | [] => none
  | it :: rest =>
    let r := sift n b st.1 it.1 it.2
    if r.1 < n then
      let ent := r :: st.2.1
      some (fill st.1 r.1 (get r.2.1 (get b r.1)) r.2, ent, newItems r.1 r.2 ent ++ rest)
    else some (st.1, st.2.1, rest)

/-- The table holding only the identities, at slots `(k, b_k)`. -/
def initTable (n : ℕ) (b : Array ℕ) : Table :=
  (b.toList.map fun p => (Array.replicate n none).setIfInBounds p (some (PermData.one n))).toArray

/-- The initial state: identities, and every generator pending at row `0`. -/
def init (n : ℕ) (b : Array ℕ) (gs : GensData) : State :=
  (initTable n b, (List.range n).map (fun k => (k, PermData.one n)), gs.map fun g => (0, g))

/-- Enough iterations for `L` generators in degree `n` (proved in `Construct.lean`). -/
def fuel (n L : ℕ) : ℕ := L + 2 * (n * n) * (n * n) + 1

/-- The construction for base order `b`. -/
def build (n : ℕ) (b : Array ℕ) (gs : GensData) : State :=
  iter (step n b) (fuel n gs.length) (init n b gs)

/-! ### Reading a table -/

/-- The number of filled slots of row `k`. -/
def rowCount (T : Table) (k : ℕ) : ℕ := ((T.getD k #[]).toList.filter Option.isSome).length

/-- The product of the row counts: the group order, for a complete table. -/
def order (n : ℕ) (T : Table) : ℕ := ((List.range n).map (rowCount T)).prod

end GraphIso.Sims
