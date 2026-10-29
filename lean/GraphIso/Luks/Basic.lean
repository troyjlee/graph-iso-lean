module

public import GraphIso.Sims.Basic
public import GraphIso.Cost.Program

/-!
# Maximal block systems: functional models

A partition of the points of a window `pts` is given by a **label array** `cl` of size `n`: two
window points are in the same class when they have the same label (`get cl`).

* `closure gs pts cl u v`: a worklist computing the finest partition that is invariant under
  the generators, coarser than `cl`, and joins `u` and `v`. The state is the labels and the
  pending pairs, starting from `[(u, v)]`. A pending pair whose points have the same label is
  dropped. Otherwise the class of the second point is relabelled to the label of the first,
  and the images of the pair under every generator are queued.
* `maxLabels n gs pts u`: one pass over the window from the discrete partition. A point `v`
  outside the class of `u` replaces the partition by `closure gs pts cl u v`, unless that
  closure has a single class.
* `maxBlocks n gs pts`: the classes of `maxLabels` for the first window point, one block per
  **leader** (a point that labels itself), in window order.

`GraphIso/Luks/Closure.lean` and `GraphIso/Luks/MaxBlocks.lean` prove what they compute; the
programs of the cost language compute these functions.
-/

@[expose] public section

namespace GraphIso.Luks

open Cost Sims

/-! ### The closure of a partition and a pair -/

/-- The images of the pair `(a, b)` under the generators. -/
def pairImages (gs : GensData) (a b : ℕ) : List (ℕ × ℕ) := gs.map fun g => (get g.1 a, get g.1 b)

/-- The new label of the window point `p` when the class labelled `cb` is relabelled `ca`. -/
def newLabel (cl : Array ℕ) (cb ca p : ℕ) : ℕ := if get cl p = cb then ca else get cl p

/-- Relabel the class labelled `cb` to `ca`, on the window points. -/
def relabel (cl : Array ℕ) (pts : List ℕ) (cb ca : ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) cl (pts.map fun p => (p, newLabel cl cb ca p))

/-- The closure state: the labels and the pending pairs. -/
abbrev CState := Array ℕ × List (ℕ × ℕ)

/-- One closure step: process the first pending pair; `none` when nothing is pending. -/
def closeStep (gs : GensData) (pts : List ℕ) (st : CState) : Option CState :=
  match st.2 with
  | [] => none
  | (a, b) :: rest =>
    if get st.1 a = get st.1 b then some (st.1, rest)
    else some (relabel st.1 pts (get st.1 b) (get st.1 a), pairImages gs a b ++ rest)

/-- Enough steps for the closure: `|pending| + (s + 1) · leaders` drops at every step. -/
def closeFuel (s m : ℕ) : ℕ := (s + 1) * m + 2

/-- The finest invariant partition coarser than `cl` joining `u` and `v`. -/
def closure (gs : GensData) (pts : List ℕ) (cl : Array ℕ) (u v : ℕ) : Array ℕ :=
  (iter (closeStep gs pts) (closeFuel gs.length pts.length) (cl, [(u, v)])).1

/-! ### Maximal block systems -/

/-- The discrete partition: every point labels itself. -/
def discrete (n : ℕ) : Array ℕ := (List.range n).toArray

/-- Every window point has the label of `u`. -/
def oneClass (cl : Array ℕ) (pts : List ℕ) (u : ℕ) : Bool := pts.all fun p => get cl p == get cl u

/-- Process the window point `v`: coarsen to the closure joining `u` and `v`, unless `v` is
already in the class of `u` or the closure has a single class. -/
def mbStep (gs : GensData) (pts : List ℕ) (u : ℕ) (cl : Array ℕ) (v : ℕ) : Array ℕ :=
  if get cl v = get cl u then cl
  else if oneClass (closure gs pts cl u v) pts u then cl
  else closure gs pts cl u v

/-- The labels of a maximal block system containing `u`. -/
def maxLabels (n : ℕ) (gs : GensData) (pts : List ℕ) (u : ℕ) : Array ℕ :=
  pts.foldl (mbStep gs pts u) (discrete n)

/-- The window points that label themselves. -/
def leaders (cl : Array ℕ) (pts : List ℕ) : List ℕ := pts.filter fun p => get cl p == p

/-- The classes of a label array, one per leader, in window order. -/
def blocksOf (cl : Array ℕ) (pts : List ℕ) : List (List ℕ) :=
  (leaders cl pts).map fun l => pts.filter fun p => get cl p == l

/-- The maximal block system for the first window point. -/
def maxBlocks (n : ℕ) (gs : GensData) (pts : List ℕ) : List (List ℕ) :=
  match pts with
  | [] => []
  | u :: _ => blocksOf (maxLabels n gs pts u) pts

end GraphIso.Luks
