module

public import GraphIsoChecks.MainM5CJ
meta import GraphIsoChecks.MainM5CJ
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-4b checks: Case 2b's Johnson route on the Clebsch graph

The staged check accepted by `PLAN-14.md` §14.5 item 5 (amended 24 October 2026), on an
instance in Case 2b's setting. Earlier stages use their proved-equal data models; the Align
suffix runs through the interpreter on distinct candidates. This is not an end-to-end run
of either case program, nor a composed execution theorem for one.

**The instance** (`f`). `G = Sym(16)`, acting alike on the window `[0, 16)` and the base
`[16, 32)` (`n = 16`, `m = 16`), with the labels `{i}`; `ψ(G) = Sym(16) ⊇ Alt(16)` (order `16!`,
read from the Schreier–Sims table). The string `x` has the distinct colours `1, …, 16` on the
window, and `y = relabel g₀ x`, so `g₀` (acting alike) is the only isomorphism. The validity of
the instance is decided on the generators (`okG`), since `G` (order `16!`) cannot be enumerated:
generators acting alike make every element act alike, so the window and the base are invariant
and `G` is faithful on the window; the labels' equivariance passes to products; transitivity on
the window is the generators' orbit.

**The full groups.** `F(x) = C = 2⁴ : Sym(5)` (order `1920`, the automorphism group of the
Clebsch graph on the base: `𝔽₂⁴`, two vectors adjacent when their difference is one of
`e₁, …, e₄, e₁ + ⋯ + e₄`), and `F(y) = g₀ C g₀⁻¹`. These are `Fmap x` and `Fmap y` for a
`G`-equivariant `Fmap` depending only on the strings on the window: `G` acts regularly on the
orbit of `x` (`x` is injective on the window and `G` is faithful there), so
`Fmap (relabel g x) = g C g⁻¹` is well defined on that orbit (and `Fmap z = Aut_G(z)` elsewhere).

**Case 2b's conditions.** `Φ` is the whole base: an orbit of `ψ(F(x))` and of `ψ(F(y))`, with
`2|Φ| = 32 > 16`; `ψ(F)` is transitive and not doubly transitive on `Φ` (`Case2bHyp` at `d = 1`:
the orbit of a pair is an orbital, of `80` or `160` of the `240` ordered pairs); the degree is
`1` for both, so `j = 0`.

**The route.**
* Case 2b's test `c2bJD` holds: `x`'s first leaf (the empty tuple, the orbital of `(0, 1)`
  refined by Weisfeiler–Leman, Split-or-Johnson at `t = (16 + 3)/2 = 9`) is a Johnson leaf:
  `J(5, 2)` on the ten non-neighbours `V₀` of the individualized vertex, the cells its five
  neighbours (singletons), `s = 2`, each point of `V₀` at the two cells adjacent to it. Item 1's
  threshold holds: `(16 + 3)/2 = 9 < |V₀| = 10`.
* The colouring `q2bD` (`1` on `Φ`, the tuple being empty) and the bound `hq`: the six points
  outside `V₀` form one colour class, `2 · 6 ≤ 16`.
* `y`'s candidates `cjLeaves2bD`: `240` choices of a pair, each with `16` Johnson leaves (one per
  individualized vertex), `3840` coloured pairs, `16` distinct. They are computed by `ys2bM`,
  which computes each choice's colouring once and the leaves once per distinct colouring;
  `ys2bM_eq` proves it equal to `cjLeaves2bD`.
* **The Align suffix of `c2bCJProg`**, run with modified input: `cjohnOps` on `x`'s coloured
  pair and the `16` distinct candidates, reduce-and-derive with `st = (2, X₀)` on each aligned
  coset (`MainM5CJ.alP`). The answer is the brute-force coset `{g₀}`; `g₀` carries `x`'s pair to
  a candidate (`halign`); the children are `StepChild |W| m` with the factor `16 · m`, below
  `RunsWithin.alignRd_cj_ns`'s `|Ys| · max(m, uB!)`.

**What runs as data.** The route's earlier programs are costly on this instance: one choice of
`Case2b.choiceProg` (Split-or-Johnson on `16` points) takes `160` seconds and a trace of `213`
million events (`12` GB) in the interpreter, and the route runs it once for `x`
(`firstLeafProg`, inside the test and again in `c2bCJProg`) and `240` times for `y`
(`cjLeaves2bProg`). Align over all `3840` candidates would take about `6` seconds each after
about `130` seconds of setup. So the test, the degrees, `x`'s first leaf and `y`'s candidates
are computed by the data functions that the programs return (`RunsWithin.c2bJTestProg`,
`RunsWithin.degProg_le`, `RunsWithin.firstLeafProg_le`, `RunsWithin.cjLeaves2bProg_le`); the
colouring and the first tuple are also run as programs (`q2bProg`, `firstTupleProg`). The
answer-correctness argument in `RunsWithin.alignRd` uses `halign`, which depends only on
candidate membership, so it applies to both the distinct candidates and the full list. The
execution iterates over every list entry: no equality of executions, costs or child summaries
is claimed. In particular, the 22 observed children belong only to the suffix on 16 candidates.

The whole file runs in about five minutes (`y`'s candidates about 80 seconds, the Align call
about 220 seconds), in under 3 GB.
-/

@[expose] public section

namespace GraphIsoChecks.MainM5CJRoute

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Toolkit
  GraphIsoChecks.Sweep GraphIsoChecks.MainM5

/-! ### `y`'s candidates, memoized -/

/-- The leaves `leavesOfD m'` at the distinct colourings of `cs`, each computed once. -/
def memoL (m' : ℕ) (cs : List (Array ℕ)) : List (Array ℕ × List SoJTree.OutD) :=
  cs.foldl (fun acc C =>
    if acc.any (·.1 == C) then acc else acc ++ [(C, Case2b.leavesOfD m' C)]) []

theorem memoL_spec (m' : ℕ) (cs : List (Array ℕ)) :
    ∀ p ∈ memoL m' cs, p.2 = Case2b.leavesOfD m' p.1 := by
  suffices h : ∀ acc : List (Array ℕ × List SoJTree.OutD),
      (∀ p ∈ acc, p.2 = Case2b.leavesOfD m' p.1) →
      ∀ p ∈ cs.foldl (fun acc C =>
        if acc.any (·.1 == C) then acc else acc ++ [(C, Case2b.leavesOfD m' C)]) acc,
        p.2 = Case2b.leavesOfD m' p.1 from h [] (by simp)
  induction cs with
  | nil => exact fun acc h => by simpa using h
  | cons C cs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    split
    · exact h
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact h p hp
      · simp only [List.mem_singleton] at hp
        subst hp
        rfl

/-- A colouring's leaves, looked up in a table (computed when absent). -/
def lookL (m' : ℕ) (T : List (Array ℕ × List SoJTree.OutD)) (C : Array ℕ) :
    List SoJTree.OutD :=
  match T.find? (·.1 == C) with
  | some p => p.2
  | none => Case2b.leavesOfD m' C

theorem lookL_eq {m' : ℕ} {T : List (Array ℕ × List SoJTree.OutD)}
    (hT : ∀ p ∈ T, p.2 = Case2b.leavesOfD m' p.1) (C : Array ℕ) :
    lookL m' T C = Case2b.leavesOfD m' C := by
  unfold lookL
  split
  next p hp =>
    have hC : p.1 = C := by simpa using List.find?_some hp
    rw [hT p (List.mem_of_find?_eq_some hp), hC]
  next => rfl

/-- **`y`'s coloured Johnson leaves, memoized**: `cjLeaves2bD` with each choice's colouring
computed once and the leaves once per distinct colouring. -/
def ys2bM {D : Ty} (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ : List ℕ)
    (j : ℕ) : List CJData :=
  (Case2b.tuplesD Φ j).flatMap fun S =>
    let m' := (Case2b.phiSD (N - n) Φ S).length
    let cs := (Case2b.pairsD m').map fun ab => Case2b.wlColOf O N n F Φ S ab.1 ab.2
    let T := memoL m' cs
    cs.flatMap fun C =>
      ((lookL m' T C).map (Case2b.extD (N - n) (Case2b.phiSD (N - n) Φ S))).flatMap
        (cjOfD (q2bD (N - n) Φ S))

/-- **The memoized list is `cjLeaves2bD`.** -/
theorem ys2bM_eq {D : Ty} (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote)
    (Φ : List ℕ) (j : ℕ) : ys2bM O N n F Φ j = cjLeaves2bD O N n F Φ j := by
  unfold ys2bM cjLeaves2bD
  congr 1
  funext S
  simp only [cjChoice2bD, Case2b.choiceLeavesD, lookL_eq (memoL_spec _ _), List.flatMap_map]

/-! ### The instance -/

/-- The linear map of `𝔽₂⁴` with `eᵢ ↦ img[i]`, vectors encoded as `0, …, 15`. -/
def lin (img : List ℕ) (v : ℕ) : ℕ :=
  (List.range 4).foldl (fun acc i => if v.testBit i then acc ^^^ img.getD i 0 else acc) 0

/-- The Clebsch graph: the difference is one of `e₁, e₂, e₃, e₄, e₁ + e₂ + e₃ + e₄`. -/
def adj (u v : ℕ) : Bool := [1, 2, 4, 8, 15].contains (u ^^^ v)

/-- **`C = 2⁴ : Sym(5)`** on the base indices: the translation by `e₁`, and the linear maps
swapping `e₁, e₂` and cycling `e₁ → e₂ → e₃ → e₄ → e₁ + ⋯ + e₄ → e₁`. -/
def cgens : List (List ℕ) :=
  [(List.range 16).map (· ^^^ 1), (List.range 16).map (lin [2, 1, 4, 8]),
   (List.range 16).map (lin [2, 4, 8, 15])]

/-- A permutation of `[0, 16)` acting alike on the window and the base (degree `32`). -/
def alike (p : List ℕ) : List ℕ := p ++ p.map (· + 16)

/-- `G = Sym(16)`: a transposition and a `16`-cycle, acting alike. -/
def s16 : List (List ℕ) :=
  [alike ([1, 0] ++ (List.range 16).drop 2), alike ((List.range 16).map fun i => (i + 1) % 16)]

/-- The inverse of a permutation of `[0, 16)`. -/
def inv16 (g : List ℕ) : List ℕ :=
  (List.range 16).map fun v => ((List.range 16).find? fun u => g.getD u 0 == v).getD 0

/-- `g p g⁻¹`. -/
def conj16 (g p : List ℕ) : List ℕ :=
  (List.range 16).map fun v => g.getD (p.getD ((inv16 g).getD v 0) 0) 0

/-- The isomorphism. -/
def g0 : List ℕ := [3, 7, 0, 12, 1, 9, 15, 4, 11, 2, 6, 14, 5, 10, 8, 13]

/-- `F(x) = C` and `F(y) = g₀ C g₀⁻¹`, acting alike. -/
def FX : GroupData Ty.unit.denote := (32, MainSteps.gD (cgens.map alike), ())
def FY : GroupData Ty.unit.denote :=
  (32, MainSteps.gD (cgens.map fun c => alike (conj16 g0 c)), ())

/-- `x`: the colours `1, …, 16` on the window; `y = relabel g₀ x`, i.e. `y (g₀ u) = x u`. -/
def x0 : List ℕ := (List.range 16).map (· + 1) ++ List.replicate 16 0
def y0 : List ℕ :=
  ((List.range 16).map fun v => x0.getD ((inv16 g0).getD v 0) 0) ++ List.replicate 16 0

/-- The instance: `n = 16`, `N = 32`, labels `{i}`. -/
def f : MainSteps.SFix := ⟨16, 32, s16, List.range 16, List.range 32, x0, y0,
  some ((List.range 16).map ([·])).toArray⟩

/-- The large orbit: the whole base. -/
def Φ : List ℕ := List.range 16

/-! ### Checks on data -/

/-- Without repetitions, in order of first occurrence. -/
def dedupL {α : Type} [BEq α] (l : List α) : List α :=
  l.foldl (fun acc e => if acc.contains e then acc else acc ++ [e]) []

/-- The orbit of `u` under the generators. -/
def orbitG (gs : List (List ℕ)) (u : ℕ) : List ℕ :=
  (List.range 32).foldl (fun acc _ => dedupL (acc ++ acc.flatMap fun v =>
    gs.map fun g => MainSteps.ap g v)) [u]

/-- A degree-`32` permutation acting alike on `[0, 16)` and `[16, 32)`. -/
def alikeB (g : List ℕ) : Bool :=
  g.length == 32 && (g.take 16).all (· < 16) && (g.take 16).dedup.length == 16 &&
    (List.range 16).all fun i => g.getD (16 + i) 0 == 16 + g.getD i 0

/-- **The instance is valid**, decided on the generators (`MainSteps.SFix.ok` enumerates the
group): alike generators, transitive on the window, valid labels, strings of length `N`, `σ = 1`;
and `ψ(G) = Sym(16)`, of order `16!`. -/
def okG : Bool :=
  f.gs.all alikeB && (orbitG f.gs 0).length == 16 &&
    MainSteps.labOK 16 16 f.gs f.w (f.L.getD #[]) && f.x.length == 32 && f.y.length == 32 &&
    f.σ == List.range 32 &&
    Sims.order 16 (Sims.build 16 (List.range 16).toArray
      (MainSteps.gD (f.gs.map (·.take 16)))).1 == Nat.factorial 16

/-- **Case 2b's conditions** on `F(x) = C` and `F(y) = g₀ C g₀⁻¹`: `C` preserves the Clebsch
graph and has order `1920`; both act alike (so lie in `G`), are transitive on the base and not
doubly transitive (the orbit of `(0, 1)` has `80`, respectively `160`, of the `240` ordered
pairs: `0, 1` are adjacent in the Clebsch graph of `x`, not in that of `y`); `x` is injective on
the window and `y = relabel g₀ x`. -/
def caseOK : Bool :=
  let C := closure 16 cgens
  let Cy := closure 16 (cgens.map (conj16 g0))
  cgens.all (fun c => (List.range 16).all fun u => (List.range 16).all fun v =>
      adj u v == adj (c.getD u 0) (c.getD v 0)) &&
    C.length == 1920 && Cy.length == 1920 &&
    FX.2.1.all (fun g => alikeB g.1.toList) && FY.2.1.all (fun g => alikeB g.1.toList) &&
    (orbitG cgens 0).length == 16 && (orbitG (cgens.map (conj16 g0)) 0).length == 16 &&
    (dedupL (C.map fun g => (g.getD 0 0, g.getD 1 0))).length == 80 &&
    (dedupL (Cy.map fun g => (g.getD 0 0, g.getD 1 0))).length == 160 &&
    (x0.take 16).dedup.length == 16 &&
    (List.range 16).all fun u => y0.getD (g0.getD u 0) 0 == x0.getD u 0

/-- **`x`'s Johnson leaf**: tag `2`; `V₀` the ten non-neighbours of the one point outside `V₀`
and the cells, the cells its five neighbours as singletons, `s = 2`, and each point of `V₀` at the
two cells adjacent to it; `(16 + 3)/2 < |V₀|`. -/
def leafOK (X₀ : SoJTree.OutD) : Bool :=
  let V₀ := X₀.2.2.1
  let cells := X₀.2.2.2.1
  let out := (List.range 16).filter fun v => decide (v ∉ V₀) && !cells.any fun c => decide (v ∈ c)
  match out with
  | [p] =>
    X₀.1 == 2 && X₀.2.2.2.2.1 == 2 && V₀.length == 10 && decide ((16 + 3) / 2 < V₀.length) &&
      cells.length == 5 && cells.all (·.length == 1) &&
      cells.all (fun c => adj p (c.headD 0)) && V₀.all (fun v => !adj p v) &&
      V₀.all fun v =>
        MainSteps.setEq (X₀.2.2.2.2.2.getD v [])
          ((List.range 5).filter fun i => adj v ((cells.getD i []).headD 0))
  | _ => false

/-- **The colour bound `hq`** for `x`'s coloured pair: outside `V₀`, every colour class has at
most `m/2 = 8` points. -/
def hqOK (X : CJData) : Bool :=
  let out := (List.range 16).filter fun v => decide (v ∉ X.1.1)
  out.all fun v => decide (2 * (out.filter fun u => get X.2 u == get X.2 v).length ≤ 16)

/-! ### The run -/

/-- **The route**, step by step (each step throws on a failure). -/
def route : IO Unit := do
  let step (name : String) (b : Bool) : IO Unit := do
    unless b do throw <| IO.userError s!"{name}: failed"
    IO.println s!"{name}: ok"
  step "the instance (G = Sym(16) alike, labels {i}, giant)" okG
  step "Case 2b's conditions (F(x) = 2⁴:Sym(5), F(y) its conjugate)" caseOK
  step "the degrees (1, so j = 0) and the test c2bJD"
    (Case2b.degD ssOracle 32 16 FX Φ == 1 && Case2b.degD ssOracle 32 16 FY Φ == 1 &&
      c2bJD ssOracle 32 16 FX Φ)
  let X₀ := (Case2b.firstLeafD ssOracle 32 16 FX Φ 0).getD SoJTree.noneD
  step "x's first leaf: J(5, 2) on the non-neighbours, |V₀| = 10 > 9" (leafOK X₀)
  let X₀c := cjFirst2bD 32 16 Φ 0 X₀
  step "the colouring (constant on Φ; programs q2bProg, firstTupleProg) and hq"
    (X₀c.2.toList == List.replicate 16 1 &&
      MainSteps.runV (q2bProg (S := groupSig Ty.unit) (rec := Solver.Rec Ty.unit) 16 Φ []) ==
        some (q2bD 16 Φ []) &&
      MainSteps.runV (firstTupleProg (S := groupSig Ty.unit) (rec := Solver.Rec Ty.unit) Φ 0) ==
        some (firstTupleD Φ 0) && hqOK X₀c)
  let Ys := ys2bM ssOracle 32 16 FY Φ 0
  let ysD := dedupL Ys
  step "y's candidates: 3840 coloured pairs, 16 distinct; g₀ carries x's pair to one (halign)"
    (Ys.length == 3840 && ysD.length == 16 && ysD.any (MainHints.cjMaps 16 g0 X₀c))
  match MainSteps.runT (MainM5CJ.alP f X₀c ysD) with
  | some (a, tr) =>
    let cs := MainSteps.records tr
    step s!"Align with cjohnOps and reduce-and-derive at (2, X₀): the answer is \{g₀}; \
        {cs.length} children, StepChild with the factor 16 · m"
      (MainSteps.ansOK 32 [alike g0] a &&
        MainSteps.solsB [alike g0] f.σ f.x f.y f.w == [alike g0] &&
        MainSteps.childrenOK f (ysD.length * 16) (MainSteps.stepB 16 16) (f.N * f.N) cs)
  | none => throw <| IO.userError "Align: the run failed"

#eval route

end GraphIsoChecks.MainM5CJRoute
