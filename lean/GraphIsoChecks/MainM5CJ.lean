module

public import GraphIsoChecks.MainM5b
meta import GraphIsoChecks.MainM5b
public import GraphIsoChecks.MainHints
meta import GraphIsoChecks.MainHints
public import GraphIso.Main.M5CJWf
meta import GraphIso.Main.M5CJWf
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-4b checks: coloured Johnson alignment in M5

Checks of the stage 14j-4b programs and data (`GraphIso/Main/M5CJ*.lean`, `M5Case2bCJ`,
`M5Case3CJ`, `M5StepCJ`), each against brute force or an independent description computed in
the same term. Runs use the verified Schreier–Sims oracle for the backend calls and milestone 1's
solver as the recursive procedure; sub-calls go to the instrumented sub-solver
`MainSteps.spySub` (as in `GraphIsoChecks.MainM5`).

**Johnson leaves need large fixtures.** A Johnson leaf of Case 2b or 3 has `V₀` of more than
`(m' + 3)/2` points of a numbered set of size `m'` (`PLAN-14.md` §14.5 item 1): a colour class of
more than half the points carrying a Johnson scheme after individualization. The smallest case is
the Clebsch graph (`m' = 16`, `J(5, 2)` on the ten non-neighbours of a vertex), on which
`GraphIsoChecks.MainM5CJRoute` checks Case 2b's Johnson route. Case 3's certificates are trivial
for `k ≤ 2` (stage 14i's checks), and the Petersen colouring of the pairs of `[5]`, given by hand
at `k = 2`, has a coloured partition as its first structure (checked below by the interpreter).
This file exercises the new pieces on small fixtures:

**Kernel-checked examples** (`decide +kernel`):
* **The colourings** `q2bD`, `q3D` against their definitions (Case 2b: `2 + i` at the `i`-th
  point of `S`, `1` on the rest of `Φ`, `0` elsewhere; Case 3: `1` on `C`, `2` on the rest of
  `V`, `0` on the support), and the programs `q2bProg`, `q3Prog` against the data.
* **The coloured leaves** (`cjOfD`, `cjOfProg`): a Johnson leaf gives its datum with the
  colouring, a coloured partition and `none` give nothing; `firstTupleProg` is `firstTupleD`.
* **A coloured Johnson leaf of Case 3's shape** (`cj32`): `J(5, 2)` on a base of `32` points
  (`V₀` the ten pairs `0–9`, the cells the five letters `10–14`, `s = 2`), coloured by `q3D`
  with `C = V₀ ∪ ⋃Λ` (`15` points), the fixed points `V = C ∪ {15, …, 23}` and the support
  `{24, …, 31}`. These are Case 3's conditions: `2 · |supp| = 16 < 32`, `t = tOf 24 = 12 < |C|`,
  and item 1, `(|C| + 3)/2 = 9 < |V₀| = 10`. It is `IsJohnson` (`t = 9`) and `JValid`, and
  satisfies **the colour bound `hq` of `rd_ns_cj`**: outside `V₀` the classes are the cells
  (`5`), the rest of `V` (`9`) and the support (`8`), each at most `32/2`. A **control**: the
  same embedding uncoloured (14j-4's Johnson pair) has a class of `17` points outside `V₀`.
* **A transported pair found among `y`'s pairs**: the image `Y` of `cj32` under the reversal of
  the base (`cjMap`, checked against the brute-force `cjMaps`) is the only pair of `[Z, Y]` that
  `cjohnIsoD` matches with `cj32` (`Z` has a different colour profile), the permutation found
  carries `cj32` to `Y`, and the program `cjohnIsoProg` agrees.

**The Johnson routes' Align call** (`al_j42`, kernel-checked in pieces by `execRuns`). Both
Johnson routes, `c2bCJProg` and `c3CJRouteProg`, end in
`Align.alignProg (rdBranch … (2, X₀)) (cjohnGensProg m) (cjohnIsoProg m) n xy w G X₀ Ys`. This
call runs on `S₄` acting on the four letters (the window, labels `{letter}`) and on a base of
the six pairs and the four letters. `X₀` is a genuine Johnson datum `J(4, 2)` (`V₀` the pairs,
cells the letters, `s = 2`) whose embedding is twisted by the transposition `(0 1)`, so `S₄`
does not preserve it. `Ys` is the image of `X₀` under the isomorphisms (brute force) and a
datum twisted by a 3-cycle (Johnson-isomorphic in `Sym(10)`, but not by `S₄`). The answer is the
brute-force coset. The children are `StepChild |W| m` with the factor `|Ys| · m`, which is at
most `RunsWithin.alignRd_cj_ns`'s `|Ys| · max(m, uB!)`. Every isomorphism carries `X₀` to a
pair of `Ys` (its hypothesis `halign`).

**Interpreter runs** (`#eval`, each throwing on a failure), supplementary:
* the same Align call on two more `J(4, 2)` pairs (four isomorphisms; none) and on `J(5, 2)`
  under `S₅` (base of the ten pairs and five letters);
* **the variants on 14j-4's fixtures** (no Johnson leaf, so 14j-4's programs run inside, after
  the variant's own test or colourings):
  - `m5Case3CJProg` on `MainM5b`'s Case 3 fixtures (one distinguished point, a non-isomorphic
    pair, the fallback), with `2 · c3Count` comparisons (the colourings are computed twice);
  - `m5Case2bCJProg` on the Klein group in `S₄`;
  - the whole step `m5StepCJProg` at `m = 4` (`k = 3`: Case 2a for both strings; Case 2a against
    Case 3; `k = 2`: Case 3).

  Each answer is the brute-force coset, and the children meet the stated bounds of
  `RunsWithin.m5Case3CJProg`, `RunsWithin.m5Case2bCJProg` and `RunsWithin.m5StepCJProg`
  (`uB = m`).
* **The Petersen colouring** (`k = 2`, by hand) of the pairs of `[5]`: the first structure of
  Case 3's pipeline is a coloured partition (tag `1`), so `m5Case3CJProg` would take 14j-4's
  route.
-/

@[expose] public section

namespace GraphIsoChecks.MainM5CJ

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Sims GraphIso.Main GraphIso.Toolkit
  GraphIso.Align GraphIsoChecks.Sweep GraphIsoChecks.Exec GraphIsoChecks.ExecSteps
  GraphIsoChecks.MainM5

/-- Run a program with no backend calls. -/
def runP {t : Ty} (p : Prog Signature.empty (Ty.unit, Ty.unit) Ty.denote t) : Option t.denote :=
  (eval Ctx.empty.O (fun _ => Prog.ret ()) 10000000 p).map Prod.fst

/-! ### The colourings -/

/-- **Case 2b's colouring by its definition**: `2 + i` at the `i`-th point of `S`, `1` on the
rest of `Φ`, `0` elsewhere. -/
def q2bB (m : ℕ) (Φ S : List ℕ) : List ℕ :=
  (List.range m).map fun v => if v ∈ S then 2 + S.idxOf v else if v ∈ Φ then 1 else 0

/-- **Case 3's colouring by its definition**: `1` on `C`, `2` on the rest of `V`, `0` on the
support. -/
def q3B (M : ℕ) (V C : List ℕ) : List ℕ :=
  (List.range M).map fun v => if v ∈ C then 1 else if v ∈ V then 2 else 0

/-- `q2bD`: `Φ = {1, 2, 4, 5, 6, 7}`, the tuple `S = (5, 2)`. -/
example : (q2bD 8 [1, 2, 4, 5, 6, 7] [5, 2] == #[0, 1, 3, 0, 1, 2, 1, 1] &&
    (q2bD 8 [1, 2, 4, 5, 6, 7] [5, 2]).toList == q2bB 8 [1, 2, 4, 5, 6, 7] [5, 2] &&
    runP (q2bProg 8 [1, 2, 4, 5, 6, 7] [5, 2]) == some (q2bD 8 [1, 2, 4, 5, 6, 7] [5, 2]) &&
    (q2bD 6 [0, 1, 2, 3, 4, 5] []).toList == q2bB 6 [0, 1, 2, 3, 4, 5] [] &&
    runP (q2bProg 6 [0, 1, 2, 3, 4, 5] []) == some (q2bD 6 [0, 1, 2, 3, 4, 5] [])) = true := by
  decide +kernel

/-- `q3D`: fixed points `V = {0, 1, 2, 3, 5, 6}`, the class `C = {1, 2, 5}`. -/
example : (q3D 8 [0, 1, 2, 3, 5, 6] [1, 2, 5] == #[2, 1, 1, 2, 0, 1, 2, 0] &&
    (q3D 8 [0, 1, 2, 3, 5, 6] [1, 2, 5]).toList == q3B 8 [0, 1, 2, 3, 5, 6] [1, 2, 5] &&
    runP (q3Prog 8 [0, 1, 2, 3, 5, 6] [1, 2, 5]) == some (q3D 8 [0, 1, 2, 3, 5, 6] [1, 2, 5]))
    = true := by
  decide +kernel

/-! ### The coloured leaves -/

/-- The pairs of `[5]`, in order, as cell indices. -/
def pairs5 : List (List ℕ) :=
  [[0, 1], [0, 2], [0, 3], [0, 4], [1, 2], [1, 3], [1, 4], [2, 3], [2, 4], [3, 4]]

/-- **`J(5, 2)` on a base of `32` points**: `V₀` the ten pairs `0–9`, the cells the five letters
`10–14`, `s = 2`; the rest `15–31`. -/
def j32 : JData := (List.range 10, (List.range 5).map (fun c => [10 + c]), 2, pairs5.toArray)

/-- Case 3's colouring at `j32`: `C = V₀ ∪ ⋃Λ` (`0–14`), the fixed points `V = C ∪ {15, …, 23}`,
the support `{24, …, 31}`. -/
def q32 : Array ℕ := q3D 32 (List.range 24) (List.range 15)

/-- **The coloured Johnson pair** of `j32`. -/
def cj32 : CJData := (j32, q32)

/-- A Johnson leaf, a coloured partition and `none`. -/
def leaves : List SoJTree.OutD :=
  [SoJTree.johnD j32.1 j32.2.1 j32.2.2.1 j32.2.2.2,
    SoJTree.partD #[0, 0, 1, 1] #[[0, 1], [2, 3]], SoJTree.noneD]

/-- **`cjOfD` and `cjOfProg`**: the Johnson leaf gives `(j32, q)`, the others nothing. -/
example : (leaves.flatMap (cjOfD q32) == [cj32] &&
    leaves.all (fun o => runP (cjOfProg q32 o) == some (cjOfD q32 o))) = true := by
  decide +kernel

/-- **`firstTupleProg`** is `firstTupleD` (the first `j`-tuple of `Φ`, or `[]`). -/
example : (runP (firstTupleProg [3, 1, 4] 2) == some (firstTupleD [3, 1, 4] 2) &&
    runP (firstTupleProg [3, 1, 4] 0) == some (firstTupleD [3, 1, 4] 0) &&
    firstTupleD [3, 1, 4] 0 == []) = true := by
  decide +kernel

/-! ### A coloured Johnson leaf of Case 3's shape -/

/-- Case 3's conditions on the data of `cj32`: the support is small (`2 · 8 < 32`), `C` is a
class of more than `tOf |V|` points, `V₀ ∪ ⋃Λ ⊆ C`, and `(|C| + 3)/2 < |V₀|` (item 1). -/
example : (decide (2 * (32 - 24) < 32) && decide (Case3.tOf 24 < 15) &&
    (j32.1 ++ j32.2.1.flatten).all (· < 15) && decide ((15 + 3) / 2 < j32.1.length)) = true := by
  decide +kernel

theorem j32_cells : (jdec 32 j32).Λ = {{10}, {11}, {12}, {13}, {14}} := by decide +kernel

/-- **`IsJohnson`** (`9 < |V₀| = 10`, `s = 2`, `2s ≤ |Λ| = 5`), field by field, as
`MainHints.j12_johnson`. -/
theorem j32_johnson : SplitJohnson.IsJohnson Finset.univ 9 (jdec 32 j32) := by
  constructor
  case cells_ne =>
    intro a ha
    rw [j32_cells] at ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  case cells_disj =>
    intro a ha b hb hne
    rw [j32_cells] at ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> first | contradiction | decide +kernel
  case surj =>
    have hp : (jdec 32 j32).Λ.powersetCard 2 = {(jdec 32 j32).f 0, (jdec 32 j32).f 1,
        (jdec 32 j32).f 2, (jdec 32 j32).f 3, (jdec 32 j32).f 4, (jdec 32 j32).f 5,
        (jdec 32 j32).f 6, (jdec 32 j32).f 7, (jdec 32 j32).f 8, (jdec 32 j32).f 9} := by
      decide +kernel
    intro T hT
    change T ∈ (jdec 32 j32).Λ.powersetCard 2 at hT
    rw [hp] at hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide +kernel, rfl⟩
    · exact ⟨1, by decide +kernel, rfl⟩
    · exact ⟨2, by decide +kernel, rfl⟩
    · exact ⟨3, by decide +kernel, rfl⟩
    · exact ⟨4, by decide +kernel, rfl⟩
    · exact ⟨5, by decide +kernel, rfl⟩
    · exact ⟨6, by decide +kernel, rfl⟩
    · exact ⟨7, by decide +kernel, rfl⟩
    · exact ⟨8, by decide +kernel, rfl⟩
    · exact ⟨9, by decide +kernel, rfl⟩
  all_goals decide +kernel

theorem j32_shape : JShape 32 j32 := by
  constructor
  case trim =>
    intro v hv
    have hv10 : 10 ≤ v := by simp [j32] at hv; omega
    simp [jfl, j32, pairs5, Array.getD, show ¬ v < 10 by omega]
  all_goals decide +kernel

/-- **`JValid`**, from the shape and `IsJohnson`. -/
theorem j32_valid : JValid 32 j32 := jvalid_of_isJohnson j32_shape j32_johnson

/-- **The colour bound `hq` of `rd_ns_cj`** for `cj32`: outside `V₀` the colours are `0` (the
cells), `3` (the rest of `V`) and `1` (the support), on `5`, `9` and `8` points. -/
theorem cj32_hq : ∀ c, 2 * (Finset.univ.filter fun γ : Fin 32 =>
    γ ∉ (jdec 32 j32).V0 ∧ cjcol 32 cj32 γ = c).card ≤ 32 := by
  have hc : ∀ γ : Fin 32, cjcol 32 cj32 γ = 0 ∨ cjcol 32 cj32 γ = 1 ∨ cjcol 32 cj32 γ = 3 := by
    decide +kernel
  intro c
  by_cases h : c = 0 ∨ c = 1 ∨ c = 3
  · rcases h with rfl | rfl | rfl <;> decide +kernel
  · have he : (Finset.univ.filter fun γ : Fin 32 =>
        γ ∉ (jdec 32 j32).V0 ∧ cjcol 32 cj32 γ = c) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun γ _ hγ => h (by rw [← hγ.2]; exact hc γ)
    rw [he]
    decide

/-- **The control**: uncoloured (colour `0` everywhere, as 14j-4's Johnson pair), the rest is
one class of `17 > 32/2` points. -/
example : 32 < 2 * (Finset.univ.filter fun γ : Fin 32 =>
    γ ∉ (jdec 32 j32).V0 ∧ cjcol 32 (j32, (List.replicate 32 0).toArray) γ = 1).card := by
  decide +kernel

/-! ### A transported pair -/

/-- **The transport** of a coloured Johnson datum by the image list `σ` of the base: `V₀`, the
cells and the colours moved by `σ`. -/
def cjMap (m : ℕ) (σ : List ℕ) (e : CJData) : CJData :=
  let inv := fun v => ((List.range m).find? fun u => ap σ u == v).getD v
  ((e.1.1.map (ap σ), e.1.2.1.map (·.map (ap σ)), e.1.2.2.1,
    ((List.range m).map fun v => e.1.2.2.2.getD (inv v) []).toArray),
   ((List.range m).map fun v => get e.2 (inv v)).toArray)

/-- The reversal of the base. -/
def rev32 : List ℕ := (List.range 32).reverse

/-- `y`'s pairs: an uncoloured copy (another colour profile) and the transported pair. -/
def ys32 : List CJData := [(j32, (List.replicate 32 0).toArray), cjMap 32 rev32 cj32]

/-- **The transported pair is found among `y`'s pairs**: `cjMap` is the transport (`cjMaps`),
only the transported pair matches `cj32` under `cjohnIsoD`, the permutation found carries
`cj32` to it, and the program agrees with the data. -/
example : (MainHints.cjMaps 32 rev32 cj32 (cjMap 32 rev32 cj32) &&
    ys32.filter (fun Y => (cjohnIsoD 32 cj32 Y).isSome) == [cjMap 32 rev32 cj32] &&
    (match cjohnIsoD 32 cj32 (cjMap 32 rev32 cj32) with
      | some τ => MainHints.cjMaps 32 (img τ) cj32 (cjMap 32 rev32 cj32)
      | none => false) &&
    ys32.all fun Y => Align.optEq (runP (cjohnIsoProg 32 cj32 Y)) (cjohnIsoD 32 cj32 Y)) =
    true := by
  decide +kernel

/-! ### The Johnson routes' Align call -/

/-- The pairs of `[k]`. -/
def prsK (k : ℕ) : List (ℕ × ℕ) :=
  (List.range k).flatMap fun a => ((List.range k).filter (a < ·)).map (a, ·)

/-- The base of `J(k, 2)`: the pairs (points `0, …, C(k, 2) − 1`), then the `k` letters. -/
def baseK (k : ℕ) : List (List ℕ) :=
  (prsK k).map (fun (ab : ℕ × ℕ) => [ab.1, ab.2]) ++ (List.range k).map ([·])

/-- `p ∈ Sym(k)` on the letters (the window `[0, k)`) and on the base. -/
def liftK (k : ℕ) (p : List ℕ) : List ℕ :=
  p ++ (baseK k).map fun b => k + (baseK k).idxOf ((b.map (p.getD · 0)).insertionSort (· ≤ ·))

/-- `Sₖ`, by a transposition and a `k`-cycle. -/
def symK (k : ℕ) : List (List ℕ) :=
  [liftK k ([1, 0] ++ (List.range k).drop 2), liftK k ((List.range k).map fun i => (i + 1) % k)]

/-- `Sₖ` on the letters and the base, labels `{letter}`, strings `x`, `y` on the letters. -/
def mkK (k : ℕ) (x y : List ℕ) : MainSteps.SFix :=
  let m := (baseK k).length
  ⟨k, k + m, symK k, List.range k, List.range (k + m), x ++ List.replicate m 0,
    y ++ List.replicate m 0, some ((List.range k).map fun c => [(baseK k).idxOf [c]]).toArray⟩

/-- **`J(k, 2)` twisted by `π`**: `V₀` the pairs, the cells the letters, `s = 2`, the pair
`{a, b}` at the cells `{π a, π b}`; colour `0`. -/
def jTw (k : ℕ) (π : List ℕ) : CJData :=
  let np := (prsK k).length
  ((List.range np, (List.range k).map (fun c => [np + c]), 2,
    ((prsK k).map fun (ab : ℕ × ℕ) =>
      [π.getD ab.1 0, π.getD ab.2 0].insertionSort (· ≤ ·)).toArray),
   (List.replicate (np + k) 0).toArray)

/-- The base action of a group element of the fixture. -/
def baseOf (f : MainSteps.SFix) (g : List ℕ) : List ℕ :=
  (List.range (f.N - f.n)).map fun u => ap g (f.n + u) - f.n

/-- The images of `X` under the isomorphisms (brute force), without repetition. -/
def imagesOf (f : MainSteps.SFix) (X : CJData) : List CJData :=
  let m := f.N - f.n
  (f.sols.map fun g => cjMap m (baseOf f g) X).foldl (fun acc e =>
    if acc.any (MainHints.cjMaps m (List.range m) e) then acc else acc ++ [e]) []

/-- **The Johnson routes' last call**: Align with `cjohnOps` over `Ys`, reduce-and-derive with
`st = (2, X)` on each aligned coset. -/
def alP (f : MainSteps.SFix) (X : CJData) (Ys : List CJData) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  Align.alignProg (fun J => rdBranch MainSteps.spySub f.n f.n (f.L.getD #[]) (2, X) J)
    (fun e => cjohnGensProg (f.N - f.n) e) (fun e e' => cjohnIsoProg (f.N - f.n) e e') f.n
    (f.x.toArray, f.y.toArray) (WinData.ofPoints f.N f.w) (f.N, gD f.gs, ()) X Ys

/-- The call's answer and children: the fixture is valid, every isomorphism carries `X` to a
pair of `Ys` (`halign`), the answer is the brute-force coset, and the children are
`StepChild |W| m` with the factor `|Ys| · m`. -/
def alQ (f : MainSteps.SFix) (X : CJData) (Ys : List CJData) (v : AnswerData Ty.unit)
    (cs : List MainSteps.Child) : Bool :=
  let m := f.N - f.n
  f.ok && f.sols.all (fun g => Ys.any (MainHints.cjMaps m (baseOf f g) X)) &&
    MainSteps.ansOK f.N f.sols v &&
    MainSteps.childrenOK f (Ys.length * m) (MainSteps.stepB f.w.length m) (f.N * f.N) cs

/-- `J(4, 2)` twisted by `(0 1)`: not preserved by `S₄`. -/
def x42 : CJData := jTw 4 [1, 0, 2, 3]
/-- Two isomorphisms (`x = 0 1 2 2`, `y = 2 1 0 2`). -/
def f42 : MainSteps.SFix := mkK 4 [0, 1, 2, 2] [2, 1, 0, 2]
/-- `y`'s pairs: the image of `x42` under the isomorphisms, and `J(4, 2)` twisted by a 3-cycle
(isomorphic to `x42` in `Sym(10)`, not under `S₄`). -/
def ys42 : List CJData := imagesOf f42 x42 ++ [jTw 4 [1, 2, 0, 3]]

example : (imagesOf f42 x42).length = 1 := by decide +kernel

run_cmd
  execRuns `al_j42.run
    (← `(RunsS ssOracle body0 recF (alP f42 x42 ys42)))
    ssOracle body0 recF (alP f42 x42 ys42) cfg5
/-- **Align with `cjohnOps` and reduce-and-derive at `st = (2, X₀)`** on `J(4, 2)` under `S₄`:
the answer is the brute-force coset (two isomorphisms) and the children meet the bound. -/
theorem al_j42 : ∃ v s, RunsS ssOracle body0 recF (alP f42 x42 ys42) v s ∧
    alQ f42 x42 ys42 v s = true :=
  ⟨_, _, al_j42.run, by decide +kernel⟩

/-! ### Interpreter runs (supplementary) -/

/-- `alQ` on an interpreter run, with `Ys` the images and a twisted copy. -/
def alOK (f : MainSteps.SFix) (X Z : CJData) : Bool :=
  let Ys := imagesOf f X ++ [Z]
  match MainSteps.runT (alP f X Ys) with
  | some (a, tr) => alQ f X Ys a (MainSteps.records tr)
  | none => false

#eval check "Align with cjohnOps: J(4,2) under S₄ (four isomorphisms; none) and J(5,2) under \
    S₅" fun _ =>
  alOK (mkK 4 [0, 0, 1, 1] [1, 0, 1, 0]) x42 (jTw 4 [1, 2, 0, 3]) &&
    alOK (mkK 4 [0, 0, 0, 1] [0, 0, 1, 1]) x42 (jTw 4 [1, 2, 0, 3]) &&
    alOK (mkK 5 [0, 0, 1, 1, 2] [1, 2, 0, 1, 0]) (jTw 5 [1, 0, 2, 3, 4]) (jTw 5 [1, 2, 0, 3, 4])

/-- **`m5Case3CJProg`** on `MainM5b`'s fixtures. -/
def c3CJP (f : MainSteps.SFix) (k : ℕ) (Vx Vy : List ℕ) :
    Prog (groupSig Ty.unit) (Solver.Rec Ty.unit) Ty.denote (Ty.answer Ty.unit) :=
  m5Case3CJProg MainSteps.spySub f.hinst f.n f.n MainM5b.l3 noSt k (f.x.toArray, f.y.toArray)
    (WinData.ofPoints f.N f.w) (f.N, gD f.gs, ()) Vx Vy

/-- `RunsWithin.m5Case3CJProg`'s bounds with `uB = m`: `2 · c3Count` comparisons, and the
factor `c3R · max(m, m!) + F` with 14j-4's factor `F = c3R · m! + m!`. -/
def c3CJOK (f : MainSteps.SFix) (k : ℕ) (Vx Vy : List ℕ) : Bool :=
  let m := f.N - f.n
  let R := Case3.c3R k Vy.length (Case2b.sojZ m)
  f.ok && match MainSteps.runT (c3CJP f k Vx Vy) with
    | some (a, tr) => MainSteps.ansOK f.N f.sols a &&
        kidsOK f f.n k (2 * c3Count Vx.length k f.n) 0
          (R * max m m.factorial + (R * m.factorial + m.factorial)) (MainSteps.records tr)
    | none => false

#eval check "m5Case3CJProg on S₃ (one distinguished point; a non-isomorphic pair; the \
    fallback)" fun _ =>
  c3CJOK MainM5b.f3a 1 [0] [1] && c3CJOK MainM5b.f3b 1 [0] [1] &&
    c3CJOK MainM5b.f3a 1 [0, 1, 2] [0, 1, 2]

/-- **`m5Case2bCJProg`** with `F(x) = F(y) = ⟨fs⟩` on the large orbit `Φ`; the test finds no
Johnson leaf, so the bounds are 14j-4's (the factor `c2bR · m!`). -/
def c2bCJOK (f : MainSteps.SFix) (fs : List (List ℕ)) (Φ : List ℕ) : Bool :=
  let m := f.N - f.n
  let F : GroupData Ty.unit.denote := (f.N, gD fs, ())
  f.ok && !c2bJD ssOracle f.N f.n F Φ &&
    match MainSteps.runT (m5Case2bCJProg MainSteps.spySub f.n f.n l4 noSt
        (f.x.toArray, f.y.toArray) (WinData.ofPoints f.N f.w) (f.N, gD f.gs, ()) F F Φ Φ) with
    | some (a, tr) => MainSteps.ansOK f.N f.sols a &&
        kidsOK f f.n 1 0 0
          (Case2b.c2bR f.N f.n Φ.length (Case2b.degD ssOracle f.N f.n F Φ - 1) (Case2b.sojZ m) *
            m.factorial) (MainSteps.records tr)
    | none => false

#eval check "m5Case2bCJProg on S₄ with F the Klein group (x = y constant)" fun _ =>
  c2bCJOK MainM5b.f2b MainM5b.klein [0, 1, 2, 3]

/-- **The whole step** `m5StepCJProg`, with the full groups computed by the certificates, against
brute force and `RunsWithin.m5StepCJProg`'s bounds (`m5CKCJ`, `m5CH`, `m5CFCJ` with `uB = m`). -/
def stepCJOK (f : MainSteps.SFix) (L : Array (List ℕ)) (k : ℕ) : Bool :=
  let R := rbR f L
  let nr := R.2.2.1
  let Nr := R.1.2.2.2.1
  match MainSteps.runV (certP f L k true), MainSteps.runV (certP f L k false),
      MainSteps.runT (m5StepCJProg MainSteps.spySub f.hinst L k noSt) with
  | some Fx, some Fy, some (a, tr) =>
    f.ok && MainSteps.ansOK f.N f.sols a &&
      kidsOK f nr k (2 * certCount Nr nr k + m5CKCJ ssOracle nr Nr k Fx Fy)
        (m5CH ssOracle nr Nr (Nr * Nr) nr Fx Fy) (m5CFCJ ssOracle nr Nr k Fx Fy (Nr - nr))
        (MainSteps.records tr)
  | _, _, _ => false

#eval check "m5StepCJProg at m = 4 (k = 3: Case 2a, Case 2a against Case 3; k = 2: Case 3)"
    fun _ =>
  stepCJOK fA l4 3 && stepCJOK fB l4 3 && stepCJOK (mk4 s4 [0, 0, 0, 1] [0, 1, 0, 0]) l4 2

/-- **The Petersen colouring** of the pairs of `[5]` (`k = 2`, codes `u + 10 v`): `0` on the
diagonal, `1` on intersecting pairs, `2` on disjoint ones. -/
def petersen : Array ℕ :=
  ((List.range 100).map fun c =>
    let u := c % 10
    let v := c / 10
    if u == v then 0
    else if (pairs5.getD u []).any (· ∈ pairs5.getD v []) then 1 else 2).toArray

#eval check "the Petersen colouring: the first structure is a coloured partition" fun _ =>
  match MainSteps.runV (Case3.firstStructProg (rec := Solver.Rec Ty.unit) 10 2 (List.range 10)
      petersen) with
  | some (some X₀) => X₀.1 == 1
  | _ => false

end GraphIsoChecks.MainM5CJ
