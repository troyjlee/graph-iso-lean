module

public import GraphIsoChecks.MainSteps
public import GraphIso.Main.Mini
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Milestone 14, stage 14j-5b checks: the mini procedure

Checks of the mini procedure (`GraphIso/Main/Mini.lean`): the base case, the chain rule, M0 and
M3 composed with `.recur`, run from the entry `miniEntry` with the verified Schreier–Sims oracle
answering the backend calls (`runMini`, the interpreter `eval` with `miniBody` as the recursive
procedure). Each check compares, in one term decided by `decide +kernel`:

* **the answer** with the brute-force solutions (`ansOK`, `SFix.sols` of
  `GraphIsoChecks.MainSteps`: the elements of `σ • ⟨gs⟩` carrying `x` to `y` on the window);
* **the cost** of the run's trace under the Schreier–Sims schedule `ssB` with the bound of
  `miniSolve_ss`, `genCost N |gs| + 2 + 15 + miniCost N (2N) (miniRk (2N) |W| none)`;
* **the path**, counted in the trace (`stats`): the recursive calls, the `kernel` calls (one per
  run of M3) and the `generate` calls above the input degree (M0's re-basing and the transfers
  at the child's degree).

The fixtures are valid instances (`SFix.ok` with `n = N` and no hint):
* `fEmpty`: an empty window, the base case at the root (one recursive call);
* `fFix4`, `fFix4No`: `⟨(2 3)⟩` fixes the window `{0, 1}`; the input coset, or `none`;
* `fCh`: `⟨(0 1), (2 3)⟩`, two orbits: the chain rule, then on each orbit M0 (two blocks) and
  M3 (the kernel of the action on the blocks), 11 recursive calls, 2 kernel calls;
* `fD4`, `fD4No`: `D₄` transitive on four positions: M0 (blocks `{0, 2}, {1, 3}`), M3 and the
  children down to the base case; four isomorphisms, or none.
-/

@[expose] public section

namespace GraphIsoChecks.MainMini

open GraphIso GraphIso.Cost GraphIso.Main GraphIso.Sims GraphIsoChecks.MainSteps
  GraphIsoChecks.Sweep

/-- Run with the verified oracle and the mini procedure as the recursive procedure. -/
def runMini {t : Ty}
    (p : Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote t) :
    Option (t.denote × Trace (groupSig Ty.unit)) :=
  eval ssOracle (miniBody Ty.unit Ty.denote) 10000000 p

/-- The entry's input for a fixture. -/
def miniIn (f : SFix) : Solver.Ty.input.denote :=
  ((f.x.toArray, f.y.toArray), (WinData.ofPoints f.N f.w, (ofList f.σ, (f.N, gD f.gs))))

/-- **The path of a run**: recursive calls, `kernel` calls, and `generate` calls above the input
degree `N`. -/
def stats (N : ℕ) (tr : Trace (groupSig Ty.unit)) : ℕ × ℕ × ℕ :=
  (tr.countP fun e => match e with | .local .recCall _ => true | _ => false,
   tr.countP fun e => match e with | .call .kernel _ _ => true | _ => false,
   tr.countP fun e => match e with | .call .generate x _ => decide (N < x.1) | _ => false)

/-- **The mini procedure on a fixture**: a valid instance without a hint; the answer is the
brute-force coset; the cost is within `miniSolve_ss`'s bound; the path is `path`. -/
def miniOK (f : SFix) (path : ℕ × ℕ × ℕ) : Bool :=
  f.ok && f.n == f.N && f.L.isNone &&
    match runMini (miniEntry Ty.unit Ty.denote (miniIn f)) with
    | some (a, tr) =>
      ansOK f.N f.sols a &&
        decide (Trace.cost ssB tr ≤ genCost f.N f.gs.length + 2 + 15 +
          miniCost f.N (2 * f.N) (miniRk (2 * f.N) f.w.length none)) &&
        stats f.N tr == path
    | none => false

/-- An empty window. -/
def fEmpty : SFix := ⟨3, 3, [[1, 2, 0]], [], [1, 0, 2], [5, 6, 7], [7, 7, 7], none⟩
/-- `⟨(2 3)⟩` fixes the window `{0, 1}`; `σ = (0 1)` carries `x` to `y`. -/
def fFix4 : SFix :=
  ⟨4, 4, [[0, 1, 3, 2]], [0, 1], [1, 0, 2, 3], [5, 6, 7, 8], [6, 5, 9, 9], none⟩
/-- The same with `y` not matched. -/
def fFix4No : SFix := { fFix4 with y := [5, 6, 9, 9] }
/-- `⟨(0 1), (2 3)⟩`: two orbits; one isomorphism `(0 1)(2 3)`. -/
def fCh : SFix :=
  ⟨4, 4, [[1, 0, 2, 3], [0, 1, 3, 2]], [0, 1, 2, 3], [0, 1, 2, 3], [1, 2, 1, 2], [2, 1, 2, 1],
    none⟩
/-- `D₄` on four positions; the four elements carrying evens to odds. -/
def fD4 : SFix :=
  ⟨4, 4, [[1, 2, 3, 0], [0, 3, 2, 1]], [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 0, 1], [1, 0, 1, 0],
    none⟩
/-- `D₄` with no isomorphism. -/
def fD4No : SFix := { fD4 with y := [0, 0, 1, 1] }

example : miniOK fEmpty (1, 0, 0) = true := by decide +kernel
example : (miniOK fFix4 (1, 0, 0) && miniOK fFix4No (1, 0, 0)) = true := by decide +kernel
example : miniOK fCh (11, 2, 4) = true := by decide +kernel
example : miniOK fD4 (18, 4, 9) = true := by decide +kernel
example : miniOK fD4No (12, 3, 3) = true := by decide +kernel

end GraphIsoChecks.MainMini
