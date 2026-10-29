module

public import GraphIso.TM.GI
meta import GraphIso.TM.GI
public import GraphIsoChecks.Exec
meta import GraphIsoChecks.Exec
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 17h: graph isomorphism on Turing machines

`PLAN-17.md` §11.

* **The specification** on graphs on `Fin 3`: the paths `0 - 1 - 2` and `1 - 0 - 2` are
  isomorphic, a path and the triangle are not (`isoDecide`, computed by the kernel), and
  `isoDecide_iff` turns these into `Nonempty (G ≃g H)` and `IsEmpty (G ≃g H)`.
* **The encoding** of the pair of paths: `ser Ty.giInput` of `3` and the adjacency lists, `40`
  symbols, at least `n = 3`.
* **The output's length** at concrete valid data on `Fin 3` (the identity and one transposition
  as generator): `length_ser_coset_le` instantiated, and the length computed.
* **The machines** on concrete pairs: by `gi_tm`, the machine `toFinTM2 giDecProg .inp .out`
  outputs the encoding of `true` on the paths and of `false` on the path and the triangle,
  within `2 ^ (c 6 ^ 8)` steps (the encodings have lengths `40` and `47`, and `λ = Nat.log 2`
  is `5` on both); by `gi_coset_tm`, the coset machine outputs `some` on the paths and `none`
  on the path and the triangle.
* **The coset entry in the cost model**, evaluated by the kernel: on the empty graphs `some` at
  local cost `144`, on the one-vertex graphs `some` at `376`, on an edge and the empty graph
  (`pe`) `none` at `86100` (`pe_runs`: `54430` trace events, proved in pieces of at most `1000`
  events). The machines themselves are not run on graphs.
* **Negative controls**: the path and the triangle are not decided isomorphic; the encodings of
  the two pairs differ; the coset entry returns `none` on `pe`.
-/

@[expose] public section

namespace GraphIsoChecks.TMGI

open Equiv GraphIso GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion GraphIso.TM

/-- The simple graph on `Fin n` whose edges are the pairs `u ≠ v` with `f u v` or `f v u`. -/
def ofAdj (n : ℕ) (f : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (f u v || f v u) = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Bool.or_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n : ℕ) (f : Fin n → Fin n → Bool) : DecidableRel (ofAdj n f).Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (f u v || f v u) = true))

/-- The path `0 - 1 - 2`. -/
abbrev path₁ : SimpleGraph (Fin 3) := ofAdj 3 fun u v => u.val + 1 == v.val

/-- The path `1 - 0 - 2`. -/
abbrev path₂ : SimpleGraph (Fin 3) := ofAdj 3 fun u v => u.val == 0 && v.val != 0

/-- The triangle. -/
abbrev tri : SimpleGraph (Fin 3) := ofAdj 3 fun _ _ => true

/-- The two paths. -/
def pp : GraphPair := ⟨3, path₁, path₂⟩

/-- A path and the triangle. -/
def pt : GraphPair := ⟨3, path₁, tri⟩

/-! ### The specification -/

theorem pp_iso : isoDecide pp = true := by
  decide +kernel

/-- **Negative control**: a path and the triangle are not isomorphic. -/
theorem pt_not_iso : isoDecide pt = false := by
  decide +kernel

example : Nonempty (path₁ ≃g path₂) := (isoDecide_iff pp).1 pp_iso

example : IsEmpty (path₁ ≃g tri) :=
  not_nonempty_iff.1 fun h => Bool.false_ne_true (pt_not_iso.symm.trans ((isoDecide_iff pt).2 h))

/-! ### The encoding -/

/-- The encoding of the two paths: `3` and the adjacency lists. -/
example : pp.enc = ser Ty.giInput (3, #[[1], [0, 2], [1]], #[[1, 2], [0], [0]]) := by
  decide +kernel

example : pp.enc.length = 40 ∧ pp.n ≤ pp.enc.length := by
  decide +kernel

/-- **Negative control**: the encodings of the two pairs differ. -/
example : pp.enc ≠ pt.enc := by
  decide +kernel

/-! ### The output's length -/

/-- The identity on `Fin 3` and the transposition `(0 1)` as generator. -/
def cosetData : Option (PermData × GensData) :=
  some ((#[0, 1, 2], #[0, 1, 2]), [(#[1, 0, 2], #[1, 0, 2])])

example : (ser Ty.giCoset cosetData).length ≤ 16 * (3 + 1) ^ 6 :=
  length_ser_coset_le fun τ hs h => by
    simp only [cosetData, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by decide, fun g hg => ?_, by decide⟩
    simp only [List.mem_singleton] at hg
    subst hg
    decide

example : (ser Ty.giCoset cosetData).length = 43 := by
  decide +kernel

/-! ### The coset entry in the cost model -/

/-- An edge and the empty graph on `Fin 2`. -/
def pe : GraphPair := ⟨2, ofAdj 2 fun _ _ => true, ofAdj 2 fun _ _ => false⟩

example : pe.data = (2, #[[1], [0]], #[[], []]) := by
  decide +kernel

/-- The coset entry on the empty graphs: `some`, local cost `144`. -/
example : (eval Ctx.empty.O ((qpSolver 192 181).proc Ty.denote) 1000
    (giCosetEntry Ty.denote (0, #[], #[]))).map (fun r => (r.2.localCost, r.1.isSome)) =
    some (144, true) := by
  decide +kernel

/-- The coset entry on the one-vertex graphs: `some`, local cost `376`. -/
example : (eval Ctx.empty.O ((qpSolver 192 181).proc Ty.denote) 1000
    (giCosetEntry Ty.denote (1, #[[]], #[[]]))).map (fun r => (r.2.localCost, r.1.isSome)) =
    some (376, true) := by
  decide +kernel

/-! The run on `pe` has `54430` trace events, and one kernel check of it peaks at about `24` GB,
so it is proved in pieces of at most `1000` events (`GraphIsoChecks.Exec`), with the trace
summary `costF` (the local cost of each event). `execRuns` would restate the composed summary
as one literal list of `54430` costs, which is too deep for the kernel; `execRunsParts` keeps
the summary as the composition lemmas build it, by appends from the pieces' literal summaries.
Its sum is then proved part by part (`sumThm`): `sum_append_eq` at every append and a kernel
`decide` on every literal part (at most `1000` numbers). -/

/-- The trace summary: the local cost of each event. -/
def costF : Event Signature.empty → List ℕ := fun e => [e.localCost]

theorem localCost_eq_costF (tr : Trace Signature.empty) :
    Trace.localCost tr = (tr.flatMap costF).sum := by
  rw [Trace.localCost_eq_sum]
  induction tr with
  | nil => rfl
  | cons e tr ih => simp [costF, ih]

theorem sum_append_eq {a b : List ℕ} {m n : ℕ} (ha : a.sum = m) (hb : b.sum = n) :
    (a ++ b).sum = m + n := by
  rw [List.sum_append, ha, hb]

section Parts

open Lean Meta Elab Command GraphIsoChecks.Exec

/-- **`execRuns` without its last step**: ``run_cmd execRunsParts `n (← `(RunsS O body f p)) O
body f p cfg`` adds the theorem `n : RunsS O body f p v s`, proved by the same kernel-checked
pieces and composition nodes as `execRuns`, where `s` is the summary as the composition lemmas
build it from the pieces' literal summaries (appends), not restated as one literal list. -/
def execRunsParts {S : Signature} {a b : Ty} {α : Type} [ToExpr α] (n : Name) (stx : Term)
    (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α)
    {t : Ty} (p : Prog S (a, b) Ty.denote t) (cfg : GraphIsoChecks.Exec.Config := {}) :
    CommandElabM Unit := do
  let base := (← getCurrNamespace) ++ n
  let some (r, sv, len) := runInfo O body f cfg.fuel p
    | throwError "execRunsParts: the run does not finish within the fuel"
  let (pre, inst, tE, pE) ← liftTermElabM do
    let e ← closed "statement" (← Term.elabTermAndSynthesize stx none)
    unless e.isAppOfArity ``RunsS 9 do
      throwError "execRunsParts: expected `RunsS O body f p`{indentExpr e}"
    let args := e.getAppArgs
    let inst ← synthInstance (← mkAppM ``DecidableEq #[args[3]!])
    pure (args.extract 0 7, inst, args[7]!, args[8]!)
  let stats ← IO.mkRef ({} : Stats)
  let c : GraphIsoChecks.Exec.Ctx := { pre, inst, base, cfg, stats }
  let (root, vE, sE) ← execNode O body f c p tE pE (serV t r, sv, len)
  liftTermElabM <| addThm base (c.runs tE pE vE sE) (mkConst root)

/-- The value of a closed expression of type `ℕ`, by `whnfD`. -/
def natVal (e : Expr) : MetaM ℕ := do
  let some n := (← whnfD e).rawNatLit? | throwError "sumThm: not a numeral{indentExpr e}"
  pure n

/-- A proof of `l.sum = n`, and `n`, for a closed `l : List ℕ`: `sum_append_eq` at an append,
otherwise a kernel `decide` (the elements of `l`, by `whnfD`, give `n`). -/
partial def sumProof (l : Expr) : MetaM (Expr × ℕ) := do
  if l.isAppOfArity ``HAppend.hAppend 6 then
    let (pa, na) ← sumProof (l.getArg! 4)
    let (pb, nb) ← sumProof (l.getArg! 5)
    pure (mkAppN (mkConst ``sum_append_eq)
      #[l.getArg! 4, l.getArg! 5, mkNatLit na, mkNatLit nb, pa, pb], na + nb)
  else
    let mut n := 0
    let mut e ← whnfD l
    while e.isAppOfArity ``List.cons 3 do
      n := n + (← natVal (e.getArg! 1))
      e ← whnfD (e.getArg! 2)
    unless e.isAppOfArity ``List.nil 1 do
      throwError "sumThm: not a list{indentExpr e}"
    pure (← mkDecideProof (← mkEq (← mkAppM ``List.sum #[l]) (mkNatLit n)), n)

/-- ``run_cmd sumThm `nm `thm`` adds the theorem `nm : s.sum = n` for the summary `s` of
`thm : RunsS O body f p v s` (`f` with values in `List ℕ`), `n` computed by `sumProof`; the
kernel checks the proof when the theorem is added. -/
def sumThm (nm thm : Name) : CommandElabM Unit := liftTermElabM do
  let s := (← inferType (mkConst thm)).getArg! 10
  let (pf, n) ← sumProof s
  addThm nm (← mkEq (← mkAppM ``List.sum #[s]) (mkNatLit n)) pf

run_cmd
  execRunsParts `pe_runs.run
    (← `(RunsS Ctx.empty.O ((qpSolver 192 181).proc Ty.denote) costF
      (giCosetEntry Ty.denote pe.data)))
    Ctx.empty.O ((qpSolver 192 181).proc Ty.denote) costF (giCosetEntry Ty.denote pe.data)
    { budget := 1000 }

run_cmd sumThm `GraphIsoChecks.TMGI.pe_runs.sum `GraphIsoChecks.TMGI.pe_runs.run

end Parts

/-- **Negative control**: the coset entry on an edge and the empty graph (`pe`) runs to `none`,
at local cost `86100`. -/
theorem pe_runs : ∃ tr, Runs Ctx.empty.O ((qpSolver 192 181).proc Ty.denote)
    (giCosetEntry Ty.denote pe.data) none tr ∧ Trace.localCost tr = 86100 := by
  obtain ⟨tr, hr, hs⟩ := pe_runs.run
  exact ⟨tr, hr, (localCost_eq_costF tr).trans ((congrArg List.sum hs).trans pe_runs.sum)⟩

/-! ### The machines -/

/-- **The decision machine** outputs the encoding of `true` on the two paths and of `false` on a
path and the triangle, within `2 ^ (c 6 ^ 8)` steps (`λ(40) = λ(47) = 5`). -/
example : ∃ c, Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) pp.enc
      (some (ser .bool true)) (2 ^ (c * 6 ^ 8))) ∧
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) pt.enc
      (some (ser .bool false)) (2 ^ (c * 6 ^ 8))) := by
  obtain ⟨c, -, -, -, h⟩ := gi_tm
  have hl : lam pp.enc.length = 5 ∧ lam pt.enc.length = 5 := by decide +kernel
  refine ⟨c, ?_, ?_⟩
  · have := h pp
    rwa [pp_iso, hl.1] at this
  · have := h pt
    rwa [pt_not_iso, hl.2] at this

/-- **The coset machine** outputs `some` on the two paths and `none` on a path and the
triangle. -/
example : ∃ c, (∃ τ hs, Nonempty (Turing.TM2OutputsInTime (toFinTM2 giCosetProg .inp .out)
      pp.enc (some (ser Ty.giCoset (some (τ, hs)))) (2 ^ (c * (lam pp.enc.length + 1) ^ 8)))) ∧
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giCosetProg .inp .out) pt.enc
      (some (ser Ty.giCoset none)) (2 ^ (c * (lam pt.enc.length + 1) ^ 8))) := by
  obtain ⟨c, hc⟩ := gi_coset_tm
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc pp
    rcases r with _ | ⟨τ, hs⟩
    · exact absurd (hnone.1 rfl) (not_isEmpty_iff.2 ((isoDecide_iff pp).1 pp_iso))
    · exact ⟨τ, hs, hM⟩
  · obtain ⟨r, hM, hnone, -⟩ := hc pt
    have hr : r = none :=
      hnone.2 (not_nonempty_iff.1 fun h =>
        Bool.false_ne_true (pt_not_iso.symm.trans ((isoDecide_iff pt).2 h)))
    exact hr ▸ hM

end GraphIsoChecks.TMGI
