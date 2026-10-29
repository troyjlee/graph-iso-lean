module

public import GraphIso.Cost.Evaluation
public import Lean.Elab.Command
public import Lean.Meta.Tactic.AuxLemma
public import Lean.Meta.Tactic.Constructor
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Kernel-checked executions in pieces

A concrete check `decide (… eval O body fuel p …)` makes the kernel interpret the whole run of
`p` in one declaration, and the kernel's memory grows with the work of that declaration: on the
M5 fixtures one such check peaks at 16–60 GB (measured under `scripts/guard.sh`). This
module proves a run in **pieces**, each checked by the kernel as a separate declaration, and
composes them; the memory is then that of the largest piece.

* **Values as trees.** `SerTree` (natural numbers and lists of trees, with a derived `ToExpr` and
  the structural equality `SerTree.beq`, sound by `SerTree.eq_of_beq`), `serV t : t.denote →
  SerTree` and `deserV t : SerTree → t.denote`, structural in the value type `t`, with
  `deserV_serV : deserV t (serV t v) = v`. Comparing trees reduces in the kernel where `Array`
  equality does not.
* **Runs with a trace summary.** `RunsS O body f p v s`: the program `p` runs (for some fuel) to
  `v` with a trace whose summary `tr.flatMap f` is `s` (for the M5 checks, `f` extracts the
  records of the instrumented sub-solver's children; `f := fun _ => []` for value-only runs).
  The composition lemmas `RunsS.bind`, `RunsS.ite`, `RunsS.caseOption_none`/`_some`,
  `RunsS.caseList_nil`/`_cons`, `RunsS.foldList_nil`/`_cons`/`_split`, `RunsS.loop_done`/`_step`,
  `RunsS.recur`, `RunsS.call`, `RunsS.prim`, `RunsS.ret` follow the program structure (from
  `runs_bind` and the other lemmas of `GraphIso.Cost.Evaluation`); `RunsS.congr_summary`.
* **Pieces from kernel checks.** `checkRunS O body f fuel p tree s : Bool` evaluates the run and
  compares its value's tree and its summary; `runsS_of_check` turns `checkRunS … = true` into
  `RunsS O body f p (deserV t tree) s`.
* **The splitter** (`execNode`, `execSplit`, `execFold`). It walks the program twice in
  lockstep: as a runtime value (in code that `run_cmd` compiles, which evaluates sub-runs and
  proposes their values, summaries and sizes, each sub-run evaluated once) and as an expression
  (unfolded to its head constructor). A sub-run of at most `cfg.budget` trace events is a
  **piece**: a theorem `RunsS O body f p (deserV t tree) s`, proved by `runsS_of_check` and the
  kernel's evaluation of `checkRunS … = true` (`decide`). A larger one is a **node**: split at
  its head constructor, each part proved first, then a theorem applying the composition lemma
  to the parts (`foldList` in chunks of at most `cfg.budget` events, by
  `List.take`/`List.drop`).
* **Every piece and every node is its own declaration**, elaborated by its own
  `liftTermElabM`, as the declarations of a command are, under the default budgets: no
  heartbeat option or baseline is changed. The kernel checks each declaration when it is added,
  so its memory is that of the largest piece.
* **The front end** is the command `execRuns`, run with `run_cmd`:
  ``run_cmd execRuns `n (← `(RunsS O body f p)) O body f p cfg`` adds the theorem
  `n : RunsS O body f p v s` with the value and the literal summary of the compiled run. A
  check is then an ordinary theorem, e.g.
  `theorem t : ∃ v s, RunsS O body f p v s ∧ Q v s = true := ⟨_, _, n, by decide +kernel⟩`.

**Trust.** The compiled evaluation only *proposes* intermediate values, summaries and split
points; every piece is checked by the kernel, and the composition is an ordinary proof term
checked by the kernel. A wrong proposal makes a piece's check or the composition fail; it cannot
produce a false theorem. Nothing here uses `native_decide` or `Lean.ofReduceBool`, and the
theorems proved with it depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

@[expose] public section

namespace GraphIsoChecks.Exec

open GraphIso GraphIso.Cost

/-! ### Values as trees -/

/-- A tree of natural numbers: the serialized form of runtime values. -/
inductive SerTree where
  | leaf (n : ℕ)
  | node (cs : List SerTree)
  deriving Repr, Lean.ToExpr

mutual

/-- Equality of trees, structural (it reduces in the kernel). -/
def SerTree.beq : SerTree → SerTree → Bool
  | .leaf n, .leaf m => n == m
  | .node cs, .node ds => SerTree.beqList cs ds
  | _, _ => false

/-- Equality of lists of trees. -/
def SerTree.beqList : List SerTree → List SerTree → Bool
  | [], [] => true
  | x :: xs, y :: ys => SerTree.beq x y && SerTree.beqList xs ys
  | _, _ => false

end

mutual

theorem SerTree.eq_of_beq : ∀ {x y : SerTree}, SerTree.beq x y = true → x = y
  | .leaf n, .leaf m, h => by
    simp only [SerTree.beq, beq_iff_eq] at h
    rw [h]
  | .node cs, .node ds, h => by
    simp only [SerTree.beq] at h
    rw [SerTree.eq_of_beqList h]
  | .leaf _, .node _, h => by simp [SerTree.beq] at h
  | .node _, .leaf _, h => by simp [SerTree.beq] at h

theorem SerTree.eq_of_beqList : ∀ {xs ys : List SerTree}, SerTree.beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [SerTree.beqList, Bool.and_eq_true] at h
    rw [SerTree.eq_of_beq h.1, SerTree.eq_of_beqList h.2]
  | [], _ :: _, h => by simp [SerTree.beqList] at h
  | _ :: _, [], h => by simp [SerTree.beqList] at h

end

/-- Serialize a runtime value. -/
def serV : (t : Ty) → t.denote → SerTree
  | .unit, _ => .node []
  | .bool, x => .leaf (cond x 1 0)
  | .nat, x => .leaf x
  | .prod a b, x => .node [serV a x.1, serV b x.2]
  | .list a, x => .node (x.map (serV a))
  | .array a, x => .node (x.toList.map (serV a))
  | .option a, x => match x with
    | none => .leaf 0
    | some y => .node [serV a y]

/-- Read a runtime value back (total: malformed trees give default values). -/
def deserV : (t : Ty) → SerTree → t.denote
  | .unit, _ => ()
  | .bool, x => match x with
    | .leaf n => n == 1
    | .node _ => false
  | .nat, x => match x with
    | .leaf n => n
    | .node _ => 0
  | .prod a b, x => match x with
    | .node [y, z] => (deserV a y, deserV b z)
    | _ => (Ty.default a, Ty.default b)
  | .list a, x => match x with
    | .node cs => cs.map (deserV a)
    | .leaf _ => []
  | .array a, x => match x with
    | .node cs => (cs.map (deserV a)).toArray
    | .leaf _ => #[]
  | .option a, x => match x with
    | .node [y] => some (deserV a y)
    | _ => none

theorem deserV_serV : ∀ (t : Ty) (v : t.denote), deserV t (serV t v) = v
  | .unit, _ => rfl
  | .bool, x => by cases x <;> rfl
  | .nat, _ => rfl
  | .prod a b, (x, y) => by simp only [serV, deserV, deserV_serV a, deserV_serV b]
  | .list a, xs => by
    simp only [serV, deserV, List.map_map]
    exact (List.map_congr_left fun x _ => deserV_serV a x).trans (List.map_id xs)
  | .array a, xs => by
    have hid : deserV a ∘ serV a = id := funext (deserV_serV a)
    simp only [serV, deserV, List.map_map, hid, List.map_id, Array.toArray_toList]
  | .option a, x => by cases x <;> simp [serV, deserV, deserV_serV a]

theorem serV_injective (t : Ty) {x y : t.denote} (h : serV t x = serV t y) : x = y := by
  rw [← deserV_serV t x, ← deserV_serV t y, h]

/-! ### Runs with a trace summary -/

section RunsS

variable {S : Signature} {a b : Ty} {α : Type} {O : Oracle S}
  {body : a.denote → Prog S (a, b) Ty.denote b} {f : Event S → List α}

/-- **A run with a trace summary**: `p` runs (for some fuel) to `v`, and the summary
`tr.flatMap f` of its trace is `s`. -/
def RunsS (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α)
    {t : Ty} (p : Prog S (a, b) Ty.denote t) (v : t.denote) (s : List α) : Prop :=
  ∃ tr, Runs O body p v tr ∧ tr.flatMap f = s

theorem RunsS.runs {t : Ty} {p : Prog S (a, b) Ty.denote t} {v : t.denote} {s : List α}
    (h : RunsS O body f p v s) : ∃ tr, Runs O body p v tr := by
  obtain ⟨tr, h, -⟩ := h
  exact ⟨tr, h⟩

theorem RunsS.ret {t : Ty} (x : t.denote) : RunsS O body f (.ret x) x [] :=
  ⟨[], runs_ret.2 ⟨rfl, rfl⟩, rfl⟩

theorem RunsS.prim {args : List Ty} {t : Ty} (p : Prim args t) (xs : Args Ty.denote args) :
    RunsS O body f (.prim p xs) (p.eval xs) (f (Event.local .prim (p.cost xs))) :=
  ⟨_, runs_prim.2 ⟨rfl, rfl⟩, by simp⟩

theorem RunsS.call (op : S.Op) (x : (S.arg op).denote) :
    RunsS O body f (.call op x) (O.run op x) (f (Event.call op x (O.run op x))) :=
  ⟨_, runs_call.2 ⟨rfl, rfl⟩, by simp⟩

theorem RunsS.bind {t a' : Ty} {p : Prog S (a, b) Ty.denote a'}
    {k : a'.denote → Prog S (a, b) Ty.denote t} {v : a'.denote} {r : t.denote} {s₁ s₂ : List α}
    (h₁ : RunsS O body f p v s₁) (h₂ : RunsS O body f (k v) r s₂) :
    RunsS O body f (.bind p k) r (s₁ ++ s₂) := by
  obtain ⟨t₁, h₁, rfl⟩ := h₁
  obtain ⟨t₂, h₂, rfl⟩ := h₂
  exact ⟨t₁ ++ t₂, runs_bind.2 ⟨v, t₁, t₂, h₁, h₂, rfl⟩, List.flatMap_append⟩

theorem RunsS.ite {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote}
    {s : List α} (h : RunsS O body f (cond c p q) r s) :
    RunsS O body f (.ite c p q) r (f (Event.local .branch 1) ++ s) := by
  obtain ⟨t', h, rfl⟩ := h
  exact ⟨_, runs_ite.2 ⟨t', h, rfl⟩, by simp⟩

theorem RunsS.caseOption_none {a' t : Ty} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {s : List α}
    (h : RunsS O body f p r s) :
    RunsS O body f (.caseOption none p q) r (f (Event.local .branch 1) ++ s) := by
  obtain ⟨t', h, rfl⟩ := h
  exact ⟨_, runs_caseOption_none.2 ⟨t', h, rfl⟩, by simp⟩

theorem RunsS.caseOption_some {a' t : Ty} {v : a'.denote} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {s : List α}
    (h : RunsS O body f (q v) r s) :
    RunsS O body f (.caseOption (some v) p q) r (f (Event.local .branch 1) ++ s) := by
  obtain ⟨t', h, rfl⟩ := h
  exact ⟨_, runs_caseOption_some.2 ⟨t', h, rfl⟩, by simp⟩

theorem RunsS.caseList_nil {a' t : Ty} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {s : List α}
    (h : RunsS O body f p r s) :
    RunsS O body f (.caseList (a := a') [] p q) r (f (Event.local .branch 1) ++ s) := by
  obtain ⟨t', h, rfl⟩ := h
  exact ⟨_, runs_caseList_nil.2 ⟨t', h, rfl⟩, by simp⟩

theorem RunsS.caseList_cons {a' t : Ty} {x : a'.denote} {xs : List a'.denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t}
    {r : t.denote} {s : List α} (h : RunsS O body f (q x xs) r s) :
    RunsS O body f (.caseList (a := a') (x :: xs) p q) r (f (Event.local .branch 1) ++ s) := by
  obtain ⟨t', h, rfl⟩ := h
  exact ⟨_, runs_caseList_cons.2 ⟨t', h, rfl⟩, by simp⟩

theorem RunsS.recur {x : a.denote} {r : b.denote} {s : List α}
    (h : RunsS O body f (body x) r s) :
    RunsS O body f (.recur x) r (f (Event.local .recCall 1) ++ s) := by
  obtain ⟨t', h, rfl⟩ := h
  exact ⟨_, runs_recur.2 ⟨t', h, rfl⟩, by simp⟩

theorem RunsS.loop_done {t : Ty} {x : t.denote} {g : t.denote → Prog S (a, b) Ty.denote (.option t)}
    {s : List α} (h : RunsS O body f (g x) none s) :
    RunsS O body f (.loop x g) x (f (Event.local .iter 1) ++ s) := by
  obtain ⟨t₁, h, rfl⟩ := h
  exact ⟨_, runs_loop.2 (Or.inl ⟨t₁, h, rfl, rfl⟩), by simp⟩

theorem RunsS.loop_step {t : Ty} {x x' r : t.denote}
    {g : t.denote → Prog S (a, b) Ty.denote (.option t)} {s₁ s₂ : List α}
    (h₁ : RunsS O body f (g x) (some x') s₁) (h₂ : RunsS O body f (.loop x' g) r s₂) :
    RunsS O body f (.loop x g) r (f (Event.local .iter 1) ++ (s₁ ++ s₂)) := by
  obtain ⟨t₁, h₁, rfl⟩ := h₁
  obtain ⟨t₂, h₂, rfl⟩ := h₂
  exact ⟨_, runs_loop.2 (Or.inr ⟨x', t₁, t₂, h₁, h₂, rfl⟩), by simp⟩

theorem RunsS.foldList_nil {a' b' : Ty} {init : b'.denote}
    {g : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} :
    RunsS O body f (.foldList (a := a') [] init g) init [] :=
  ⟨[], runs_foldList.2 (.nil _), rfl⟩

theorem RunsS.foldList_cons {a' b' : Ty} {x : a'.denote} {xs : List a'.denote}
    {acc acc' r : b'.denote} {g : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    {s₁ s₂ : List α} (h₁ : RunsS O body f (g acc x) acc' s₁)
    (h₂ : RunsS O body f (.foldList xs acc' g) r s₂) :
    RunsS O body f (.foldList (x :: xs) acc g) r (f (Event.local .iter 1) ++ (s₁ ++ s₂)) := by
  obtain ⟨t₁, h₁, rfl⟩ := h₁
  obtain ⟨t₂, h₂, rfl⟩ := h₂
  exact ⟨_, runs_foldList.2 (.cons h₁ (runs_foldList.1 h₂)), by simp⟩

theorem foldRuns_append {a' b' : Ty} {g : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} :
    ∀ {xs₁ xs₂ : List a'.denote} {acc acc' r : b'.denote} {t₁ t₂ : Trace S},
      FoldRuns O body g xs₁ acc acc' t₁ → FoldRuns O body g xs₂ acc' r t₂ →
        FoldRuns O body g (xs₁ ++ xs₂) acc r (t₁ ++ t₂)
  | [], _, _, _, _, _, _, h₁, h₂ => by
    cases h₁
    exact h₂
  | _ :: _, _, _, _, _, _, _, h₁, h₂ => by
    cases h₁ with
    | cons hx hrest =>
      rw [List.cons_append, List.cons_append, List.append_assoc]
      exact .cons hx (foldRuns_append hrest h₂)

theorem RunsS.foldList_split {a' b' : Ty} {xs xs₁ xs₂ : List a'.denote} {acc acc' r : b'.denote}
    {g : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} {s₁ s₂ : List α}
    (hx : xs = xs₁ ++ xs₂) (h₁ : RunsS O body f (.foldList xs₁ acc g) acc' s₁)
    (h₂ : RunsS O body f (.foldList xs₂ acc' g) r s₂) :
    RunsS O body f (.foldList xs acc g) r (s₁ ++ s₂) := by
  obtain ⟨t₁, h₁, rfl⟩ := h₁
  obtain ⟨t₂, h₂, rfl⟩ := h₂
  subst hx
  exact ⟨t₁ ++ t₂, runs_foldList.2 (foldRuns_append (runs_foldList.1 h₁) (runs_foldList.1 h₂)),
    List.flatMap_append⟩

/-! ### Pieces from kernel checks -/

/-- **The check of a piece**: the run of `p` (with fuel `fuel`) returns a value whose tree is
`tree`, with a trace whose summary is `s`. -/
def checkRunS [DecidableEq α] (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b)
    (f : Event S → List α) (fuel : ℕ) {t : Ty} (p : Prog S (a, b) Ty.denote t) (tree : SerTree)
    (s : List α) : Bool :=
  match eval O body fuel p with
  | some (r, tr) => SerTree.beq (serV t r) tree && decide (tr.flatMap f = s)
  | none => false

theorem runsS_of_check [DecidableEq α] {fuel : ℕ} {t : Ty} {p : Prog S (a, b) Ty.denote t}
    {tree : SerTree} {s : List α} (h : checkRunS O body f fuel p tree s = true) :
    RunsS O body f p (deserV t tree) s := by
  unfold checkRunS at h
  split at h
  · rename_i r tr he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h₁, h₂⟩ := h
    rw [← SerTree.eq_of_beq h₁, deserV_serV]
    exact ⟨tr, ⟨fuel, he⟩, h₂⟩
  · cases h

theorem RunsS.congr_summary {t : Ty} {p : Prog S (a, b) Ty.denote t} {v : t.denote}
    {s s' : List α} (h : RunsS O body f p v s) (hs : s = s') : RunsS O body f p v s' :=
  hs ▸ h

end RunsS

/-! ### The splitter -/

section Splitter

open Lean Meta Elab Command

/-- Configuration of `execRuns`. -/
structure Config where
  /-- The largest number of trace events a single kernel-checked piece may cover. -/
  budget : ℕ := 5000
  /-- The fuel of each piece's evaluation. -/
  fuel : ℕ := 10000000
  /-- Report the number of declarations and the largest piece. -/
  verbose : Bool := false

/-- What the compiled evaluation reports about a run: its value, its summary, its length. -/
def runInfo {S : Signature} {a b : Ty} {α : Type} (O : Oracle S)
    (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α) (fuel : ℕ) {t : Ty}
    (p : Prog S (a, b) Ty.denote t) : Option (t.denote × List α × ℕ) :=
  (eval O body fuel p).map fun x => (x.1, x.2.flatMap f, x.2.length)

/-- The binder names of a `∀`-type. -/
def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- Apply the lemma `lem` to the goal `g`: its conclusion is unified with the goal, its binders
named in `assign` get the given expressions (after the conclusion, which fixes their types), and
the hypotheses named in `hyps` are returned as new goals. -/
def applyNamed (g : MVarId) (lem : Name) (assign : List (Name × Expr)) (hyps : List Name) :
    MetaM (List MVarId) := do
  let ty ← inferType (mkConst lem)
  let names := binderNames ty
  let (ms, _, concl) ← forallMetaTelescope ty
  unless ← withAssignableSyntheticOpaque (isDefEq concl (← g.getType)) do
    throwError "execRuns: {lem} does not match the goal{indentExpr (← g.getType)}"
  for (nm, e) in assign do
    match names.idxOf? nm with
    | some i =>
      unless ← isDefEq ms[i]! e do
        throwError "execRuns: cannot assign {nm} in {lem}:{indentExpr e}\nof type\
          {indentExpr (← inferType e)}\nto a binder of type{indentExpr (← inferType ms[i]!)}"
    | none => throwError "execRuns: {lem} has no binder {nm}"
  g.assign (mkAppN (mkConst lem) ms)
  hyps.mapM fun nm => do
    match names.idxOf? nm with
    | some i => pure ms[i]!.mvarId!
    | none => throwError "execRuns: {lem} has no hypothesis {nm}"

/-- The expression `deserV t tree` for a runtime value. -/
def valueExpr (tE : Expr) (t : Ty) (v : t.denote) : Expr :=
  mkApp2 (mkConst ``deserV) tE (toExpr (serV t v))

/-- Statistics of a split. -/
structure Stats where
  pieces : ℕ := 0
  nodes : ℕ := 0
  largest : ℕ := 0

/-- The fixed part of the statements of a split: the arguments `S a b α O body f` of `RunsS`,
the summary type's `DecidableEq` instance, the prefix of the declarations' names, the
configuration and the statistics. -/
structure Ctx where
  pre : Array Expr
  inst : Expr
  base : Name
  cfg : Config
  stats : IO.Ref Stats

/-- The statement `RunsS O body f p v s` (`tE`: the type index of `p`). -/
def Ctx.runs (c : Ctx) (tE pE vE sE : Expr) : Expr :=
  mkAppN (mkConst ``RunsS) (c.pre ++ #[tE, pE, vE, sE])

/-- A fresh declaration name under the split's prefix. -/
def Ctx.fresh (c : Ctx) (kind : String) : CommandElabM Name := do
  let st ← c.stats.get
  pure (c.base ++ Name.mkSimple s!"{kind}{st.pieces + st.nodes}")

/-- Add the theorem `nm : ty := pf`; the kernel checks it now, as its own declaration. -/
def addThm (nm : Name) (ty pf : Expr) : CoreM Unit :=
  withOptions (Lean.Elab.async.set · false) <|
    addDecl (.thmDecl { name := nm, levelParams := [], type := ty, value := pf })

/-- No metavariables are left in `e`. -/
def closed (what : String) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.hasMVar then throwError "execRuns: the {what} is not determined{indentExpr e}"
  pure e

/-- **A piece**: the declaration `nm : RunsS O body f p (deserV t tree) s`, proved by
`runsS_of_check` and the kernel's evaluation of `checkRunS O body f fuel p tree s = true`
(`decide`). -/
def pieceDecl (c : Ctx) (nm : Name) (tE pE tree sE : Expr) : TermElabM Unit := do
  let p := c.pre
  let fuelE := mkNatLit c.cfg.fuel
  let check := mkAppN (mkConst ``checkRunS)
    #[p[0]!, p[1]!, p[2]!, p[3]!, c.inst, p[4]!, p[5]!, p[6]!, fuelE, tE, pE, tree, sE]
  let prop ← mkEq check (mkConst ``Bool.true)
  let pf ← mkDecideProof prop
  let proof := mkAppN (mkConst ``runsS_of_check)
    #[p[0]!, p[1]!, p[2]!, p[3]!, p[4]!, p[5]!, p[6]!, c.inst, fuelE, tE, pE, tree, sE, pf]
  addThm nm (c.runs tE pE (mkApp2 (mkConst ``deserV) tE tree) sE) proof

/-- The goal `RunsS O body f pW ?v ?s` with the lemma `lem` applied (`applyNamed`). -/
def applyAt (c : Ctx) (tE pW : Expr) (lem : Name) (assign : List (Name × Expr))
    (hyps : List Name) : MetaM (MVarId × List MVarId) := do
  let g ← mkFreshExprMVar (c.runs tE pW (← mkFreshExprMVar none) (← mkFreshExprMVar none))
  let hs ← applyNamed g.mvarId! lem assign hyps
  pure (g.mvarId!, hs)

/-- **A composite node**: the run of `pE` (whose head normal form `pW` starts with the
constructor that `lem` decomposes) from the runs of its parts. First the parts' programs are
read off the lemma's hypotheses (one elaboration), then each part is proved by its `kids`
entry (its own declarations), then the node's declaration
`nm : RunsS O body f pE v s := lem … (part₁) … (partₖ)` (one elaboration, checked by the
kernel). Returns its name, value and summary. -/
def composeNode (c : Ctx) (tE pE pW : Expr) (lem : Name) (assign : List (Name × Expr))
    (hyps : List Name) (kids : List (Expr → Expr → CommandElabM (Name × Expr × Expr))) :
    CommandElabM (Name × Expr × Expr) := do
  let parts ← liftTermElabM do
    let (_, hs) ← applyAt c tE pW lem assign hyps
    hs.mapM fun h => do
      let ty ← instantiateMVars (← h.getType)
      unless ty.isAppOfArity ``RunsS 11 do
        throwError "execRuns: {lem}: a hypothesis is not a `RunsS` statement"
      pure (← closed "type" (ty.getArg! 7), ← closed "program" (ty.getArg! 8))
  let mut done : Array Name := #[]
  for (k, (tE', pE')) in kids.zip parts do
    done := done.push (← k tE' pE').1
  let nm ← c.fresh "node"
  c.stats.modify fun st => { st with nodes := st.nodes + 1 }
  liftTermElabM do
    let (g, hs) ← applyAt c tE pW lem assign hyps
    for (h, cn) in hs.zip done.toList do
      unless ← isDefEq (← h.getType) (← inferType (mkConst cn)) do
        throwError "execRuns: {lem}: the part {cn} does not match{indentExpr (← h.getType)}"
      h.assign (mkConst cn)
    let ty ← instantiateMVars (← g.getType)
    let vE ← closed "value" (ty.getArg! 9)
    let sE ← closed "summary" (ty.getArg! 10)
    let pf ← closed "proof" (mkMVar g)
    addThm nm (c.runs tE pE vE sE) pf
    pure (nm, vE, sE)

/-- `whnfD` of a closed expression, in its own elaboration. -/
def whnfClosed (e : Expr) : CommandElabM Expr :=
  liftTermElabM do closed "head normal form" (← whnfD e)

mutual

/-- **The splitter.** Prove the run of `p` (the runtime program; `pE` its expression, `tE` the
expression of its type index, `info` its run's value, summary and number of events, computed
once by the caller) as declarations: one kernel-checked piece if the run has at most
`cfg.budget` events, otherwise a composite node split at the head constructor (`execSplit`).
Returns the name of the declaration `RunsS O body f pE v s`, and `v`, `s`. -/
partial def execNode {S : Signature} {a b : Ty} {α : Type} [ToExpr α]
    (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α)
    (c : Ctx) {t : Ty} (p : Prog S (a, b) Ty.denote t) (tE pE : Expr)
    (info : SerTree × List α × ℕ) : CommandElabM (Name × Expr × Expr) := do
  let (r, s, n) := info
  if n ≤ max c.cfg.budget 1 then
    let nm ← c.fresh "piece"
    c.stats.modify fun st => { st with pieces := st.pieces + 1, largest := max st.largest n }
    let tree := toExpr r
    let sE := toExpr s
    liftTermElabM <| pieceDecl c nm tE pE tree sE
    pure (nm, mkApp2 (mkConst ``deserV) tE tree, sE)
  else
    execSplit O body f c p tE pE info

/-- Split a run at the head constructor of its program (`composeNode` with the matching
composition lemma). The parts' runs are evaluated only where the parent's information does not
determine them (the first part of a `bind`, one iteration of a `loop` or a fold). -/
partial def execSplit {S : Signature} {a b : Ty} {α : Type} [ToExpr α]
    (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α)
    (c : Ctx) {t : Ty} (p : Prog S (a, b) Ty.denote t) (tE pE : Expr)
    (info : SerTree × List α × ℕ) : CommandElabM (Name × Expr × Expr) := do
  let pW ← whnfClosed pE
  let pa := pW.getAppArgs
  let (r, s, n) := info
  -- the summary of a part after one local event
  let br := s.drop (f (Event.local .branch 1)).length
  match t, p with
  | _, .bind (a := a') p₁ k =>
    let some (r₁, s₁, n₁) := runInfo O body f c.cfg.fuel p₁
      | throwError "execRuns: the run does not finish within the fuel"
    composeNode c tE pE pW ``RunsS.bind
      [(`a', pa[3]!), (`t, pa[4]!), (`p, pa[5]!), (`k, pa[6]!), (`v, valueExpr pa[3]! a' r₁)]
      [`h₁, `h₂]
      [fun tE' pE' => execNode O body f c p₁ tE' pE' (serV a' r₁, s₁, n₁),
       fun tE' pE' => execNode O body f c (k r₁) tE' pE' (r, s.drop s₁.length, n - n₁)]
  | _, .ite cnd q₁ q₂ =>
    composeNode c tE pE pW ``RunsS.ite
      [(`t, pa[3]!), (`c, pa[4]!), (`p, pa[5]!), (`q, pa[6]!)] [`h]
      [fun tE' pE' => execNode O body f c (cond cnd q₁ q₂) tE' pE' (r, br, n - 1)]
  | _, .caseOption o q₁ q₂ =>
    match o with
    | none =>
      composeNode c tE pE pW ``RunsS.caseOption_none
        [(`a', pa[3]!), (`t, pa[4]!), (`p, pa[6]!), (`q, pa[7]!)] [`h]
        [fun tE' pE' => execNode O body f c q₁ tE' pE' (r, br, n - 1)]
    | some v =>
      let oW ← whnfClosed pa[5]!
      composeNode c tE pE pW ``RunsS.caseOption_some
        [(`a', pa[3]!), (`t, pa[4]!), (`v, oW.appArg!), (`p, pa[6]!), (`q, pa[7]!)] [`h]
        [fun tE' pE' => execNode O body f c (q₂ v) tE' pE' (r, br, n - 1)]
  | _, .caseList l q₁ q₂ =>
    match l with
    | [] =>
      composeNode c tE pE pW ``RunsS.caseList_nil
        [(`a', pa[3]!), (`t, pa[4]!), (`p, pa[6]!), (`q, pa[7]!)] [`h]
        [fun tE' pE' => execNode O body f c q₁ tE' pE' (r, br, n - 1)]
    | x :: xs =>
      let la := (← whnfClosed pa[5]!).getAppArgs
      composeNode c tE pE pW ``RunsS.caseList_cons
        [(`a', pa[3]!), (`t, pa[4]!), (`x, la[1]!), (`xs, la[2]!), (`p, pa[6]!),
          (`q, pa[7]!)] [`h]
        [fun tE' pE' => execNode O body f c (q₂ x xs) tE' pE' (r, br, n - 1)]
  | t', .foldList (a := a') xs init step =>
    execFold O body f c (a' := a') (b' := t') xs init step tE pE pW pa (r, s, n)
  | t', .loop x step =>
    let some (o, s₁, n₁) := runInfo O body f c.cfg.fuel (step x)
      | throwError "execRuns: the run does not finish within the fuel"
    let it := (f (Event.local .iter 1)).length
    match o with
    | none =>
      composeNode c tE pE pW ``RunsS.loop_done [(`t, pa[3]!), (`x, pa[4]!), (`g, pa[5]!)] [`h]
        [fun tE' pE' => execNode O body f c (step x) tE' pE' (serV (.option t') none, s₁, n₁)]
    | some x' =>
      composeNode c tE pE pW ``RunsS.loop_step
        [(`t, pa[3]!), (`x, pa[4]!), (`x', valueExpr pa[3]! t' x'), (`g, pa[5]!)] [`h₁, `h₂]
        [fun tE' pE' =>
          execNode O body f c (step x) tE' pE' (serV (.option t') (some x'), s₁, n₁),
         fun tE' pE' => execNode O body f c (.loop x' step) tE' pE'
          (r, (s.drop it).drop s₁.length, n - 1 - n₁)]
  | _, .recur x =>
    composeNode c tE pE pW ``RunsS.recur [(`x, pa[3]!)] [`h]
      [fun tE' pE' => execNode O body f c (body x) tE' pE'
        (r, s.drop (f (Event.local .recCall 1)).length, n - 1)]
  | _, .ret _ | _, .prim _ _ | _, .call _ _ =>
    throwError "execRuns: a single event over the budget"

/-- Split the run of a fold: a prefix of at most `cfg.budget` events as one part
(`RunsS.foldList_split`), or the first element alone when it is larger (`RunsS.foldList_cons`).
`pa` are the arguments of the head normal form `pW` (a `Prog.foldList`) of `pE`. -/
partial def execFold {S : Signature} {a b : Ty} {α : Type} [ToExpr α]
    (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α)
    (c : Ctx) {a' b' : Ty} (xs : List a'.denote) (init : b'.denote)
    (step : b'.denote → a'.denote → Prog S (a, b) Ty.denote b') (tE pE pW : Expr)
    (pa : Array Expr) (info : SerTree × List α × ℕ) : CommandElabM (Name × Expr × Expr) := do
  let (r, s, n) := info
  let it := (f (Event.local .iter 1)).length
  -- the longest prefix of at most `budget` events
  let mut acc := init
  let mut used := 0
  let mut sl := 0
  let mut j := 0
  let mut first : Option (b'.denote × List α × ℕ) := none
  for x in xs do
    let some (acc', s', m) := runInfo O body f c.cfg.fuel (step acc x)
      | throwError "execRuns: the run does not finish within the fuel"
    if j = 0 then first := some (acc', s', m)
    if used + m + 1 > c.cfg.budget then break
    acc := acc'
    used := used + m + 1
    sl := sl + it + s'.length
    j := j + 1
  if j = 0 then
    match xs, first with
    | x :: rest, some (acc₁, s₁, m₁) =>
      let la := (← whnfClosed pa[5]!).getAppArgs
      composeNode c tE pE pW ``RunsS.foldList_cons
        [(`a', pa[3]!), (`b', pa[4]!), (`x, la[1]!), (`xs, la[2]!), (`acc, pa[6]!),
          (`acc', valueExpr pa[4]! b' acc₁), (`g, pa[7]!)] [`h₁, `h₂]
        [fun tE' pE' => execNode O body f c (step init x) tE' pE' (serV b' acc₁, s₁, m₁),
         fun tE' pE' => execNode O body f c (.foldList rest acc₁ step) tE' pE'
          (r, (s.drop it).drop s₁.length, n - 1 - m₁)]
    | _, _ => throwError "execRuns: empty fold over the budget"
  else
    let accE := valueExpr pa[4]! b' acc
    let (take, drop, hx) ← liftTermElabM do
      let jE := mkNatLit j
      let take ← mkAppM ``List.take #[jE, pa[5]!]
      let drop ← mkAppM ``List.drop #[jE, pa[5]!]
      let hx ← mkEqSymm (← mkAppM ``List.take_append_drop #[jE, pa[5]!])
      pure (← closed "prefix" take, ← closed "suffix" drop, ← closed "split" hx)
    composeNode c tE pE pW ``RunsS.foldList_split
      [(`a', pa[3]!), (`b', pa[4]!), (`xs, pa[5]!), (`xs₁, take), (`xs₂, drop),
        (`acc, pa[6]!), (`acc', accE), (`g, pa[7]!), (`hx, hx)] [`h₁, `h₂]
      [fun tE' pE' => execNode O body f c (.foldList (xs.take j) init step) tE' pE'
        (serV b' acc, s.take sl, used),
       fun tE' pE' => execNode O body f c (.foldList (xs.drop j) acc step) tE' pE'
        (r, s.drop sl, n - used)]

end

/-- **Prove a run in kernel-checked pieces**, run with `run_cmd`:
``execRuns n (← `(RunsS O body f p)) O body f p cfg``, where the syntax and the runtime
arguments name the same `O`, `body`, `f`, `p`. It adds the theorem
`n : RunsS O body f p v s` (in the current namespace), where `v` and `s` are the value and the
summary of the compiled run (`v = deserV t tree`, `s` a literal list). Every node of the split
is its own theorem (`n.pieceᵢ`: a kernel check of `checkRunS … = true`; `n.nodeᵢ`: a
composition lemma applied to its parts), elaborated by its own `liftTermElabM`, as the
declarations of a command are, with the default budgets; the last step restates the root's
summary as the literal `s` (`RunsS.congr_summary`, by the kernel's evaluation). -/
def execRuns {S : Signature} {a b : Ty} {α : Type} [ToExpr α] (n : Name) (stx : Term)
    (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) (f : Event S → List α)
    {t : Ty} (p : Prog S (a, b) Ty.denote t) (cfg : Config := {}) : CommandElabM Unit := do
  let base := (← getCurrNamespace) ++ n
  let some (r, sv, len) := runInfo O body f cfg.fuel p
    | throwError "execRuns: the run does not finish within the fuel"
  let (pre, inst, tE, pE) ← liftTermElabM do
    let e ← closed "statement" (← Term.elabTermAndSynthesize stx none)
    unless e.isAppOfArity ``RunsS 9 do
      throwError "execRuns: expected `RunsS O body f p`{indentExpr e}"
    let args := e.getAppArgs
    let inst ← synthInstance (← mkAppM ``DecidableEq #[args[3]!])
    pure (args.extract 0 7, inst, args[7]!, args[8]!)
  let stats ← IO.mkRef ({} : Stats)
  let c : Ctx := { pre, inst, base, cfg, stats }
  let (root, vE, sE) ← execNode O body f c p tE pE (serV t r, sv, len)
  liftTermElabM do
    let svE := toExpr sv
    let hs := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkApp (mkConst ``List [0]) pre[3]!) svE
    let pf := mkAppN (mkConst ``RunsS.congr_summary)
      (pre ++ #[tE, pE, vE, sE, svE, mkConst root, hs])
    addThm base (c.runs tE pE vE svE) pf
  if cfg.verbose then
    let st ← stats.get
    logInfo m!"execRuns: {st.pieces} pieces, {st.nodes} nodes, the largest {st.largest} events"

end Splitter

end GraphIsoChecks.Exec
