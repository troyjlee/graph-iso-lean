module

public import GraphIso.Cost.BackendRefinement

/-!
# Cost specifications of programs

`RunsWithin X body p v c`: the program `p` runs to the value `v` with a trace whose cost under
the schedule `X.B` is at most `c`, and every backend call in the trace satisfies the
precondition `X.Pre`. The last condition is what `runs_subst` needs to substitute a backend
implementation, and what lets a proof use the backend contract at each call.

The lemmas compose specifications constructor by constructor; costs add. A specification
fixes the result uniquely (`RunsWithin.unique`), since runs are deterministic.
-/

@[expose] public section

namespace GraphIso.Cost

variable {S : Signature}

/-- A verification context: an oracle, a backend cost schedule, and call preconditions. -/
structure Ctx (S : Signature) where
  /-- The backend. -/
  O : Oracle S
  /-- The backend cost schedule. -/
  B : CostSchedule S
  /-- Preconditions that every backend call must satisfy. -/
  Pre : (op : S.Op) → (S.arg op).denote → Prop

variable {a b : Ty} (X : Ctx S) (body : a.denote → Prog S (a, b) Ty.denote b)

/-- `p` runs to `v` at cost at most `c`, with every backend call satisfying its precondition. -/
def RunsWithin {t : Ty} (p : Prog S (a, b) Ty.denote t) (v : t.denote) (c : ℕ) : Prop :=
  ∃ tr, Runs X.O body p v tr ∧ Trace.cost X.B tr ≤ c ∧ Trace.CallsSatisfy X.Pre tr

variable {X body}

namespace RunsWithin

theorem mono {t : Ty} {p : Prog S (a, b) Ty.denote t} {v : t.denote} {c c' : ℕ}
    (h : RunsWithin X body p v c) (hc : c ≤ c') : RunsWithin X body p v c' :=
  let ⟨tr, hr, hcost, hpre⟩ := h
  ⟨tr, hr, Nat.le_trans hcost hc, hpre⟩

theorem unique {t : Ty} {p : Prog S (a, b) Ty.denote t} {v v' : t.denote} {c : ℕ} {tr : Trace S}
    (h : RunsWithin X body p v c) (h' : Runs X.O body p v' tr) : v = v' :=
  let ⟨_, hr, _, _⟩ := h
  (hr.unique h').1

theorem ret {t : Ty} (x : t.denote) : RunsWithin X body (.ret x) x 0 :=
  ⟨[], runs_ret.2 ⟨rfl, rfl⟩, Nat.le_refl _, by simp [Trace.CallsSatisfy]⟩

theorem bind {t a' : Ty} {p : Prog S (a, b) Ty.denote a'}
    {k : a'.denote → Prog S (a, b) Ty.denote t}
    {v : a'.denote} {r : t.denote} {c₁ c₂ : ℕ} (h₁ : RunsWithin X body p v c₁)
    (h₂ : RunsWithin X body (k v) r c₂) : RunsWithin X body (.bind p k) r (c₁ + c₂) := by
  obtain ⟨t₁, r₁, k₁, p₁⟩ := h₁
  obtain ⟨t₂, r₂, k₂, p₂⟩ := h₂
  refine ⟨t₁ ++ t₂, runs_bind.2 ⟨v, t₁, t₂, r₁, r₂, rfl⟩, ?_, ?_⟩
  · rw [Trace.cost_append]
    omega
  · exact Trace.CallsSatisfy.append.2 ⟨p₁, p₂⟩

/-- Goal-directed sequencing: the continuation is read off the goal. -/
theorem bind_le {t a' : Ty} {p : Prog S (a, b) Ty.denote a'}
    {k : a'.denote → Prog S (a, b) Ty.denote t} {v : a'.denote} {r : t.denote} {c₁ c₂ c : ℕ}
    (h₁ : RunsWithin X body p v c₁) (h₂ : RunsWithin X body (k v) r c₂) (hc : c₁ + c₂ ≤ c) :
    RunsWithin X body (.bind p k) r c :=
  (bind h₁ h₂).mono hc

theorem of_eq {t : Ty} {p : Prog S (a, b) Ty.denote t} {v v' : t.denote} {c : ℕ}
    (h : RunsWithin X body p v c) (e : v = v') : RunsWithin X body p v' c :=
  e ▸ h

theorem prim {args : List Ty} {t : Ty} (p : Prim args t) (xs : Args Ty.denote args) :
    RunsWithin X body (.prim p xs) (p.eval xs) (p.cost xs) :=
  ⟨_, runs_prim.2 ⟨rfl, rfl⟩, by simp [Trace.cost], by simp [Trace.CallsSatisfy, Trace.calls]⟩

/-- A primitive, with its result and cost given up to equality and bound. -/
theorem prim_le {args : List Ty} {t : Ty} {p : Prim args t} {xs : Args Ty.denote args}
    {v : t.denote} {c : ℕ} (hv : p.eval xs = v) (hc : p.cost xs ≤ c) :
    RunsWithin X body (.prim p xs) v c :=
  (hv ▸ prim p xs).mono hc

theorem ite {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body (cond c p q) r k) : RunsWithin X body (.ite c p q) r (1 + k) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_ite.2 ⟨tr, hr, rfl⟩, by simp only [Trace.cost_cons, Event.cost_local]; omega,
    Trace.CallsSatisfy.cons_local.2 hp⟩

theorem ite_true {t : Ty} {p q : Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body p r k) : RunsWithin X body (.ite true p q) r (1 + k) := ite h

theorem ite_false {t : Ty} {p q : Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body q r k) : RunsWithin X body (.ite false p q) r (1 + k) := ite h

theorem caseOption_none {a' t : Ty} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body p r k) : RunsWithin X body (.caseOption none p q) r (1 + k) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_caseOption_none.2 ⟨tr, hr, rfl⟩,
    by simp only [Trace.cost_cons, Event.cost_local]; omega, Trace.CallsSatisfy.cons_local.2 hp⟩

theorem caseOption_some {a' t : Ty} {v : a'.denote} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body (q v) r k) :
    RunsWithin X body (.caseOption (some v) p q) r (1 + k) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_caseOption_some.2 ⟨tr, hr, rfl⟩,
    by simp only [Trace.cost_cons, Event.cost_local]; omega, Trace.CallsSatisfy.cons_local.2 hp⟩

theorem caseList_nil {a' t : Ty} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body p r k) :
    RunsWithin X body (.caseList (a := a') [] p q) r (1 + k) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_caseList_nil.2 ⟨tr, hr, rfl⟩,
    by simp only [Trace.cost_cons, Event.cost_local]; omega, Trace.CallsSatisfy.cons_local.2 hp⟩

theorem caseList_cons {a' t : Ty} {x : a'.denote} {xs : List a'.denote}
    {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (h : RunsWithin X body (q x xs) r k) :
    RunsWithin X body (.caseList (a := a') (x :: xs) p q) r (1 + k) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_caseList_cons.2 ⟨tr, hr, rfl⟩,
    by simp only [Trace.cost_cons, Event.cost_local]; omega, Trace.CallsSatisfy.cons_local.2 hp⟩

theorem foldList_nil {a' b' : Ty} {init : b'.denote}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} :
    RunsWithin X body (.foldList [] init f) init 0 :=
  ⟨[], runs_foldList.2 (.nil _), Nat.le_refl _, by simp [Trace.CallsSatisfy]⟩

theorem foldList_cons {a' b' : Ty} {x : a'.denote} {xs : List a'.denote} {init acc r : b'.denote}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} {c₁ c₂ : ℕ}
    (h₁ : RunsWithin X body (f init x) acc c₁) (h₂ : RunsWithin X body (.foldList xs acc f) r c₂) :
    RunsWithin X body (.foldList (x :: xs) init f) r (1 + c₁ + c₂) := by
  obtain ⟨t₁, r₁, k₁, p₁⟩ := h₁
  obtain ⟨t₂, r₂, k₂, p₂⟩ := h₂
  refine ⟨_, runs_foldList.2 (.cons r₁ (runs_foldList.1 r₂)), ?_, ?_⟩
  · simp only [Trace.cost_cons, Event.cost_local, Trace.cost_append]
    omega
  · exact Trace.CallsSatisfy.cons_local.2 (Trace.CallsSatisfy.append.2 ⟨p₁, p₂⟩)

theorem loop_none {s : Ty} {x : s.denote} {f : s.denote → Prog S (a, b) Ty.denote (.option s)}
    {c : ℕ} (h : RunsWithin X body (f x) none c) : RunsWithin X body (.loop x f) x (1 + c) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_loop.2 (Or.inl ⟨tr, hr, rfl, rfl⟩),
    by simp only [Trace.cost_cons, Event.cost_local]; omega, Trace.CallsSatisfy.cons_local.2 hp⟩

theorem loop_some {s : Ty} {x x' r : s.denote}
    {f : s.denote → Prog S (a, b) Ty.denote (.option s)} {c₁ c₂ : ℕ}
    (h₁ : RunsWithin X body (f x) (some x') c₁) (h₂ : RunsWithin X body (.loop x' f) r c₂) :
    RunsWithin X body (.loop x f) r (1 + c₁ + c₂) := by
  obtain ⟨t₁, r₁, k₁, p₁⟩ := h₁
  obtain ⟨t₂, r₂, k₂, p₂⟩ := h₂
  refine ⟨_, runs_loop.2 (Or.inr ⟨x', t₁, t₂, r₁, r₂, rfl⟩), ?_, ?_⟩
  · simp only [Trace.cost_cons, Event.cost_local, Trace.cost_append]
    omega
  · exact Trace.CallsSatisfy.cons_local.2 (Trace.CallsSatisfy.append.2 ⟨p₁, p₂⟩)

theorem recur {x : a.denote} {r : b.denote} {c : ℕ} (h : RunsWithin X body (body x) r c) :
    RunsWithin X body (.recur x) r (1 + c) := by
  obtain ⟨tr, hr, hc, hp⟩ := h
  exact ⟨_, runs_recur.2 ⟨tr, hr, rfl⟩, by simp only [Trace.cost_cons, Event.cost_local]; omega,
    Trace.CallsSatisfy.cons_local.2 hp⟩

theorem call {op : S.Op} {x : (S.arg op).denote} (hx : X.Pre op x) :
    RunsWithin X body (.call op x) (X.O.run op x) (X.B.call op x (X.O.run op x)) :=
  ⟨_, runs_call.2 ⟨rfl, rfl⟩, by simp [Trace.cost],
    fun e he => by simp [Trace.calls] at he; subst he; exact hx⟩

/-- Sequencing with the cost of the continuation left open (for `run_step`). -/
theorem step {t a' : Ty} {p : Prog S (a, b) Ty.denote a'}
    {k : a'.denote → Prog S (a, b) Ty.denote t} {v : a'.denote} {r : t.denote} {c₁ c₂ : ℕ}
    (h₁ : RunsWithin X body p v c₁) (h₂ : RunsWithin X body (k v) r c₂) :
    RunsWithin X body (.bind p k) r (c₁ + c₂) :=
  h₁.bind h₂

end RunsWithin

/-- `run_with t`: apply the specification lemma `t` whose remaining premise has an undetermined
cost, and continue with that premise; the cost is fixed by the later steps. Typical use:
`apply RunsWithin.mono`, then in `case h` a chain of `run_step` / `run_with` steps, and in
`case hc` the arithmetic. -/
macro "run_with " t:term : tactic => `(tactic| (refine' $t; rotate_left))

/-- `run_step h`: sequence the run `h` of the first program of a `bind`. -/
macro "run_step " h:term : tactic => `(tactic| run_with RunsWithin.step $h _)

/-- A context over the empty signature: no backend at all. -/
def Ctx.empty : Ctx Signature.empty where
  O := ⟨fun op => op.elim⟩
  B := ⟨fun op => op.elim⟩
  Pre := fun op => op.elim

end GraphIso.Cost
