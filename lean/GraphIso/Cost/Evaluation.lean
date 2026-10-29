module

public import GraphIso.Cost.Program

/-!
# Evaluation with traces of charged operations

`eval O body fuel p` runs the program `p` inside the recursive procedure `body`, with backend
calls answered by the oracle `O`. It returns the result together with the **trace** of
charged events that the run actually performed: one `Event.local` for each primitive (with its
`Prim.cost`), branch, loop or fold iteration and recursive call, and one `Event.call`
recording each backend operation with its actual argument and result. The trace is produced
by the evaluator from the program structure; programs have no access to it.

Fuel only bounds the evaluation depth so that `eval` is a total Lean function; it is not a
cost. `Runs O body p v tr` says that some fuel suffices and the run returns `v` with trace
`tr`; runs are unique (`Runs.unique`).

For a backend cost schedule `B`,
`Trace.cost B tr = Trace.localCost tr + Σ_{backend events e} B e` (`Trace.cost_eq`), which is
additive (`Trace.cost_append`) and monotone in `B` (`Trace.cost_mono`).
-/

@[expose] public section

namespace GraphIso.Cost

variable {S : Signature}

/-- An abstract backend: a function for each backend operation. -/
structure Oracle (S : Signature) where
  /-- The result of an operation on an argument. -/
  run : (op : S.Op) → (S.arg op).denote → (S.res op).denote

/-- Kinds of local work. -/
inductive LocalKind where
  | prim
  | branch
  | iter
  | recCall
  deriving DecidableEq, Repr

/-- A charged event. -/
inductive Event (S : Signature) where
  /-- Local work of the given kind and number of units. -/
  | local (kind : LocalKind) (units : ℕ)
  /-- A backend call, with its actual argument and result. -/
  | call (op : S.Op) (x : (S.arg op).denote) (y : (S.res op).denote)

/-- A trace of charged events. -/
abbrev Trace (S : Signature) := List (Event S)

/-! ### Traced partial results -/

/-- Information order on partial results: `OLe o o'` if `o'` agrees with `o` whenever `o` is
defined. -/
def OLe {α : Type} (o o' : Option α) : Prop := ∀ r, o = some r → o' = some r

theorem OLe.refl {α : Type} (o : Option α) : OLe o o := fun _ h => h

/-- Sequence two traced results, concatenating their traces. -/
def seqT {α β : Type} (o : Option (α × Trace S)) (k : α → Option (β × Trace S)) :
    Option (β × Trace S) :=
  match o with
  | none => none
  | some (v, t₁) =>
    match k v with
    | none => none
    | some (r, t₂) => some (r, t₁ ++ t₂)

/-- Prepend an event to a traced result. -/
def consT {α : Type} (e : Event S) (o : Option (α × Trace S)) : Option (α × Trace S) :=
  match o with
  | none => none
  | some (r, t) => some (r, e :: t)

section Combinators

variable {α β : Type}

theorem seqT_eq_some {o : Option (α × Trace S)} {k : α → Option (β × Trace S)} {r : β}
    {tr : Trace S} :
    seqT o k = some (r, tr) ↔
      ∃ v t₁ t₂, o = some (v, t₁) ∧ k v = some (r, t₂) ∧ tr = t₁ ++ t₂ := by
  constructor
  · intro h
    rcases o with _ | ⟨v, t₁⟩
    · simp [seqT] at h
    · rcases hk : k v with _ | ⟨r', t₂⟩
      · simp [seqT, hk] at h
      · simp only [seqT, hk, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨v, t₁, t₂, rfl, hk, rfl⟩
  · rintro ⟨v, t₁, t₂, rfl, hk, rfl⟩
    simp [seqT, hk]

theorem consT_eq_some {e : Event S} {o : Option (α × Trace S)} {r : α} {tr : Trace S} :
    consT e o = some (r, tr) ↔ ∃ t, o = some (r, t) ∧ tr = e :: t := by
  constructor
  · intro h
    rcases o with _ | ⟨r', t⟩
    · simp [consT] at h
    · simp only [consT, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t, rfl, rfl⟩
  · rintro ⟨t, rfl, rfl⟩
    rfl

theorem OLe.seqT {o o' : Option (α × Trace S)} {k k' : α → Option (β × Trace S)}
    (ho : OLe o o') (hk : ∀ v, OLe (k v) (k' v)) : OLe (Cost.seqT o k) (Cost.seqT o' k') := by
  rintro ⟨r, tr⟩ h
  obtain ⟨v, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 h
  exact seqT_eq_some.2 ⟨v, t₁, t₂, ho _ h₁, hk v _ h₂, rfl⟩

theorem OLe.consT {e : Event S} {o o' : Option (α × Trace S)} (ho : OLe o o') :
    OLe (Cost.consT e o) (Cost.consT e o') := by
  rintro ⟨r, tr⟩ h
  obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
  exact consT_eq_some.2 ⟨t, ho _ h₁, rfl⟩

end Combinators

/-- Run a step function over a list, threading an accumulator and concatenating traces.
Each element is charged one iteration event. -/
def foldRun {α β : Type} (step : β → α → Option (β × Trace S)) :
    List α → β → Option (β × Trace S)
  | [], acc => some (acc, [])
  | x :: xs, acc => consT (Event.local .iter 1) (seqT (step acc x) fun acc' => foldRun step xs acc')

theorem foldRun_mono {α β : Type} {step step' : β → α → Option (β × Trace S)}
    (h : ∀ acc x, OLe (step acc x) (step' acc x)) :
    ∀ (xs : List α) (acc : β), OLe (foldRun step xs acc) (foldRun step' xs acc)
  | [], _ => OLe.refl _
  | x :: xs, acc => OLe.consT (OLe.seqT (h acc x) fun acc' => foldRun_mono h xs acc')

variable {a b : Ty}

/-- Fuel-bounded evaluation, returning the result and the trace of charged events.

Case analysis matches on the scrutinee before evaluating a branch, so compiled code evaluates
only the branch taken (a branch passed as an ordinary argument would be evaluated eagerly). -/
def eval (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) :
    ℕ → {t : Ty} → Prog S (a, b) Ty.denote t → Option (t.denote × Trace S)
  | 0, _, _ => none
  | _ + 1, _, .ret x => some (x, [])
  | fuel + 1, _, .bind p k => seqT (eval O body fuel p) fun v => eval O body fuel (k v)
  | _ + 1, _, .prim p xs => some (p.eval xs, [Event.local .prim (p.cost xs)])
  | fuel + 1, _, .ite c p q => consT (Event.local .branch 1) (eval O body fuel (cond c p q))
  | fuel + 1, _, .caseOption o p q =>
    consT (Event.local .branch 1)
      (match o with
        | none => eval O body fuel p
        | some v => eval O body fuel (q v))
  | fuel + 1, _, .caseList l p q =>
    consT (Event.local .branch 1)
      (match l with
        | [] => eval O body fuel p
        | x :: xs => eval O body fuel (q x xs))
  | fuel + 1, _, .foldList xs init f => foldRun (fun acc x => eval O body fuel (f acc x)) xs init
  | fuel + 1, _, .loop s f =>
    consT (Event.local .iter 1)
      (seqT (eval O body fuel (f s)) fun o =>
        match o with
        | none => some (s, [])
        | some s' => eval O body fuel (.loop s' f))
  | fuel + 1, _, .recur x => consT (Event.local .recCall 1) (eval O body fuel (body x))
  | _ + 1, _, .call op x => some (O.run op x, [Event.call op x (O.run op x)])

section Mono

variable {O : Oracle S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- One more unit of fuel never changes a successful evaluation. -/
theorem eval_le_succ :
    ∀ (fuel : ℕ) {t : Ty} (p : Prog S (a, b) Ty.denote t),
      OLe (eval O body fuel p) (eval O body (fuel + 1) p)
  | 0, _, _ => fun _ h => by simp [eval] at h
  | fuel + 1, _, p => by
    have ih : ∀ {t : Ty} (p : Prog S (a, b) Ty.denote t),
        OLe (eval O body fuel p) (eval O body (fuel + 1) p) := fun p => eval_le_succ fuel p
    cases p with
    | ret x => exact OLe.refl _
    | bind p k => exact OLe.seqT (ih p) fun v => ih (k v)
    | prim p xs => exact OLe.refl _
    | ite c p q => exact OLe.consT (ih _)
    | caseOption o p q => cases o <;> exact OLe.consT (ih _)
    | caseList l p q => cases l <;> exact OLe.consT (ih _)
    | foldList xs init f => exact foldRun_mono (fun acc x => ih _) xs init
    | loop s f =>
      refine OLe.consT (OLe.seqT (ih _) fun o => ?_)
      cases o with
      | none => exact OLe.refl _
      | some s' => exact ih _
    | recur x => exact OLe.consT (ih _)
    | call op x => exact OLe.refl _

theorem eval_mono {fuel fuel' : ℕ} (hle : fuel ≤ fuel') {t : Ty}
    {p : Prog S (a, b) Ty.denote t} {r : t.denote × Trace S}
    (h : eval O body fuel p = some r) : eval O body fuel' p = some r := by
  induction hle with
  | refl => exact h
  | step _ ih => exact eval_le_succ _ _ _ ih

end Mono

/-! ### Runs -/

/-- The program `p` runs (for some fuel) to the value `v` with trace `tr`. -/
def Runs (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b) {t : Ty}
    (p : Prog S (a, b) Ty.denote t) (v : t.denote) (tr : Trace S) : Prop :=
  ∃ fuel, eval O body fuel p = some (v, tr)

section Runs

variable {O : Oracle S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- Runs are deterministic. -/
theorem Runs.unique {t : Ty} {p : Prog S (a, b) Ty.denote t} {v v' : t.denote}
    {tr tr' : Trace S} (h : Runs O body p v tr) (h' : Runs O body p v' tr') :
    v = v' ∧ tr = tr' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨f', hf'⟩ := h'
  have e₁ := eval_mono (Nat.le_max_left f f') hf
  have e₂ := eval_mono (Nat.le_max_right f f') hf'
  rw [e₁] at e₂
  simp only [Option.some.injEq, Prod.mk.injEq] at e₂
  exact e₂

theorem runs_ret {t : Ty} {x v : t.denote} {tr : Trace S} :
    Runs O body (.ret x) v tr ↔ v = x ∧ tr = [] := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · simp only [eval, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, rfl⟩

theorem runs_bind {t a' : Ty} {p : Prog S (a, b) Ty.denote a'}
    {k : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {tr : Trace S} :
    Runs O body (.bind p k) r tr ↔
      ∃ v t₁ t₂, Runs O body p v t₁ ∧ Runs O body (k v) r t₂ ∧ tr = t₁ ++ t₂ := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨v, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 h
      exact ⟨v, t₁, t₂, ⟨f, h₁⟩, ⟨f, h₂⟩, rfl⟩
  · rintro ⟨v, t₁, t₂, ⟨f₁, h₁⟩, ⟨f₂, h₂⟩, rfl⟩
    exact ⟨max f₁ f₂ + 1, seqT_eq_some.2 ⟨v, t₁, t₂, eval_mono (Nat.le_max_left _ _) h₁,
      eval_mono (Nat.le_max_right _ _) h₂, rfl⟩⟩

theorem runs_prim {args : List Ty} {t : Ty} {p : Prim args t} {xs : Args Ty.denote args}
    {v : t.denote} {tr : Trace S} :
    Runs O body (.prim p xs) v tr ↔ v = p.eval xs ∧ tr = [Event.local .prim (p.cost xs)] := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · simp only [eval, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, rfl⟩

theorem runs_ite {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote}
    {tr : Trace S} :
    Runs O body (.ite c p q) r tr ↔
      ∃ t', Runs O body (cond c p q) r t' ∧ tr = Event.local .branch 1 :: t' := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 h
      exact ⟨t', ⟨f, h₁⟩, rfl⟩
  · rintro ⟨t', ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, consT_eq_some.2 ⟨t', hf, rfl⟩⟩

theorem runs_caseOption_none {a' t : Ty} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {tr : Trace S} :
    Runs O body (.caseOption none p q) r tr ↔
      ∃ t', Runs O body p r t' ∧ tr = Event.local .branch 1 :: t' := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 h
      exact ⟨t', ⟨f, h₁⟩, rfl⟩
  · rintro ⟨t', ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, consT_eq_some.2 ⟨t', hf, rfl⟩⟩

theorem runs_caseOption_some {a' t : Ty} {v : a'.denote} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {tr : Trace S} :
    Runs O body (.caseOption (some v) p q) r tr ↔
      ∃ t', Runs O body (q v) r t' ∧ tr = Event.local .branch 1 :: t' := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 h
      exact ⟨t', ⟨f, h₁⟩, rfl⟩
  · rintro ⟨t', ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, consT_eq_some.2 ⟨t', hf, rfl⟩⟩

theorem runs_caseList_nil {a' t : Ty} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {tr : Trace S} :
    Runs O body (.caseList (a := a') [] p q) r tr ↔
      ∃ t', Runs O body p r t' ∧ tr = Event.local .branch 1 :: t' := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 h
      exact ⟨t', ⟨f, h₁⟩, rfl⟩
  · rintro ⟨t', ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, consT_eq_some.2 ⟨t', hf, rfl⟩⟩

theorem runs_caseList_cons {a' t : Ty} {x : a'.denote} {xs : List a'.denote}
    {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {tr : Trace S} :
    Runs O body (.caseList (a := a') (x :: xs) p q) r tr ↔
      ∃ t', Runs O body (q x xs) r t' ∧ tr = Event.local .branch 1 :: t' := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 h
      exact ⟨t', ⟨f, h₁⟩, rfl⟩
  · rintro ⟨t', ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, consT_eq_some.2 ⟨t', hf, rfl⟩⟩

/-- Runs of a fold: the body runs on each element in turn, from the given accumulator. -/
inductive FoldRuns {a' b' : Ty} (O : Oracle S) (body : a.denote → Prog S (a, b) Ty.denote b)
    (f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b') :
    List a'.denote → b'.denote → b'.denote → Trace S → Prop where
  | nil (acc : b'.denote) : FoldRuns O body f [] acc acc []
  | cons {x : a'.denote} {xs : List a'.denote} {acc acc' r : b'.denote} {t₁ t₂ : Trace S} :
      Runs O body (f acc x) acc' t₁ → FoldRuns O body f xs acc' r t₂ →
      FoldRuns O body f (x :: xs) acc r (Event.local .iter 1 :: (t₁ ++ t₂))

theorem runs_foldList {a' b' : Ty} {xs : List a'.denote} {init : b'.denote}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'} {r : b'.denote} {tr : Trace S} :
    Runs O body (.foldList xs init f) r tr ↔ FoldRuns O body f xs init r tr := by
  constructor
  · rintro ⟨_ | fuel, h⟩
    · simp [eval] at h
    · change foldRun (fun acc x => eval O body fuel (f acc x)) xs init = some (r, tr) at h
      induction xs generalizing init r tr with
      | nil =>
        simp only [foldRun, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2]
        exact .nil _
      | cons x xs ih =>
        obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
        obtain ⟨acc', t₁, t₂, h₂, h₃, rfl⟩ := seqT_eq_some.1 h₁
        exact .cons ⟨fuel, h₂⟩ (ih h₃)
  · intro h
    suffices ∃ fuel, foldRun (fun acc x => eval O body fuel (f acc x)) xs init = some (r, tr) by
      obtain ⟨fuel, hf⟩ := this
      exact ⟨fuel + 1, hf⟩
    induction h with
    | nil acc => exact ⟨0, rfl⟩
    | @cons x xs acc acc' r t₁ t₂ h₁ _ ih =>
      obtain ⟨f₁, hf₁⟩ := h₁
      obtain ⟨f₂, hf₂⟩ := ih
      refine ⟨max f₁ f₂, consT_eq_some.2 ⟨_, seqT_eq_some.2 ⟨acc', t₁, t₂,
        eval_mono (Nat.le_max_left _ _) hf₁, ?_, rfl⟩, rfl⟩⟩
      exact foldRun_mono (fun acc x => fun r hr => eval_mono (Nat.le_max_right f₁ f₂) hr) xs acc'
        _ hf₂

theorem runs_loop {s : Ty} {x : s.denote} {f : s.denote → Prog S (a, b) Ty.denote (.option s)}
    {r : s.denote} {tr : Trace S} :
    Runs O body (.loop x f) r tr ↔
      (∃ t₁, Runs O body (f x) none t₁ ∧ r = x ∧ tr = Event.local .iter 1 :: t₁) ∨
      (∃ x' t₁ t₂, Runs O body (f x) (some x') t₁ ∧ Runs O body (.loop x' f) r t₂ ∧
        tr = Event.local .iter 1 :: (t₁ ++ t₂)) := by
  constructor
  · rintro ⟨_ | fuel, h⟩
    · simp [eval] at h
    · obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
      obtain ⟨o, t₁, t₂, h₂, h₃, rfl⟩ := seqT_eq_some.1 h₁
      cases o with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h₃
        obtain ⟨rfl, rfl⟩ := h₃
        exact Or.inl ⟨t₁, ⟨fuel, h₂⟩, rfl, by simp⟩
      | some x' => exact Or.inr ⟨x', t₁, t₂, ⟨fuel, h₂⟩, ⟨fuel, h₃⟩, rfl⟩
  · rintro (⟨t₁, ⟨fuel, hf⟩, rfl, rfl⟩ | ⟨x', t₁, t₂, ⟨f₁, h₁⟩, ⟨f₂, h₂⟩, rfl⟩)
    · exact ⟨fuel + 1, consT_eq_some.2 ⟨t₁, seqT_eq_some.2 ⟨none, t₁, [], hf, rfl, by simp⟩, rfl⟩⟩
    · exact ⟨max f₁ f₂ + 1, consT_eq_some.2 ⟨_, seqT_eq_some.2 ⟨some x', t₁, t₂,
        eval_mono (Nat.le_max_left _ _) h₁, eval_mono (Nat.le_max_right _ _) h₂, rfl⟩, rfl⟩⟩

theorem runs_recur {x : a.denote} {r : b.denote} {tr : Trace S} :
    Runs O body (.recur x) r tr ↔
      ∃ t', Runs O body (body x) r t' ∧ tr = Event.local .recCall 1 :: t' := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 h
      exact ⟨t', ⟨f, h₁⟩, rfl⟩
  · rintro ⟨t', ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, consT_eq_some.2 ⟨t', hf, rfl⟩⟩

theorem runs_call {op : S.Op} {x : (S.arg op).denote} {v : (S.res op).denote} {tr : Trace S} :
    Runs O body (.call op x) v tr ↔ v = O.run op x ∧ tr = [Event.call op x (O.run op x)] := by
  constructor
  · rintro ⟨_ | f, h⟩
    · simp [eval] at h
    · simp only [eval, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨h.1.symm, h.2.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨1, rfl⟩

end Runs

/-! ### Costs -/

/-- A backend cost schedule: the charge for each backend event. -/
structure CostSchedule (S : Signature) where
  /-- The charge for calling `op` on `x` with result `y`. -/
  call : (op : S.Op) → (S.arg op).denote → (S.res op).denote → ℕ

instance : LE (CostSchedule S) := ⟨fun B B' => ∀ op x y, B.call op x y ≤ B'.call op x y⟩

namespace Event

/-- Units of local work. -/
def localCost : Event S → ℕ
  | .local _ u => u
  | .call _ _ _ => 0

/-- The charge for a backend event. -/
def callCost (B : CostSchedule S) : Event S → ℕ
  | .local _ _ => 0
  | .call op x y => B.call op x y

/-- The total charge of an event. -/
def cost (B : CostSchedule S) : Event S → ℕ
  | .local _ u => u
  | .call op x y => B.call op x y

@[simp] theorem cost_local (B : CostSchedule S) (k : LocalKind) (u : ℕ) :
    (Event.local k u : Event S).cost B = u := rfl

@[simp] theorem cost_call (B : CostSchedule S) (op : S.Op) (x : (S.arg op).denote)
    (y : (S.res op).denote) : (Event.call op x y).cost B = B.call op x y := rfl

@[simp] theorem localCost_local (k : LocalKind) (u : ℕ) :
    (Event.local k u : Event S).localCost = u := rfl

@[simp] theorem localCost_call (op : S.Op) (x : (S.arg op).denote) (y : (S.res op).denote) :
    (Event.call op x y).localCost = 0 := rfl

theorem cost_eq (B : CostSchedule S) (e : Event S) : e.cost B = e.localCost + e.callCost B := by
  cases e <;> simp [cost, localCost, callCost]

end Event

namespace Trace

/-! The sums over a trace accumulate from the left, so compiled code sums a long trace in
constant stack space; `localCost_eq_sum`, `callCost_eq_sum` and `cost_eq_sum` restate them as
sums. -/

/-- Total local work. -/
def localCost (tr : Trace S) : ℕ := tr.foldl (fun c e => c + e.localCost) 0

/-- Total backend charge. -/
def callCost (B : CostSchedule S) (tr : Trace S) : ℕ :=
  tr.foldl (fun c e => c + e.callCost B) 0

/-- Total cost under the backend schedule `B`. -/
def cost (B : CostSchedule S) (tr : Trace S) : ℕ := tr.foldl (fun c e => c + e.cost B) 0

/-- A backend event: an operation with its actual argument and result. -/
abbrev CallRecord (S : Signature) := Σ op : S.Op, (S.arg op).denote × (S.res op).denote

/-- The backend events of a trace, in order. -/
def calls : Trace S → List (CallRecord S)
  | [] => []
  | .local _ _ :: tr => calls tr
  | .call op x y :: tr => ⟨op, x, y⟩ :: calls tr

variable (B : CostSchedule S) (tr tr₁ tr₂ : Trace S)

theorem foldl_add_eq_sum (f : Event S → ℕ) :
    tr.foldl (fun c e => c + f e) 0 = (tr.map f).sum := by
  rw [List.sum_eq_foldl, List.foldl_map]

theorem localCost_eq_sum : localCost tr = (tr.map Event.localCost).sum := foldl_add_eq_sum _ _

theorem callCost_eq_sum : callCost B tr = (tr.map (Event.callCost B)).sum :=
  foldl_add_eq_sum _ _

theorem cost_eq_sum : cost B tr = (tr.map (Event.cost B)).sum := foldl_add_eq_sum _ _

theorem cost_eq : cost B tr = localCost tr + callCost B tr := by
  rw [cost_eq_sum, localCost_eq_sum, callCost_eq_sum]
  induction tr with
  | nil => simp
  | cons e tr ih =>
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Event.cost_eq]
    omega

theorem callCost_eq_sum_calls :
    callCost B tr = ((calls tr).map fun e => B.call e.1 e.2.1 e.2.2).sum := by
  rw [callCost_eq_sum]
  induction tr with
  | nil => simp [calls]
  | cons e tr ih =>
    cases e with
    | «local» k u => simpa [calls, Event.callCost] using ih
    | call op x y =>
      simp only [calls, Event.callCost, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]

/-- `cost_B(t) = localCost(t) + Σ_{e ∈ backendEvents(t)} B(e)`. -/
theorem cost_eq_localCost_add_sum_calls :
    cost B tr = localCost tr + ((calls tr).map fun e => B.call e.1 e.2.1 e.2.2).sum := by
  rw [cost_eq, callCost_eq_sum_calls]

@[simp] theorem cost_nil : Trace.cost B ([] : Trace S) = 0 := rfl
@[simp] theorem localCost_nil : Trace.localCost ([] : Trace S) = 0 := rfl
@[simp] theorem calls_nil : Trace.calls ([] : Trace S) = [] := rfl

@[simp] theorem cost_cons (e : Event S) : cost B (e :: tr) = e.cost B + cost B tr := by
  simp [cost_eq_sum]

@[simp] theorem localCost_cons (e : Event S) :
    localCost (e :: tr) = e.localCost + localCost tr := by
  simp [localCost_eq_sum]

/-- Additivity under sequential composition. -/
@[simp] theorem cost_append : cost B (tr₁ ++ tr₂) = cost B tr₁ + cost B tr₂ := by
  simp [cost_eq_sum]

@[simp] theorem localCost_append : localCost (tr₁ ++ tr₂) = localCost tr₁ + localCost tr₂ := by
  simp [localCost_eq_sum]

@[simp] theorem callCost_append : callCost B (tr₁ ++ tr₂) = callCost B tr₁ + callCost B tr₂ := by
  simp [callCost_eq_sum]

@[simp] theorem calls_append : calls (tr₁ ++ tr₂) = calls tr₁ ++ calls tr₂ := by
  induction tr₁ with
  | nil => rfl
  | cons e tr ih => cases e <;> simp [calls, ih]

/-- Monotonicity under increasing backend bounds. -/
theorem cost_mono {B B' : CostSchedule S} (h : B ≤ B') (tr : Trace S) : cost B tr ≤ cost B' tr := by
  induction tr with
  | nil => exact Nat.le_refl _
  | cons e tr ih =>
    rw [cost_cons, cost_cons]
    refine Nat.add_le_add ?_ ih
    cases e with
    | «local» k u => exact Nat.le_refl _
    | call op x y => exact h op x y

/-- A trace without backend events costs its local work under every schedule. -/
theorem cost_of_calls_eq_nil (h : calls tr = []) : cost B tr = localCost tr := by
  rw [cost_eq_localCost_add_sum_calls, h]
  simp

end Trace

end GraphIso.Cost
