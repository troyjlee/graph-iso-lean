module

public import GraphIso.Cost.Evaluation

/-!
# Backend substitution

An implementation of a backend signature `S` by programs over another signature `S'` gives,
for each operation, a program for every client recursion type and every variable type
(`Impl S S'`). The recursion type is ordinary data that an implementation can inspect, so the
type does not prevent calls into the client: `Impl.Wf` (in `GraphIso.Cost.WellFormed`)
forbids `recur` explicitly. The substitution theorem below does not need that restriction:
`Implements` already requires the cost bound for every client body.

`Prog.subst impl p` replaces every backend call of `p` by its implementation. The main theorem,
`runs_subst`, says: if `p` runs against the oracle `O` with trace `tr`, every backend event of
`tr` satisfies the precondition `Pre`, and each implementation returns the oracle's answer on
such inputs within the schedule `B` (`Implements`), then the substituted program returns the
same value with a trace `tr'` satisfying

  `Trace.cost B' tr' ≤ Trace.cost B tr = localCost tr + Σ_{e ∈ calls tr} B e`.

Each backend call is charged through its implementation in `tr'` and through its contracted
bound in `tr`, never both: the substituted program has no calls of `S` at all.
-/

@[expose] public section

namespace GraphIso.Cost

variable {S S' : Signature}

/-- Implementations of the operations of `S` by programs over `S'`, for every client
recursion type and every variable type. Accepted implementations also satisfy `Impl.Wf`,
which forbids recursive calls. -/
abbrev Impl (S S' : Signature) : Type 1 :=
  (op : S.Op) → (rec : Ty × Ty) → (var : Ty → Type) → var (S.arg op) → Prog S' rec var (S.res op)

namespace Prog

/-- Replace every backend call by its implementation. -/
def subst (impl : Impl S S') {rec : Ty × Ty} {var : Ty → Type} :
    {t : Ty} → Prog S rec var t → Prog S' rec var t
  | _, .ret x => .ret x
  | _, .bind p k => .bind (p.subst impl) fun v => (k v).subst impl
  | _, .prim p xs => .prim p xs
  | _, .ite c p q => .ite c (p.subst impl) (q.subst impl)
  | _, .caseOption o p q => .caseOption o (p.subst impl) fun v => (q v).subst impl
  | _, .caseList l p q => .caseList l (p.subst impl) fun x xs => (q x xs).subst impl
  | _, .foldList xs init f => .foldList xs init fun acc x => (f acc x).subst impl
  | _, .loop s f => .loop s fun v => (f v).subst impl
  | _, .recur x => .recur x
  | _, .call op x => impl op rec var x

theorem subst_cond (impl : Impl S S') {rec : Ty × Ty} {var : Ty → Type} {t : Ty} (c : Bool)
    (p q : Prog S rec var t) : (cond c p q).subst impl = cond c (p.subst impl) (q.subst impl) := by
  cases c <;> rfl

end Prog

/-- Substitute the implementations into a closed procedure. -/
def Proc.subst {a b : Ty} (impl : Impl S S') (P : Proc S a b) : Proc S' a b :=
  fun var x => (P var x).subst impl

/-- Every backend event of a trace satisfies `Pre`. -/
def Trace.CallsSatisfy (Pre : (op : S.Op) → (S.arg op).denote → Prop) (tr : Trace S) : Prop :=
  ∀ e ∈ Trace.calls tr, Pre e.1 e.2.1

theorem Trace.CallsSatisfy.append {Pre : (op : S.Op) → (S.arg op).denote → Prop}
    {tr₁ tr₂ : Trace S} :
    Trace.CallsSatisfy Pre (tr₁ ++ tr₂) ↔
      Trace.CallsSatisfy Pre tr₁ ∧ Trace.CallsSatisfy Pre tr₂ := by
  simp only [Trace.CallsSatisfy, Trace.calls_append, List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem Trace.CallsSatisfy.cons_local {Pre : (op : S.Op) → (S.arg op).denote → Prop}
    {k : LocalKind} {u : ℕ} {tr : Trace S} :
    Trace.CallsSatisfy Pre (Event.local k u :: tr) ↔ Trace.CallsSatisfy Pre tr := by
  simp [Trace.CallsSatisfy, Trace.calls]

/-- On inputs satisfying `Pre`, the implementation of every operation returns the oracle's
answer, inside any enclosing procedure, at cost at most the schedule `B`. -/
def Implements (O : Oracle S) (B : CostSchedule S) (Pre : (op : S.Op) → (S.arg op).denote → Prop)
    (impl : Impl S S') (O' : Oracle S') (B' : CostSchedule S') : Prop :=
  ∀ op x, Pre op x → ∀ (a b : Ty) (body : a.denote → Prog S' (a, b) Ty.denote b),
    ∃ tr, Runs O' body (impl op (a, b) Ty.denote x) (O.run op x) tr ∧
      Trace.cost B' tr ≤ B.call op x (O.run op x)

section Subst

variable {a b : Ty} {O : Oracle S} {B : CostSchedule S}
  {Pre : (op : S.Op) → (S.arg op).denote → Prop} {impl : Impl S S'} {O' : Oracle S'}
  {B' : CostSchedule S'} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The fold case of `runs_subst`, given the result for the body. -/
private theorem foldRun_subst {a' b' : Ty} {fuel : ℕ}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    (ih : ∀ (acc : b'.denote) (x : a'.denote) (v : b'.denote) (tr : Trace S),
      eval O body fuel (f acc x) = some (v, tr) → Trace.CallsSatisfy Pre tr →
      ∃ tr', Runs O' (fun y => (body y).subst impl) ((f acc x).subst impl) v tr' ∧
        Trace.cost B' tr' ≤ Trace.cost B tr) :
    ∀ (xs : List a'.denote) (acc r : b'.denote) (tr : Trace S),
      foldRun (fun acc x => eval O body fuel (f acc x)) xs acc = some (r, tr) →
      Trace.CallsSatisfy Pre tr →
      ∃ tr', FoldRuns O' (fun y => (body y).subst impl) (fun acc x => (f acc x).subst impl)
        xs acc r tr' ∧ Trace.cost B' tr' ≤ Trace.cost B tr
  | [], acc, r, tr, h, _ => by
    simp only [foldRun, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], .nil _, Nat.le_refl _⟩
  | x :: xs, acc, r, tr, h, hpre => by
    obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
    obtain ⟨acc', t₁, t₂, h₂, h₃, rfl⟩ := seqT_eq_some.1 h₁
    rw [Trace.CallsSatisfy.cons_local, Trace.CallsSatisfy.append] at hpre
    obtain ⟨t₁', r₁, c₁⟩ := ih acc x acc' t₁ h₂ hpre.1
    obtain ⟨t₂', r₂, c₂⟩ := foldRun_subst ih xs acc' r t₂ h₃ hpre.2
    refine ⟨_, .cons r₁ r₂, ?_⟩
    simp only [Event.cost_local, Trace.cost_cons, Trace.cost_append]
    omega

/-- **Backend substitution.** Replacing each backend call by an implementation that meets the
contract preserves the result, and the cost of the substituted run is at most the cost of the
original run under the contracted schedule. -/
theorem runs_subst (himpl : Implements O B Pre impl O' B') :
    ∀ (fuel : ℕ) {t : Ty} (p : Prog S (a, b) Ty.denote t) (v : t.denote) (tr : Trace S),
      eval O body fuel p = some (v, tr) → Trace.CallsSatisfy Pre tr →
      ∃ tr', Runs O' (fun y => (body y).subst impl) (p.subst impl) v tr' ∧
        Trace.cost B' tr' ≤ Trace.cost B tr
  | 0, _, _, _, _, h, _ => by simp [eval] at h
  | fuel + 1, _, p, v, tr, h, hpre => by
    have ih : ∀ {t : Ty} (p : Prog S (a, b) Ty.denote t) (v : t.denote) (tr : Trace S),
        eval O body fuel p = some (v, tr) → Trace.CallsSatisfy Pre tr →
        ∃ tr', Runs O' (fun y => (body y).subst impl) (p.subst impl) v tr' ∧
          Trace.cost B' tr' ≤ Trace.cost B tr := fun p => runs_subst himpl fuel p
    cases p with
    | ret x =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], runs_ret.2 ⟨rfl, rfl⟩, Nat.le_refl _⟩
    | bind p k =>
      obtain ⟨w, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 h
      rw [Trace.CallsSatisfy.append] at hpre
      obtain ⟨t₁', r₁, c₁⟩ := ih p w t₁ h₁ hpre.1
      obtain ⟨t₂', r₂, c₂⟩ := ih (k w) v t₂ h₂ hpre.2
      refine ⟨t₁' ++ t₂', runs_bind.2 ⟨w, t₁', t₂', r₁, r₂, rfl⟩, ?_⟩
      simp only [Trace.cost_append]
      omega
    | prim q xs =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, runs_prim.2 ⟨rfl, rfl⟩, by simp [Trace.cost, Event.cost]⟩
    | ite c p q =>
      obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
      rw [Trace.CallsSatisfy.cons_local] at hpre
      obtain ⟨t', r₁, c₁⟩ := ih _ v t h₁ hpre
      refine ⟨_, runs_ite.2 ⟨t', ?_, rfl⟩, ?_⟩
      · rwa [← Prog.subst_cond]
      · simp only [Event.cost_local, Trace.cost_cons]
        omega
    | caseOption o p q =>
      obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
      rw [Trace.CallsSatisfy.cons_local] at hpre
      cases o with
      | none =>
        obtain ⟨t', r₁, c₁⟩ := ih p v t h₁ hpre
        exact ⟨_, runs_caseOption_none.2 ⟨t', r₁, rfl⟩,
          by simp only [Event.cost_local, Trace.cost_cons]; omega⟩
      | some w =>
        obtain ⟨t', r₁, c₁⟩ := ih (q w) v t h₁ hpre
        exact ⟨_, runs_caseOption_some.2 ⟨t', r₁, rfl⟩,
          by simp only [Event.cost_local, Trace.cost_cons]; omega⟩
    | caseList l p q =>
      obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
      rw [Trace.CallsSatisfy.cons_local] at hpre
      cases l with
      | nil =>
        obtain ⟨t', r₁, c₁⟩ := ih p v t h₁ hpre
        exact ⟨_, runs_caseList_nil.2 ⟨t', r₁, rfl⟩,
          by simp only [Event.cost_local, Trace.cost_cons]; omega⟩
      | cons x xs =>
        obtain ⟨t', r₁, c₁⟩ := ih (q x xs) v t h₁ hpre
        exact ⟨_, runs_caseList_cons.2 ⟨t', r₁, rfl⟩,
          by simp only [Event.cost_local, Trace.cost_cons]; omega⟩
    | foldList xs init f =>
      obtain ⟨tr', r₁, c₁⟩ := foldRun_subst (fun acc x => ih (f acc x)) xs init v tr h hpre
      exact ⟨tr', runs_foldList.2 r₁, c₁⟩
    | loop s f =>
      obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
      obtain ⟨o, t₁, t₂, h₂, h₃, rfl⟩ := seqT_eq_some.1 h₁
      rw [Trace.CallsSatisfy.cons_local, Trace.CallsSatisfy.append] at hpre
      obtain ⟨t₁', r₁, c₁⟩ := ih (f s) o t₁ h₂ hpre.1
      cases o with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h₃
        obtain ⟨rfl, rfl⟩ := h₃
        refine ⟨_, runs_loop.2 (Or.inl ⟨t₁', r₁, rfl, rfl⟩), ?_⟩
        simp only [Event.cost_local, Trace.cost_cons, Trace.cost_append, Trace.cost_nil]
        omega
      | some s' =>
        obtain ⟨t₂', r₂, c₂⟩ := ih (.loop s' f) v t₂ h₃ hpre.2
        refine ⟨_, runs_loop.2 (Or.inr ⟨s', t₁', t₂', r₁, r₂, rfl⟩), ?_⟩
        simp only [Event.cost_local, Trace.cost_cons, Trace.cost_append]
        omega
    | recur x =>
      obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 h
      rw [Trace.CallsSatisfy.cons_local] at hpre
      obtain ⟨t', r₁, c₁⟩ := ih (body x) v t h₁ hpre
      exact ⟨_, runs_recur.2 ⟨t', r₁, rfl⟩, by simp only [Event.cost_local, Trace.cost_cons]; omega⟩
    | call op x =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hx : Pre op x := hpre ⟨op, x, O.run op x⟩ (by simp [Trace.calls])
      obtain ⟨tr', r₁, c₁⟩ := himpl op x hx a b (fun y => (body y).subst impl)
      exact ⟨tr', r₁, by simpa [Trace.cost, Event.cost] using c₁⟩

/-- `runs_subst` for runs. -/
theorem Runs.subst (himpl : Implements O B Pre impl O' B') {t : Ty}
    {p : Prog S (a, b) Ty.denote t} {v : t.denote} {tr : Trace S} (h : Runs O body p v tr)
    (hpre : Trace.CallsSatisfy Pre tr) :
    ∃ tr', Runs O' (fun y => (body y).subst impl) (p.subst impl) v tr' ∧
      Trace.cost B' tr' ≤ Trace.cost B tr :=
  let ⟨fuel, hf⟩ := h
  runs_subst himpl fuel p v tr hf hpre

end Subst

/-- **Backend substitution for closed procedures.** -/
theorem Proc.runs_subst {a b : Ty} {O : Oracle S} {B : CostSchedule S}
    {Pre : (op : S.Op) → (S.arg op).denote → Prop} {impl : Impl S S'} {O' : Oracle S'}
    {B' : CostSchedule S'} (himpl : Implements O B Pre impl O' B') (P : Proc S a b)
    {x : a.denote} {v : b.denote} {tr : Trace S} (h : Runs O (P Ty.denote) (P Ty.denote x) v tr)
    (hpre : Trace.CallsSatisfy Pre tr) :
    ∃ tr', Runs O' ((P.subst impl) Ty.denote) ((P.subst impl) Ty.denote x) v tr' ∧
      Trace.cost B' tr' ≤ Trace.cost B tr :=
  h.subst himpl hpre

/-- A trace over the empty signature has no backend events, so its cost is its local work. -/
theorem Trace.cost_empty (B : CostSchedule Signature.empty) (tr : Trace Signature.empty) :
    Trace.cost B tr = Trace.localCost tr := by
  apply Trace.cost_of_calls_eq_nil
  induction tr with
  | nil => rfl
  | cons e tr ih =>
    cases e with
    | «local» k u => simpa [Trace.calls] using ih
    | call op x y => exact op.elim

end GraphIso.Cost
