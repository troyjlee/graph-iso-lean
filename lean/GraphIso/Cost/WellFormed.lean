module

public import GraphIso.Cost.BackendRefinement

/-!
# Well-formed programs

The type `Proc S a b = ∀ var, var a → Prog S (a, b) var b` does **not** by itself make a
procedure parametric in `var`: Lean can inspect `var` by classical case analysis on a type
equality such as `var .nat = ℕ`, and so compute on runtime values outside the charged
constructors (see `GraphIsoChecks/WellFormed.lean`). Likewise an implementation receives the
client's recursion type `rec` as data and can match on it.

Following Chlipala's PHOAS development, accepted programs therefore carry an explicit
relational well-formedness witness. `Prog.Wf r Γ p₁ p₂` relates the same program at two
variable instantiations: both sides have the same constructors, primitives and operations,
every variable occurrence is a pair of variables related by the context `Γ`, and binders
extend the context with an arbitrary pair of fresh variables. The flag `r` says whether
`recur` is allowed.

* `Proc.Wf P`: `P` instantiated at any two variable types is related, with recursion allowed.
* `Impl.Wf impl`: every implementation, for every client recursion type, is related with
  recursion **forbidden**; so an implementation cannot call back into the client.
* Well-formedness is preserved by substitution (`Prog.Wf.subst`, `Proc.Wf.subst`), and the
  bundled `WfProc.subst` packages it.

Because the relation must hold for *every* pair of instantiations and every choice of bound
values, a choice that a program makes by inspecting runtime values can only select between
alternatives with the same constructors, primitives and operations, and between variables
holding equal values (as in `if y = x then ret x else ret y`): any other dependence is
separated by instantiating the two sides with different values. So such a choice cannot change
results or charged costs. This is the formal invariant behind the claim that programs compute
only through charged constructors; the argument just given is informal, as is the standard
correspondence with first-order syntax. The `prog_wf` tactic proves the invariant for concrete
programs by following their syntax.
-/

@[expose] public section

namespace GraphIso.Cost

variable {S S' : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type}

/-- Contexts relating variables of two instantiations. -/
abbrev WfCtx (var₁ var₂ : Ty → Type) := List (Σ t : Ty, var₁ t × var₂ t)

/-- Related argument lists: every argument pair is in the context. -/
inductive Args.Wf (Γ : WfCtx var₁ var₂) : {ts : List Ty} → Args var₁ ts → Args var₂ ts → Prop where
  | nil : Args.Wf Γ .nil .nil
  | cons {t : Ty} {ts : List Ty} {x₁ : var₁ t} {x₂ : var₂ t} {xs₁ : Args var₁ ts}
      {xs₂ : Args var₂ ts} :
      ⟨t, x₁, x₂⟩ ∈ Γ → Args.Wf Γ xs₁ xs₂ → Args.Wf Γ (.cons x₁ xs₁) (.cons x₂ xs₂)

/-- Relational well-formedness of a program at two variable instantiations; `r` allows
`recur`. -/
inductive Prog.Wf (r : Bool) :
    WfCtx var₁ var₂ → {t : Ty} → Prog S rec var₁ t → Prog S rec var₂ t → Prop where
  | ret {Γ : WfCtx var₁ var₂} {t : Ty} {x₁ : var₁ t} {x₂ : var₂ t} :
      ⟨t, x₁, x₂⟩ ∈ Γ → Prog.Wf r Γ (.ret x₁) (.ret x₂)
  | bind {Γ : WfCtx var₁ var₂} {a t : Ty} {p₁ : Prog S rec var₁ a} {p₂ : Prog S rec var₂ a}
      {k₁ : var₁ a → Prog S rec var₁ t} {k₂ : var₂ a → Prog S rec var₂ t} :
      Prog.Wf r Γ p₁ p₂ → (∀ v₁ v₂, Prog.Wf r (⟨a, v₁, v₂⟩ :: Γ) (k₁ v₁) (k₂ v₂)) →
      Prog.Wf r Γ (.bind p₁ k₁) (.bind p₂ k₂)
  | prim {Γ : WfCtx var₁ var₂} {args : List Ty} {t : Ty} (p : Prim args t)
      {xs₁ : Args var₁ args} {xs₂ : Args var₂ args} :
      Args.Wf Γ xs₁ xs₂ → Prog.Wf r Γ (.prim p xs₁) (.prim p xs₂)
  | ite {Γ : WfCtx var₁ var₂} {t : Ty} {c₁ : var₁ .bool} {c₂ : var₂ .bool}
      {p₁ q₁ : Prog S rec var₁ t} {p₂ q₂ : Prog S rec var₂ t} :
      ⟨.bool, c₁, c₂⟩ ∈ Γ → Prog.Wf r Γ p₁ p₂ → Prog.Wf r Γ q₁ q₂ →
      Prog.Wf r Γ (.ite c₁ p₁ q₁) (.ite c₂ p₂ q₂)
  | caseOption {Γ : WfCtx var₁ var₂} {a t : Ty} {o₁ : var₁ (.option a)} {o₂ : var₂ (.option a)}
      {p₁ : Prog S rec var₁ t} {p₂ : Prog S rec var₂ t}
      {q₁ : var₁ a → Prog S rec var₁ t} {q₂ : var₂ a → Prog S rec var₂ t} :
      ⟨.option a, o₁, o₂⟩ ∈ Γ → Prog.Wf r Γ p₁ p₂ →
      (∀ v₁ v₂, Prog.Wf r (⟨a, v₁, v₂⟩ :: Γ) (q₁ v₁) (q₂ v₂)) →
      Prog.Wf r Γ (.caseOption o₁ p₁ q₁) (.caseOption o₂ p₂ q₂)
  | caseList {Γ : WfCtx var₁ var₂} {a t : Ty} {l₁ : var₁ (.list a)} {l₂ : var₂ (.list a)}
      {p₁ : Prog S rec var₁ t} {p₂ : Prog S rec var₂ t}
      {q₁ : var₁ a → var₁ (.list a) → Prog S rec var₁ t}
      {q₂ : var₂ a → var₂ (.list a) → Prog S rec var₂ t} :
      ⟨.list a, l₁, l₂⟩ ∈ Γ → Prog.Wf r Γ p₁ p₂ →
      (∀ x₁ x₂ xs₁ xs₂,
        Prog.Wf r (⟨a, x₁, x₂⟩ :: ⟨.list a, xs₁, xs₂⟩ :: Γ) (q₁ x₁ xs₁) (q₂ x₂ xs₂)) →
      Prog.Wf r Γ (.caseList l₁ p₁ q₁) (.caseList l₂ p₂ q₂)
  | foldList {Γ : WfCtx var₁ var₂} {a b : Ty} {xs₁ : var₁ (.list a)} {xs₂ : var₂ (.list a)}
      {i₁ : var₁ b} {i₂ : var₂ b} {f₁ : var₁ b → var₁ a → Prog S rec var₁ b}
      {f₂ : var₂ b → var₂ a → Prog S rec var₂ b} :
      ⟨.list a, xs₁, xs₂⟩ ∈ Γ → ⟨b, i₁, i₂⟩ ∈ Γ →
      (∀ acc₁ acc₂ x₁ x₂,
        Prog.Wf r (⟨b, acc₁, acc₂⟩ :: ⟨a, x₁, x₂⟩ :: Γ) (f₁ acc₁ x₁) (f₂ acc₂ x₂)) →
      Prog.Wf r Γ (.foldList xs₁ i₁ f₁) (.foldList xs₂ i₂ f₂)
  | loop {Γ : WfCtx var₁ var₂} {s : Ty} {x₁ : var₁ s} {x₂ : var₂ s}
      {f₁ : var₁ s → Prog S rec var₁ (.option s)} {f₂ : var₂ s → Prog S rec var₂ (.option s)} :
      ⟨s, x₁, x₂⟩ ∈ Γ → (∀ v₁ v₂, Prog.Wf r (⟨s, v₁, v₂⟩ :: Γ) (f₁ v₁) (f₂ v₂)) →
      Prog.Wf r Γ (.loop x₁ f₁) (.loop x₂ f₂)
  | recur {Γ : WfCtx var₁ var₂} {x₁ : var₁ rec.1} {x₂ : var₂ rec.1} :
      r = true → ⟨rec.1, x₁, x₂⟩ ∈ Γ → Prog.Wf r Γ (.recur x₁) (.recur x₂)
  | call {Γ : WfCtx var₁ var₂} (op : S.Op) {x₁ : var₁ (S.arg op)} {x₂ : var₂ (S.arg op)} :
      ⟨S.arg op, x₁, x₂⟩ ∈ Γ → Prog.Wf r Γ (.call op x₁) (.call op x₂)

namespace Args.Wf

theorem weaken {Γ Γ' : WfCtx var₁ var₂} {ts : List Ty} {xs₁ : Args var₁ ts} {xs₂ : Args var₂ ts}
    (h : Args.Wf Γ xs₁ xs₂) (hΓ : Γ ⊆ Γ') : Args.Wf Γ' xs₁ xs₂ := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (hΓ hx) ih

end Args.Wf

namespace Prog.Wf

/-- Weakening: well-formedness is preserved by enlarging the context. -/
theorem weaken {r : Bool} {Γ Γ' : WfCtx var₁ var₂} {t : Ty} {p₁ : Prog S rec var₁ t}
    {p₂ : Prog S rec var₂ t} (h : Prog.Wf r Γ p₁ p₂) (hΓ : Γ ⊆ Γ') : Prog.Wf r Γ' p₁ p₂ := by
  induction h generalizing Γ' with
  | ret hx => exact .ret (hΓ hx)
  | bind _ _ ih₁ ih₂ => exact .bind (ih₁ hΓ) fun v₁ v₂ => ih₂ v₁ v₂ (List.cons_subset_cons _ hΓ)
  | prim p hxs => exact .prim p (hxs.weaken hΓ)
  | ite hc _ _ ih₁ ih₂ => exact .ite (hΓ hc) (ih₁ hΓ) (ih₂ hΓ)
  | caseOption ho _ _ ih₁ ih₂ =>
    exact .caseOption (hΓ ho) (ih₁ hΓ) fun v₁ v₂ => ih₂ v₁ v₂ (List.cons_subset_cons _ hΓ)
  | caseList hl _ _ ih₁ ih₂ =>
    exact .caseList (hΓ hl) (ih₁ hΓ) fun x₁ x₂ xs₁ xs₂ =>
      ih₂ x₁ x₂ xs₁ xs₂ (List.cons_subset_cons _ (List.cons_subset_cons _ hΓ))
  | foldList hxs hi _ ih =>
    exact .foldList (hΓ hxs) (hΓ hi) fun acc₁ acc₂ x₁ x₂ =>
      ih acc₁ acc₂ x₁ x₂ (List.cons_subset_cons _ (List.cons_subset_cons _ hΓ))
  | loop hx _ ih => exact .loop (hΓ hx) fun v₁ v₂ => ih v₁ v₂ (List.cons_subset_cons _ hΓ)
  | recur hr hx => exact .recur hr (hΓ hx)
  | call op hx => exact .call op (hΓ hx)

/-- A program well-formed without recursion is well-formed with it. -/
theorem of_false {r : Bool} {Γ : WfCtx var₁ var₂} {t : Ty} {p₁ : Prog S rec var₁ t}
    {p₂ : Prog S rec var₂ t} (h : Prog.Wf false Γ p₁ p₂) : Prog.Wf r Γ p₁ p₂ := by
  induction h with
  | ret hx => exact .ret hx
  | bind _ _ ih₁ ih₂ => exact .bind ih₁ ih₂
  | prim p hxs => exact .prim p hxs
  | ite hc _ _ ih₁ ih₂ => exact .ite hc ih₁ ih₂
  | caseOption ho _ _ ih₁ ih₂ => exact .caseOption ho ih₁ ih₂
  | caseList hl _ _ ih₁ ih₂ => exact .caseList hl ih₁ ih₂
  | foldList hxs hi _ ih => exact .foldList hxs hi ih
  | loop hx _ ih => exact .loop hx ih
  | recur hr _ => exact absurd hr Bool.false_ne_true
  | call op hx => exact .call op hx

/-- Is the program a recursive call (at its head)? -/
def _root_.GraphIso.Cost.Prog.isRecur {var : Ty → Type} {t : Ty} : Prog S rec var t → Bool
  | .recur _ => true
  | _ => false

theorem isRecur_eq_false {Γ : WfCtx var₁ var₂} {t : Ty} {p₁ : Prog S rec var₁ t}
    {p₂ : Prog S rec var₂ t} (h : Prog.Wf false Γ p₁ p₂) : p₁.isRecur = false := by
  cases h with
  | recur hr _ => exact absurd hr Bool.false_ne_true
  | _ => rfl

/-- A program well-formed without recursion is not a recursive call. -/
theorem not_recur {Γ : WfCtx var₁ var₂} {x₁ : var₁ rec.1} {x₂ : var₂ rec.1} :
    ¬ Prog.Wf (S := S) false Γ (.recur x₁) (.recur x₂) := fun h => by
  have := isRecur_eq_false h
  simp [Prog.isRecur] at this

/-- Inversion for `ret`: the returned variables are related by the context. -/
theorem ret_inv {r : Bool} {Γ : WfCtx var₁ var₂} {t : Ty} {x₁ : var₁ t} {x₂ : var₂ t}
    (h : Prog.Wf (S := S) (rec := rec) r Γ (.ret x₁) (.ret x₂)) : ⟨t, x₁, x₂⟩ ∈ Γ := by
  generalize hp₁ : (Prog.ret x₁ : Prog S rec var₁ t) = p₁ at h
  generalize hp₂ : (Prog.ret x₂ : Prog S rec var₂ t) = p₂ at h
  cases h with
  | ret hx =>
    cases hp₁
    cases hp₂
    exact hx
  | _ => cases hp₁

end Prog.Wf

/-- A well-formed procedure: related at any two instantiations, with recursion allowed. -/
def Proc.Wf {a b : Ty} (P : Proc S a b) : Prop :=
  ∀ (var₁ var₂ : Ty → Type) (x₁ : var₁ a) (x₂ : var₂ a),
    Prog.Wf true [⟨a, x₁, x₂⟩] (P var₁ x₁) (P var₂ x₂)

/-- Well-formed implementations: for every client recursion type, related at any two
instantiations, with recursion forbidden. -/
def Impl.Wf (impl : Impl S S') : Prop :=
  ∀ (op : S.Op) (rec : Ty × Ty) (var₁ var₂ : Ty → Type) (x₁ : var₁ (S.arg op))
    (x₂ : var₂ (S.arg op)),
    Prog.Wf false [⟨S.arg op, x₁, x₂⟩] (impl op rec var₁ x₁) (impl op rec var₂ x₂)

/-- Substituting well-formed implementations preserves well-formedness. -/
theorem Prog.Wf.subst {impl : Impl S S'} (himpl : impl.Wf) {r : Bool} {Γ : WfCtx var₁ var₂}
    {t : Ty} {p₁ : Prog S rec var₁ t} {p₂ : Prog S rec var₂ t} (h : Prog.Wf r Γ p₁ p₂) :
    Prog.Wf r Γ (p₁.subst impl) (p₂.subst impl) := by
  induction h with
  | ret hx => exact .ret hx
  | bind _ _ ih₁ ih₂ => exact .bind ih₁ ih₂
  | prim p hxs => exact .prim p hxs
  | ite hc _ _ ih₁ ih₂ => exact .ite hc ih₁ ih₂
  | caseOption ho _ _ ih₁ ih₂ => exact .caseOption ho ih₁ ih₂
  | caseList hl _ _ ih₁ ih₂ => exact .caseList hl ih₁ ih₂
  | foldList hxs hi _ ih => exact .foldList hxs hi ih
  | loop hx _ ih => exact .loop hx ih
  | recur hr hx => exact .recur hr hx
  | call op hx =>
    refine ((himpl op rec var₁ var₂ _ _).weaken fun y hy => ?_).of_false
    rw [List.mem_singleton.1 hy]
    exact hx

theorem Proc.Wf.subst {a b : Ty} {P : Proc S a b} {impl : Impl S S'} (hP : P.Wf)
    (himpl : impl.Wf) : (P.subst impl).Wf :=
  fun var₁ var₂ x₁ x₂ => (hP var₁ var₂ x₁ x₂).subst himpl

/-- A procedure together with its well-formedness witness. -/
structure WfProc (S : Signature) (a b : Ty) where
  /-- The procedure. -/
  proc : Proc S a b
  /-- Its well-formedness. -/
  wf : proc.Wf

/-- Implementations together with their well-formedness witness. -/
structure WfImpl (S S' : Signature) where
  /-- The implementations. -/
  impl : Impl S S'
  /-- Their well-formedness (in particular, no recursive calls). -/
  wf : impl.Wf

/-- Substitution of well-formed implementations into a well-formed procedure. -/
def WfProc.subst {a b : Ty} (P : WfProc S a b) (I : WfImpl S S') : WfProc S' a b :=
  ⟨P.proc.subst I.impl, P.wf.subst I.wf⟩

/-- Backend substitution for well-formed procedures and implementations. -/
theorem WfProc.runs_subst {a b : Ty} {O : Oracle S} {B : CostSchedule S}
    {Pre : (op : S.Op) → (S.arg op).denote → Prop} {I : WfImpl S S'} {O' : Oracle S'}
    {B' : CostSchedule S'} (himpl : Implements O B Pre I.impl O' B') (P : WfProc S a b)
    {x : a.denote} {v : b.denote} {tr : Trace S}
    (h : Runs O (P.proc Ty.denote) (P.proc Ty.denote x) v tr)
    (hpre : Trace.CallsSatisfy Pre tr) :
    ∃ tr', Runs O' ((P.subst I).proc Ty.denote) ((P.subst I).proc Ty.denote x) v tr' ∧
      Trace.cost B' tr' ≤ Trace.cost B tr :=
  Proc.runs_subst himpl P.proc h hpre

/-- Prove a well-formedness goal by following the syntax of a concrete program: apply the
constructor matching the program, introduce fresh variable pairs at binders, and discharge
context membership. -/
macro "prog_wf" : tactic =>
  `(tactic| repeat' (first | assumption | (intro _ _) | constructor!))

end GraphIso.Cost
