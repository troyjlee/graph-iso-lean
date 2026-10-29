module

public import GraphIso.Cost.Spec

/-!
# Local programs

`Prog.Local p`: the program `p` contains no backend call and no recursive call; every other
constructor is allowed, with local continuations. A local program's runs perform no backend
operation: every trace an evaluation returns has no backend event (`Prog.Local.eval_calls`,
`Prog.Local.runs_calls`), whatever the oracle and the enclosing procedure.

Threshold programs (`Main.ThrSpec`, stage 14j-5d) are required to be local.
-/

@[expose] public section

namespace GraphIso.Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **Local programs**: no `.call` and no `.recur`, hereditarily through every continuation. -/
inductive Prog.Local : {t : Ty} → Prog S rec var t → Prop where
  | ret {t : Ty} (x : var t) : Prog.Local (.ret x)
  | bind {a t : Ty} {p : Prog S rec var a} {k : var a → Prog S rec var t} :
      Prog.Local p → (∀ v, Prog.Local (k v)) → Prog.Local (.bind p k)
  | prim {args : List Ty} {t : Ty} (p : Prim args t) (xs : Args var args) :
      Prog.Local (.prim p xs)
  | ite {t : Ty} (c : var .bool) {p q : Prog S rec var t} :
      Prog.Local p → Prog.Local q → Prog.Local (.ite c p q)
  | caseOption {a t : Ty} (o : var (.option a)) {p : Prog S rec var t}
      {q : var a → Prog S rec var t} :
      Prog.Local p → (∀ v, Prog.Local (q v)) → Prog.Local (.caseOption o p q)
  | caseList {a t : Ty} (l : var (.list a)) {p : Prog S rec var t}
      {q : var a → var (.list a) → Prog S rec var t} :
      Prog.Local p → (∀ x xs, Prog.Local (q x xs)) → Prog.Local (.caseList l p q)
  | foldList {a b : Ty} (xs : var (.list a)) (init : var b) {f : var b → var a → Prog S rec var b} :
      (∀ acc x, Prog.Local (f acc x)) → Prog.Local (.foldList xs init f)
  | loop {s : Ty} (x : var s) {f : var s → Prog S rec var (.option s)} :
      (∀ y, Prog.Local (f y)) → Prog.Local (.loop x f)

/-- A backend call is not local. -/
theorem Prog.not_local_call (op : S.Op) (x : var (S.arg op)) :
    ¬ (Prog.call (rec := rec) op x).Local := nofun

/-- A recursive call is not local. -/
theorem Prog.not_local_recur (x : var rec.1) : ¬ (Prog.recur (S := S) x).Local := nofun

section Eval

variable {a b : Ty} {O : Oracle S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem foldRun_calls {α β : Type} {step : β → α → Option (β × Trace S)}
    (h : ∀ acc x r t, step acc x = some (r, t) → Trace.calls t = []) :
    ∀ (xs : List α) (acc : β) {r : β} {tr : Trace S}, foldRun step xs acc = some (r, tr) →
      Trace.calls tr = []
  | [], _, _, _, he => by
    simp only [foldRun, Option.some.injEq, Prod.mk.injEq] at he
    rw [← he.2]
    rfl
  | x :: xs, acc, _, _, he => by
    obtain ⟨t, ht, rfl⟩ := consT_eq_some.1 he
    obtain ⟨v, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 ht
    change Trace.calls (t₁ ++ t₂) = []
    rw [Trace.calls_append, h acc x _ _ h₁, foldRun_calls h xs v h₂]
    rfl

/-- **A local program performs no backend operation**: every trace of its evaluation has no
backend event. -/
theorem Prog.Local.eval_calls :
    ∀ (fuel : ℕ) {t : Ty} {p : Prog S (a, b) Ty.denote t}, p.Local →
      ∀ {v : t.denote} {tr : Trace S}, eval O body fuel p = some (v, tr) → Trace.calls tr = []
  | 0, _, _, _, _, _, he => by simp [eval] at he
  | fuel + 1, _, _, hp, _, _, he => by
    cases hp with
    | ret x =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]
      rfl
    | bind hp hk =>
      obtain ⟨v, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 he
      rw [Trace.calls_append, eval_calls fuel hp h₁, eval_calls fuel (hk v) h₂]
      rfl
    | prim p xs =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at he
      rw [← he.2]
      rfl
    | ite c hp hq =>
      obtain ⟨t, ht, rfl⟩ := consT_eq_some.1 he
      change Trace.calls t = []
      cases hc : c
      · rw [hc] at ht; exact eval_calls fuel hq ht
      · rw [hc] at ht; exact eval_calls fuel hp ht
    | caseOption o hp hq =>
      obtain ⟨t, ht, rfl⟩ := consT_eq_some.1 he
      change Trace.calls t = []
      cases o with
      | none => exact eval_calls fuel hp ht
      | some v => exact eval_calls fuel (hq v) ht
    | caseList l hp hq =>
      obtain ⟨t, ht, rfl⟩ := consT_eq_some.1 he
      change Trace.calls t = []
      cases l with
      | nil => exact eval_calls fuel hp ht
      | cons x xs => exact eval_calls fuel (hq x xs) ht
    | foldList xs init hf =>
      exact foldRun_calls (fun acc x _ _ h => eval_calls fuel (hf acc x) h) xs init he
    | loop x hf =>
      obtain ⟨t, ht, rfl⟩ := consT_eq_some.1 he
      change Trace.calls t = []
      obtain ⟨o, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 ht
      rw [Trace.calls_append, eval_calls fuel (hf x) h₁]
      cases o with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h₂
        rw [← h₂.2]
        rfl
      | some y => exact eval_calls fuel (.loop y hf) h₂

/-- **A local program's runs** have no backend event. -/
theorem Prog.Local.runs_calls {t : Ty} {p : Prog S (a, b) Ty.denote t} (hp : p.Local)
    {v : t.denote} {tr : Trace S} (h : Runs O body p v tr) : Trace.calls tr = [] :=
  let ⟨fuel, he⟩ := h
  hp.eval_calls fuel he

end Eval

end GraphIso.Cost
