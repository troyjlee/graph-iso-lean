module

public import GraphIso.Cost.Spec
public import GraphIso.Cost.WellFormed
public import GraphIso.Representation.Permutation

/-!
# Generic list and array programs

Programs of the cost language for mapping over lists and arrays and for conjunctions over
lists, with their exact results and cost bounds. The per-element work is an arbitrary
program, so these combinators also carry backend calls made by the element program.

* `mapList xs f`: `xs.map F` at cost `1 + Σ (c x + 2) + (|xs| + 1)`.
* `mapArray arr f`: `amap F arr` (that is, `arr.map F`) at cost
  `(|arr| + 1) + mapList + (|arr| + 1)`.
* `allList xs p`: `xs.all P` at cost `1 + Σ (c x + 2)`.

Each combinator is well-formed whenever its element program is, for every extension of the
context (`wf_mapList`, `wf_mapArray`, `wf_allList`).
-/

@[expose] public section

namespace GraphIso.Programs

open Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Map a program over a list: fold, consing results onto an accumulator, then reverse. -/
def mapList {a' b' : Ty} (xs : var (.list a')) (f : var a' → Prog S rec var b') :
    Prog S rec var (.list b') :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList xs nil fun acc x => .bind (f x) fun y => .op2 .cons y acc) fun racc =>
  .op1 .reverse racc

/-- Map a program over an array, through lists. -/
def mapArray {a' b' : Ty} (arr : var (.array a')) (f : var a' → Prog S rec var b') :
    Prog S rec var (.array b') :=
  .bind (.op1 .arrayToList arr) fun l =>
  .bind (mapList l f) fun l' =>
  .op1 .arrayOfList l'

/-- The disjunction of a Boolean program over a list. -/
def anyList {a' : Ty} (xs : var (.list a')) (p : var a' → Prog S rec var .bool) :
    Prog S rec var .bool :=
  .bind (.op0 (.boolLit false)) fun f =>
  .foldList xs f fun acc x => .bind (p x) fun c => .op2 .or acc c

/-- The conjunction of a Boolean program over a list. -/
def allList {a' : Ty} (xs : var (.list a')) (p : var a' → Prog S rec var .bool) :
    Prog S rec var .bool :=
  .bind (.op0 (.boolLit true)) fun t =>
  .foldList xs t fun acc x => .bind (p x) fun c => .op2 .and acc c

section Specs

variable {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

private theorem fold_cons_spec {a' b' : Ty} {f : a'.denote → Prog S (a, b) Ty.denote b'}
    {F : a'.denote → b'.denote} {cf : a'.denote → ℕ} :
    ∀ (xs : List a'.denote) (acc : List b'.denote),
      (∀ x ∈ xs, RunsWithin X body (f x) (F x) (cf x)) →
      RunsWithin X body
        (.foldList xs acc fun acc x => .bind (f x) fun y => .op2 .cons y acc)
        ((xs.map F).reverse ++ acc) ((xs.map fun x => cf x + 2).sum)
  | [], acc, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, acc, hf => by
    have h₁ : RunsWithin X body (.bind (f x) fun y => .op2 .cons y acc) (F x :: acc)
        (cf x + 1) :=
      (hf x List.mem_cons_self).bind (RunsWithin.prim (S := S) .cons _)
    have h₂ := fold_cons_spec xs (F x :: acc) fun y hy => hf y (List.mem_cons_of_mem _ hy)
    have h := RunsWithin.foldList_cons h₁ h₂
    have e₁ : ((x :: xs).map F).reverse ++ acc = (xs.map F).reverse ++ (F x :: acc) := by simp
    have e₂ : ((x :: xs).map fun x => cf x + 2).sum =
        1 + (cf x + 1) + (xs.map fun x => cf x + 2).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    rw [e₁, e₂]
    exact h

theorem RunsWithin.mapList {a' b' : Ty} {xs : List a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote b'} {F : a'.denote → b'.denote}
    {cf : a'.denote → ℕ} (hf : ∀ x ∈ xs, RunsWithin X body (f x) (F x) (cf x)) :
    RunsWithin X body (Programs.mapList xs f) (xs.map F)
      (1 + (xs.map fun x => cf x + 2).sum + (xs.length + 1)) := by
  refine RunsWithin.bind_le (c₂ := (xs.map fun x => cf x + 2).sum + (xs.length + 1))
    (RunsWithin.prim _ _) ?_ (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := xs.length + 1) (fold_cons_spec xs [] hf) ?_ (Nat.le_refl _)
  exact RunsWithin.prim_le (by simp [Prim.eval]) (by simp [Prim.cost])

/-- `mapList` with a uniform per-element cost bound. -/
theorem RunsWithin.mapList_le {a' b' : Ty} {xs : List a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote b'} {F : a'.denote → b'.denote} {c : ℕ}
    (hf : ∀ x ∈ xs, RunsWithin X body (f x) (F x) c) :
    RunsWithin X body (Programs.mapList xs f) (xs.map F) (xs.length * (c + 3) + 2) := by
  refine (RunsWithin.mapList (cf := fun _ => c) hf).mono ?_
  rw [sum_map_const]
  simp only [Nat.mul_add]
  omega

theorem RunsWithin.mapArray {a' b' : Ty} {arr : Array a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote b'} {F : a'.denote → b'.denote} {c : ℕ}
    (hf : ∀ x ∈ arr.toList, RunsWithin X body (f x) (F x) c) :
    RunsWithin X body (Programs.mapArray arr f) (amap F arr) (arr.size * (c + 5) + 4) := by
  refine RunsWithin.bind_le (c₂ := arr.size * (c + 4) + 3) (RunsWithin.prim _ _) ?_ ?_
  · refine RunsWithin.bind_le (c₂ := arr.size + 1) (RunsWithin.mapList_le hf) ?_ ?_
    · exact RunsWithin.prim_le rfl (by simp [Prim.cost, Prim.eval])
    · simp only [Prim.eval, Array.length_toList, Nat.mul_add]
      omega
  · simp only [Prim.cost, Args.head_cons, Nat.mul_add]
    omega

private theorem fold_and_spec {a' : Ty} {p : a'.denote → Prog S (a, b) Ty.denote .bool}
    {P : a'.denote → Bool} {cp : a'.denote → ℕ} :
    ∀ (xs : List a'.denote) (acc : Bool),
      (∀ x ∈ xs, RunsWithin X body (p x) (P x) (cp x)) →
      RunsWithin X body (.foldList xs acc fun acc x => .bind (p x) fun c => .op2 .and acc c)
        (acc && xs.all P) ((xs.map fun x => cp x + 2).sum)
  | [], acc, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, acc, hp => by
    have h₁ : RunsWithin X body (.bind (p x) fun c => .op2 .and acc c) (acc && P x)
        (cp x + 1) :=
      (hp x List.mem_cons_self).bind (RunsWithin.prim (S := S) .and _)
    have h₂ := fold_and_spec xs (acc && P x) fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have h := RunsWithin.foldList_cons h₁ h₂
    have e₁ : (acc && (x :: xs).all P) = ((acc && P x) && xs.all P) := by
      simp [List.all_cons, Bool.and_assoc]
    have e₂ : ((x :: xs).map fun x => cp x + 2).sum =
        1 + (cp x + 1) + (xs.map fun x => cp x + 2).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    rw [e₁, e₂]
    exact h

theorem RunsWithin.allList {a' : Ty} {xs : List a'.denote}
    {p : a'.denote → Prog S (a, b) Ty.denote .bool} {P : a'.denote → Bool} {cp : a'.denote → ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) (cp x)) :
    RunsWithin X body (Programs.allList xs p) (xs.all P)
      (1 + (xs.map fun x => cp x + 2).sum) := by
  refine RunsWithin.bind_le (c₂ := (xs.map fun x => cp x + 2).sum) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost])
  exact (fold_and_spec xs true hp).of_eq (by simp)

theorem RunsWithin.allList_le {a' : Ty} {xs : List a'.denote}
    {p : a'.denote → Prog S (a, b) Ty.denote .bool} {P : a'.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (Programs.allList xs p) (xs.all P) (xs.length * (c + 2) + 1) := by
  refine (RunsWithin.allList (cp := fun _ => c) hp).mono ?_
  rw [sum_map_const]
  simp only [Nat.mul_add]
  omega

private theorem fold_or_spec {a' : Ty} {p : a'.denote → Prog S (a, b) Ty.denote .bool}
    {P : a'.denote → Bool} {c : ℕ} :
    ∀ (xs : List a'.denote) (acc : Bool),
      (∀ x ∈ xs, RunsWithin X body (p x) (P x) c) →
      RunsWithin X body (.foldList xs acc fun acc x => .bind (p x) fun c => .op2 .or acc c)
        (acc || xs.any P) (xs.length * (c + 2))
  | [], acc, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, acc, hp => by
    have h₁ : RunsWithin X body (.bind (p x) fun c => .op2 .or acc c) (acc || P x) (c + 1) :=
      (hp x List.mem_cons_self).bind (RunsWithin.prim (S := S) .or _)
    have h₂ := fold_or_spec xs (acc || P x) fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have h := RunsWithin.foldList_cons h₁ h₂
    have e₁ : (acc || (x :: xs).any P) = ((acc || P x) || xs.any P) := by
      simp [List.any_cons, Bool.or_assoc]
    have e₂ : (x :: xs).length * (c + 2) = 1 + (c + 1) + xs.length * (c + 2) := by
      simp only [List.length_cons, Nat.succ_mul]
      omega
    rw [e₁, e₂]
    exact h

theorem RunsWithin.anyList_le {a' : Ty} {xs : List a'.denote}
    {p : a'.denote → Prog S (a, b) Ty.denote .bool} {P : a'.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (Programs.anyList xs p) (xs.any P) (xs.length * (c + 2) + 1) := by
  refine RunsWithin.bind_le (c₂ := xs.length * (c + 2)) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  exact (fold_or_spec xs false hp).of_eq (by simp)

/-- A fold whose body keeps an invariant `I` and, under it, has a functional model `F` and a
uniform cost bound `c`. -/
theorem RunsWithin.foldList_inv {a' b' : Ty}
    {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    {F : b'.denote → a'.denote → b'.denote} {I : b'.denote → Prop} {c : ℕ} :
    ∀ (xs : List a'.denote) (init : b'.denote),
      (∀ acc, I acc → ∀ x ∈ xs, RunsWithin X body (f acc x) (F acc x) c ∧ I (F acc x)) →
      I init →
      RunsWithin X body (.foldList xs init f) (xs.foldl F init) (xs.length * (c + 1)) ∧
        I (xs.foldl F init)
  | [], init, _, hI => ⟨by simpa using RunsWithin.foldList_nil, hI⟩
  | x :: xs, init, hf, hI => by
    obtain ⟨h₁, hI₁⟩ := hf init hI x List.mem_cons_self
    obtain ⟨h₂, hI₂⟩ := RunsWithin.foldList_inv xs (F init x)
      (fun acc hacc y hy => hf acc hacc y (List.mem_cons_of_mem _ hy)) hI₁
    refine ⟨(RunsWithin.foldList_cons h₁ h₂).mono ?_, hI₂⟩
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- A fold whose body has a functional model `F` and per-element cost `cf`. -/
theorem RunsWithin.foldList_of {a' b' : Ty} {f : b'.denote → a'.denote → Prog S (a, b) Ty.denote b'}
    {F : b'.denote → a'.denote → b'.denote} {cf : a'.denote → ℕ} :
    ∀ (xs : List a'.denote) (init : b'.denote),
      (∀ acc, ∀ x ∈ xs, RunsWithin X body (f acc x) (F acc x) (cf x)) →
      RunsWithin X body (.foldList xs init f) (xs.foldl F init) ((xs.map fun x => cf x + 1).sum)
  | [], init, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, init, hf => by
    have h := RunsWithin.foldList_cons (hf init x List.mem_cons_self)
      (RunsWithin.foldList_of xs (F init x) fun acc y hy => hf acc y (List.mem_cons_of_mem _ hy))
    refine h.mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem fold_cons_exists {a' b' : Ty} {f : a'.denote → Prog S (a, b) Ty.denote b'}
    {Q : a'.denote → b'.denote → Prop} {c : ℕ} :
    ∀ (xs : List a'.denote) (acc : List b'.denote),
      (∀ x ∈ xs, ∃ v, RunsWithin X body (f x) v c ∧ Q x v) →
      ∃ vs, RunsWithin X body
        (.foldList xs acc fun acc x => .bind (f x) fun y => .op2 .cons y acc)
        (vs.reverse ++ acc) (xs.length * (c + 2)) ∧ List.Forall₂ Q xs vs
  | [], acc, _ => ⟨[], by simpa using RunsWithin.foldList_nil, .nil⟩
  | x :: xs, acc, hf => by
    obtain ⟨v, hv, hq⟩ := hf x List.mem_cons_self
    obtain ⟨vs, hvs, hq'⟩ := fold_cons_exists xs (v :: acc)
      fun y hy => hf y (List.mem_cons_of_mem _ hy)
    refine ⟨v :: vs, ?_, .cons hq hq'⟩
    have h := RunsWithin.foldList_cons
      (hv.bind (RunsWithin.prim (S := S) (X := X) (body := body) .cons (.cons v (.cons acc .nil))))
      hvs
    refine (h.of_eq (by simp)).mono ?_
    simp only [List.length_cons, Nat.succ_mul, Prim.cost]
    omega

/-- `mapList` with per-element results given existentially, related to the inputs by `Q`. -/
theorem RunsWithin.mapList_exists {a' b' : Ty} {xs : List a'.denote}
    {f : a'.denote → Prog S (a, b) Ty.denote b'} {Q : a'.denote → b'.denote → Prop} {c : ℕ}
    (hf : ∀ x ∈ xs, ∃ v, RunsWithin X body (f x) v c ∧ Q x v) :
    ∃ vs, RunsWithin X body (Programs.mapList xs f) vs (xs.length * (c + 3) + 2) ∧
      List.Forall₂ Q xs vs := by
  obtain ⟨vs, hvs, hq⟩ := fold_cons_exists xs [] hf
  refine ⟨vs, ?_, hq⟩
  refine RunsWithin.bind_le (c₂ := xs.length * (c + 2) + (xs.length + 1))
    (RunsWithin.prim _ _) ?_ ?_
  · refine RunsWithin.bind_le (c₂ := xs.length + 1) hvs ?_ (Nat.le_refl _)
    refine RunsWithin.prim_le (by simp [Prim.eval]) ?_
    simp [Prim.cost, hq.length_eq]
  · simp only [Prim.cost, Nat.mul_add]
    omega

end Specs

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

/-- Well-formedness of an element program, in every extension of the context. -/
def WfFun {a' t : Ty} (r : Bool) (Γ : WfCtx var₁ var₂) (f₁ : var₁ a' → Prog S rec var₁ t)
    (f₂ : var₂ a' → Prog S rec var₂ t) : Prop :=
  ∀ Γ' : WfCtx var₁ var₂, Γ ⊆ Γ' → ∀ x₁ x₂, ⟨a', x₁, x₂⟩ ∈ Γ' → Prog.Wf r Γ' (f₁ x₁) (f₂ x₂)

theorem WfFun.mono {a' t : Ty} {Γ Γ' : WfCtx var₁ var₂} {f₁ : var₁ a' → Prog S rec var₁ t}
    {f₂ : var₂ a' → Prog S rec var₂ t} (h : WfFun r Γ f₁ f₂) (hΓ : Γ ⊆ Γ') : WfFun r Γ' f₁ f₂ :=
  fun Γ'' h' => h Γ'' (List.Subset.trans hΓ h')

theorem wf_mapList {a' b' : Ty} {xs₁ : var₁ (.list a')} {xs₂ : var₂ (.list a')}
    {f₁ : var₁ a' → Prog S rec var₁ b'} {f₂ : var₂ a' → Prog S rec var₂ b'}
    (hxs : ⟨.list a', xs₁, xs₂⟩ ∈ Γ) (hf : WfFun r Γ f₁ f₂) :
    Prog.Wf r Γ (mapList xs₁ f₁) (mapList xs₂ f₂) := by
  unfold mapList
  prog_wf
  all_goals exact hf _ (fun y hy => by simp [hy]) _ _ (by simp)

theorem wf_mapArray {a' b' : Ty} {arr₁ : var₁ (.array a')} {arr₂ : var₂ (.array a')}
    {f₁ : var₁ a' → Prog S rec var₁ b'} {f₂ : var₂ a' → Prog S rec var₂ b'}
    (harr : ⟨.array a', arr₁, arr₂⟩ ∈ Γ) (hf : WfFun r Γ f₁ f₂) :
    Prog.Wf r Γ (mapArray arr₁ f₁) (mapArray arr₂ f₂) := by
  unfold mapArray
  refine .bind (.prim _ (.cons harr .nil)) fun l₁ l₂ => .bind ?_ fun m₁ m₂ => ?_
  · exact wf_mapList (by simp) (hf.mono fun y hy => by simp [hy])
  · prog_wf

theorem wf_anyList {a' : Ty} {xs₁ : var₁ (.list a')} {xs₂ : var₂ (.list a')}
    {p₁ : var₁ a' → Prog S rec var₁ .bool} {p₂ : var₂ a' → Prog S rec var₂ .bool}
    (hxs : ⟨.list a', xs₁, xs₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (anyList xs₁ p₁) (anyList xs₂ p₂) := by
  unfold anyList
  prog_wf
  all_goals exact hp _ (fun y hy => by simp [hy]) _ _ (by simp)

theorem wf_allList {a' : Ty} {xs₁ : var₁ (.list a')} {xs₂ : var₂ (.list a')}
    {p₁ : var₁ a' → Prog S rec var₁ .bool} {p₂ : var₂ a' → Prog S rec var₂ .bool}
    (hxs : ⟨.list a', xs₁, xs₂⟩ ∈ Γ) (hp : WfFun r Γ p₁ p₂) :
    Prog.Wf r Γ (allList xs₁ p₁) (allList xs₂ p₂) := by
  unfold allList
  prog_wf
  all_goals exact hp _ (fun y hy => by simp [hy]) _ _ (by simp)

end Wf

end GraphIso.Programs
