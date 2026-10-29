module

public import GraphIso.Sims.SiftProg
public import GraphIso.Programs.List

/-!
# A generic worklist program

Stage 14d, item 4 (`PLAN-14.md` §8), the machinery: a `.loop` over a stack of frames, with no
`.recur` (which is reserved for the main recursion). A frame is processed by a step program
`f` computing a data step `F fr = (produced outputs, child frames)`; the children are pushed and
the outputs collected. The instantiation to Split-or-Johnson's frames comes later.

* `enumMs F ρ fr`: the multiset of all outputs reached from `fr`, by well-founded recursion on a
  rank `ρ` that the children decrease (`enumMs_eq`).
* `worklistD F ρ sz stack out`: the result on data, the iterate of one step `wlStep F` with
  enough fuel; `worklistD_ms` gives it as `out` plus the outputs reached from the stack.
* `RunsWithin.worklistProg`: if each step costs at most `K (1 + w fr + #outputs)`, the children
  have smaller ranks, and the work, the outputs and the children's sizes fit in the frame's size
  `sz fr ≥ 1`, then the program returns `worklistD` at cost at most
  `(K + 11) Σ (ρ fr + 2) sz fr + 7` over the initial stack. The potential pays for the frames
  that produce nothing (the factor `ρ + 2`) and for the loop's bookkeeping (the `11`).
-/

@[expose] public section

namespace GraphIso.SoJTree

open Cost Programs GraphIso.Sims

/-! ### The model -/

section Model

variable {α β : Type}

/-- **The multiset of all outputs reached from a frame**: its own outputs and, recursively,
those of its children of smaller rank. -/
def enumMs (F : α → List β × List α) (ρ : α → ℕ) (fr : α) : Multiset β :=
  ((F fr).1 : Multiset β) +
    ((F fr).2.map fun ch => if _h : ρ ch < ρ fr then enumMs F ρ ch else 0).sum
termination_by ρ fr

/-- One step on the state `(stack, out)`: pop a frame, push its children and collect its
outputs. -/
def wlStep (F : α → List β × List α) : List α × List β → Option (List α × List β)
  | ([], _) => none
  | (fr :: rest, out) => some ((F fr).2 ++ rest, (F fr).1 ++ out)

/-- The potential of a stack: `Σ (ρ fr + 2) sz fr`. -/
def wlPot (ρ sz : α → ℕ) (stack : List α) : ℕ := (stack.map fun fr => (ρ fr + 2) * sz fr).sum

/-- **The worklist on data**: the iterate of `wlStep` with fuel `wlPot + 1`. -/
def worklistD (F : α → List β × List α) (ρ sz : α → ℕ) (stack : List α) (out : List β) :
    List β :=
  (iter (wlStep F) (wlPot ρ sz stack + 1) (stack, out)).2

variable {F : α → List β × List α} {I : α → Prop} {ρ sz w : α → ℕ}

theorem enumMs_eq (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr) {fr : α}
    (hfr : I fr) : enumMs F ρ fr = ((F fr).1 : Multiset β) + ((F fr).2.map (enumMs F ρ)).sum := by
  rw [enumMs]
  congr 2
  exact List.map_congr_left fun ch hch => by simp [(h₂ fr hfr ch hch).2]

theorem wl_pot_append (ρ sz : α → ℕ) (l l' : List α) :
    wlPot ρ sz (l ++ l') = wlPot ρ sz l + wlPot ρ sz l' := by
  simp [wlPot]

theorem wl_sum_le {R : ℕ} : ∀ l : List α, (∀ ch ∈ l, ρ ch + 2 ≤ R) →
    wlPot ρ sz l ≤ R * (l.map sz).sum
  | [], _ => by simp [wlPot]
  | ch :: l, h => by
    have h1 := wl_sum_le l fun c hc => h c (List.mem_cons_of_mem _ hc)
    have h2 : (ρ ch + 2) * sz ch ≤ R * sz ch := Nat.mul_le_mul_right _ (h ch List.mem_cons_self)
    simp only [wlPot, List.map_cons, List.sum_cons] at h1 ⊢
    rw [Nat.mul_add]
    omega

theorem wl_length_le : ∀ l : List α, (∀ ch ∈ l, 1 ≤ sz ch) → l.length ≤ (l.map sz).sum
  | [], _ => by simp
  | ch :: l, h => by
    have h1 := wl_length_le l fun c hc => h c (List.mem_cons_of_mem _ hc)
    have h2 := h ch List.mem_cons_self
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **The potential drop of one frame**: the children's potential, the frame's size and
`ρ + 1` times its work and outputs fit in `(ρ fr + 2) sz fr`. -/
theorem wl_pot_drop (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr)
    (h₃ : ∀ fr, I fr → w fr + (F fr).1.length + ((F fr).2.map sz).sum ≤ sz fr) {fr : α}
    (hfr : I fr) :
    wlPot ρ sz (F fr).2 + sz fr + (ρ fr + 1) * (w fr + (F fr).1.length) ≤ (ρ fr + 2) * sz fr := by
  have hc := wl_sum_le (ρ := ρ) (sz := sz) (R := ρ fr + 1) (F fr).2 fun ch hch => by
    have := (h₂ fr hfr ch hch).2
    omega
  have h3 := h₃ fr hfr
  have hm : (ρ fr + 1) * (((F fr).2.map sz).sum + (w fr + (F fr).1.length)) ≤
      (ρ fr + 1) * sz fr := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add] at hm
  have e : (ρ fr + 2) * sz fr = (ρ fr + 1) * sz fr + sz fr := by ring
  omega

theorem wl_iter_done (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr)
    (h₃ : ∀ fr, I fr → w fr + (F fr).1.length + ((F fr).2.map sz).sum ≤ sz fr)
    (h₄ : ∀ fr, I fr → 1 ≤ sz fr) :
    ∀ (m : ℕ) (stack : List α) (out : List β), (∀ fr ∈ stack, I fr) → wlPot ρ sz stack < m →
      wlStep F (iter (wlStep F) m (stack, out)) = none
  | 0, _, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, [], out, _, _ => by simp [iter, wlStep]
  | m + 1, fr :: rest, out, hI, hm => by
    have hfr := hI fr List.mem_cons_self
    simp only [iter, wlStep]
    refine wl_iter_done h₂ h₃ h₄ m _ _ (fun ch hch => ?_) ?_
    · rcases List.mem_append.1 hch with h | h
      · exact (h₂ fr hfr ch h).1
      · exact hI ch (List.mem_cons_of_mem _ h)
    · have hd := wl_pot_drop (w := w) h₂ h₃ hfr
      have h4 := h₄ fr hfr
      rw [wl_pot_append]
      simp only [wlPot, List.map_cons, List.sum_cons] at hm ⊢
      simp only [wlPot] at hd
      omega

theorem wl_iter_ms (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr) :
    ∀ (m : ℕ) (stack : List α) (out : List β), (∀ fr ∈ stack, I fr) →
      ((iter (wlStep F) m (stack, out)).2 : Multiset β) +
          ((iter (wlStep F) m (stack, out)).1.map (enumMs F ρ)).sum =
        (out : Multiset β) + (stack.map (enumMs F ρ)).sum
  | 0, _, _, _ => rfl
  | m + 1, [], out, _ => by simp [iter, wlStep]
  | m + 1, fr :: rest, out, hI => by
    have hfr := hI fr List.mem_cons_self
    have hI' : ∀ ch ∈ (F fr).2 ++ rest, I ch := fun ch hch => by
      rcases List.mem_append.1 hch with h | h
      · exact (h₂ fr hfr ch h).1
      · exact hI ch (List.mem_cons_of_mem _ h)
    simp only [iter, wlStep]
    rw [wl_iter_ms h₂ m _ _ hI']
    simp only [List.map_cons, List.sum_cons]
    rw [enumMs_eq h₂ hfr]
    simp only [List.map_append, List.sum_append, ← Multiset.coe_add]
    ac_rfl

/-- **The worklist on data returns every output reached from the stack.** -/
theorem worklistD_ms (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr)
    (h₃ : ∀ fr, I fr → w fr + (F fr).1.length + ((F fr).2.map sz).sum ≤ sz fr)
    (h₄ : ∀ fr, I fr → 1 ≤ sz fr) {stack : List α} (hI : ∀ fr ∈ stack, I fr) (out : List β) :
    (worklistD F ρ sz stack out : Multiset β) =
      (out : Multiset β) + (stack.map (enumMs F ρ)).sum := by
  have hms := wl_iter_ms h₂ (wlPot ρ sz stack + 1) stack out hI
  have hdone := wl_iter_done (w := w) h₂ h₃ h₄ (wlPot ρ sz stack + 1) stack out hI
    (Nat.lt_succ_self _)
  have hnil : (iter (wlStep F) (wlPot ρ sz stack + 1) (stack, out)).1 = [] := by
    revert hdone
    rcases iter (wlStep F) (wlPot ρ sz stack + 1) (stack, out) with ⟨_ | _, _⟩ <;>
      simp [wlStep]
  rw [hnil] at hms
  simpa [worklistD] using hms

end Model

/-! ### The program -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type} {φ ω : Ty}

/-- One iteration on the state `(stack, out)`: pop a frame, run `f`, push the children and
collect the outputs; `none` on the empty stack. -/
def wlBody (f : var φ → Prog S rec var (.prod (.list ω) (.list φ)))
    (st : var (.prod (.list φ) (.list ω))) : Prog S rec var (.option (.prod (.list φ) (.list ω))) :=
  .bind (.op1 .fst st) fun stk => .bind (.op1 .snd st) fun out =>
  .caseList stk (.op0 .none) fun fr rest =>
    .bind (f fr) fun res => .bind (.op1 .fst res) fun ls => .bind (.op1 .snd res) fun chs =>
    .bind (.op2 .append chs rest) fun stk' => .bind (.op2 .append ls out) fun out' =>
    .bind (.op2 .pair stk' out') fun st' => .op1 .some st'

/-- **The worklist program**: run the frames of `stack`, collecting their outputs onto `out`. -/
def worklistProg (f : var φ → Prog S rec var (.prod (.list ω) (.list φ)))
    (stack : var (.list φ)) (out : var (.list ω)) : Prog S rec var (.list ω) :=
  .bind (.op2 .pair stack out) fun st => .bind (.loop st (wlBody f)) fun fin => .op1 .snd fin

end Prog

section Spec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}
  {φ ω : Ty} {f : φ.denote → Prog S (a, b) Ty.denote (.prod (.list ω) (.list φ))}

theorem RunsWithin.wl_caseList_nil {a' t : Ty} {l : (Ty.list a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t}
    {r : t.denote} {k : ℕ} (hl : l = []) (h : RunsWithin X body p r k) :
    RunsWithin X body (.caseList l p q) r (1 + k) := by
  subst hl
  exact RunsWithin.caseList_nil h

theorem RunsWithin.wl_caseList_cons {a' t : Ty} {l : (Ty.list a').denote} {x : a'.denote}
    {xs : List a'.denote} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {k : ℕ}
    (hl : l = x :: xs) (h : RunsWithin X body (q x xs) r k) :
    RunsWithin X body (.caseList l p q) r (1 + k) := by
  subst hl
  exact RunsWithin.caseList_cons h

theorem RunsWithin.wl_body_nil (out : List ω.denote) :
    RunsWithin X body (wlBody f ([], out)) none 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.wl_caseList_nil (by rfl) _
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.wl_body_cons {fr : φ.denote} {rest : List φ.denote} {out : List ω.denote}
    {v : List ω.denote × List φ.denote} {c : ℕ} (hf : RunsWithin X body (f fr) v c) :
    RunsWithin X body (wlBody f (fr :: rest, out)) (some (v.2 ++ rest, v.1 ++ out))
      (c + v.2.length + v.1.length + 9) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.wl_caseList_cons (by rfl) _
    run_step hf
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval]
    omega

variable {F : φ.denote → List ω.denote × List φ.denote} {I : φ.denote → Prop}
  {ρ sz w : φ.denote → ℕ} {K : ℕ}

/-- **The worklist program's specification.** -/
theorem RunsWithin.worklistProg
    (h₁ : ∀ fr, I fr → RunsWithin X body (f fr) (F fr) (K * (1 + w fr + (F fr).1.length)))
    (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr)
    (h₃ : ∀ fr, I fr → w fr + (F fr).1.length + ((F fr).2.map sz).sum ≤ sz fr)
    (h₄ : ∀ fr, I fr → 1 ≤ sz fr) {stack : List φ.denote} (hI : ∀ fr ∈ stack, I fr)
    (out : List ω.denote) :
    RunsWithin X body (SoJTree.worklistProg f stack out) (worklistD F ρ sz stack out)
      ((K + 11) * wlPot ρ sz stack + 7) := by
  set Φ : List φ.denote × List ω.denote → ℕ := fun x => (K + 11) * wlPot ρ sz x.1 + 5 with hΦ
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (s := .prod (.list φ) (.list ω))
    (f := wlBody f) (F := wlStep F) (I := fun x => ∀ fr ∈ x.1, I fr) (Φ := Φ) ?_
    (Φ (stack, out) + 1) (stack, out) hI (Nat.lt_succ_self _)
  · -- the loop's value is `worklistD`'s iterate
    have hdone := wl_iter_done (w := w) h₂ h₃ h₄ (wlPot ρ sz stack + 1) stack out hI
      (Nat.lt_succ_self _)
    have heq := iter_eq_of_fix (wlPot ρ sz stack + 1) (stack, out) hdone (Φ (stack, out) + 1)
      (by
        have : wlPot ρ sz stack ≤ (K + 11) * wlPot ρ sz stack := Nat.le_mul_of_pos_left _ (by omega)
        simp only [hΦ]
        omega)
    rw [heq] at hloop
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step hloop
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, hΦ]
      omega
  · rintro ⟨_ | ⟨fr, rest⟩, out⟩ hx
    · refine ⟨4, RunsWithin.wl_body_nil out, fun _ => by simp [hΦ], fun x' hx' => ?_⟩
      simp [wlStep] at hx'
    · have hfr : I fr := hx fr List.mem_cons_self
      refine ⟨K * (1 + w fr + (F fr).1.length) + (F fr).2.length + (F fr).1.length + 9,
        RunsWithin.wl_body_cons (h₁ fr hfr), fun h => by simp [wlStep] at h, fun x' hx' => ?_⟩
      simp only [wlStep, Option.some.injEq] at hx'
      subst hx'
      refine ⟨fun ch hch => ?_, ?_⟩
      · rcases List.mem_append.1 hch with h | h
        · exact (h₂ fr hfr ch h).1
        · exact hx ch (List.mem_cons_of_mem _ h)
      · -- the potential pays for the iteration
        have hd := wl_pot_drop (w := w) h₂ h₃ hfr
        have h3 := h₃ fr hfr
        have h4 := h₄ fr hfr
        have hlen := wl_length_le (sz := sz) (F fr).2 fun ch hch => h₄ ch (h₂ fr hfr ch hch).1
        set P := wlPot ρ sz (F fr).2
        set R := wlPot ρ sz rest
        set L := (F fr).1.length
        set W := w fr
        set Z := sz fr
        set r := ρ fr
        have hpot : wlPot ρ sz (fr :: rest) = (r + 2) * Z + R := by
          simp [wlPot, r, Z, R]
        have hpot' : wlPot ρ sz ((F fr).2 ++ rest) = P + R := wl_pot_append ρ sz _ _
        simp only [hΦ, hpot, hpot']
        -- `(K + 11) (r + 2) Z ≥ (K + 11) (P + Z + (r + 1)(W + L))`
        have hA : (K + 11) * (P + Z + (r + 1) * (W + L)) ≤ (K + 11) * ((r + 2) * Z) :=
          Nat.mul_le_mul_left _ hd
        have hB : (K + 11) * (W + L) ≤ (K + 11) * ((r + 1) * (W + L)) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
        have hKZ : K ≤ K * Z := Nat.le_mul_of_pos_right _ h4
        have e1 : (K + 11) * (P + Z + (r + 1) * (W + L)) =
            (K + 11) * P + K * Z + 11 * Z + (K + 11) * ((r + 1) * (W + L)) := by ring
        have e2 : (K + 11) * (W + L) = K * W + K * L + 11 * W + 11 * L := by ring
        have e3 : K * (1 + W + L) = K + K * W + K * L := by ring
        have e4 : (K + 11) * (P + R) = (K + 11) * P + (K + 11) * R := by ring
        have e5 : (K + 11) * ((r + 2) * Z + R) = (K + 11) * ((r + 2) * Z) + (K + 11) * R := by
          ring
        rw [e3, e4, e5]
        omega

end Spec

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {φ ω : Ty}

theorem wf_worklistProg {f₁ : var₁ φ → Prog S rec var₁ (.prod (.list ω) (.list φ))}
    {f₂ : var₂ φ → Prog S rec var₂ (.prod (.list ω) (.list φ))} (hf : WfFun r Γ f₁ f₂)
    {stack₁ : var₁ (.list φ)} {stack₂ : var₂ (.list φ)} {out₁ : var₁ (.list ω)}
    {out₂ : var₂ (.list ω)} (hs : ⟨.list φ, stack₁, stack₂⟩ ∈ Γ)
    (ho : ⟨.list ω, out₁, out₂⟩ ∈ Γ) :
    Prog.Wf r Γ (worklistProg f₁ stack₁ out₁) (worklistProg f₂ stack₂ out₂) := by
  unfold worklistProg wlBody
  refine .bind (.prim _ (.cons hs (.cons ho .nil))) fun st₁ st₂ => .bind (.loop (by simp)
    fun v₁ v₂ => ?_) fun fin₁ fin₂ => .prim _ (.cons (by simp) .nil)
  refine .bind (.prim _ (.cons (by simp) .nil)) fun k₁ k₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun o₁ o₂ => .caseList (by simp) (.prim _ .nil)
      fun x₁ x₂ xs₁ xs₂ => .bind (hf _ (fun y hy => by simp [hy]) _ _ (by simp)) fun r₁ r₂ => ?_
  prog_wf

end Wf

end GraphIso.SoJTree
