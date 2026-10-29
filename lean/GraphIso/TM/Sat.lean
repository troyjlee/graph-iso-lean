module

public import GraphIso.TM.Code

/-!
# Specifications of stack programs

Stage 17b (`PLAN-17.md` §5). `Sat prog x c t Q` says that the code `x` runs from `c` within `t`
steps to a configuration satisfying `Q`. Since `Exec` is deterministic, this is a partial
description of the unique run. The rules follow the code:

* `Sat.act`, `Sat.skip`, `Sat.seq`, `Sat.ite_true`, `Sat.ite_false`, `Sat.call`, `Sat.mono`;
* within a budget `t` (the step count of what follows is what is left): `Sat.seq_le`,
  `Sat.act_le`, `Sat.act_seq`, `Sat.ite_true_le`, `Sat.ite_false_le`;
* **`Sat.loop`**: with an invariant `I m` indexed by the number `m` of remaining iterations, if
  the condition holds and the body runs within `t` steps from `I (m + 1)` to `I m`, and fails in
  `I 0` where `Q` holds, then the loop runs from `I m` within `m (t + 1) + 1` steps to `Q`.
* **`Sat.loop_list`** (stage 17d, `PLAN-17.md` §7): with an invariant `I rs` indexed by the
  list `rs` of items still to process, if the condition holds and the body runs within `f a`
  steps from `I (a :: rs)` to `I rs`, and fails in `I []` where `Q` holds, then the loop runs
  from `I rs` within `∑ a ∈ rs, (f a + 1) + 1` steps to `Q`.
* `Sat.exec`: a `Sat` gives an `Exec` within the bound.
-/

@[expose] public section

namespace GraphIso.TM

variable {K Γ : Type} {R : ℕ} {P : Type} [DecidableEq K] [DecidableEq Γ] [Inhabited Γ]

/-- The code runs from `c` within `t` steps to a configuration satisfying `Q`. -/
def Sat (prog : Program K Γ R P) (x : Code K Γ R P) (c : Cfg K Γ R) (t : ℕ)
    (Q : Cfg K Γ R → Prop) : Prop :=
  ∃ c' n, Exec prog x c c' n ∧ n ≤ t ∧ Q c'

namespace Sat

variable {prog : Program K Γ R P} {x y : Code K Γ R P} {c : Cfg K Γ R} {t t' t₁ t₂ : ℕ}
  {Q Q' : Cfg K Γ R → Prop}

theorem exec (h : Sat prog x c t Q) : ∃ c' n, Exec prog x c c' n ∧ n ≤ t ∧ Q c' := h

theorem mono (h : Sat prog x c t Q) (ht : t ≤ t') (hQ : ∀ c', Q c' → Q' c') :
    Sat prog x c t' Q' := by
  obtain ⟨c', n, he, hn, hq⟩ := h
  exact ⟨c', n, he, Nat.le_trans hn ht, hQ c' hq⟩

theorem act (a : Act K Γ R) (h : Q (a.run c)) : Sat prog (.act a) c 1 Q :=
  ⟨_, 1, .act a c, Nat.le_refl _, h⟩

theorem skip (h : Q c) : Sat prog .skip c 1 Q := ⟨c, 1, .skip c, Nat.le_refl _, h⟩

theorem seq {Q₁ : Cfg K Γ R → Prop} (h₁ : Sat prog x c t₁ Q₁)
    (h₂ : ∀ c', Q₁ c' → Sat prog y c' t₂ Q) : Sat prog (.seq x y) c (t₁ + t₂ + 1) Q := by
  obtain ⟨c₁, n₁, e₁, hn₁, hq₁⟩ := h₁
  obtain ⟨c₂, n₂, e₂, hn₂, hq₂⟩ := h₂ c₁ hq₁
  exact ⟨c₂, _, .seq e₁ e₂, by omega, hq₂⟩

/-- Sequencing within a budget: the second part gets what the first leaves. -/
theorem seq_le {Q₁ : Cfg K Γ R → Prop} (h₁ : Sat prog x c t₁ Q₁) (ht : t₁ < t)
    (h₂ : ∀ c', Q₁ c' → Sat prog y c' (t - t₁ - 1) Q) : Sat prog (.seq x y) c t Q :=
  (seq h₁ h₂).mono (by omega) fun _ h => h

/-- An action within a budget. -/
theorem act_le {a : Act K Γ R} (ht : 1 ≤ t) (h : Q (a.run c)) : Sat prog (.act a) c t Q :=
  (act a h).mono ht fun _ h => h

/-- An action followed by code, within a budget. -/
theorem act_seq {a : Act K Γ R} (ht : 2 ≤ t) (h : Sat prog y (a.run c) (t - 2) Q) :
    Sat prog (.seq (.act a) y) c t Q :=
  (seq (Q₁ := fun c' => c' = a.run c) (act a rfl) fun _ hc => hc ▸ h).mono (by omega)
    fun _ h => h

theorem ite_true {b : Cond Γ R} (hb : b.eval c.regs = true) (h : Sat prog x c t Q) :
    Sat prog (.ite b x y) c (t + 1) Q := by
  obtain ⟨c', n, e, hn, hq⟩ := h
  exact ⟨c', _, .ite_true hb e, by omega, hq⟩

theorem ite_false {b : Cond Γ R} (hb : b.eval c.regs = false) (h : Sat prog y c t Q) :
    Sat prog (.ite b x y) c (t + 1) Q := by
  obtain ⟨c', n, e, hn, hq⟩ := h
  exact ⟨c', _, .ite_false hb e, by omega, hq⟩

theorem ite {b : Cond Γ R} (h₁ : b.eval c.regs = true → Sat prog x c t Q)
    (h₂ : b.eval c.regs = false → Sat prog y c t Q) : Sat prog (.ite b x y) c (t + 1) Q := by
  cases hb : b.eval c.regs
  · exact ite_false hb (h₂ hb)
  · exact ite_true hb (h₁ hb)

theorem ite_true_le {b : Cond Γ R} (hb : b.eval c.regs = true) (ht : 1 ≤ t)
    (h : Sat prog x c (t - 1) Q) : Sat prog (.ite b x y) c t Q :=
  (ite_true hb h).mono (by omega) fun _ h => h

theorem ite_false_le {b : Cond Γ R} (hb : b.eval c.regs = false) (ht : 1 ≤ t)
    (h : Sat prog y c (t - 1) Q) : Sat prog (.ite b x y) c t Q :=
  (ite_false hb h).mono (by omega) fun _ h => h

theorem call {p : P} (h : Sat prog (prog.body p) c t Q) : Sat prog (.call p) c (t + 2) Q := by
  obtain ⟨c', n, e, hn, hq⟩ := h
  exact ⟨c', _, .call e, by omega, hq⟩

/-- **Loops**, with an invariant indexed by the number of remaining iterations. -/
theorem loop {b : Cond Γ R} {I : ℕ → Cfg K Γ R → Prop}
    (hstep : ∀ m c, I (m + 1) c → b.eval c.regs = true ∧ Sat prog x c t (I m))
    (hstop : ∀ c, I 0 c → b.eval c.regs = false ∧ Q c) :
    ∀ m c, I m c → Sat prog (.loop b x) c (m * (t + 1) + 1) Q := by
  intro m
  induction m with
  | zero =>
    intro c hc
    obtain ⟨hb, hq⟩ := hstop c hc
    exact ⟨c, 1, .loop_false hb, by omega, hq⟩
  | succ m ih =>
    intro c hc
    obtain ⟨hb, c₁, n₁, e₁, hn₁, hq₁⟩ := hstep m c hc
    obtain ⟨c₂, n₂, e₂, hn₂, hq₂⟩ := ih c₁ hq₁
    refine ⟨c₂, _, .loop_true hb e₁ e₂, ?_, hq₂⟩
    rw [Nat.succ_mul]
    omega

/-- **Loops over a list**: an invariant indexed by the list of items still to process, and a
budget `f a` for the iteration processing the item `a`. -/
theorem loop_list {α : Type} {b : Cond Γ R} {I : List α → Cfg K Γ R → Prop} {f : α → ℕ}
    (hstep : ∀ a rs c, I (a :: rs) c → b.eval c.regs = true ∧ Sat prog x c (f a) (I rs))
    (hstop : ∀ c, I [] c → b.eval c.regs = false ∧ Q c) :
    ∀ rs c, I rs c → Sat prog (.loop b x) c ((rs.map fun a => f a + 1).sum + 1) Q := by
  intro rs
  induction rs with
  | nil =>
    intro c hc
    obtain ⟨hb, hq⟩ := hstop c hc
    exact ⟨c, 1, .loop_false hb, by simp, hq⟩
  | cons a rs ih =>
    intro c hc
    obtain ⟨hb, c₁, n₁, e₁, hn₁, hq₁⟩ := hstep a rs c hc
    obtain ⟨c₂, n₂, e₂, hn₂, hq₂⟩ := ih c₁ hq₁
    refine ⟨c₂, _, .loop_true hb e₁ e₂, ?_, hq₂⟩
    simp only [List.map_cons, List.sum_cons]
    omega

end Sat

end GraphIso.TM
