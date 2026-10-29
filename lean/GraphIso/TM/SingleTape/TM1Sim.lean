module

public import GraphIso.TM.SingleTape.Model

/-!
# Machines with local state on a single tape, counted, with finite control

Stage 18d (`PLAN-18.md` §5). Mathlib's `TM1to0.tr` turns a machine with one tape and local state
(`TM1`) into a single-tape machine (`TM0`) whose states are a statement still to run and the local
state; mathlib proves the simulation (`TM1to0.tr_respects`) without counting steps, and that a
finite set of labels closed under `goto` gives a finite set of states closed under transitions
(`TM1to0.tr_supports`). Here:

* **Statement size** (`stmtSize q`): the most moves and writes on a path through `q`, plus one for
  the final `goto` or `halt` (which the translation executes as a write of the scanned symbol).
* **One step, counted** (`stepAux_steps`, `tr1_simIn`): a step of the `TM1` machine is between
  `1` and `stmtSize` steps of the translation; with every statement of size at most `s`, a run of
  `N` steps is at most `N s` steps (`tr1_run`). A halted configuration translates to one where the
  translation halts (`tr1_halt`).
* **Finite control** (`Reachable`, `restrict`): a single-tape machine restricted to the states
  reachable from its start state, with the same runs (`restrict_steps`) and halts
  (`restrict_halt`). If a finite set of states contains the start state and is closed under
  transitions (mathlib's `TM0.Supports`), the reachable states are finite (`finite_reachable`).
* **The finite machine** (`FinTM0.ofTM1 M h`): for a `TM1` machine `M` with a finite alphabet,
  finitely many local states and a finite set of labels supporting it (`h : ∃ S,
  TM1.Supports M S`), the translation `TM1to0.tr M` restricted to its reachable states. These are
  finite by mathlib's `TM1to0.tr_supports`; the finiteness is a proposition (`Finite`), so no
  enumeration of the states is computed. **`ofTM1_outputs`**: if `M` runs from `TM1.init l` to a
  halted configuration with the tape `Tape.mk₁ l'` in `N` steps, and every statement has size at
  most `s`, then `TM0OutputsInTime (FinTM0.ofTM1 M h) l l' (N s)`.
-/

@[expose] public section

namespace GraphIso.TM.SingleTape

open Turing StateTransition

section Size

variable {Γ Λ σ : Type*}

/-- **The size of a statement**: the most moves and writes on a path through it, plus one for the
final `goto` or `halt`. -/
def stmtSize : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => stmtSize q + 1
  | .write _ q => stmtSize q + 1
  | .load _ q => stmtSize q
  | .branch _ q₁ q₂ => max (stmtSize q₁) (stmtSize q₂)
  | .goto _ => 1
  | .halt => 1

end Size

section Tr

variable {Γ : Type*} [Inhabited Γ] {Λ : Type*} [Inhabited Λ] {σ : Type*} [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

/-- A first step equal to the first step of a run of positive length gives that run. -/
theorem stepsIn_of_step_eq {α : Type*} {f : α → Option α} {a b c : α} {n : ℕ} (e : f a = f b)
    (h : StepsIn f n b c) (hn : 1 ≤ n) : StepsIn f n a c := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d, hd, h⟩ := stepsIn_succ.1 h
  exact StepsIn.head (e.trans hd) h

/-- **A statement, counted**: the translation runs the statement `q` in between `1` and
`stmtSize q` steps. -/
theorem stepAux_steps (q : TM1.Stmt Γ Λ σ) : ∀ (v : σ) (T : Tape Γ), ∃ n, 1 ≤ n ∧
    n ≤ stmtSize q ∧ StepsIn (TM0.step (TM1to0.tr M)) n ⟨(some q, v), T⟩
      (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q with
  | move d q IH =>
    intro v T
    obtain ⟨n, -, hn, h⟩ := IH v (T.move d)
    exact ⟨n + 1, by omega, by simp only [stmtSize]; omega, StepsIn.head rfl h⟩
  | write a q IH =>
    intro v T
    obtain ⟨n, -, hn, h⟩ := IH v (T.write (a T.1 v))
    exact ⟨n + 1, by omega, by simp only [stmtSize]; omega, StepsIn.head rfl h⟩
  | load a q IH =>
    intro v T
    obtain ⟨n, h1, hn, h⟩ := IH (a T.1 v) T
    exact ⟨n, h1, hn, stepsIn_of_step_eq (b := ⟨(some q, a T.1 v), T⟩) rfl h h1⟩
  | branch p q₁ q₂ IH₁ IH₂ =>
    intro v T
    cases e : p T.1 v
    · obtain ⟨n, h1, hn, h⟩ := IH₂ v T
      refine ⟨n, h1, hn.trans (le_max_right _ _), ?_⟩
      rw [TM1.stepAux, e]
      exact stepsIn_of_step_eq (by simp only [TM0.step, TM1to0.tr, TM1to0.trAux, e]; rfl) h h1
    · obtain ⟨n, h1, hn, h⟩ := IH₁ v T
      refine ⟨n, h1, hn.trans (le_max_left _ _), ?_⟩
      rw [TM1.stepAux, e]
      exact stepsIn_of_step_eq (by simp only [TM0.step, TM1to0.tr, TM1to0.trAux, e]; rfl) h h1
  | goto l =>
    intro v T
    refine ⟨1, le_rfl, le_rfl, StepsIn.single ?_⟩
    simp only [TM0.step, TM1to0.tr, TM1to0.trAux, TM1.stepAux, TM1to0.trCfg, Option.map_some,
      Tape.write_self]
  | halt =>
    intro v T
    refine ⟨1, le_rfl, le_rfl, StepsIn.single ?_⟩
    simp only [TM0.step, TM1to0.tr, TM1to0.trAux, TM1.stepAux, TM1to0.trCfg, Option.map_some,
      Option.map_none, Tape.write_self]

/-- **The translation, counted**: with every statement of size at most `s`, each step of `M` is
at most `s` steps of the translation. -/
theorem tr1_simIn {s : ℕ} (hs : ∀ l, stmtSize (M l) ≤ s) :
    SimIn (TM1.step M) (TM0.step (TM1to0.tr M)) (fun c₁ c₀ => TM1to0.trCfg M c₁ = c₀)
      fun _ => s := by
  rintro ⟨_ | l, v, T⟩ b₁ a₂ h rfl
  · cases h
  · obtain rfl := Option.some.inj h
    obtain ⟨n, -, hn, h⟩ := stepAux_steps M (M l) v T
    exact ⟨_, n, hn.trans (hs l), h, rfl⟩

/-- **Runs, counted**: `N` steps of `M` are at most `N s` steps of the translation. -/
theorem tr1_run {s : ℕ} (hs : ∀ l, stmtSize (M l) ≤ s) {N : ℕ} {c c' : TM1.Cfg Γ Λ σ}
    (h : StepsIn (TM1.step M) N c c') :
    ∃ n ≤ N * s, StepsIn (TM0.step (TM1to0.tr M)) n (TM1to0.trCfg M c) (TM1to0.trCfg M c') := by
  obtain ⟨b, n, hn, hr, rfl⟩ := (tr1_simIn M hs).run h rfl fun _ _ _ _ => le_rfl
  exact ⟨n, hn, hr⟩

/-- **Halting**: a halted configuration translates to one where the translation halts. -/
theorem tr1_halt (v : σ) (T : Tape Γ) :
    TM0.step (TM1to0.tr M) (TM1to0.trCfg M ⟨none, v, T⟩) = none :=
  rfl

end Tr

section Restrict

variable {Γ : Type*} {Λ : Type*} [Inhabited Λ]

/-- **The reachable states** of a single-tape machine: those reached from the start state by
transitions. -/
def Reachable (M : TM0.Machine Γ Λ) (q : Λ) : Prop :=
  Relation.ReflTransGen (fun q q' => ∃ a s, M q a = some (q', s)) default q

variable {M : TM0.Machine Γ Λ}

theorem reachable_start : Reachable M default :=
  Relation.ReflTransGen.refl

theorem Reachable.step {q q' : Λ} {a : Γ} {s : TM0.Stmt Γ} (hq : Reachable M q)
    (h : M q a = some (q', s)) : Reachable M q' :=
  hq.tail ⟨a, s, h⟩

/-- Reachable states are in every set containing the start state and closed under transitions. -/
theorem Reachable.mem {S : Set Λ} (hS : TM0.Supports M S) {q : Λ} (hq : Reachable M q) :
    q ∈ S := by
  induction hq with
  | refl => exact hS.1
  | tail _ h ih =>
    obtain ⟨a, s, h⟩ := h
    exact hS.2 h ih

/-- **Finitely many reachable states**, given a finite set of states containing the start state
and closed under transitions. -/
theorem finite_reachable {S : Finset Λ} (hS : TM0.Supports M ↑S) : Finite {q // Reachable M q} :=
  Finite.of_injective (fun q => (⟨q.1, q.2.mem hS⟩ : {q // q ∈ S}))
    fun _ _ h => Subtype.ext (congrArg Subtype.val h :)

variable (M)

/-- **The machine restricted to its reachable states.** -/
def restrict (q : {q // Reachable M q}) (a : Γ) : Option ({q // Reachable M q} × TM0.Stmt Γ) :=
  match h : M q.1 a with
  | none => none
  | some p => some (⟨p.1, q.2.step h⟩, p.2)

/-- The start state of the restriction. -/
def restrictStart : {q // Reachable M q} :=
  ⟨default, reachable_start⟩

instance : Inhabited {q // Reachable M q} :=
  ⟨restrictStart M⟩

variable {M}

theorem restrict_eq_some {q : {q // Reachable M q}} {a : Γ} {p : Λ × TM0.Stmt Γ}
    (h : M q.1 a = some p) : restrict M q a = some (⟨p.1, q.2.step h⟩, p.2) := by
  unfold restrict
  split
  · next h' => rw [h] at h'; cases h'
  · next p' h' => rw [h] at h'; cases h'; rfl

theorem restrict_eq_none {q : {q // Reachable M q}} {a : Γ} (h : M q.1 a = none) :
    restrict M q a = none := by
  unfold restrict
  split
  · rfl
  · next p' h' => rw [h] at h'; cases h'

variable [Inhabited Γ]

/-- **The restriction's runs** are the machine's runs. -/
theorem restrict_steps {n : ℕ} :
    ∀ {q : {q // Reachable M q}} {T : Tape Γ} {c : TM0.Cfg Γ Λ},
      StepsIn (TM0.step M) n ⟨q.1, T⟩ c →
        ∃ hc, StepsIn (TM0.step (restrict M)) n ⟨q, T⟩ ⟨⟨c.q, hc⟩, c.Tape⟩ := by
  induction n with
  | zero =>
    intro q T c h
    obtain rfl := stepsIn_zero.1 h
    exact ⟨q.2, StepsIn.zero _⟩
  | succ n ih =>
    intro q T c h
    obtain ⟨b, hb, h⟩ := stepsIn_succ.1 h
    obtain ⟨⟨q', st⟩, hm, rfl⟩ := Option.map_eq_some_iff.1 hb
    obtain ⟨hc, h⟩ := ih (q := ⟨q', q.2.step hm⟩) h
    refine ⟨hc, StepsIn.head ?_ h⟩
    simp only [TM0.step, restrict_eq_some hm, Option.map_some]

/-- **The restriction halts** where the machine halts. -/
theorem restrict_halt {q : {q // Reachable M q}} {T : Tape Γ} (h : TM0.step M ⟨q.1, T⟩ = none) :
    TM0.step (restrict M) ⟨q, T⟩ = none := by
  simp only [TM0.step, Option.map_eq_none_iff] at h ⊢
  exact restrict_eq_none h

end Restrict

section Fin

variable {Γ : Type} [Inhabited Γ] [Finite Γ] {Λ : Type} [Inhabited Λ] {σ : Type} [Inhabited σ]
  [Finite σ]

/-- **The finite single-tape machine of a `TM1` machine** with a finite set of labels supporting
it (`h`), a finite alphabet and finitely many local states: mathlib's translation `TM1to0.tr M`
restricted to its reachable states. -/
def FinTM0.ofTM1 (M : Λ → TM1.Stmt Γ Λ σ) (h : ∃ S, TM1.Supports M S) : FinTM0 where
  Γ := Γ
  blank := default
  Λ := {q // Reachable (TM1to0.tr M) q}
  start := restrictStart _
  ΛFin := by
    obtain ⟨S, hS⟩ := h
    have := Fintype.ofFinite σ
    exact finite_reachable (TM1to0.tr_supports M hS)
  m := restrict (TM1to0.tr M)

/-- **The finite machine, counted**: if `M` runs from `TM1.init l` to a halted configuration with
the tape `Tape.mk₁ l'` in `N` steps, and every statement of `M` has size at most `s`, then the
finite machine outputs `l'` on `l` within `N s` transitions. -/
theorem ofTM1_outputs (M : Λ → TM1.Stmt Γ Λ σ) (h : ∃ S, TM1.Supports M S) {s : ℕ}
    (hs : ∀ l, stmtSize (M l) ≤ s) {l l' : List Γ} {N : ℕ} {v : σ}
    (hr : StepsIn (TM1.step M) N (TM1.init l) ⟨none, v, Tape.mk₁ l'⟩) :
    TM0OutputsInTime (FinTM0.ofTM1 M h) l l' (N * s) := by
  obtain ⟨n, hn, hr⟩ := tr1_run M hs hr
  obtain ⟨hc, hr⟩ := restrict_steps (q := restrictStart (TM1to0.tr M)) hr
  exact ⟨⟨_, hc⟩, n, hn, hr, restrict_halt (tr1_halt M v _)⟩

end Fin

end GraphIso.TM.SingleTape
