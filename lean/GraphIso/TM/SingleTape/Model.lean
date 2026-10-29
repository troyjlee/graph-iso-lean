module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Basic.Finite.Sum

/-!
# Single-tape machines: finite machines, timed outputs and framed tapes

Stage 18b (`PLAN-18.md` §3). The contracts for the simulation of stack machines (mathlib's
`Turing.TM2`) by single-tape machines (mathlib's `Turing.TM0`). This module imports mathlib
only.

* **Counted runs.** `StepsIn f n a b`: the transition function `f` takes `a` to `b` in exactly
  `n` transitions, i.e. `(flip bind f)^[n] a = some b`, the iteration of mathlib's
  `StateTransition.EvalsTo`. It composes (`StepsIn.trans`), is deterministic
  (`StepsIn.halt_unique`: two runs from the same configuration to configurations where `f`
  halts have the same length and end), and gives mathlib's `Reaches` and `EvalsToInTime`.
* **Quantitative simulation** (`SimIn f₁ f₂ R κ`): every transition of `f₁` from `a₁` is
  matched, from every `R`-related configuration, by at most `κ a₁` transitions of `f₂` to an
  `R`-related configuration. `SimIn.run`: a run of `N` transitions of `f₁` along which `κ` is at
  most `K` is matched by at most `N K` transitions of `f₂`.
* **Finite single-tape machines** (`FinTM0`): mathlib's `TM0` machine with a tape alphabet `Γ`,
  its blank `blank`, states `Λ` and a start state `start`, both types `Finite`. The `Inhabited`
  instances used by mathlib's `TM0.step` and `TM0.init` are exactly `blank` and `start`.
* **Timed outputs** (`TM0OutputsInTime M l l' m`): started in `M.start` on the tape `l` (the head
  on its first symbol, blanks elsewhere: `TM0.init l`), `M` makes at most `m` transitions to a
  configuration where it halts (`TM0.step` returns `none`) whose tape is `l'`, the head on its
  first symbol and blanks elsewhere (`Tape.mk₁ l'`). Transitions are counted; the halt itself
  costs nothing. Then `ListBlank.mk l' ∈ TM0.eval M.machine l` (`mem_eval`), so the output is unique
  up to trailing blanks (`unique`).
* **Framed tapes.** The alphabet `Sym W α β`: work symbols `W` (the blank is `work default`),
  two marks, input symbols `α` and output symbols `β`. `encodeIn x = lmark :: x ++ [rmark]` and
  `encodeOut y = lmark :: y ++ [rmark]` (each symbol wrapped), of lengths `|x| + 2` and
  `|y| + 2`. They are injective, and so are their tapes (`mk_encodeOut_inj`): the final `rmark`
  is not blank, so no output is lost as trailing blanks.
-/

@[expose] public section

namespace GraphIso.TM.SingleTape

open Turing StateTransition

/-! ### Counted runs -/

section Steps

variable {σ : Type*} (f : σ → Option σ)

/-- `f` takes `a` to `b` in exactly `n` transitions. -/
def StepsIn (n : ℕ) (a b : σ) : Prop :=
  (flip bind f)^[n] (some a) = some b

variable {f}

theorem iterate_none (n : ℕ) : (flip bind f)^[n] (none : Option σ) = none :=
  Function.iterate_fixed rfl n

theorem StepsIn.zero (a : σ) : StepsIn f 0 a a :=
  rfl

theorem stepsIn_zero {a b : σ} : StepsIn f 0 a b ↔ a = b :=
  ⟨fun h => Option.some.inj h, fun h => h ▸ rfl⟩

theorem stepsIn_succ {n : ℕ} {a c : σ} :
    StepsIn f (n + 1) a c ↔ ∃ b, f a = some b ∧ StepsIn f n b c := by
  unfold StepsIn
  rw [Function.iterate_succ_apply]
  change (flip bind f)^[n] (f a) = some c ↔ _
  rcases h : f a with _ | b
  · rw [iterate_none]
    simp
  · simp

theorem StepsIn.head {n : ℕ} {a b c : σ} (h : f a = some b) (h' : StepsIn f n b c) :
    StepsIn f (n + 1) a c :=
  stepsIn_succ.2 ⟨b, h, h'⟩

theorem StepsIn.single {a b : σ} (h : f a = some b) : StepsIn f 1 a b :=
  StepsIn.head h (StepsIn.zero b)

theorem StepsIn.trans {m n : ℕ} {a b c : σ} (h₁ : StepsIn f m a b) (h₂ : StepsIn f n b c) :
    StepsIn f (m + n) a c := by
  unfold StepsIn at *
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

theorem StepsIn.tail {n : ℕ} {a b c : σ} (h : StepsIn f n a b) (h' : f b = some c) :
    StepsIn f (n + 1) a c :=
  h.trans (StepsIn.single h')

theorem StepsIn.det {n : ℕ} {a b c : σ} (h₁ : StepsIn f n a b) (h₂ : StepsIn f n a c) :
    b = c :=
  Option.some.inj (h₁.symm.trans h₂)

/-- A run cannot continue past a configuration where `f` halts. -/
theorem StepsIn.eq_of_halt {n : ℕ} {a b : σ} (h : StepsIn f n a b) (hb : f a = none) :
    n = 0 ∧ a = b := by
  cases n with
  | zero => exact ⟨rfl, stepsIn_zero.1 h⟩
  | succ n =>
    obtain ⟨c, hc, -⟩ := stepsIn_succ.1 h
    rw [hb] at hc
    cases hc

/-- **Determinism**: two runs from `a` to configurations where `f` halts have the same length
and the same end. -/
theorem StepsIn.halt_unique {n n' : ℕ} {a b b' : σ} (h : StepsIn f n a b) (hb : f b = none)
    (h' : StepsIn f n' a b') (hb' : f b' = none) : n = n' ∧ b = b' := by
  induction n generalizing a n' with
  | zero =>
    obtain rfl := stepsIn_zero.1 h
    obtain ⟨rfl, rfl⟩ := h'.eq_of_halt hb
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := stepsIn_succ.1 h
    cases n' with
    | zero =>
      obtain rfl := stepsIn_zero.1 h'
      rw [hb'] at hc
      cases hc
    | succ n' =>
      obtain ⟨c', hc', h'⟩ := stepsIn_succ.1 h'
      obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
      obtain ⟨rfl, rfl⟩ := ih h h'
      exact ⟨rfl, rfl⟩

theorem StepsIn.reaches {n : ℕ} {a b : σ} (h : StepsIn f n a b) : Reaches f a b := by
  induction n generalizing a with
  | zero => exact stepsIn_zero.1 h ▸ Relation.ReflTransGen.refl
  | succ n ih =>
    obtain ⟨c, hc, h⟩ := stepsIn_succ.1 h
    exact Relation.ReflTransGen.head hc (ih h)

/-- A counted run is mathlib's `EvalsToInTime` within any larger bound. -/
def StepsIn.evalsToInTime {n m : ℕ} {a b : σ} (h : StepsIn f n a b) (hm : n ≤ m) :
    EvalsToInTime f a (some b) m :=
  ⟨⟨n, h⟩, hm⟩

theorem EvalsToInTime.stepsIn {m : ℕ} {a b : σ} (h : EvalsToInTime f a (some b) m) :
    ∃ n ≤ m, StepsIn f n a b :=
  ⟨h.steps, h.steps_le_m, h.evals_in_steps⟩

end Steps

/-! ### Quantitative simulation -/

section Sim

variable {σ₁ σ₂ : Type*}

/-- **Quantitative simulation**: every transition of `f₁` from `a₁` is matched, from every
configuration `R`-related to `a₁`, by at most `κ a₁` transitions of `f₂` to a configuration
`R`-related to the successor. -/
def SimIn (f₁ : σ₁ → Option σ₁) (f₂ : σ₂ → Option σ₂) (R : σ₁ → σ₂ → Prop) (κ : σ₁ → ℕ) :
    Prop :=
  ∀ ⦃a₁ b₁ a₂⦄, f₁ a₁ = some b₁ → R a₁ a₂ → ∃ b₂ n, n ≤ κ a₁ ∧ StepsIn f₂ n a₂ b₂ ∧ R b₁ b₂

/-- **Runs under a quantitative simulation**: a run of `N` transitions of `f₁` along which `κ`
is at most `K` is matched by at most `N K` transitions of `f₂`. -/
theorem SimIn.run {f₁ : σ₁ → Option σ₁} {f₂ : σ₂ → Option σ₂} {R : σ₁ → σ₂ → Prop}
    {κ : σ₁ → ℕ} (H : SimIn f₁ f₂ R κ) {N K : ℕ} {a₁ b₁ : σ₁} {a₂ : σ₂}
    (h : StepsIn f₁ N a₁ b₁) (hR : R a₁ a₂)
    (hK : ∀ i c, i < N → StepsIn f₁ i a₁ c → κ c ≤ K) :
    ∃ b₂ n, n ≤ N * K ∧ StepsIn f₂ n a₂ b₂ ∧ R b₁ b₂ := by
  induction N generalizing a₁ a₂ with
  | zero => exact ⟨a₂, 0, Nat.zero_le _, StepsIn.zero a₂, stepsIn_zero.1 h ▸ hR⟩
  | succ N ih =>
    obtain ⟨c, hc, h⟩ := stepsIn_succ.1 h
    obtain ⟨c₂, n₁, hn₁, h₁, hR₁⟩ := H hc hR
    have hκ := hK 0 a₁ (Nat.succ_pos N) (StepsIn.zero a₁)
    obtain ⟨b₂, n₂, hn₂, h₂, hR₂⟩ := ih h hR₁ fun i c' hi hc' =>
      hK (i + 1) c' (Nat.succ_lt_succ hi) (StepsIn.head hc hc')
    refine ⟨b₂, n₁ + n₂, ?_, h₁.trans h₂, hR₂⟩
    rw [Nat.succ_mul]
    omega

end Sim

/-! ### Finite single-tape machines -/

/-- **A finite single-tape machine**: mathlib's `TM0` machine (a transition function from a
state and the symbol under the head to `none`, halting, or a new state and one move or write),
with a finite tape alphabet `Γ` and its blank symbol `blank`, finitely many states `Λ` and a start
state `start`. -/
structure FinTM0 where
  /-- The tape alphabet. -/
  Γ : Type
  /-- The blank symbol. -/
  blank : Γ
  /-- The tape alphabet is finite. -/
  [ΓFin : Finite Γ]
  /-- The states. -/
  Λ : Type
  /-- The start state. -/
  start : Λ
  /-- There are finitely many states. -/
  [ΛFin : Finite Λ]
  /-- The transition function. -/
  m : Λ → Γ → Option (Λ × TM0.Stmt Γ)

namespace FinTM0

variable (M : FinTM0)

/-- The blank is the tape alphabet's default (mathlib's convention for tapes). -/
instance inhabitedΓ : Inhabited M.Γ :=
  ⟨M.blank⟩

/-- The start state is the states' default (mathlib's convention for `TM0.init`). -/
instance inhabitedΛ : Inhabited M.Λ :=
  ⟨M.start⟩

instance : Finite M.Γ :=
  M.ΓFin

instance : Finite M.Λ :=
  M.ΛFin

/-- The machine as mathlib's `TM0.Machine`. -/
def machine : TM0.Machine M.Γ M.Λ :=
  M.m

/-- One transition: mathlib's `TM0.step`. -/
def step : TM0.Cfg M.Γ M.Λ → Option (TM0.Cfg M.Γ M.Λ) :=
  TM0.step M.machine

/-- The initial configuration on the tape `l`: mathlib's `TM0.init`, in the start state. -/
theorem init_q (l : List M.Γ) : (TM0.init l : TM0.Cfg M.Γ M.Λ).q = M.start :=
  rfl

end FinTM0

/-- **Timed output of a single-tape machine**: started in `M.start` on the tape `l` (the head on
its first symbol, blanks elsewhere), `M` makes at most `m` transitions to a configuration where it
halts whose tape is `l'`, the head on its first symbol, blanks elsewhere. Only transitions are
counted; the halt (`TM0.step` returning `none`) costs nothing. -/
def TM0OutputsInTime (M : FinTM0) (l l' : List M.Γ) (m : ℕ) : Prop :=
  ∃ q n, n ≤ m ∧ StepsIn M.step n (TM0.init l) ⟨q, Tape.mk₁ l'⟩ ∧
    M.step ⟨q, Tape.mk₁ l'⟩ = none

namespace TM0OutputsInTime

variable {M : FinTM0} {l l' : List M.Γ} {m : ℕ}

theorem mono (h : TM0OutputsInTime M l l' m) {m' : ℕ} (hm : m ≤ m') :
    TM0OutputsInTime M l l' m' := by
  obtain ⟨q, n, hn, hr, hh⟩ := h
  exact ⟨q, n, hn.trans hm, hr, hh⟩

/-- A timed output is an output of mathlib's `TM0.eval`. -/
theorem mem_eval (h : TM0OutputsInTime M l l' m) :
    ListBlank.mk l' ∈ TM0.eval M.machine l := by
  obtain ⟨q, n, -, hr, hh⟩ := h
  refine (Part.mem_map_iff _).2 ⟨⟨q, Tape.mk₁ l'⟩, StateTransition.mem_eval.2 ⟨hr.reaches, hh⟩, ?_⟩
  exact Tape.mk'_right₀ _ _

/-- **The output is unique** up to trailing blanks. -/
theorem unique {l₁ l₂ : List M.Γ} {m₁ m₂ : ℕ} (h₁ : TM0OutputsInTime M l l₁ m₁)
    (h₂ : TM0OutputsInTime M l l₂ m₂) : ListBlank.mk l₁ = ListBlank.mk l₂ :=
  Part.mem_unique h₁.mem_eval h₂.mem_eval

/-- **The running time is exact**: two timed outputs on the same tape halt after the same
number of transitions; so a timed output within `m` steps and one ending after `n` transitions
force `n ≤ m`. -/
theorem steps_le {l₁ : List M.Γ} {q : M.Λ} {n : ℕ} (h : TM0OutputsInTime M l l' m)
    (hr : StepsIn M.step n (TM0.init l) ⟨q, Tape.mk₁ l₁⟩) (hh : M.step ⟨q, Tape.mk₁ l₁⟩ = none) :
    n ≤ m := by
  obtain ⟨q', n', hn', hr', hh'⟩ := h
  obtain ⟨rfl, -⟩ := hr.halt_unique hh hr' hh'
  exact hn'

end TM0OutputsInTime

/-! ### Framed tapes -/

/-- Lists ending in the same symbol other than the blank have the same tape only if they are
equal: trailing blanks are the only identification. -/
theorem mk_append_inj {Γ : Type*} [Inhabited Γ] {l₁ l₂ : List Γ} {a : Γ} (ha : a ≠ default)
    (h : ListBlank.mk (l₁ ++ [a]) = ListBlank.mk (l₂ ++ [a])) : l₁ = l₂ := by
  have hn : ∀ n, (l₁ ++ [a]).getI n = (l₂ ++ [a]).getI n := fun n => by
    rw [← ListBlank.nth_mk, ← ListBlank.nth_mk, h]
  have last : ∀ {u v : List Γ}, (∀ n, (u ++ [a]).getI n = (v ++ [a]).getI n) →
      ¬u.length < v.length := fun {u v} huv hlt => by
    have := huv v.length
    rw [List.getI_eq_default _ (by simp; omega), List.getI_eq_getElem _ (by simp)] at this
    simp at this
    exact ha this.symm
  have hlen : l₁.length = l₂.length := by
    have h₁ := last hn
    have h₂ := last fun n => (hn n).symm
    omega
  have : l₁ ++ [a] = l₂ ++ [a] := by
    apply List.ext_getElem (by simp [hlen])
    intro n hn₁ hn₂
    rw [← List.getI_eq_getElem _ hn₁, ← List.getI_eq_getElem _ hn₂, hn n]
  exact List.append_cancel_right this

/-- **The alphabet of a compiled machine**: work symbols `W` (the blank is `work default`), a
left and a right mark, input symbols `α` and output symbols `β`. -/
inductive Sym (W α β : Type) where
  /-- A work symbol. -/
  | work (w : W)
  /-- The left mark of a framed list. -/
  | lmark
  /-- The right mark of a framed list. -/
  | rmark
  /-- An input symbol. -/
  | inp (a : α)
  /-- An output symbol. -/
  | out (b : β)

namespace Sym

variable {W α β : Type}

/-- The blank is the default work symbol. -/
instance [Inhabited W] : Inhabited (Sym W α β) :=
  ⟨work default⟩

/-- The symbols as a sum type. -/
def toSum : Sym W α β → W ⊕ Bool ⊕ α ⊕ β
  | work w => .inl w
  | lmark => .inr (.inl true)
  | rmark => .inr (.inl false)
  | inp a => .inr (.inr (.inl a))
  | out b => .inr (.inr (.inr b))

theorem toSum_injective : Function.Injective (toSum : Sym W α β → _) := by
  intro x y h
  cases x <;> cases y <;> simp_all [toSum]

instance [Finite W] [Finite α] [Finite β] : Finite (Sym W α β) :=
  Finite.of_injective _ toSum_injective

end Sym

open Sym

variable {W α β : Type}

/-- **The input tape**: the input's symbols between the two marks. -/
def encodeIn (x : List α) : List (Sym W α β) :=
  lmark :: x.map inp ++ [rmark]

/-- **The output tape**: the output's symbols between the two marks. -/
def encodeOut (y : List β) : List (Sym W α β) :=
  lmark :: y.map out ++ [rmark]

theorem length_encodeIn (x : List α) : (encodeIn x : List (Sym W α β)).length = x.length + 2 := by
  simp [encodeIn]

theorem length_encodeOut (y : List β) :
    (encodeOut y : List (Sym W α β)).length = y.length + 2 := by
  simp [encodeOut]

theorem encodeIn_injective : Function.Injective (encodeIn : List α → List (Sym W α β)) := by
  intro x y h
  simp only [encodeIn, List.cons_append, List.cons.injEq, List.append_cancel_right_eq,
    true_and] at h
  exact List.map_injective_iff.2 (fun _ _ h => by cases h; rfl) h

theorem encodeOut_injective : Function.Injective (encodeOut : List β → List (Sym W α β)) := by
  intro x y h
  simp only [encodeOut, List.cons_append, List.cons.injEq, List.append_cancel_right_eq,
    true_and] at h
  exact List.map_injective_iff.2 (fun _ _ h => by cases h; rfl) h

/-- **Framed outputs are not lost as trailing blanks**: outputs with the same tape are equal. -/
theorem mk_encodeOut_inj [Inhabited W] {y₁ y₂ : List β}
    (h : ListBlank.mk (encodeOut y₁ : List (Sym W α β)) = ListBlank.mk (encodeOut y₂)) :
    y₁ = y₂ := by
  apply encodeOut_injective (W := W) (α := α)
  have h' := mk_append_inj (a := rmark) (fun h => by cases h)
    (l₁ := lmark :: y₁.map out) (l₂ := lmark :: y₂.map out) h
  simp only [encodeOut, h']

/-- **Framed inputs are not lost as trailing blanks.** -/
theorem mk_encodeIn_inj [Inhabited W] {x₁ x₂ : List α}
    (h : ListBlank.mk (encodeIn x₁ : List (Sym W α β)) = ListBlank.mk (encodeIn x₂)) :
    x₁ = x₂ := by
  apply encodeIn_injective (W := W) (β := β)
  have h' := mk_append_inj (a := rmark) (fun h => by cases h)
    (l₁ := lmark :: x₁.map inp) (l₂ := lmark :: x₂.map inp) h
  simp only [encodeIn, h']

end GraphIso.TM.SingleTape
