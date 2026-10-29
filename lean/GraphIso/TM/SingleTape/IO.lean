module

public import GraphIso.TM.SingleTape.Model

/-!
# Single-tape machines: mirrored work tapes and scanning loops

Stage 18e (`PLAN-18.md` §6), the generic part of the input and output adapters. This module
imports mathlib only.

* **Mirrored work tapes** (`tapeMirror`, `workTape`): a tape read from right to left, and a tape
  of work symbols `W` as a mirrored tape of `Sym W α β` (`workTape T = tapeMirror (T.map work)`).
  A move on a mirrored tape is the opposite move on the tape (`tapeMirror_move`).
* **Simulated statements** (`simStmt f h q`): a statement over the work symbols run on the
  mirrored tape: moves reversed, symbols read through `unwork` and written as `work`, labels
  mapped by `f`, and `halt` replaced by a jump to the label `h`. **`stepAux_simStmt`**: it
  computes exactly the image (`simCfg`) of the statement's result. **`steps_sim`**: if a machine
  `M₂` runs `simStmt f h (M₁ l)` at every label `f l`, every run of `M₁` of `n` steps is a run of
  `M₂` of `n` steps between the images; a halted configuration of `M₁` is mapped to the label
  `h` (where the next phase of `M₂` starts). Simulated statements are supported by any set of
  labels holding the images of the labels and `h` (`supportsStmt_simStmt`).
* **Scanning loops** (`scan_steps`): a label whose statement rewrites each symbol satisfying `P`
  by `g` and moves on, in a fixed direction, runs over a list of `n` such symbols in exactly `n`
  steps; a frame `F` (the identity, or `tapeMirror`) states it for both directions.
-/

@[expose] public section

namespace GraphIso.TM.SingleTape

open Turing StateTransition

/-! ### Mirrored tapes -/

/-- The opposite direction. -/
def flipDir : Dir → Dir
  | .left => .right
  | .right => .left

section Mirror

variable {Γ : Type*} [Inhabited Γ]

/-- **A tape read from right to left.** -/
def tapeMirror (T : Tape Γ) : Tape Γ :=
  ⟨T.head, T.right, T.left⟩

@[simp] theorem tapeMirror_head (T : Tape Γ) : (tapeMirror T).head = T.head :=
  rfl

@[simp] theorem tapeMirror_tapeMirror (T : Tape Γ) : tapeMirror (tapeMirror T) = T :=
  rfl

theorem tapeMirror_move (T : Tape Γ) (d : Dir) :
    tapeMirror (T.move d) = (tapeMirror T).move (flipDir d) := by
  cases d <;> rfl

theorem tapeMirror_write (T : Tape Γ) (a : Γ) : tapeMirror (T.write a) = (tapeMirror T).write a :=
  rfl

theorem tapeMirror_mk' (L R : ListBlank Γ) : tapeMirror (Tape.mk' L R) = ⟨R.head, R.tail, L⟩ :=
  rfl

end Mirror

/-! ### Work tapes and simulated statements -/

section Sim

variable {W α β : Type} [Inhabited W]

open Sym

/-- The work symbols as a pointed map into the alphabet. -/
def workMap : PointedMap W (Sym W α β) :=
  ⟨work, rfl⟩

/-- The work symbol read from a symbol (the blank for the others). -/
def unwork : Sym W α β → W
  | work w => w
  | _ => default

/-- **A tape of work symbols as a mirrored tape of symbols.** -/
def workTape (T : Tape W) : Tape (Sym W α β) :=
  tapeMirror (T.map workMap)

@[simp] theorem workTape_head (T : Tape W) : (workTape T : Tape (Sym W α β)).head = work T.head :=
  rfl

theorem workTape_move (T : Tape W) (d : Dir) :
    (workTape (T.move d) : Tape (Sym W α β)) = (workTape T).move (flipDir d) := by
  rw [workTape, Tape.map_move, tapeMirror_move]
  rfl

theorem workTape_write (T : Tape W) (a : W) :
    (workTape (T.write a) : Tape (Sym W α β)) = (workTape T).write (work a) := by
  rw [workTape, Tape.map_write, tapeMirror_write]
  rfl

variable {Λ₁ Λ₂ σ : Type}

/-- **A statement over the work symbols, run on the mirrored tape**: moves reversed, symbols read
through `unwork` and written as `work`, labels mapped by `f`, `halt` replaced by a jump to `h`. -/
def simStmt (f : Λ₁ → Λ₂) (h : Λ₂) : TM1.Stmt W Λ₁ σ → TM1.Stmt (Sym W α β) Λ₂ σ
  | .move d q => .move (flipDir d) (simStmt f h q)
  | .write g q => .write (fun a v => work (g (unwork a) v)) (simStmt f h q)
  | .load g q => .load (fun a v => g (unwork a) v) (simStmt f h q)
  | .branch p q₁ q₂ => .branch (fun a v => p (unwork a) v) (simStmt f h q₁) (simStmt f h q₂)
  | .goto l => .goto fun a v => f (l (unwork a) v)
  | .halt => .goto fun _ _ => h

/-- The image of a configuration: the label mapped by `f` (`h` for the halted configuration),
the same local state, the mirrored work tape. -/
def simCfg (f : Λ₁ → Λ₂) (h : Λ₂) (c : TM1.Cfg W Λ₁ σ) : TM1.Cfg (Sym W α β) Λ₂ σ :=
  ⟨some (c.l.elim h f), c.var, workTape c.Tape⟩

/-- **A simulated statement computes the image of the statement's result.** -/
theorem stepAux_simStmt (f : Λ₁ → Λ₂) (h : Λ₂) (q : TM1.Stmt W Λ₁ σ) :
    ∀ (v : σ) (T : Tape W), TM1.stepAux (simStmt (α := α) (β := β) f h q) v (workTape T) =
      simCfg f h (TM1.stepAux q v T) := by
  induction q with
  | move d q IH =>
    intro v T
    rw [simStmt, TM1.stepAux, ← workTape_move, IH, TM1.stepAux]
  | write g q IH =>
    intro v T
    rw [simStmt, TM1.stepAux, workTape_head, unwork, ← workTape_write, IH, TM1.stepAux]
  | load g q IH =>
    intro v T
    rw [simStmt, TM1.stepAux, workTape_head, unwork, IH, TM1.stepAux]
  | branch p q₁ q₂ IH₁ IH₂ =>
    intro v T
    rw [simStmt, TM1.stepAux, workTape_head, unwork, TM1.stepAux]
    cases p T.head v
    · exact IH₂ v T
    · exact IH₁ v T
  | goto l =>
    intro v T
    rfl
  | halt =>
    intro v T
    rfl

/-- **Simulated runs**: if `M₂` runs `simStmt f h (M₁ l)` at every label `f l`, every run of `M₁`
is a run of `M₂` of the same length between the images. -/
theorem steps_sim {M₁ : Λ₁ → TM1.Stmt W Λ₁ σ} {M₂ : Λ₂ → TM1.Stmt (Sym W α β) Λ₂ σ}
    {f : Λ₁ → Λ₂} {h : Λ₂} (hM : ∀ l, M₂ (f l) = simStmt f h (M₁ l)) {n : ℕ}
    {c c' : TM1.Cfg W Λ₁ σ} (hr : StepsIn (TM1.step M₁) n c c') :
    StepsIn (TM1.step M₂) n (simCfg f h c) (simCfg f h c') := by
  induction n generalizing c with
  | zero => exact stepsIn_zero.1 hr ▸ StepsIn.zero _
  | succ n ih =>
    obtain ⟨b, hb, hr⟩ := stepsIn_succ.1 hr
    obtain ⟨_ | l, v, T⟩ := c
    · cases hb
    · obtain rfl := Option.some.inj hb
      refine StepsIn.head ?_ (ih hr)
      change some (TM1.stepAux (M₂ (f l)) v (workTape T)) = _
      rw [hM, stepAux_simStmt]

/-- **Simulated statements are supported** by any set holding the images of the labels and `h`. -/
theorem supportsStmt_simStmt [Inhabited Λ₂] {f : Λ₁ → Λ₂} {h : Λ₂} {S₁ : Finset Λ₁}
    {S₂ : Finset Λ₂} (hf : ∀ l ∈ S₁, f l ∈ S₂) (hh : h ∈ S₂) {q : TM1.Stmt W Λ₁ σ}
    (hq : TM1.SupportsStmt S₁ q) : TM1.SupportsStmt S₂ (simStmt (α := α) (β := β) f h q) := by
  induction q with
  | move d q IH => exact IH hq
  | write g q IH => exact IH hq
  | load g q IH => exact IH hq
  | branch p q₁ q₂ IH₁ IH₂ => exact ⟨IH₁ hq.1, IH₂ hq.2⟩
  | goto l => exact fun a v => hf _ (hq _ _)
  | halt => exact fun _ _ => hh

end Sim

/-! ### Scanning loops -/

section Scan

variable {Γ Λ σ : Type} [Inhabited Γ]

/-- **A scanning loop**: if the label `ℓ` rewrites each symbol `a` with `P a` by `g a` and moves
`d`, and `F` turns right moves into moves `d`, then over `n` symbols satisfying `P` it takes
exactly `n` steps. -/
theorem scan_steps {M : Λ → TM1.Stmt Γ Λ σ} {ℓ : Λ} {P : Γ → Bool} {g : Γ → Γ}
    {q : TM1.Stmt Γ Λ σ} {d : Dir} {F : Tape Γ → Tape Γ}
    (hM : M ℓ = .branch (fun a _ => P a) (.write (fun a _ => g a) (.move d (.goto fun _ _ => ℓ)))
      q)
    (hF : ∀ T, (F T).head = T.head) (hFw : ∀ T a, F (T.write a) = (F T).write a)
    (hFm : ∀ T, F (T.move .right) = (F T).move d) (v : σ) :
    ∀ (A : List Γ) (L R : ListBlank Γ), (∀ a ∈ A, P a = true) →
      StepsIn (TM1.step M) A.length ⟨some ℓ, v, F (Tape.mk' L (ListBlank.append A R))⟩
        ⟨some ℓ, v, F (Tape.mk' (ListBlank.append (A.map g).reverse L) R)⟩ := by
  intro A
  induction A with
  | nil => intro L R _; exact StepsIn.zero _
  | cons a A ih =>
    intro L R hA
    have h1 := ih (L.cons (g a)) R fun b hb => hA b (List.mem_cons_of_mem a hb)
    have e : ListBlank.append ((a :: A).map g).reverse L =
        ListBlank.append (A.map g).reverse (L.cons (g a)) := by
      rw [List.map_cons, List.reverse_cons, ListBlank.append_assoc]
      rfl
    rw [e]
    refine StepsIn.head ?_ h1
    change some (TM1.stepAux (M ℓ) v _) = _
    rw [hM]
    simp only [TM1.stepAux, hF, Tape.mk'_head, ListBlank.append, ListBlank.head_cons,
      hA a List.mem_cons_self, Bool.cond_true]
    rw [← hFw, ← hFm, Tape.write_mk', Tape.move_right_mk', ListBlank.tail_cons,
      ListBlank.head_cons, ListBlank.tail_cons]

end Scan

end GraphIso.TM.SingleTape
