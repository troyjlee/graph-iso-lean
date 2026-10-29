module

public import GraphIso.TM.SingleTape.Sim
public import GraphIso.TM.SingleTape.IO

/-!
# Compiling stack machines to single-tape machines

Stage 18e (`PLAN-18.md` §6). For a bundled stack machine `tm` (mathlib's `FinTM2`) whose stack
alphabets are finite (`hΓ`), `compile tm hΓ` is a finite single-tape machine (`FinTM0`), and:

**`compile_outputs`**: if `TM2OutputsInTime tm x (some y) T`, then
`TM0OutputsInTime (compile tm hΓ) (encodeIn x) (encodeOut y) (compileConst tm * (|x| + T + 1)²)`,
with `compileConst tm = 4 (2 s² + 3 s + 6)` and `s = tmActs tm` (the most stack actions of a
statement of `tm`). The machine and the constant depend only on `tm`; the input and output
tapes are the framed tapes of stage 18b (`encodeIn`, `encodeOut`); the input and output stacks
may differ. Every transition is counted, including the preparation of the input and the cleanup
of the output.

The machine (`compM tm`, a `TM1` machine with labels `Lab`, alphabet
`Sym (TM2to1.Γ' tm.K tm.Γ) (tm.Γ tm.k₀) (tm.Γ tm.k₁)` and local state `tm.σ`) has three phases:

1. **Input** (`inStart`, `inScan`, `inMark`): erase the left mark, rewrite each input symbol `a`
   as the simulator's cell holding `a` on the input stack (`inCell`), erase the right mark, step
   back and set the bottom mark: `|x| + 3` steps (`input_steps`), ending in mathlib's initial
   simulator configuration `TM1.init (trInit tm.k₀ x)`, mirrored (`inMark_tape`): the
   simulator's stacks grow to the left, so the input needs no reversal. Mathlib's `trCfg_init`
   relates it to `initList tm x` (`initList_eq_init`).
2. **Simulation** (`sim l`): mathlib's simulator `TM2to1.tr tm.m` run on the mirrored tape
   (`simStmt`, stage 18e's `IO`), its `halt` replaced by a jump to the output phase; stage 18c
   counts its steps (`tr2_outputs`).
3. **Output** (`outStart`, `outScan`): write the right mark after the bottom cell, rewrite each
   output stack cell as an output symbol moving left (`toOut`), write the left mark on the first
   cell without an output entry and halt: `|y| + 2` steps (`output_steps`). When `tm` halts every
   stack but the output stack is empty (`haltList`), so the simulator's tape holds exactly the
   output stack (`halt_tape`) and the final tape is `Tape.mk₁ (encodeOut y)`, blanks elsewhere.

So `compM tm` runs within `(2 s² + 3 s + 6) (|x| + T + 1)²` steps (`compM_run`, using
`|y| ≤ |x| + s T`). Every statement of `compM tm` has size at most `4` (`compM_size`), and a
finite set of labels supports it (`compM_supports`: the adapter labels and the support of
mathlib's simulator, `tr_supports_univ`). So `compile tm hΓ = FinTM0.ofTM1 (compM tm) _`
(stage 18d) has finitely many states, and its runs are at most `4` times as long as those of
`compM tm`.
-/

@[expose] public section

namespace GraphIso.TM.SingleTape

open Turing StateTransition Function TM2to1 _root_.GraphIso.TM.SingleTape.Sym

/-! ### Statement sizes -/

section Size

variable {W α β : Type} [Inhabited W] {Λ₁ Λ₂ σ : Type}

/-- A simulated statement has the size of the statement. -/
theorem stmtSize_simStmt (f : Λ₁ → Λ₂) (h : Λ₂) (q : TM1.Stmt W Λ₁ σ) :
    stmtSize (simStmt (α := α) (β := β) f h q) = stmtSize q := by
  induction q with
  | move d q IH => exact congrArg (· + 1) IH
  | write g q IH => exact congrArg (· + 1) IH
  | load g q IH => exact IH
  | branch p q₁ q₂ IH₁ IH₂ => exact congrArg₂ max IH₁ IH₂
  | goto l => rfl
  | halt => rfl

end Size

/-- **The labels of a compiled machine**: the input adapter, the simulator's labels, the output
adapter. -/
inductive Lab (Λ' : Type) where
  /-- Erase the left mark. -/
  | inStart
  /-- Rewrite the input symbols. -/
  | inScan
  /-- Set the bottom mark. -/
  | inMark
  /-- A label of mathlib's simulator. -/
  | sim (l : Λ')
  /-- Write the right mark. -/
  | outStart
  /-- Rewrite the output stack. -/
  | outScan

/-- The machine starts with the input adapter. -/
instance {Λ' : Type} : Inhabited (Lab Λ') :=
  ⟨.inStart⟩

section Compile

variable (tm : FinTM2)

/-- The work symbols: the alphabet of mathlib's simulator. -/
abbrev WorkSym : Type :=
  Γ' tm.K tm.Γ

/-- The alphabet of a compiled machine. -/
abbrev CSym : Type :=
  Sym (WorkSym tm) (tm.Γ tm.k₀) (tm.Γ tm.k₁)

/-- The labels of a compiled machine. -/
abbrev CLab : Type :=
  Lab (Λ' tm.K tm.Γ tm.Λ tm.σ)

/-- A cell of the simulator: the bottom mark and the stack entries. -/
def cell (b : Bool) (c : ∀ k, Option (tm.Γ k)) : WorkSym tm :=
  (b, c)

/-- The cell of the simulator holding `a` on the input stack. -/
def inCell (a : tm.Γ tm.k₀) : ∀ k, Option (tm.Γ k) :=
  update (fun _ => none) tm.k₀ (some a)

/-- The cell of the simulator holding `b` on the output stack. -/
def outCell (b : tm.Γ tm.k₁) : ∀ k, Option (tm.Γ k) :=
  update (fun _ => none) tm.k₁ (some b)

/-- An input symbol as a work symbol. -/
def toWork : CSym tm → CSym tm
  | inp a => work (false, inCell tm a)
  | s => s

/-- Whether a symbol is an input symbol. -/
def isInp : CSym tm → Bool
  | inp _ => true
  | _ => false

/-- Set the bottom mark of a work symbol. -/
def setBottom : CSym tm → CSym tm
  | work w => work (true, w.2)
  | s => s

/-- The output stack's entry of a work symbol. -/
def outOf : CSym tm → Option (tm.Γ tm.k₁)
  | work w => w.2 tm.k₁
  | _ => none

/-- An output stack entry as an output symbol. -/
def toOut (a : CSym tm) : CSym tm :=
  match outOf tm a with
  | some b => out b
  | none => a

/-- **The compiled machine**, with local state. -/
def compM : CLab tm → TM1.Stmt (CSym tm) (CLab tm) tm.σ
  | .inStart => .write (fun _ _ => default) (.move .right (.goto fun _ _ => .inScan))
  | .inScan =>
    .branch (fun a _ => isInp tm a)
      (.write (fun a _ => toWork tm a) (.move .right (.goto fun _ _ => .inScan)))
      (.write (fun _ _ => default) (.move .left (.goto fun _ _ => .inMark)))
  | .inMark => .write (fun a _ => setBottom tm a) (.goto fun _ _ => .sim (.normal tm.main))
  | .sim l => simStmt .sim .outStart (tr tm.m l)
  | .outStart =>
    .move .right (.write (fun _ _ => rmark) (.move .left (.goto fun _ _ => .outScan)))
  | .outScan =>
    .branch (fun a _ => (outOf tm a).isSome)
      (.write (fun a _ => toOut tm a) (.move .left (.goto fun _ _ => .outScan)))
      (.write (fun _ _ => lmark) .halt)


/-! ### The input adapter -/

/-- The tape after the input adapter is the simulator's initial tape, mirrored. -/
theorem inMark_tape (cs : List (WorkSym tm)) :
    (⟨setBottom tm (ListBlank.mk (cs.map work)).head, (ListBlank.mk (cs.map work)).tail,
        (ListBlank.mk []).cons default⟩ : Tape (CSym tm)) =
      workTape (Tape.mk₁ ((true, cs.headI.2) :: cs.tail)) := by
  rw [show ((ListBlank.mk []).cons default : ListBlank (CSym tm)) = ListBlank.mk [] from
    ListBlank.cons_head_tail (ListBlank.mk [])]
  cases cs <;> rfl

/-- **The input adapter**: `|x| + 3` steps from the input tape to the simulator's initial
configuration (`TM1.init (trInit tm.k₀ x)`), mirrored. -/
theorem input_steps (x : List (tm.Γ tm.k₀)) :
    StepsIn (TM1.step (compM tm)) (x.length + 3) (TM1.init (encodeIn x))
      (simCfg .sim .outStart (TM1.init (trInit tm.k₀ x))) := by
  have h₁ : StepsIn (TM1.step (compM tm)) 1 (TM1.init (encodeIn x))
      ⟨some .inScan, tm.initialState, Tape.mk' (ListBlank.mk [])
        (ListBlank.append (x.map inp) (ListBlank.mk [rmark]))⟩ := by
    refine StepsIn.single ?_
    rw [ListBlank.append_mk, ← ListBlank.cons_head_tail (ListBlank.mk ([] : List (CSym tm)))]
    rfl
  have h₂ := scan_steps (M := compM tm) (ℓ := .inScan) (P := isInp tm) (g := toWork tm)
    (d := .right) (F := id) rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl) tm.initialState
    (x.map inp) (ListBlank.mk []) (ListBlank.mk [rmark]) fun a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
      rfl
  have h₃ : ∀ L : ListBlank (CSym tm), StepsIn (TM1.step (compM tm)) 2
      ⟨some .inScan, tm.initialState, id (Tape.mk' L (ListBlank.mk [rmark]))⟩
      ⟨some (.sim (.normal tm.main)), tm.initialState,
        ⟨setBottom tm L.head, L.tail, (ListBlank.mk []).cons default⟩⟩ := fun L => rfl
  have e : ListBlank.append ((x.map inp).map (toWork tm)).reverse (ListBlank.mk []) =
      ListBlank.mk ((x.reverse.map fun a => cell tm false (inCell tm a)).map work) := by
    rw [ListBlank.append_mk, List.append_nil, List.map_map, List.map_map, List.map_reverse]
    rfl
  have h := (h₁.trans h₂).trans (h₃ _)
  rw [e, inMark_tape, List.length_map] at h
  rw [show x.length + 3 = 1 + x.length + 2 by omega]
  exact h

/-! ### The output adapter -/

/-- An output stack cell holds its symbol on the output stack. -/
theorem outOf_outCell (bl : Bool) (b : tm.Γ tm.k₁) :
    outOf tm (work (cell tm bl (outCell tm b))) = some b := by
  simp [outOf, outCell, cell]

/-- An output stack cell becomes its output symbol. -/
theorem toOut_outCell (bl : Bool) (b : tm.Γ tm.k₁) :
    toOut tm (work (cell tm bl (outCell tm b))) = out b := by
  rw [toOut, outOf_outCell]

/-- **The final tape of the simulator**: when `tm` halts, every stack but the output stack is
empty, so the simulator's tape holds exactly the output stack. -/
theorem halt_tape {y : List (tm.Γ tm.k₁)} {L : ListBlank (∀ k, Option (tm.Γ k))}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk (((haltList tm y).stk k).map some).reverse) :
    L = ListBlank.mk (y.reverse.map (outCell tm)) := by
  refine ListBlank.ext fun i => funext fun k => ?_
  have h := congrArg (fun L' => ListBlank.nth L' i) (hL k)
  simp only [ListBlank.nth_map] at h
  change L.nth i k = _ at h
  rw [h, ListBlank.nth_mk, ListBlank.nth_mk, List.getI_eq_getElem?_getD,
    List.getI_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k = tm.k₁
  · subst hk
    rw [haltList_stk_self, ← List.map_reverse, List.getElem?_map]
    cases y.reverse[i]? with
    | none => rfl
    | some b => simp [outCell]
  · rw [haltList_stk_ne tm y hk]
    cases y.reverse[i]? with
    | none => rfl
    | some b =>
      simp [outCell, hk]
      rfl

/-- **The output adapter**: `|r| + 2` steps from the simulator's final configuration with the
output stack `r.reverse` (mirrored) to the output tape, halting. -/
theorem output_steps (r : List (tm.Γ tm.k₁)) (v : tm.σ) :
    StepsIn (TM1.step (compM tm)) (r.length + 2)
      ⟨some .outStart, v, workTape (Tape.mk' ∅ (addBottom (ListBlank.mk (r.map (outCell tm)))))⟩
      ⟨none, v, Tape.mk₁ (encodeOut r.reverse)⟩ := by
  cases r with
  | nil => rfl
  | cons b₀ r =>
    set A : List (CSym tm) :=
      (cell tm true (outCell tm b₀) :: (r.map (outCell tm)).map (cell tm false)).map work with hA
    have h₁ : StepsIn (TM1.step (compM tm)) 1
        ⟨some .outStart, v,
          workTape (Tape.mk' ∅ (addBottom (ListBlank.mk ((b₀ :: r).map (outCell tm)))))⟩
        ⟨some .outScan, v, tapeMirror (Tape.mk' (ListBlank.mk [rmark]) (ListBlank.mk A))⟩ :=
      StepsIn.single rfl
    have h₂ := scan_steps (M := compM tm) (ℓ := .outScan) (P := fun a => (outOf tm a).isSome)
      (g := toOut tm) (d := .left) (F := tapeMirror) rfl tapeMirror_head tapeMirror_write
      (fun T => tapeMirror_move T .right) v A (ListBlank.mk [rmark]) (ListBlank.mk [])
      fun a ha => by
        rw [hA, List.mem_map] at ha
        obtain ⟨c, hc, rfl⟩ := ha
        rw [List.mem_cons, List.mem_map] at hc
        rcases hc with rfl | ⟨d, hd, rfl⟩
        · simp only [outOf_outCell, Option.isSome_some]
        · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hd
          simp only [outOf_outCell, Option.isSome_some]
    rw [ListBlank.append_mk, List.append_nil, ListBlank.append_mk] at h₂
    have h₃ : ∀ l : List (CSym tm), StepsIn (TM1.step (compM tm)) 1
        ⟨some .outScan, v, tapeMirror (Tape.mk' (ListBlank.mk l) (ListBlank.mk []))⟩
        ⟨none, v, Tape.mk₁ (lmark :: l)⟩ := fun l => rfl
    have e : (A.map (toOut tm)).reverse ++ [rmark] = (b₀ :: r).reverse.map out ++ [rmark] := by
      have e₁ : A.map (toOut tm) = (b₀ :: r).map out := by
        simp [hA, Function.comp_def, toOut_outCell]
      rw [e₁, List.map_reverse]
    have h := (h₁.trans h₂).trans (h₃ _)
    rw [e] at h
    rw [show (b₀ :: r).length + 2 = 1 + A.length + 1 by
      simp only [hA, List.length_map, List.length_cons]
      omega]
    exact h

/-! ### The whole run -/

/-- **The compiled machine's run**: if `tm` outputs `y` on `x` within `T` steps, `compM tm` runs
from the input tape to the output tape, halting, within `(2 s² + 3 s + 6) (|x| + T + 1)²`
steps, `s = tmActs tm`. -/
theorem compM_run {x : List (tm.Γ tm.k₀)} {y : List (tm.Γ tm.k₁)} {T : ℕ}
    (h : TM2OutputsInTime tm x (some y) T) :
    ∃ N, N ≤ (2 * tmActs tm ^ 2 + 3 * tmActs tm + 6) * (x.length + T + 1) ^ 2 ∧
      StepsIn (TM1.step (compM tm)) N (TM1.init (encodeIn x))
        ⟨none, tm.initialState, Tape.mk₁ (encodeOut y)⟩ := by
  have hc := trCfg_init (Λ := tm.Λ) (σ := tm.σ) tm.k₀ x
  rw [← initList_eq_init] at hc
  obtain ⟨c₁', n, hc', hn, hle⟩ := tr2_outputs tm h hc
  have hsim := steps_sim (α := tm.Γ tm.k₀) (β := tm.Γ tm.k₁) (M₂ := compM tm) (f := Lab.sim)
    (h := .outStart) (fun _ => rfl) hn
  obtain ⟨L, hL⟩ := hc'
  rw [halt_tape tm hL] at hsim
  have hout := output_steps tm y.reverse tm.initialState
  rw [List.reverse_reverse] at hout
  have hy := length_out_le tm h
  refine ⟨x.length + 3 + n + (y.reverse.length + 2), ?_,
    ((input_steps tm x).trans hsim).trans hout⟩
  rw [List.length_reverse]
  set s := tmActs tm
  set u := x.length + T + 1
  have hT : T + 1 ≤ u := by omega
  have h1 : (2 * s ^ 2 + 2 * s + 1) * (T + 1) * u ≤ (2 * s ^ 2 + 2 * s + 1) * u ^ 2 := by
    rw [Nat.pow_two u, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hT)
  have h2 : s * T ≤ s * u ^ 2 :=
    Nat.mul_le_mul_left _ ((Nat.le_succ T).trans (hT.trans (Nat.le_self_pow two_ne_zero u)))
  have h3 : 2 * x.length + 5 ≤ 5 * u ^ 2 :=
    (show 2 * x.length + 5 ≤ 5 * u by omega).trans
      (Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero u))
  linarith

/-! ### Size, support and the finite machine -/

/-- **Every statement of the compiled machine has size at most `4`.** -/
theorem compM_size (l : CLab tm) : stmtSize (compM tm l) ≤ 4 := by
  cases l with
  | sim l => exact (stmtSize_simStmt _ _ _).le.trans ((stmtSize_tr tm.m l).trans (by decide))
  | inStart => exact Nat.le_of_ble_eq_true rfl
  | inScan => exact Nat.le_of_ble_eq_true rfl
  | inMark => exact Nat.le_of_ble_eq_true rfl
  | outStart => exact Nat.le_of_ble_eq_true rfl
  | outScan => exact Nat.le_of_ble_eq_true rfl

/-- **A finite set of labels supports the compiled machine**: the adapter labels and mathlib's
`TM2to1.trSupp` of all labels of `tm`. -/
theorem compM_supports : ∃ S, TM1.Supports (compM tm) S := by
  classical
  obtain ⟨S₁, hs⟩ := tr_supports_univ tm
  let S₀ : Finset (CLab tm) := S₁.map ⟨Lab.sim, fun _ _ h => Lab.sim.inj h⟩
  have h₀ : ∀ l ∈ S₁, Lab.sim l ∈ S₀ := fun l hl => Finset.mem_map_of_mem _ hl
  refine ⟨{.inStart, .inScan, .inMark, .outStart, .outScan} ∪ S₀, ?_, fun l hl => ?_⟩
  · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
  · have hS : ∀ l ∈ S₀, l ∈ ({.inStart, .inScan, .inMark, .outStart, .outScan} ∪ S₀ :
        Finset (CLab tm)) := fun l hl => Finset.mem_union_right _ hl
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, S₀,
      Finset.mem_map] at hl
    rcases hl with (rfl | rfl | rfl | rfl | rfl) | ⟨l', hl', rfl⟩
    · exact fun _ _ => by simp
    · exact ⟨fun _ _ => by simp, fun _ _ => by simp⟩
    · exact fun _ _ => hS _ (h₀ _ hs.1)
    · exact fun _ _ => by simp
    · exact ⟨fun _ _ => by simp, trivial⟩
    · exact supportsStmt_simStmt (fun l hl => hS _ (h₀ l hl)) (by simp) (hs.2 l' hl')

/-- The alphabet of a compiled machine is finite when the stack alphabets are. -/
theorem finite_cSym (hΓ : ∀ k, Finite (tm.Γ k)) : Finite (CSym tm) := by
  have : Finite (WorkSym tm) := finite_Γ' tm hΓ
  infer_instance

/-- **The compiled machine**: `compM tm` as a finite single-tape machine (stage 18d), given finite
stack alphabets. -/
def compile (hΓ : ∀ k, Finite (tm.Γ k)) : FinTM0 :=
  haveI := finite_cSym tm hΓ
  haveI := tm.σFin
  FinTM0.ofTM1 (compM tm) (compM_supports tm)

/-- The constant of the compiler: `4 (2 s² + 3 s + 6)` with `s = tmActs tm`. -/
def compileConst : ℕ :=
  4 * (2 * tmActs tm ^ 2 + 3 * tmActs tm + 6)

/-- **The compiler, counted**: if `tm` outputs `y` on `x` within `T` steps, the compiled machine
outputs `encodeOut y` on `encodeIn x` within `compileConst tm (|x| + T + 1)²` transitions. -/
theorem compile_outputs (hΓ : ∀ k, Finite (tm.Γ k)) {x : List (tm.Γ tm.k₀)}
    {y : List (tm.Γ tm.k₁)} {T : ℕ} (h : TM2OutputsInTime tm x (some y) T) :
    TM0OutputsInTime (compile tm hΓ) (encodeIn x) (encodeOut y)
      (compileConst tm * (x.length + T + 1) ^ 2) := by
  obtain ⟨N, hN, hr⟩ := compM_run tm h
  have := finite_cSym tm hΓ
  have := tm.σFin
  refine (ofTM1_outputs (compM tm) (compM_supports tm) (compM_size tm) hr).mono ?_
  unfold compileConst
  linarith

end Compile

end GraphIso.TM.SingleTape
