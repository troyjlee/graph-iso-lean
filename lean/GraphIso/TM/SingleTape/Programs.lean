module

public import GraphIso.TM.Machine
public import GraphIso.TM.SingleTape.Sim

/-!
# Stack programs on one tape

Stage 18d (`PLAN-18.md` §5), the instantiation for the project's compiled stack programs
(`toFinTM2 prog kin kout`, milestone 17): their stack alphabets are the program's symbols and,
on the return stack, the machine's finitely many labels, so they are finite
(`finite_toFinTM2`); the local state (registers and a return slot) is finite in every `FinTM2`.
So the finite single-tape simulator `simTM0` of stage 18d applies to every compiled program:
**`exec_simTM0`**: if `main` runs from the input configuration of `l` to the output
configuration of `l'` in `n` steps, the finite simulator runs from mathlib's initial tape
`trInit (some kin) l` to a halting configuration whose tape holds the stacks of
`haltList (toFinTM2 prog kin kout) l'`, within `3 (2 s² + 2 s + 1) (n + 2) (|l| + n + 2)`
transitions.
-/

@[expose] public section

namespace GraphIso.TM

open Turing SingleTape

variable {K Γ : Type} {R : ℕ} {P : Type} [DecidableEq K] [DecidableEq Γ] [DecidableEq P]
  [Fintype P] [Inhabited Γ] [Fintype K] [Fintype Γ]

/-- **The stack alphabets of a compiled stack program are finite**: the program's alphabet and
the labels of the return stack. -/
theorem finite_toFinTM2 (prog : Program K Γ R P) (kin kout : K) :
    ∀ k, Finite ((toFinTM2 prog kin kout).Γ k)
  | none => (inferInstance : Finite (Label prog))
  | some _ => (inferInstance : Finite Γ)

/-- **A compiled stack program on the finite single-tape simulator.** -/
theorem exec_simTM0 (prog : Program K Γ R P) (kin kout : K) {l l' : List Γ} {n : ℕ}
    (h : Exec prog (prog.body prog.main) (inCfg kin l) (inCfg kout l') n) :
    ∃ L : ListBlank (∀ k, Option ((toFinTM2 prog kin kout).Γ k)),
      (∀ k, L.map (proj k) =
        ListBlank.mk (((haltList (toFinTM2 prog kin kout) l').stk k).map some).reverse) ∧
      ∃ q m, m ≤ 3 * ((2 * tmActs (toFinTM2 prog kin kout) ^ 2 +
          2 * tmActs (toFinTM2 prog kin kout) + 1) * (n + 2) * (l.length + n + 2)) ∧
        StepsIn (simTM0 _ (finite_toFinTM2 prog kin kout)).step m
          (TM0.init (TM2to1.trInit (some kin) l)) ⟨q, Tape.mk' ∅ (TM2to1.addBottom L)⟩ ∧
        (simTM0 _ (finite_toFinTM2 prog kin kout)).step
          ⟨q, Tape.mk' ∅ (TM2to1.addBottom L)⟩ = none :=
  simTM0_outputs _ _ (outputsInTime prog kin kout h)

end GraphIso.TM
