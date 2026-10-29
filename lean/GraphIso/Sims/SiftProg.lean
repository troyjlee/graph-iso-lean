module

public import GraphIso.Sims.Construct
public import GraphIso.Programs.Perm

/-!
# Sifting in the cost language

* `RunsWithin.loop_pot`: a loop whose body computes a step function `F` and whose charges are
  paid by a potential `Φ` (each iteration costs at most the drop of `Φ`, and the last at most
  `Φ` itself) returns the iterate of `F` within cost `Φ` of the initial state. The potential
  also bounds the number of iterations, so `iter F m` is the result for every `m > Φ`.
* `siftProg n b T k x` computes `sift n b T k x` at cost at most `siftCost n`
  (`RunsWithin.siftProg`), when the filled slots of `T` and `x` are valid of degree `n` and
  `k ≤ n`: at most `n` continuing iterations, each one composition.
-/

@[expose] public section

namespace GraphIso

namespace Cost.Ty

/-- Sims tables. -/
abbrev table : Ty := .array (.array (.option Ty.perm))
/-- Entries and pending items: a row and an element. -/
abbrev item : Ty := .prod .nat Ty.perm
/-- States of the construction. -/
abbrev state : Ty := .prod table (.prod (.list item) (.list item))

end Cost.Ty

namespace Sims

open Cost Programs

/-! ### Iteration -/

theorem iter_eq_of_fix {α : Type} {F : α → Option α} :
    ∀ (m₀ : ℕ) (x : α), F (iter F m₀ x) = none → ∀ m, m₀ ≤ m → iter F m x = iter F m₀ x
  | 0, x, h, m, _ => by
    cases m with
    | zero => rfl
    | succ m => simp only [iter] at h ⊢; rw [h]
  | m₀ + 1, x, h, m, hm => by
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [iter] at h ⊢
    rcases hF : F x with _ | x'
    · rfl
    · rw [hF] at h
      exact iter_eq_of_fix m₀ x' h m (by omega)

section Loop

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- **Loops paid by a potential.** -/
theorem RunsWithin.loop_pot {s : Ty} {f : s.denote → Prog S (a, b) Ty.denote (.option s)}
    {F : s.denote → Option s.denote} {I : s.denote → Prop} {Φ : s.denote → ℕ}
    (hf : ∀ x, I x → ∃ c, RunsWithin X body (f x) (F x) c ∧ (F x = none → c + 1 ≤ Φ x) ∧
      ∀ x', F x = some x' → I x' ∧ c + 1 + Φ x' ≤ Φ x) :
    ∀ (m : ℕ) (x : s.denote), I x → Φ x < m →
      RunsWithin X body (.loop x f) (iter F m x) (Φ x)
  | 0, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, x, hI, hm => by
    obtain ⟨c, hrun, hnone, hsome⟩ := hf x hI
    rcases hF : F x with _ | x'
    · simp only [iter, hF]
      rw [hF] at hrun
      exact (RunsWithin.loop_none hrun).mono (by have := hnone hF; omega)
    · simp only [iter, hF]
      rw [hF] at hrun
      obtain ⟨hI', hle⟩ := hsome x' hF
      exact (RunsWithin.loop_some hrun
        (RunsWithin.loop_pot hf m x' hI' (by omega))).mono (by omega)

theorem RunsWithin.ite_pos {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (hc : c = true) (h : RunsWithin X body p r k) :
    RunsWithin X body (.ite c p q) r (1 + k) := by
  subst hc
  exact RunsWithin.ite_true h

theorem RunsWithin.ite_neg {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (hc : c = false) (h : RunsWithin X body q r k) :
    RunsWithin X body (.ite c p q) r (1 + k) := by
  subst hc
  exact RunsWithin.ite_false h

end Loop

/-! ### Sifting -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One sifting iteration. -/
def siftBody (n : var .nat) (b : var (.array .nat)) (T : var Ty.table)
    (st : var (.prod .nat Ty.perm)) : Prog S rec var (.option (.prod .nat Ty.perm)) :=
  .bind (.op1 .fst st) fun k => .bind (.op1 .snd st) fun x =>
  .bind (.op2 .natLt k n) fun c =>
  .ite c
    (.bind (.op2 .arrayGet b k) fun bk => .bind (permApply x bk) fun j =>
      .bind (.op2 .arrayGet T k) fun row => .bind (.op2 .arrayGet row j) fun sl =>
      .caseOption sl (.op0 .none) fun σ =>
        .bind (permInv σ) fun σi => .bind (permMul σi x) fun x' =>
        .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add k one) fun k' =>
        .bind (.op2 .pair k' x') fun st' => .op1 .some st')
    (.op0 .none)

/-- Sift `x` from row `k`. -/
def siftProg (n : var .nat) (b : var (.array .nat)) (T : var Ty.table) (k : var .nat)
    (x : var Ty.perm) : Prog S rec var (.prod .nat Ty.perm) :=
  .bind (.op2 .pair k x) fun st => .loop st fun st => siftBody n b T st

end Prog

/-- The cost bound of sifting in degree `n`. -/
def siftCost (n : ℕ) : ℕ := n * (12 * n + 40) + 21

section Specs

variable {S : Signature} {a b' : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b') Ty.denote b'}
  {n : ℕ} {b : Array ℕ} {T : Table}

/-- The filled slots of `T` are valid of degree `n`. -/
def SlotsValid (n : ℕ) (T : Table) : Prop :=
  ∀ {k j : ℕ} {σ : PermData}, slot T k j = some σ → σ.Valid n

theorem TableWF.slotsValid {G : Subgroup (Equiv.Perm (Fin n))} (hT : TableWF n b G T) :
    SlotsValid n T := hT.valid

theorem siftStep_fix (n : ℕ) (b : Array ℕ) (T : Table) :
    ∀ (m : ℕ) (st : ℕ × PermData), n ≤ st.1 + m →
      siftStep n b T (iter (siftStep n b T) m st) = none
  | 0, st, h => by simp [iter, siftStep, show ¬ st.1 < n by omega]
  | m + 1, st, h => by
    simp only [iter]
    rcases hF : siftStep n b T st with _ | st'
    · exact hF
    · apply siftStep_fix n b T m st'
      unfold siftStep at hF
      split_ifs at hF
      · split at hF
        · cases hF
        · cases hF
          simp only
          omega

/-- The potential paying for the sifting loop. -/
def siftPot (n : ℕ) (st : ℕ × PermData) : ℕ := (n - st.1) * (12 * n + 40) + 20

theorem RunsWithin.siftBody (hT : SlotsValid n T) {st : ℕ × PermData} (hst : st.2.Valid n) :
    ∃ c, RunsWithin X body (Sims.siftBody n b T st) (siftStep n b T st) c ∧
      (siftStep n b T st = none → c + 1 ≤ siftPot n st) ∧
      ∀ st', siftStep n b T st = some st' →
        (st'.1 ≤ n ∧ st'.2.Valid n) ∧ c + 1 + siftPot n st' ≤ siftPot n st := by
  obtain ⟨k, x⟩ := st
  simp only at hst
  by_cases hk : k < n
  · rcases hs : slot T k (get x.1 (get b k)) with _ | σ
    · -- empty slot
      have hF : siftStep n b T (k, x) = none := by simp [siftStep, hk, hs]
      refine ⟨14, ?_, (fun _ => by simp only [siftPot]; omega),
        (fun st' h => by rw [hF] at h; cases h)⟩
      rw [hF]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval, hk, decide_true]
        run_with RunsWithin.ite_true _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.permApply _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        change RunsWithin X body
          (Prog.caseOption (a := Ty.perm) (slot T k (get x.1 (get b k))) _ _) _ _
        rw [hs]
        exact RunsWithin.caseOption_none (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost]
        omega
    · -- continue with `σ⁻¹ x`
      have hσ := hT hs
      have hF : siftStep n b T (k, x) = some (k + 1, σ.inv.mul x) := by
        simp [siftStep, hk, hs]
      refine ⟨12 * n + 39, ?_, (fun h => by rw [hF] at h; cases h), fun st' h => ?_⟩
      · rw [hF]
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          simp only [Prim.eval, hk, decide_true]
          run_with RunsWithin.ite_true _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.permApply _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          simp only [Prim.eval]
          change RunsWithin X body
            (Prog.caseOption (a := Ty.perm) (slot T k (get x.1 (get b k))) _ _) _ _
          rw [hs]
          run_with RunsWithin.caseOption_some _
          run_step (RunsWithin.permInv σ)
          run_step (RunsWithin.permMul hσ.inv hst)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.prim _ _
        case hc =>
          simp only [Prim.cost]
          omega
      · rw [hF] at h
        cases h
        refine ⟨⟨by omega, hσ.inv.mul hst⟩, ?_⟩
        simp only [siftPot]
        obtain ⟨d, hd⟩ : ∃ d, n - k = d + 1 := ⟨n - k - 1, by omega⟩
        have hd' : n - (k + 1) = d := by omega
        rw [hd, hd', Nat.add_mul, Nat.one_mul]
        omega
  · have hF : siftStep n b T (k, x) = none := by simp [siftStep, hk]
    refine ⟨5, ?_, (fun _ => by simp only [siftPot]; omega),
      (fun st' h => by rw [hF] at h; cases h)⟩
    rw [hF]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval, hk, decide_false]
      run_with RunsWithin.ite_false _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost]
      omega

/-- **Sifting costs at most `siftCost n`.** -/
theorem RunsWithin.siftProg (hT : SlotsValid n T) {k : ℕ} (hk : k ≤ n) {x : PermData}
    (hx : x.Valid n) :
    RunsWithin X body (Sims.siftProg n b T k x) (sift n b T k x) (siftCost n) := by
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (f := Sims.siftBody n b T)
    (I := fun st : ℕ × PermData => st.1 ≤ n ∧ st.2.Valid n) (Φ := siftPot n)
    (fun st hst => RunsWithin.siftBody hT hst.2) (siftPot n (k, x) + 1) (k, x) ⟨hk, hx⟩
    (Nat.lt_succ_self _)
  have hfix := siftStep_fix n b T (n - k) (k, x) (by simp only; omega)
  have h₁ := iter_eq_of_fix (n - k) (k, x) hfix (siftPot n (k, x) + 1) (by
    simp only [siftPot]
    have : n - k ≤ (n - k) * (12 * n + 40) := Nat.le_mul_of_pos_right _ (by omega)
    omega)
  have h₂ := iter_eq_of_fix (n - k) (k, x) hfix n (by omega)
  rw [h₁, ← h₂] at hloop
  refine (RunsWithin.bind_le (RunsWithin.prim _ _) hloop le_rfl).mono ?_
  simp only [Prim.cost, siftPot, siftCost]
  have : (n - k) * (12 * n + 40) ≤ n * (12 * n + 40) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  omega

end Specs

end Sims

end GraphIso
