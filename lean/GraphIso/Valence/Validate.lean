module

public import GraphIso.Valence.Entry
public import GraphIso.Graph.Validate

/-!
# Validating graph data of maximum degree `Δ`

* `validGB Δ n G`: `G` has `n` lists of at most `Δ` entries each, every entry `v` of the list
  of `u` satisfies `v < n`, `v ≠ u` and `u` is listed by `v`, and no list repeats an entry. It
  decides `G.ValidD Δ n` (`validGB_iff`).
* `validGraphProg Δ` computes it. **On every input** it costs at most `validCost Δ n`: the
  lengths are tested by case analysis on the first `Δ + 1` cells (`shortProg Δ`), so long lists
  are never scanned, and the other tests run only once every list is short.
* The connectivity check `connProg` of milestone 4 is run on valid data, at cost at most
  `connCost Δ n`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims

/-! ### Models -/

/-- Valid graph data on `n` points, of maximum degree at most `Δ`. -/
def validGB (Δ n : ℕ) (G : GraphData) : Bool :=
  (G.size == n) && ((List.range n).all fun u => decide ((nbrs G u).length ≤ Δ)) &&
    (List.range n).all (nbOkB n G)

theorem validGB_iff {Δ n : ℕ} {G : GraphData} : validGB Δ n G = true ↔ G.ValidD Δ n := by
  simp only [validGB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, nbOkB, entryOkB, nodupB_iff, adjB_iff, Bool.not_eq_true',
    beq_eq_false_iff_ne]
  constructor
  · rintro ⟨⟨hs, hd⟩, hok⟩
    have hge : ∀ u, ¬ u < n → nbrs G u = [] := fun u hu => nbrs_of_ge (by omega)
    refine ⟨hs, fun u v huv => ?_, fun u => ?_, fun u v huv => ?_, fun u huu => ?_, fun u => ?_⟩
    · by_cases hu : u < n
      · exact ((hok u hu).1 v huv).1.1
      · rw [Adj, hge u hu] at huv
        exact absurd huv (List.not_mem_nil)
    · by_cases hu : u < n
      · exact (hok u hu).2
      · rw [hge u hu]
        exact List.nodup_nil
    · by_cases hu : u < n
      · exact ((hok u hu).1 v huv).2
      · rw [Adj, hge u hu] at huv
        exact absurd huv (List.not_mem_nil)
    · by_cases hu : u < n
      · exact ((hok u hu).1 u huu).1.2 rfl
      · rw [Adj, hge u hu] at huu
        exact absurd huu (List.not_mem_nil)
    · by_cases hu : u < n
      · exact hd u hu
      · rw [hge u hu]
        simp
  · intro hG
    refine ⟨⟨hG.size, fun u _ => hG.deg u⟩, fun u _ => ⟨fun v huv => ⟨⟨hG.lt u v huv, ?_⟩,
      hG.symm u v huv⟩, hG.nodup u⟩⟩
    rintro rfl
    exact hG.irrefl _ huv

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- At most `k` entries, by case analysis on the first `k + 1` cells. -/
def shortProg : ℕ → var (.list .nat) → Prog S rec var .bool
  | 0, l => .caseList l (.op0 (.boolLit true)) fun _ _ => .op0 (.boolLit false)
  | k + 1, l => .caseList l (.op0 (.boolLit true)) fun _ t => shortProg k t

/-- The list of `u` has at most `Δ` entries. -/
def shortAtProg (Δ : ℕ) (G : var Ty.graph) (u : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet G u) fun ns => shortProg Δ ns

/-- **The validity check.** -/
def validGraphProg (Δ : ℕ) (n : var .nat) (G : var Ty.graph) : Prog S rec var .bool :=
  .bind (.op1 .arraySize G) fun sz => .bind (.op2 .natEq sz n) fun hs =>
  .ite hs
    (.bind (.op1 .range n) fun rn => .bind (allList rn fun u => shortAtProg Δ G u) fun sh =>
      .ite sh (allList rn fun u => nbOkProg n G u) (.op0 (.boolLit false)))
    (.op0 (.boolLit false))

end Prog

/-! ### Specifications -/

/-- The cost bound of the test of one list. -/
def cN (Δ : ℕ) : ℕ := Δ * (9 * Δ + 17) + 4

/-- The cost bound of the validity check. -/
def validCost (Δ n : ℕ) : ℕ := (Δ + cN Δ + 8) * n + 8

/-- The cost bound of the connectivity check. -/
def connCost (Δ n : ℕ) : ℕ := levelsCost Δ n 1 + 6 * n + 6

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.shortProg : ∀ (k : ℕ) (l : List ℕ),
    RunsWithin X body (Valence.shortProg k l) (decide (l.length ≤ k)) (k + 2)
  | 0, [] => (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono
      (by simp [Prim.cost])
  | 0, x :: l => (RunsWithin.caseList_cons (RunsWithin.prim_le (by simp [Prim.eval])
      le_rfl)).mono (by simp [Prim.cost])
  | k + 1, [] => (RunsWithin.caseList_nil (RunsWithin.prim_le (by simp [Prim.eval])
      le_rfl)).mono (by simp [Prim.cost])
  | k + 1, x :: l => (RunsWithin.caseList_cons ((RunsWithin.shortProg k l).of_eq
      (by simp))).mono (by omega)

theorem RunsWithin.shortAtProg (Δ : ℕ) (G : GraphData) (u : ℕ) :
    RunsWithin X body (Valence.shortAtProg Δ G u) (decide ((nbrs G u).length ≤ Δ)) (Δ + 3) :=
  (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.shortProg _ _)).mono (by
    simp only [Prim.cost]
    omega)

theorem RunsWithin.nbOkProg {Δ n : ℕ} {G : GraphData} (hs : G.size = n)
    (hsh : ∀ u < n, (nbrs G u).length ≤ Δ) (u : ℕ) (hu : u < n) :
    RunsWithin X body (Graph.nbOkProg n G u) (nbOkB n G u) (cN Δ) := by
  have hl := hsh u hu
  have hv : ∀ v, (nbrs G v).length ≤ Δ := fun v => by
    by_cases h : v < n
    · exact hsh v h
    · rw [nbrs_of_ge (by omega)]
      simp
  have h₁ : (nbrs G u).length * (3 * Δ + 7 + 2) ≤ Δ * (3 * Δ + 9) := Nat.mul_le_mul hl le_rfl
  have h₂ : (nbrs G u).length * (6 * Δ + 6 + 2) ≤ Δ * (6 * Δ + 8) := Nat.mul_le_mul hl le_rfl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.allList_le (c := 3 * Δ + 7) fun v _ =>
      (RunsWithin.entryOkProg u v).mono (by have := hv v; omega))
    run_step (RunsWithin.allList_le (c := 6 * Δ + 6) fun x _ =>
      (RunsWithin.onceProg (nbrs G u) x).mono (by omega))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, cN]
    change 1 + ((nbrs G u).length * (3 * Δ + 7 + 2) + 1 +
      ((nbrs G u).length * (6 * Δ + 6 + 2) + 1 + 1)) ≤ _
    nlinarith

/-- **The validity check, on every input.** -/
theorem RunsWithin.validGraphProg (Δ n : ℕ) (G : GraphData) :
    RunsWithin X body (Valence.validGraphProg Δ n G) (validGB Δ n G) (validCost Δ n) := by
  by_cases hs : G.size = n
  · have hsh := RunsWithin.allList_le (X := X) (body := body) (a' := .nat)
      (xs := List.range n)
      (p := fun u => Valence.shortAtProg Δ G u) (c := Δ + 3) fun u _ =>
        RunsWithin.shortAtProg Δ G u
    by_cases hall : ((List.range n).all fun u => decide ((nbrs G u).length ≤ Δ)) = true
    · have hsh' : ∀ u < n, (nbrs G u).length ≤ Δ := fun u hu => by
        simpa using (List.all_eq_true.1 hall) u (List.mem_range.2 hu)
      have hok := RunsWithin.allList_le (X := X) (body := body) (a' := .nat)
        (xs := List.range n) (p := fun u => Graph.nbOkProg n G u) (c := cN Δ) fun u hu =>
          RunsWithin.nbOkProg hs hsh' u (List.mem_range.1 hu)
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by simp [Prim.eval, hs]) _
        run_step (RunsWithin.prim _ _)
        run_step hsh
        rw [hall]
        run_with RunsWithin.ite_pos rfl _
        exact hok.of_eq (by simp [validGB, hs, hall])
      case hc =>
        simp only [Prim.cost, Args.head_cons, List.length_range, validCost]
        have : (Δ + cN Δ + 8) * n = n * (Δ + 3 + 2) + n * (cN Δ + 2) + n := by ring
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by simp [Prim.eval, hs]) _
        run_step (RunsWithin.prim _ _)
        run_step hsh
        rw [show ((List.range n).all fun u => decide ((nbrs G u).length ≤ Δ)) = false by
          simpa using hall]
        run_with RunsWithin.ite_neg rfl _
        exact RunsWithin.prim_le (by simp [Prim.eval, validGB, hall]) le_rfl
      case hc =>
        simp only [Prim.cost, Args.head_cons, List.length_range, validCost]
        have : (Δ + cN Δ + 8) * n = n * (Δ + 3 + 2) + n * (cN Δ + 2) + n := by ring
        omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (by simp [Prim.eval, hs]) _
      exact RunsWithin.prim_le (by simp [Prim.eval, validGB, hs]) le_rfl
    case hc =>
      simp only [Prim.cost, validCost]
      omega

theorem RunsWithin.connProg {Δ n : ℕ} {G : GraphData} (hG : G.ValidD Δ n) :
    RunsWithin X body (Graph.connProg n G) (connB n G) (connCost Δ n) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.levelsProg hG _)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.allList_le (c := 2) fun v _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl).of_eq
        rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_cons,
      List.length_nil, connCost, Nat.zero_add]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}

theorem wf_shortProg : ∀ (k : ℕ) {Γ : WfCtx var₁ var₂} {l₁ : var₁ (.list .nat)}
    {l₂ : var₂ (.list .nat)}, ⟨.list .nat, l₁, l₂⟩ ∈ Γ →
    Prog.Wf (S := S) (rec := rec) r Γ (shortProg k l₁) (shortProg k l₂)
  | 0, _, _, _, hl => .caseList hl (.prim _ .nil) fun _ _ _ _ => .prim _ .nil
  | k + 1, _, _, _, hl => .caseList hl (.prim _ .nil) fun _ _ _ _ => wf_shortProg k (by simp)

theorem wf_validGraphProg (Δ : ℕ) {Γ : WfCtx var₁ var₂} {n₁ : var₁ .nat} {n₂ : var₂ .nat}
    {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (validGraphProg Δ n₁ G₁) (validGraphProg Δ n₂ G₂) := by
  unfold validGraphProg
  refine .bind (.prim _ (.cons hG .nil)) fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp [hn]) .nil))) fun _ _ =>
    .ite (List.Mem.head _) (.bind (.prim _ (.cons (by simp [hn]) .nil)) fun _ _ =>
      .bind (wf_allList (List.Mem.head _) fun Γ' hΓ _ _ hx =>
        .bind (.prim _ (.cons (hΓ (by simp [hG])) (.cons hx .nil))) fun _ _ =>
          wf_shortProg Δ (List.Mem.head _)) fun _ _ =>
      .ite (List.Mem.head _) ?_ (.prim _ .nil)) (.prim _ .nil)
  unfold nbOkProg entryOkProg adjProg memProg onceProg countProg Luks.filterList allList anyList
  prog_wf

end Wf

end GraphIso.Graph.Valence
