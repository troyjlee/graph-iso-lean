module

public import GraphIso.Graph.Entry

/-!
# Validating graph data

* `validGB n G`: `G` has `n` lists of at most three entries each, every entry `v` of the list of
  `u` satisfies `v < n`, `v ≠ u` and `u` is listed by `v`, and no list repeats an entry. It
  decides `G.Valid n` (`validGB_iff`).
* `connB n G`: every point has level below `n` from `0`; it decides `Conn n G`.
* `validGraphProg` and `connProg` compute them. **On every input** the validity check costs at
  most `151 n + 8`: the lengths are tested by case analysis on the first four cells, so long
  lists are never scanned, and the other tests run only once every list is short. The
  connectivity check is run on valid data, at cost at most `connCost n`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims

/-! ### Models -/

/-- The entry `v` of the list of `u` is a point other than `u`, listing `u` back. -/
def entryOkB (n : ℕ) (G : GraphData) (u v : ℕ) : Bool :=
  (decide (v < n) && !(v == u)) && adjB G v u

/-- No repeated entries. -/
def nodupB (l : List ℕ) : Bool := l.all fun x => (l.filter fun y => y == x).length == 1

/-- The list of `u` is valid. -/
def nbOkB (n : ℕ) (G : GraphData) (u : ℕ) : Bool :=
  (nbrs G u).all (entryOkB n G u) && nodupB (nbrs G u)

/-- Valid graph data on `n` points, of maximum degree at most three. -/
def validGB (n : ℕ) (G : GraphData) : Bool :=
  (G.size == n) && ((List.range n).all fun u => decide ((nbrs G u).length ≤ 3)) &&
    (List.range n).all (nbOkB n G)

/-- Every point has level below `n` from `0`. -/
def connB (n : ℕ) (G : GraphData) : Bool :=
  (List.range n).all fun v => decide (get (levels n G [0]) v < n)

theorem nodupB_iff {l : List ℕ} : nodupB l = true ↔ l.Nodup := by
  rw [List.nodup_iff_count_eq_one, nodupB, List.all_eq_true]
  simp only [beq_iff_eq, List.count_eq_length_filter]

theorem validGB_iff {n : ℕ} {G : GraphData} : validGB n G = true ↔ G.Valid n := by
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

theorem connB_iff {n : ℕ} {G : GraphData} : connB n G = true ↔ Conn n G := by
  simp [connB, Conn]

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- At most three entries, by case analysis on the first four cells. -/
def shortProg (l : var (.list .nat)) : Prog S rec var .bool :=
  .caseList l (.op0 (.boolLit true)) fun _ t₁ => .caseList t₁ (.op0 (.boolLit true)) fun _ t₂ =>
    .caseList t₂ (.op0 (.boolLit true)) fun _ t₃ =>
      .caseList t₃ (.op0 (.boolLit true)) fun _ _ => .op0 (.boolLit false)

/-- The entry test. -/
def entryOkProg (n : var .nat) (G : var Ty.graph) (u v : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .natLt v n) fun lt => .bind (.op2 .natEq v u) fun e => .bind (.op1 .not e)
    fun ne => .bind (.op2 .and lt ne) fun c => .bind (adjProg G v u) fun back => .op2 .and c back

/-- The number of occurrences of `x`. -/
def countProg (l : var (.list .nat)) (x : var .nat) : Prog S rec var .nat :=
  .bind (Luks.filterList l fun y => .op2 .natEq y x) fun f => .op1 .length f

/-- One occurrence of `x`. -/
def onceProg (l : var (.list .nat)) (x : var .nat) : Prog S rec var .bool :=
  .bind (countProg l x) fun c => .bind (.op0 (.natLit 1)) fun one => .op2 .natEq c one

/-- The list of `u` is valid. -/
def nbOkProg (n : var .nat) (G : var Ty.graph) (u : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet G u) fun ns => .bind (allList ns fun v => entryOkProg n G u v) fun b₁ =>
  .bind (allList ns fun x => onceProg ns x) fun b₂ => .op2 .and b₁ b₂

/-- The list of `u` is short. -/
def shortAtProg (G : var Ty.graph) (u : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet G u) fun ns => shortProg ns

/-- **The validity check.** -/
def validGraphProg (n : var .nat) (G : var Ty.graph) : Prog S rec var .bool :=
  .bind (.op1 .arraySize G) fun sz => .bind (.op2 .natEq sz n) fun hs =>
  .ite hs
    (.bind (.op1 .range n) fun rn => .bind (allList rn fun u => shortAtProg G u) fun sh =>
      .ite sh (allList rn fun u => nbOkProg n G u) (.op0 (.boolLit false)))
    (.op0 (.boolLit false))

/-- The level of `v` is below `n`. -/
def levLtProg (lev : var (.array .nat)) (n v : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet lev v) fun lv => .op2 .natLt lv n

/-- **The connectivity check.** -/
def connProg (n : var .nat) (G : var Ty.graph) : Prog S rec var .bool :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nl => .bind (.op2 .cons z nl)
    fun roots => .bind (levelsProg n G roots) fun lev => .bind (.op1 .range n) fun rn =>
  allList rn fun v => levLtProg lev n v

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.shortProg (l : List ℕ) :
    RunsWithin X body (Graph.shortProg l) (decide (l.length ≤ 3)) 5 := by
  rcases l with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, _ | ⟨x₄, t⟩⟩⟩⟩
  · exact (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono (by simp [Prim.cost])
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_nil
      (RunsWithin.prim_le rfl le_rfl))).mono (by simp [Prim.cost])
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_cons (RunsWithin.caseList_nil
      (RunsWithin.prim_le rfl le_rfl)))).mono (by simp [Prim.cost])
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_cons (RunsWithin.caseList_cons
      (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl))))).mono (by simp [Prim.cost])
  · refine (RunsWithin.caseList_cons (RunsWithin.caseList_cons (RunsWithin.caseList_cons
      (RunsWithin.caseList_cons (RunsWithin.prim_le ?_ le_rfl))))).mono (by simp [Prim.cost])
    simp [Prim.eval]

theorem RunsWithin.entryOkProg {n : ℕ} {G : GraphData} (u v : ℕ) :
    RunsWithin X body (Graph.entryOkProg n G u v) (entryOkB n G u v)
      (3 * (nbrs G v).length + 7) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.adjProg G v u)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.countProg (l : List ℕ) (x : ℕ) :
    RunsWithin X body (Graph.countProg l x) (l.filter fun y => y == x).length
      (6 * l.length + 3) := by
  have hf := Luks.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := l)
    (p := fun y => .op2 .natEq y x) (P := fun y => y == x) (c := 1)
    fun y _ => RunsWithin.prim_le rfl le_rfl
  apply RunsWithin.mono
  case h =>
    run_step hf
    exact RunsWithin.prim_le (c := l.length + 1) rfl (by
      simp only [Prim.cost, Args.head_cons]
      exact Nat.succ_le_succ (List.length_filter_le _ _))
  case hc =>
    omega

theorem RunsWithin.onceProg (l : List ℕ) (x : ℕ) :
    RunsWithin X body (Graph.onceProg l x) ((l.filter fun y => y == x).length == 1)
      (6 * l.length + 6) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.countProg l x)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.nbOkProg {n : ℕ} {G : GraphData} (hs : G.size = n)
    (hsh : ∀ u < n, (nbrs G u).length ≤ 3) (u : ℕ) (hu : u < n) :
    RunsWithin X body (Graph.nbOkProg n G u) (nbOkB n G u) 140 := by
  have hl := hsh u hu
  have hv : ∀ v, (nbrs G v).length ≤ 3 := fun v => by
    by_cases h : v < n
    · exact hsh v h
    · rw [nbrs_of_ge (by omega)]
      simp
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.allList_le (c := 16) fun v _ =>
      (RunsWithin.entryOkProg u v).mono (by have := hv v; omega))
    run_step (RunsWithin.allList_le (c := 24) fun x _ =>
      (RunsWithin.onceProg (nbrs G u) x).mono (by omega))
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    change 1 + ((nbrs G u).length * (16 + 2) + 1 + ((nbrs G u).length * (24 + 2) + 1 + 1)) ≤ _
    omega

theorem RunsWithin.shortAtProg (G : GraphData) (u : ℕ) :
    RunsWithin X body (Graph.shortAtProg G u) (decide ((nbrs G u).length ≤ 3)) 6 :=
  (RunsWithin.bind (RunsWithin.prim _ _) (RunsWithin.shortProg _)).mono (by simp [Prim.cost])

/-- **The validity check, on every input.** -/
theorem RunsWithin.validGraphProg (n : ℕ) (G : GraphData) :
    RunsWithin X body (Graph.validGraphProg n G) (validGB n G) (151 * n + 8) := by
  by_cases hs : G.size = n
  · have hsh := RunsWithin.allList_le (X := X) (body := body) (a' := .nat)
      (xs := List.range n)
      (p := fun u => Graph.shortAtProg G u) (c := 6) fun u _ => RunsWithin.shortAtProg G u
    by_cases hall : ((List.range n).all fun u => decide ((nbrs G u).length ≤ 3)) = true
    · have hsh' : ∀ u < n, (nbrs G u).length ≤ 3 := fun u hu => by
        simpa using (List.all_eq_true.1 hall) u (List.mem_range.2 hu)
      have hok := RunsWithin.allList_le (X := X) (body := body) (a' := .nat)
        (xs := List.range n) (p := fun u => Graph.nbOkProg n G u) (c := 140) fun u hu =>
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
        simp only [Prim.cost, Args.head_cons, List.length_range]
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by simp [Prim.eval, hs]) _
        run_step (RunsWithin.prim _ _)
        run_step hsh
        rw [show ((List.range n).all fun u => decide ((nbrs G u).length ≤ 3)) = false by
          simpa using hall]
        run_with RunsWithin.ite_neg rfl _
        exact RunsWithin.prim_le (by simp [Prim.eval, validGB, hall]) le_rfl
      case hc =>
        simp only [Prim.cost, Args.head_cons, List.length_range]
        omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (by simp [Prim.eval, hs]) _
      exact RunsWithin.prim_le (by simp [Prim.eval, validGB, hs]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega

/-- The cost bound of the connectivity check. -/
def connCost (n : ℕ) : ℕ := levelsCost n 1 + 6 * n + 6

theorem RunsWithin.connProg {n : ℕ} {G : GraphData} (hG : G.Valid n) :
    RunsWithin X body (Graph.connProg n G) (connB n G) (connCost n) := by
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
  {Γ : WfCtx var₁ var₂}

theorem wf_validGraphProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ Ty.graph}
    {G₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (validGraphProg n₁ G₁) (validGraphProg n₂ G₂) := by
  unfold validGraphProg shortAtProg shortProg nbOkProg entryOkProg adjProg memProg onceProg
    countProg Luks.filterList allList anyList
  prog_wf

theorem wf_connProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ Ty.graph}
    {G₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (connProg n₁ G₁) (connProg n₂ G₂) := by
  unfold connProg
  refine .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (wf_levelsProg (by simp [hn]) (by simp [hG]) (List.Mem.head _)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hn]) .nil)) fun _ _ => ?_
  unfold levLtProg allList
  prog_wf

end Wf

end GraphIso.Graph
