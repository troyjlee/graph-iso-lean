module

public import GraphIso.Valence.CompProg
public import GraphIso.Solver.Valence
public import GraphIso.Graph.All

/-!
# Isomorphism of graphs of maximum degree `Δ`, connected or not

`allProg Δ n X Y` is milestone 5's `allProg` with the connected test `mainProg Δ`: it computes
the components of `X` and `Y`, then matches them greedily. Each component `cs` of `X` takes the
first remaining component of `Y` of the same size whose data the connected test finds
isomorphic, and the matching fails when none remains or when a component of `Y` is left over.
The matched isomorphisms are glued. The invariants `PartnerInv` and `MatchInv` and the
balance argument are milestone 5's, now for any maximum degree.

* `RunsWithin.partnerStepProg`, `RunsWithin.matchStepProg`: one candidate and one component of
  `X`, for a bound `B` on the connected test on at most `n` points (`mainCost Δ c k ≤ B` for
  `k ≤ n`). For `Δ = 5`, `B = mainBound n = 28000 (2n + 2)²²²` (`mainCost_five_le`).
* **`RunsWithin.allProg`**: with the Schreier–Sims backend, for valid data of maximum degree
  `Δ ≥ 2` (connected or not) and a constant `c ≥ 1` with `LayerPrim Δ c`, the result is `none`
  exactly when `X` and `Y` are not isomorphic, and otherwise lists the values of an
  isomorphism; the cost is at most `allCost Δ B n`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims Luks

/-! ### Programs -/

section Prog

variable {var : Ty → Type} {D : Ty}

/-- One candidate `ds` for the component `cs` with data `A`. -/
def partnerStepProg (Δ : ℕ) (Y : var Ty.graph) (cs : var (.list .nat)) (A : var Ty.graph)
    (st : var Ty.findSt) (ds : var (.list .nat)) :
    Prog (groupSig D) (Solver.Rec D) var Ty.findSt :=
  .bind (.op1 .fst st) fun f => .bind (.op1 .snd st) fun kept =>
  .bind (.op2 .cons ds kept) fun kept' => .bind (.op2 .pair f kept') fun keep =>
  .caseOption f
    (.bind (.op1 .length ds) fun ld => .bind (.op1 .length cs) fun lc =>
      .bind (.op2 .natEq ld lc) fun eq =>
      .ite eq
        (.bind (subGProg Y ds) fun B => .bind (mainProg Δ lc A B) fun r =>
          .caseOption r (.ret keep) fun iso =>
            .bind (.op2 .pair ds iso) fun di => .bind (.op1 .some di) fun f' =>
            .op2 .pair f' kept)
        (.ret keep))
    fun _ => .ret keep

/-- Match the component `cs` of `X`. -/
def matchStepProg (Δ : ℕ) (X Y : var Ty.graph) (st : var Ty.matchSt) (cs : var (.list .nat)) :
    Prog (groupSig D) (Solver.Rec D) var Ty.matchSt :=
  .caseOption st (.op0 .none) fun mu =>
    .bind (.op1 .fst mu) fun M => .bind (.op1 .snd mu) fun U =>
    .bind (subGProg X cs) fun A =>
    .bind (.op0 .none) fun f₀ => .bind (.op0 .nil) fun k₀ => .bind (.op2 .pair f₀ k₀) fun s₀ =>
    .bind (.foldList U s₀ fun s ds => partnerStepProg Δ Y cs A s ds) fun r =>
    .bind (.op1 .fst r) fun f => .bind (.op1 .snd r) fun kept =>
    .caseOption f (.op0 .none) fun di =>
      .bind (.op2 .pair cs di) fun t => .bind (.op2 .cons t M) fun M' =>
      .bind (.op2 .pair M' kept) fun mu' => .op1 .some mu'

/-- **Isomorphism of graphs of maximum degree `Δ`, connected or not.** -/
def allProg (Δ : ℕ) (n : var .nat) (X Y : var Ty.graph) :
    Prog (groupSig D) (Solver.Rec D) var (.option (.array .nat)) :=
  .bind (compsProg n X) fun cX => .bind (compsProg n Y) fun cY =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .pair nl cY) fun mu₀ => .bind (.op1 .some mu₀) fun st₀ =>
  .bind (.foldList cX st₀ fun st cs => matchStepProg Δ X Y st cs) fun st =>
  .caseOption st (.op0 .none) fun mu =>
    .bind (.op1 .fst mu) fun M => .bind (.op1 .snd mu) fun U =>
    .caseList U (.bind (glueProg n M) fun arr => .op1 .some arr) fun _ _ => .op0 .none

end Prog

/-! ### Specifications -/

/-- The bound on the connected test on at most `n` points, for maximum degree five. -/
def mainBound (n : ℕ) : ℕ := 28000 * (2 * n + 2) ^ 222

/-- The cost bound of one candidate, for a bound `B` on the connected test. -/
def partnerCost (Δ B n : ℕ) : ℕ := subGCost Δ n + B + 2 * n + 16

/-- The cost bound of matching one component. -/
def matchCost (Δ B n : ℕ) : ℕ := subGCost Δ n + n * (partnerCost Δ B n + 1) + 16

/-- The cost bound of the algorithm. -/
def allCost (Δ B n : ℕ) : ℕ := 2 * compsCost Δ n + n * (matchCost Δ B n + 1) + glueCost n + 16

theorem mainCost_le_mainBound {k n : ℕ} (h : k ≤ n) : mainCost 5 13 k ≤ mainBound n :=
  (mainCost_five_le k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

section Main

variable {Δ c B n : ℕ} {X Y : GraphData} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n)
  (hΔ₂ : 2 ≤ Δ) (hc : LayerPrim Δ c) (hc1 : 1 ≤ c) (hBm : ∀ k ≤ n, mainCost Δ c k ≤ B)
include hX hY hΔ₂ hc hc1 hBm

theorem RunsWithin.partnerStepProg {cs ds : List ℕ} (hcs : cs ∈ comps n X) (hds : ds ∈ comps n Y)
    {pre : List (List ℕ)} {st : Option (List ℕ × Array ℕ) × List (List ℕ)}
    (hI : PartnerInv X Y cs pre st) :
    ∃ st', RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Valence.partnerStepProg (D := Ty.unit) Δ Y cs (subG X cs) st ds) st' (partnerCost Δ B n) ∧
      PartnerInv X Y cs (pre ++ [ds]) st' := by
  obtain ⟨f, kept⟩ := st
  have hk : cs.length ≤ n := length_le_of_mem_comps hcs
  have hk' : ds.length ≤ n := length_le_of_mem_comps hds
  rcases f with _ | ⟨d₀, iso₀⟩
  · simp only [PartnerInv] at hI
    obtain ⟨hp, hno⟩ := hI
    have hp' : List.Perm (ds :: kept) (pre ++ [ds]) :=
      (hp.cons ds).trans (List.perm_append_singleton ds pre).symm
    by_cases hl : ds.length = cs.length
    · have hcl := closed_of_mem_comps hX hcs
      have hnd := nodup_of_mem_comps hcs
      have hcl' := closed_of_mem_comps hY hds
      have hnd' := nodup_of_mem_comps hds
      have hA := valid_subG hcl hnd hX
      have hB : (subG Y ds).ValidD Δ cs.length := hl ▸ valid_subG hcl' hnd' hY
      have hcA := conn_subG hX hcs
      have hcB : Conn cs.length (subG Y ds) := hl ▸ conn_subG hY hds
      obtain ⟨res, hrun, hnone, hsome⟩ :=
        Valence.RunsWithin.mainProg hA hB hΔ₂ hc hc1 hcA hcB
      have hmc : mainCost Δ c cs.length ≤ B := hBm _ hk
      have hsub := Valence.RunsWithin.subGProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote)
        hY.deg ds
      have hsc : subGCost Δ ds.length ≤ subGCost Δ n := subGCost_mono hk'
      have heq : (ds.length == cs.length) = true := by simp [hl]
      rcases res with _ | iso
      · refine ⟨(none, ds :: kept), ?_, ?_⟩
        · apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_with RunsWithin.caseOption_eq_none rfl _
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_with RunsWithin.ite_pos heq _
            run_step hsub
            run_step hrun
            run_with RunsWithin.caseOption_eq_none rfl _
            exact RunsWithin.ret (t := Ty.findSt) _
          case hc =>
            simp only [Prim.cost, Args.head_cons, partnerCost]
            omega
        · simp only [PartnerInv]
          refine ⟨hp', fun d hd hg => ?_⟩
          rcases List.mem_append.1 hd with hd | hd
          · exact hno d hd hg
          · rw [List.mem_singleton] at hd
            subst hd
            obtain ⟨k, h₁, h₂, φ, hφ⟩ := hg
            rw [size_subG] at h₁
            subst h₁
            exact hnone.1 rfl ⟨φ, hφ⟩
      · obtain ⟨-, φ, hφ, hv⟩ := hsome iso rfl
        refine ⟨(some (ds, iso), kept), ?_, ?_⟩
        · apply RunsWithin.mono
          case h =>
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_with RunsWithin.caseOption_eq_none rfl _
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            run_with RunsWithin.ite_pos heq _
            run_step hsub
            run_step hrun
            run_with RunsWithin.caseOption_eq_some rfl _
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            exact RunsWithin.prim_le rfl le_rfl
          case hc =>
            simp only [Prim.cost, Args.head_cons, partnerCost]
            omega
        · simp only [PartnerInv]
          exact ⟨(hp.cons ds).trans (List.perm_append_singleton ds pre).symm, hl, φ, hφ, hv⟩
    · have hne : (ds.length == cs.length) = false := by simpa using hl
      refine ⟨(none, ds :: kept), ?_, ?_⟩
      · apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.caseOption_eq_none rfl _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg hne _
          exact RunsWithin.ret (t := Ty.findSt) _
        case hc =>
          simp only [Prim.cost, Args.head_cons, partnerCost]
          omega
      · simp only [PartnerInv]
        refine ⟨hp', fun d hd hg => ?_⟩
        rcases List.mem_append.1 hd with hd | hd
        · exact hno d hd hg
        · rw [List.mem_singleton] at hd
          subst hd
          obtain ⟨k, h₁, h₂, -⟩ := hg
          rw [size_subG] at h₁ h₂
          exact hl (h₂.trans h₁.symm)
  · simp only [PartnerInv] at hI
    obtain ⟨hp, hok⟩ := hI
    refine ⟨(some (d₀, iso₀), ds :: kept), ?_, ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOption_eq_some rfl _
        exact RunsWithin.ret (t := Ty.findSt) _
      case hc =>
        simp only [Prim.cost, partnerCost]
        omega
    · simp only [PartnerInv]
      exact ⟨(List.Perm.swap ds d₀ kept).trans ((hp.cons ds).trans
        (List.perm_append_singleton ds pre).symm), hok⟩

theorem RunsWithin.matchStepProg {cs : List ℕ} {rest : List (List ℕ)}
    {st : Option (List (List ℕ × List ℕ × Array ℕ) × List (List ℕ))}
    (hI : MatchInv n X Y (cs :: rest) st) :
    ∃ st', RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Valence.matchStepProg (D := Ty.unit) Δ X Y st cs) st' (matchCost Δ B n) ∧
      MatchInv n X Y rest st' := by
  rcases st with _ | ⟨M, U⟩
  · refine ⟨none, ?_, hI⟩
    apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseOption_none _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, matchCost]
      omega
  simp only [MatchInv] at hI
  obtain ⟨hx, hy, hM, hbal⟩ := hI
  have hcs : cs ∈ comps n X := hx.mem_iff.1 (List.mem_append_right _ List.mem_cons_self)
  have hU : ∀ ds ∈ U, ds ∈ comps n Y := fun ds h => hy.mem_iff.1 (List.mem_append_right _ h)
  have hUlen : U.length ≤ n := by
    have := hy.length_eq
    have := length_comps_le (N := n) (G := Y)
    simp only [List.length_append, List.length_map] at *
    omega
  obtain ⟨r, hfold, hr⟩ := RunsWithin.foldList_exists (X := ssCtx)
    (body := luksBody Ty.unit Ty.denote) (a' := .list .nat) (b' := Ty.findSt)
    (f := fun s ds => Valence.partnerStepProg (D := Ty.unit) Δ Y cs (subG X cs) s ds)
    (I := PartnerInv X Y cs) (c := partnerCost Δ B n) U [] (none, [])
    (fun _ _ ds hds hI => RunsWithin.partnerStepProg hX hY hΔ₂ hc hc1 hBm hcs (hU ds hds) hI)
    (by simp [PartnerInv])
  rw [List.nil_append] at hr
  have hsubA := Valence.RunsWithin.subGProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote)
    hX.deg cs
  have hsc : subGCost Δ cs.length ≤ subGCost Δ n := subGCost_mono (length_le_of_mem_comps hcs)
  have hfc : U.length * (partnerCost Δ B n + 1) ≤ n * (partnerCost Δ B n + 1) :=
    Nat.mul_le_mul_right _ hUlen
  obtain ⟨f, kept⟩ := r
  rcases f with _ | ⟨ds, iso⟩
  · simp only [PartnerInv] at hr
    refine ⟨none, ?_, fun hiso => ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hsubA
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hfold
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOption_eq_none rfl _
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, matchCost]
        omega
    · obtain ⟨ds, hds, hg⟩ := (hbal hiso).exists
      exact hr.2 ds hds hg
  · simp only [PartnerInv] at hr
    obtain ⟨hp, hok⟩ := hr
    refine ⟨some ((cs, ds, iso) :: M, kept), ?_, ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hsubA
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hfold
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOption_eq_some rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, matchCost]
        omega
    · simp only [MatchInv]
      refine ⟨?_, ?_, fun t ht => ?_, fun hiso => (hbal hiso).step hp hok.giso⟩
      · simp only [List.map_cons, List.cons_append]
        exact List.perm_middle.symm.trans hx
      · simp only [List.map_cons, List.cons_append]
        exact List.perm_middle.symm.trans ((hp.append_left _).trans hy)
      · rcases List.mem_cons.1 ht with rfl | ht
        · exact hok
        · exact hM t ht

/-- **Isomorphism of graphs of maximum degree five, connected or not.** With the
Schreier–Sims backend, for valid data, the result is `none` exactly when `X` and `Y` are not
isomorphic, and otherwise lists the values of an isomorphism. -/
theorem RunsWithin.allProg :
    ∃ res, RunsWithin ssCtx (luksBody Ty.unit Ty.denote)
        (Valence.allProg (D := Ty.unit) Δ n X Y) res (allCost Δ B n) ∧
      (res = none ↔ ¬ ∃ φ, IsIso n X Y φ) ∧
      ∀ arr, res = some arr → arr.size = n ∧
        ∃ φ : Perm (Fin n), IsIso n X Y φ ∧ ∀ v < n, get arr v = act φ v := by
  have hcX := Valence.RunsWithin.compsProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hX
  have hcY := Valence.RunsWithin.compsProg (X := ssCtx) (body := luksBody Ty.unit Ty.denote) hY
  have hlenX := length_comps_le (N := n) (G := X)
  obtain ⟨st, hfold, hst⟩ := RunsWithin.foldList_rest (X := ssCtx)
    (body := luksBody Ty.unit Ty.denote) (a' := .list .nat) (b' := Ty.matchSt)
    (f := fun st cs => Valence.matchStepProg (D := Ty.unit) Δ X Y st cs) (I := MatchInv n X Y)
    (c := matchCost Δ B n) (comps n X) (some ([], comps n Y))
    (fun _ _ _ hI => RunsWithin.matchStepProg hX hY hΔ₂ hc hc1 hBm hI)
    (by
      simp only [MatchInv]
      exact ⟨by simp, by simp, by simp, fun ⟨_, hφ⟩ => balanced_comps hX hY hφ⟩)
  have hfc : (comps n X).length * (matchCost Δ B n + 1) ≤ n * (matchCost Δ B n + 1) :=
    Nat.mul_le_mul_right _ hlenX
  rcases st with _ | ⟨M, U⟩
  · simp only [MatchInv] at hst
    refine ⟨none, ?_, ⟨fun _ => hst, fun _ => rfl⟩, fun arr h => by cases h⟩
    apply RunsWithin.mono
    case h =>
      run_step hcX
      run_step hcY
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_with RunsWithin.caseOption_none _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, allCost]
      omega
  simp only [MatchInv] at hst
  obtain ⟨hx, hy, hM, hbal⟩ := hst
  rcases U with _ | ⟨d, U⟩
  · rw [List.append_nil] at hx hy
    have hws : List.Perm (M.foldl glueStep []) (M.flatMap glueWrites) := by
      simpa using perm_foldl_glueStep M []
    obtain ⟨hsize, φ, hφ, hv⟩ := glue_spec hX hY hx hy hM hws
    have hMb : ∀ t ∈ M, t.1.length ≤ n ∧ t.2.1.length ≤ n := fun t ht =>
      ⟨length_le_of_mem_comps (hx.mem_iff.1 (List.mem_map_of_mem ht)),
        length_le_of_mem_comps (hy.mem_iff.1 (List.mem_map_of_mem ht))⟩
    have hMl : M.length ≤ n := by
      have := hx.length_eq
      rw [List.length_map] at this
      omega
    refine ⟨some (glue n (M.foldl glueStep [])), ?_,
      ⟨fun h => (Option.some_ne_none _ h).elim, fun h => absurd ⟨φ, hφ⟩ h⟩, fun arr harr => ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_step hcX
        run_step hcY
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hfold
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_nil _
        run_step (RunsWithin.glueProg hMb hMl)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, allCost]
        omega
    · cases harr
      exact ⟨hsize, φ, hφ, hv⟩
  · refine ⟨none, ?_, ⟨fun _ hiso => List.cons_ne_nil d U (hbal hiso).eq_nil, fun _ => rfl⟩,
      fun arr h => by cases h⟩
    apply RunsWithin.mono
    case h =>
      run_step hcX
      run_step hcY
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_with RunsWithin.caseOption_some _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_cons _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, allCost]
      omega

end Main

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {var₁ var₂ : Ty → Type} {Γ : WfCtx var₁ var₂}

theorem wf_partnerStepProg (Δ : ℕ) {Y₁ A₁ : var₁ Ty.graph} {Y₂ A₂ : var₂ Ty.graph}
    {cs₁ ds₁ : var₁ (.list .nat)} {cs₂ ds₂ : var₂ (.list .nat)} {st₁ : var₁ Ty.findSt}
    {st₂ : var₂ Ty.findSt} (hY : ⟨Ty.graph, Y₁, Y₂⟩ ∈ Γ) (hcs : ⟨.list .nat, cs₁, cs₂⟩ ∈ Γ)
    (hA : ⟨Ty.graph, A₁, A₂⟩ ∈ Γ) (hst : ⟨Ty.findSt, st₁, st₂⟩ ∈ Γ)
    (hds : ⟨.list .nat, ds₁, ds₂⟩ ∈ Γ) :
    Prog.Wf true Γ (partnerStepProg (D := D) Δ Y₁ cs₁ A₁ st₁ ds₁)
      (partnerStepProg (D := D) Δ Y₂ cs₂ A₂ st₂ ds₂) := by
  unfold partnerStepProg
  exact .bind (.prim _ (.cons hst .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hst]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hds]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .caseOption (by simp)
      (.bind (.prim _ (.cons (by simp [hds]) .nil)) fun _ _ =>
        .bind (.prim _ (.cons (by simp [hcs]) .nil)) fun _ _ =>
        .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
        .ite (List.Mem.head _)
          (.bind (wf_subGProg (by simp [hY]) (by simp [hds])) fun _ _ =>
            .bind (wf_mainProg Δ (by simp) (by simp [hA]) (List.Mem.head _)) fun _ _ =>
            .caseOption (List.Mem.head _) (.ret (by simp)) fun _ _ =>
              .bind (.prim _ (.cons (by simp [hds]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
              .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
              .prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil)))
          (.ret (by simp)))
      fun _ _ => .ret (by simp)

theorem wf_matchStepProg (Δ : ℕ) {X₁ Y₁ : var₁ Ty.graph} {X₂ Y₂ : var₂ Ty.graph}
    {st₁ : var₁ Ty.matchSt} {st₂ : var₂ Ty.matchSt} {cs₁ : var₁ (.list .nat)}
    {cs₂ : var₂ (.list .nat)} (hX : ⟨Ty.graph, X₁, X₂⟩ ∈ Γ) (hY : ⟨Ty.graph, Y₁, Y₂⟩ ∈ Γ)
    (hst : ⟨Ty.matchSt, st₁, st₂⟩ ∈ Γ) (hcs : ⟨.list .nat, cs₁, cs₂⟩ ∈ Γ) :
    Prog.Wf true Γ (matchStepProg (D := D) Δ X₁ Y₁ st₁ cs₁)
      (matchStepProg (D := D) Δ X₂ Y₂ st₂ cs₂) := by
  unfold matchStepProg
  exact .caseOption hst (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_subGProg (by simp [hX]) (by simp [hcs])) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (.foldList (by simp) (List.Mem.head _) fun _ _ _ _ =>
      wf_partnerStepProg Δ (by simp [hY]) (by simp [hcs]) (by simp) (List.Mem.head _)
        (by simp))
      fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .caseOption (by simp) (.prim _ .nil) fun _ _ =>
      .bind (.prim _ (.cons (by simp [hcs]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
      .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ =>
      .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ =>
      .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_allProg (Δ : ℕ) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {X₁ Y₁ : var₁ Ty.graph}
    {X₂ Y₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hX : ⟨Ty.graph, X₁, X₂⟩ ∈ Γ)
    (hY : ⟨Ty.graph, Y₁, Y₂⟩ ∈ Γ) :
    Prog.Wf true Γ (allProg (D := D) Δ n₁ X₁ Y₁) (allProg (D := D) Δ n₂ X₂ Y₂) := by
  unfold allProg
  exact .bind (wf_compsProg hn hX) fun _ _ =>
    .bind (wf_compsProg (by simp [hn]) (by simp [hY])) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.foldList (by simp) (List.Mem.head _) fun _ _ _ _ =>
      wf_matchStepProg Δ (by simp [hX]) (by simp [hY]) (List.Mem.head _) (by simp)) fun _ _ =>
    .caseOption (List.Mem.head _) (.prim _ .nil) fun _ _ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .caseList (List.Mem.head _)
        (.bind (wf_glueProg (by simp [hn]) (by simp)) fun _ _ =>
          .prim _ (.cons (List.Mem.head _) .nil))
        fun _ _ _ _ => .prim _ .nil

end Wf

end GraphIso.Graph.Valence
