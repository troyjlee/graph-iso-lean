module

public import GraphIso.Valence.Algorithm
public import GraphIso.Graph.Entry

/-!
# Well-formedness of the algorithm for maximum degree `Δ`

The well-formedness of the composite programs, recursion allowed (their recursive calls are
the string-isomorphism solver's, inside `solveEntry`): the instance builder
(`wf_stepInputProg`), the layer step (`wf_stepProg`), the edge test (`wf_edgeProg`) and the
algorithm (`wf_mainProg`). The checked entries (`GraphIso/Solver/Valence.lean`) are built on
them.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Cost Programs

section Wf

variable {D : Ty} {var₁ var₂ : Ty → Type} {Γ : WfCtx var₁ var₂}

theorem wf_stepInputProg (Δ : ℕ) {S : Signature} {rec : Ty × Ty} {b : Bool}
    {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat} {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph}
    {l₁ : var₁ (.array .nat)} {l₂ : var₂ (.array .nat)} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ)
    (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) b Γ (stepInputProg Δ N₁ G₁ l₁ r₁ g₁)
      (stepInputProg Δ N₂ G₂ l₂ r₂ g₂) := by
  unfold stepInputProg
  refine .bind (wf_levListProg hN hl hr) fun Lr₁ Lr₂ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hr]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (wf_levListProg (by simp [hN]) (by simp [hl]) (List.Mem.head _)) fun New₁ New₂ =>
    .bind (wf_subsProg Δ (by simp)) fun Sb₁ Sb₂ =>
    .bind (wf_mapList (by simp [hg]) fun Γ' hΓ _ _ hx => wf_indProg (hΓ (by simp [hN]))
      (hΓ (by simp)) hx) fun _ _ =>
    .bind (wf_xArrProg Δ (by simp [hG]) (by simp [hl]) (by simp [hN]) (by simp [hr]) (by simp)
      (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hN]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (List.Mem.head _) fun Γ' hΓ _ _ hx =>
      .prim _ (.cons (hΓ (by simp [hN])) (.cons hx .nil))) fun _ _ =>
    .bind (wf_mkWindow (by simp) (List.Mem.head _)) fun _ _ =>
    .bind (wf_permOne (by simp)) fun _ _ => ?_
  prog_wf

theorem wf_stepProg (Δ : ℕ) {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat} {G₁ : var₁ Ty.graph}
    {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)} {l₂ : var₂ (.array .nat)}
    {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf true Γ (stepProg Δ (D := D) N₁ G₁ l₁ r₁ g₁) (stepProg Δ (D := D) N₂ G₂ l₂ r₂ g₂) := by
  unfold stepProg
  refine .bind (wf_stepInputProg Δ hN hG hl hr hg) fun i₁ i₂ => .bind ?_ fun a₁ a₂ => ?_
  · exact (Solver.solveEntry_wf i₁ i₂).weaken fun e he => by
      simp only [List.mem_singleton] at he
      subst he
      exact List.Mem.head _
  · unfold Graph.stepOutProg
    prog_wf

theorem wf_edgeProg (Δ : ℕ) {n₁ N₁ a₁ b₁ a₁' b₁' : var₁ .nat} {n₂ N₂ a₂ b₂ a₂' b₂' : var₂ .nat}
    {Z₁ : var₁ Ty.graph} {Z₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hZ : ⟨Ty.graph, Z₁, Z₂⟩ ∈ Γ) (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ)
    (hb : ⟨.nat, b₁, b₂⟩ ∈ Γ) (ha' : ⟨.nat, a₁', a₂'⟩ ∈ Γ) (hb' : ⟨.nat, b₁', b₂'⟩ ∈ Γ) :
    Prog.Wf true Γ (edgeProg Δ (D := D) n₁ N₁ Z₁ a₁ b₁ a₁' b₁')
      (edgeProg Δ (D := D) n₂ N₂ Z₂ a₂ b₂ a₂' b₂') := by
  unfold edgeProg
  refine .bind (.prim _ (.cons hn (.cons ha' .nil))) fun c₁ c₂ =>
    .bind (.prim _ (.cons (by simp [hn]) (.cons (by simp [hb']) .nil))) fun d₁ d₂ =>
    .bind (.prim _ .nil) fun nl₁ nl₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun l₁ l₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun l₁' l₂' =>
    .bind (.prim _ (.cons (by simp [hb]) (.cons (List.Mem.head _) .nil))) fun l₁'' l₂'' =>
    .bind (.prim _ (.cons (by simp [ha]) (.cons (List.Mem.head _) .nil))) fun R₁ R₂ =>
    .bind (wf_levelsProg (by simp [hN]) (by simp [hZ]) (List.Mem.head _)) fun lv₁ lv₂ =>
    .bind (by unfold gens0Prog swapProg swapFProg permMul mapArray mapList; prog_wf)
      fun s₁ s₂ =>
    .bind (.prim _ (.cons (by simp [hN]) .nil)) fun rN₁ rN₂ =>
    .bind (.foldList (List.Mem.head _) (by simp) fun gs₁ gs₂ r₁ r₂ =>
      wf_stepProg Δ (by simp [hN]) (by simp [hZ]) (by simp) (by simp) (List.Mem.head _))
      fun gN₁ gN₂ => ?_
  unfold findProg findStepProg testProg permApply isoArrProg mapList
  prog_wf

theorem wf_mainProg (Δ : ℕ) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {X₁ Y₁ : var₁ Ty.graph}
    {X₂ Y₂ : var₂ Ty.graph} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hX : ⟨Ty.graph, X₁, X₂⟩ ∈ Γ)
    (hY : ⟨Ty.graph, Y₁, Y₂⟩ ∈ Γ) :
    Prog.Wf true Γ (mainProg Δ (D := D) n₁ X₁ Y₁) (mainProg Δ (D := D) n₂ X₂ Y₂) := by
  unfold mainProg
  refine .bind (.prim _ (.cons hn (.cons hn .nil))) fun N₁ N₂ =>
    .bind (wf_unionProg (by simp [hn]) (by simp [hX]) (by simp [hY])) fun Z₁ Z₂ =>
    .bind (.prim _ .nil) fun a₁ a₂ =>
    .bind (.prim _ (.cons (by simp [hX]) (.cons (List.Mem.head _) .nil))) fun s₁ s₂ =>
    .caseList (List.Mem.head _) (by prog_wf) fun b₁ b₂ _ _ =>
    .bind (by unfold edgesProg; prog_wf) fun es₁ es₂ =>
    .bind (.prim _ .nil) fun nn₁ nn₂ =>
    .foldList (by simp) (List.Mem.head _) fun acc₁ acc₂ e₁ e₂ => ?_
  unfold edgeStepProg
  refine .caseOption (List.Mem.head _) ?_ fun _ _ => .ret (by simp)
  exact .bind (.prim _ (.cons (by simp) .nil)) fun a₁' a₂' =>
    .bind (.prim _ (.cons (by simp) .nil)) fun b₁' b₂' =>
    wf_edgeProg Δ (by simp [hn]) (by simp) (by simp) (by simp) (by simp) (by simp)
      (List.Mem.head _)

end Wf

end GraphIso.Graph.Valence
