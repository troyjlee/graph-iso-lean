module

public import GraphIso.Sims.CosetsProg

/-!
# Well-formedness of the Schreier–Sims programs

Each program is related to itself at any two variable instantiations, with recursion
forbidden (`Prog.Wf false`), whenever its arguments are related by the context. Leaf programs
are checked by `prog_wf`; composite programs combine the lemmas of their parts.
-/

@[expose] public section

namespace GraphIso.Sims

open Cost Programs

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_siftProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {T₁ : var₁ Ty.table} {T₂ : var₂ Ty.table} {k₁ : var₁ .nat}
    {k₂ : var₂ .nat} {x₁ : var₁ Ty.perm} {x₂ : var₂ Ty.perm} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) (hT : ⟨Ty.table, T₁, T₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hx : ⟨Ty.perm, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (siftProg n₁ b₁ T₁ k₁ x₁) (siftProg n₂ b₂ T₂ k₂ x₂) := by
  unfold siftProg siftBody permApply permInv permMul mapArray mapList
  prog_wf

theorem wf_fillProg {T₁ : var₁ Ty.table} {T₂ : var₂ Ty.table} {k₁ j₁ : var₁ .nat}
    {k₂ j₂ : var₂ .nat} {h₁ : var₁ Ty.perm} {h₂ : var₂ Ty.perm} (hT : ⟨Ty.table, T₁, T₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) (hh : ⟨Ty.perm, h₁, h₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (fillProg T₁ k₁ j₁ h₁) (fillProg T₂ k₂ j₂ h₂) := by
  unfold fillProg
  prog_wf

theorem wf_newItemsProg {k₁ : var₁ .nat} {k₂ : var₂ .nat} {h₁ : var₁ Ty.perm}
    {h₂ : var₂ Ty.perm} {e₁ : var₁ (.list Ty.item)} {e₂ : var₂ (.list Ty.item)}
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hh : ⟨Ty.perm, h₁, h₂⟩ ∈ Γ) (he : ⟨.list Ty.item, e₁, e₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (newItemsProg k₁ h₁ e₁) (newItemsProg k₂ h₂ e₂) := by
  unfold newItemsProg newItemsBody permMul mapArray mapList
  prog_wf

theorem wf_stepBody {n₁ : var₁ .nat} {n₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {s₁ : var₁ Ty.state} {s₂ : var₂ Ty.state}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) (hs : ⟨Ty.state, s₁, s₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (stepBody n₁ b₁ s₁) (stepBody n₂ b₂ s₂) := by
  unfold stepBody
  refine .bind (.prim _ (.cons hs .nil)) fun T₁ T₂ => .bind (.prim _ (.cons (by simp [hs]) .nil))
    fun ep₁ ep₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun ent₁ ent₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun pend₁ pend₂ =>
    .caseList (List.Mem.head _) (.prim _ .nil) fun it₁ it₂ rest₁ rest₂ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun k₁ k₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun x₁ x₂ =>
    .bind (wf_siftProg (by simp [hn]) (by simp [hb]) (by simp) (by simp) (List.Mem.head _))
      fun r₁ r₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun k'₁ k'₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp [hn]) .nil))) fun f₁ f₂ =>
    .ite (List.Mem.head _) ?_ ?_
  · refine .bind (.prim _ (.cons (by simp) .nil)) fun h₁ h₂ =>
      .bind (.prim _ (.cons (by simp [hb]) (.cons (by simp) .nil))) fun bk₁ bk₂ =>
      .bind (wf_permApply (by simp) (List.Mem.head _)) fun j₁ j₂ =>
      .bind (wf_fillProg (by simp) (by simp) (List.Mem.head _) (by simp)) fun T'₁ T'₂ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun e₁ e₂ =>
      .bind (wf_newItemsProg (by simp) (by simp) (List.Mem.head _)) fun nw₁ nw₂ =>
      .bind (.prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))) fun p₁ p₂ =>
      .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun ep₁ ep₂ =>
      .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun st₁ st₂ =>
      .prim _ (.cons (List.Mem.head _) .nil)
  · prog_wf

theorem wf_initProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (initProg n₁ b₁ g₁) (initProg n₂ b₂ g₂) := by
  unfold initProg initTableProg permOne mapList
  prog_wf

theorem wf_buildProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (buildProg n₁ b₁ g₁) (buildProg n₂ b₂ g₂) := by
  unfold buildProg
  exact .bind (wf_initProg hn hb hg) fun s₁ s₂ => .loop (List.Mem.head _) fun v₁ v₂ =>
    wf_stepBody (by simp [hn]) (by simp [hb]) (List.Mem.head _)

theorem wf_frontBaseProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (frontBaseProg n₁ w₁) (frontBaseProg n₂ w₂) := by
  unfold frontBaseProg
  prog_wf

theorem wf_emptyWinProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (emptyWinProg n₁) (emptyWinProg n₂) := by
  unfold emptyWinProg
  prog_wf

theorem wf_pointWinProg {n₁ u₁ : var₁ .nat} {n₂ u₂ : var₂ .nat} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (pointWinProg n₁ u₁) (pointWinProg n₂ u₂) := by
  unfold pointWinProg
  prog_wf

theorem wf_tableEntriesProg {n₁ k₁ : var₁ .nat} {n₂ k₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tableEntriesProg n₁ b₁ g₁ k₁)
      (tableEntriesProg n₂ b₂ g₂ k₂) := by
  unfold tableEntriesProg
  refine .bind (wf_buildProg hn hb hg) fun s₁ s₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil))
    fun ep₁ ep₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun e₁ e₂ => ?_
  unfold entriesFromProg
  prog_wf

theorem wf_groupOfProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {h₁ : var₁ Ty.gens} {h₂ : var₂ Ty.gens}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hh : ⟨Ty.gens, h₁, h₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (groupOfProg n₁ h₁) (groupOfProg n₂ h₂) := by
  unfold groupOfProg
  prog_wf

theorem wf_generateProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (generateProg n₁ g₁) (generateProg n₂ g₂) := by
  unfold generateProg
  exact .bind (wf_emptyWinProg hn) fun w₁ w₂ =>
    .bind (wf_frontBaseProg (by simp [hn]) (List.Mem.head _)) fun b₁ b₂ =>
    .bind (.prim _ .nil) fun z₁ z₂ =>
    .bind (wf_tableEntriesProg (by simp [hn]) (by simp) (by simp [hg]) (List.Mem.head _))
      fun h₁ h₂ => wf_groupOfProg (by simp [hn]) (List.Mem.head _)

theorem wf_stabProg {n₁ u₁ : var₁ .nat} {n₂ u₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (stabProg n₁ g₁ u₁) (stabProg n₂ g₂ u₂) := by
  unfold stabProg
  exact .bind (wf_pointWinProg hn hu) fun w₁ w₂ =>
    .bind (wf_frontBaseProg (by simp [hn]) (List.Mem.head _)) fun b₁ b₂ =>
    .bind (.prim _ .nil) fun z₁ z₂ =>
    .bind (wf_tableEntriesProg (by simp [hn]) (by simp) (by simp [hg]) (List.Mem.head _))
      fun h₁ h₂ => wf_groupOfProg (by simp [hn]) (List.Mem.head _)

theorem wf_kernelProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (kernelProg n₁ g₁ w₁) (kernelProg n₂ g₂ w₂) := by
  unfold kernelProg
  exact .bind (wf_frontBaseProg hn hw) fun b₁ b₂ =>
    .bind (.prim _ (.cons (by simp [hw]) .nil)) fun p₁ p₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun m₁ m₂ =>
    .bind (wf_tableEntriesProg (by simp [hn]) (by simp) (by simp [hg]) (List.Mem.head _))
      fun h₁ h₂ => wf_groupOfProg (by simp [hn]) (List.Mem.head _)

theorem wf_memProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    {π₁ : var₁ Ty.perm} {π₂ : var₂ Ty.perm} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hπ : ⟨Ty.perm, π₁, π₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (memProg n₁ g₁ π₁) (memProg n₂ g₂ π₂) := by
  unfold memProg
  exact .bind (wf_emptyWinProg hn) fun w₁ w₂ =>
    .bind (wf_frontBaseProg (by simp [hn]) (List.Mem.head _)) fun b₁ b₂ =>
    .bind (wf_buildProg (by simp [hn]) (List.Mem.head _) (by simp [hg])) fun s₁ s₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun T₁ T₂ =>
    .bind (.prim _ .nil) fun z₁ z₂ =>
    .bind (wf_siftProg (by simp [hn]) (by simp) (by simp) (List.Mem.head _) (by simp [hπ]))
      fun q₁ q₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun k₁ k₂ =>
    .prim _ (.cons (List.Mem.head _) (.cons (by simp [hn]) .nil))

theorem wf_liftProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} {π₁ : var₁ Ty.perm} {π₂ : var₂ Ty.perm}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hπ : ⟨Ty.perm, π₁, π₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (liftProg n₁ g₁ w₁ π₁) (liftProg n₂ g₂ w₂ π₂) := by
  unfold liftProg
  refine .bind (wf_frontBaseProg hn hw) fun b₁ b₂ =>
    .bind (wf_buildProg (by simp [hn]) (List.Mem.head _) (by simp [hg])) fun s₁ s₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun T₁ T₂ =>
    .bind (.prim _ (.cons (by simp [hw]) .nil)) fun p₁ p₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun a₁ a₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun m₁ m₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun i₁ i₂ =>
    .bind (wf_permOne (by simp [hn])) fun e₁ e₂ =>
    .foldList (by simp) (List.Mem.head _) fun c₁ c₂ j₁ j₂ => ?_
  unfold liftBody permApply permMul mapArray mapList
  prog_wf

theorem wf_orbitBFSProg {n₁ u₁ : var₁ .nat} {n₂ u₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (orbitBFSProg n₁ g₁ u₁) (orbitBFSProg n₂ g₂ u₂) := by
  unfold orbitBFSProg orbitStepBody visitBody permOne permApply permMul mapArray mapList
  prog_wf

theorem wf_orbitsProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (orbitsProg n₁ g₁ w₁) (orbitsProg n₂ g₂ w₂) := by
  unfold orbitsProg
  refine .bind (.prim _ .nil) fun f₁ f₂ => .bind (.prim _ (.cons (by simp [hn])
    (.cons (List.Mem.head _) .nil))) fun s₁ s₂ => .bind (.prim _ .nil) fun l₁ l₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun a₁ a₂ =>
    .bind (.prim _ (.cons (by simp [hw]) .nil)) fun p₁ p₂ =>
    .bind (.foldList (List.Mem.head _) (by simp) fun c₁ c₂ x₁ x₂ => ?_) fun e₁ e₂ =>
    .prim _ (.cons (List.Mem.head _) .nil)
  unfold orbitsBody
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun t₁ t₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun o₁ o₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun m₁ m₂ =>
    .ite (List.Mem.head _) (.ret (by simp)) ?_
  refine .bind (wf_orbitBFSProg (by simp [hn]) (by simp [hg]) (by simp)) fun q₁ q₂ => ?_
  unfold mapList
  prog_wf

theorem wf_coveredProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {b₁ : var₁ (.array .nat)}
    {b₂ : var₂ (.array .nat)} {T₁ : var₁ Ty.table} {T₂ : var₂ Ty.table} {rs₁ : var₁ Ty.gens}
    {rs₂ : var₂ Ty.gens} {x₁ : var₁ Ty.perm} {x₂ : var₂ Ty.perm} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hb : ⟨.array .nat, b₁, b₂⟩ ∈ Γ) (hT : ⟨Ty.table, T₁, T₂⟩ ∈ Γ)
    (hrs : ⟨Ty.gens, rs₁, rs₂⟩ ∈ Γ) (hx : ⟨Ty.perm, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (coveredProg n₁ b₁ T₁ rs₁ x₁)
      (coveredProg n₂ b₂ T₂ rs₂ x₂) := by
  unfold coveredProg anyList
  refine .bind (.prim _ .nil) fun f₁ f₂ =>
    .foldList (by simp [hrs]) (List.Mem.head _) fun c₁ c₂ y₁ y₂ => ?_
  refine .bind ?_ fun d₁ d₂ => .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))
  refine .bind (wf_permInv (by simp)) fun i₁ i₂ =>
    .bind (wf_permMul (List.Mem.head _) (by simp [hx])) fun z₁ z₂ =>
    .bind (.prim _ .nil) fun o₁ o₂ =>
    .bind (wf_siftProg (by simp [hn]) (by simp [hb]) (by simp [hT]) (List.Mem.head _) (by simp))
      fun q₁ q₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun k₁ k₂ =>
    .prim _ (.cons (List.Mem.head _) (.cons (by simp [hn]) .nil))

theorem wf_cosetRepsProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ k₁ : var₁ Ty.gens}
    {g₂ k₂ : var₂ Ty.gens} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hk : ⟨Ty.gens, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cosetRepsProg n₁ g₁ k₁) (cosetRepsProg n₂ g₂ k₂) := by
  unfold cosetRepsProg
  refine .bind (wf_emptyWinProg hn) fun w₁ w₂ =>
    .bind (wf_frontBaseProg (by simp [hn]) (List.Mem.head _)) fun b₁ b₂ =>
    .bind (wf_buildProg (by simp [hn]) (List.Mem.head _) (by simp [hk])) fun s₁ s₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun T₁ T₂ =>
    .bind (wf_permOne (by simp [hn])) fun e₁ e₂ =>
    .bind (.prim _ .nil) fun l₁ l₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun c₁ c₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) (.cons (List.Mem.head _) .nil))) fun st₁ st₂ =>
    .bind (.loop (List.Mem.head _) fun v₁ v₂ => ?_) fun f₁ f₂ =>
    .prim _ (.cons (List.Mem.head _) .nil)
  unfold repsStepBody
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun rp₁ rp₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun q₁ q₂ =>
    .caseList (List.Mem.head _) (.prim _ .nil) fun x₁ x₂ xs₁ xs₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun a₁ a₂ =>
    .bind (.foldList (by simp [hg]) (List.Mem.head _) fun c₁ c₂ y₁ y₂ => ?_) fun z₁ z₂ =>
    .prim _ (.cons (List.Mem.head _) .nil)
  unfold repsVisitBody
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun t₁ t₂ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun u₁ u₂ =>
    .bind (wf_permMul (by simp) (by simp)) fun x₁ x₂ =>
    .bind (wf_coveredProg (by simp [hn]) (by simp) (by simp) (by simp) (List.Mem.head _))
      fun cv₁ cv₂ => .ite (List.Mem.head _) (.ret (by simp)) ?_
  prog_wf

end Wf

end GraphIso.Sims
