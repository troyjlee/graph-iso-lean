module

public import GraphIso.Graph.Components

/-!
# Programs for components

* `compsProg N G`: the components, by one level computation from each point; a point
  contributes its component when it reaches no smaller point. It computes `comps N G`
  (`RunsWithin.compsProg`) at cost at most `compsCost N`.
* `subGProg G cs`: the component data `subG G cs`, within `subGCost cs.length`.
* `glueProg n M`: the glued array of the matched pairs `M`, `glue n ws` for a write list `ws`
  that is a permutation of `M.flatMap glueWrites` (`RunsWithin.glueProg`).
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims

/-- Matched components: `(cs, ds, values of an isomorphism of their data)`. -/
abbrev Ty.cmatch : Ty := .prod (.list .nat) (.prod (.list .nat) (.array .nat))

/-! ### Models -/

/-- One step of the component fold: the component of `u` if `u` is a representative. -/
def compStep (n : ℕ) (G : GraphData) (acc : List (List ℕ)) (u : ℕ) : List (List ℕ) :=
  if (List.range u).any (fun v => decide (get (levels n G [u]) v < n)) then acc
  else compOf n G u :: acc

theorem foldl_compStep (n : ℕ) (G : GraphData) : ∀ (l : List ℕ) (acc : List (List ℕ)),
    l.foldl (compStep n G) acc = ((l.filter (isRep n G)).map (compOf n G)).reverse ++ acc
  | [], acc => rfl
  | u :: l, acc => by
    rw [List.foldl_cons, foldl_compStep n G l]
    unfold compStep
    cases h : (List.range u).any fun v => decide (get (levels n G [u]) v < n) <;>
      simp [isRep, h]

theorem comps_eq_fold (n : ℕ) (G : GraphData) :
    ((List.range n).foldl (compStep n G) []).reverse = comps n G := by
  rw [foldl_compStep, List.append_nil, List.reverse_reverse, comps, reps]

/-- One write of a matched pair, prepended. -/
def writeStep (t : List ℕ × List ℕ × Array ℕ) (acc : List (ℕ × ℕ)) (i : ℕ) : List (ℕ × ℕ) :=
  (t.1.getD i 0, t.2.1.getD (get t.2.2 i) 0) :: acc

/-- The writes of a matched pair, prepended in reverse. -/
def glueStep (acc : List (ℕ × ℕ)) (t : List ℕ × List ℕ × Array ℕ) : List (ℕ × ℕ) :=
  (List.range t.1.length).foldl (writeStep t) acc

theorem foldl_writeStep (t : List ℕ × List ℕ × Array ℕ) : ∀ (l : List ℕ) (acc : List (ℕ × ℕ)),
    l.foldl (writeStep t) acc =
      (l.map fun i => (t.1.getD i 0, t.2.1.getD (get t.2.2 i) 0)).reverse ++ acc
  | [], acc => rfl
  | i :: l, acc => by
    rw [List.foldl_cons, foldl_writeStep t l]
    simp [writeStep]

theorem glueStep_eq (acc : List (ℕ × ℕ)) (t : List ℕ × List ℕ × Array ℕ) :
    glueStep acc t = (glueWrites t).reverse ++ acc := by
  rw [glueStep, foldl_writeStep, glueWrites]

theorem perm_foldl_glueStep : ∀ (M : List (List ℕ × List ℕ × Array ℕ)) (acc : List (ℕ × ℕ)),
    List.Perm (M.foldl glueStep acc) (M.flatMap glueWrites ++ acc)
  | [], acc => by simp
  | t :: M, acc => by
    rw [List.foldl_cons, glueStep_eq, List.flatMap_cons, List.append_assoc]
    refine (perm_foldl_glueStep M _).trans ?_
    exact (((List.reverse_perm _).append_right acc).append_left _).trans
      (List.perm_append_comm_assoc _ _ _)

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One step of the component fold. -/
def compStepProg (N : var .nat) (G : var Ty.graph) (acc : var (.list (.list .nat)))
    (u : var .nat) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op0 .nil) fun nl => .bind (.op2 .cons u nl) fun roots =>
  .bind (levelsProg N G roots) fun lev =>
  .bind (.op1 .range u) fun ru =>
  .bind (anyList ru fun v => levLtProg lev N v) fun low =>
  .ite low (.ret acc)
    (.bind (.op1 .range N) fun rN =>
      .bind (Luks.filterList rN fun v => levLtProg lev N v) fun c => .op2 .cons c acc)

/-- **The components.** -/
def compsProg (N : var .nat) (G : var Ty.graph) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range N) fun rN => .bind (.op0 .nil) fun nl =>
  .bind (.foldList rN nl fun acc u => compStepProg N G acc u) fun cs => .op1 .reverse cs

/-- One row of the component data: the positions of the neighbours of `u`. -/
def subRowProg (G : var Ty.graph) (cs : var (.list .nat)) (u : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .arrayGet G u) fun ns => mapList ns fun w => idxOfProg cs w

/-- **The component data.** -/
def subGProg (G : var Ty.graph) (cs : var (.list .nat)) : Prog S rec var Ty.graph :=
  .bind (mapList cs fun u => subRowProg G cs u) fun rows => .op1 .arrayOfList rows

/-- One write of a matched pair. -/
def writeProg (cs ds : var (.list .nat)) (iso : var (.array .nat))
    (acc : var (.list (.prod .nat .nat))) (i : var .nat) :
    Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (getDProg cs i z) fun u =>
  .bind (.op2 .arrayGet iso i) fun j => .bind (getDProg ds j z) fun w =>
  .bind (.op2 .pair u w) fun uw => .op2 .cons uw acc

/-- The writes of a matched pair. -/
def glueStepProg (acc : var (.list (.prod .nat .nat))) (t : var Ty.cmatch) :
    Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op1 .fst t) fun cs => .bind (.op1 .snd t) fun di =>
  .bind (.op1 .fst di) fun ds => .bind (.op1 .snd di) fun iso =>
  .bind (.op1 .length cs) fun k => .bind (.op1 .range k) fun rk =>
  .foldList rk acc fun acc i => writeProg cs ds iso acc i

/-- **Gluing.** -/
def glueProg (n : var .nat) (M : var (.list Ty.cmatch)) : Prog S rec var (.array .nat) :=
  .bind (.op0 .nil) fun nl => .bind (.foldList M nl fun acc t => glueStepProg acc t) fun ws =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk n z) fun arr =>
  .op2 .arrayUpdate arr ws

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.levLtProg (lev : Array ℕ) (N v : ℕ) :
    RunsWithin X body (Graph.levLtProg lev N v) (decide (get lev v < N)) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl

/-- The cost bound of one step of the component fold. -/
def compStepCost (N : ℕ) : ℕ := levelsCost N 1 + 12 * N + 20

theorem RunsWithin.compStepProg {N : ℕ} {G : GraphData} (hG : G.Valid N)
    (acc : List (List ℕ)) {u : ℕ} (hu : u ≤ N) :
    RunsWithin X body (Graph.compStepProg N G acc u) (compStep N G acc u) (compStepCost N) := by
  have hany := RunsWithin.anyList_le (X := X) (body := body) (a' := .nat) (c := 2)
    (xs := List.range u)
    (P := fun v => decide (get (levels N G [u]) v < N)) fun v _ =>
      RunsWithin.levLtProg _ N v
  by_cases hb : ((List.range u).any fun v => decide (get (levels N G [u]) v < N)) = true
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.levelsProg hG _)
      run_step (RunsWithin.prim _ _)
      run_step hany
      run_with RunsWithin.ite_pos hb _
      exact (RunsWithin.ret (t := .list (.list .nat)) acc).of_eq
        (by simp only [compStep, hb, ↓reduceIte])
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_cons,
        List.length_nil, compStepCost]
      nlinarith
  · have hb' : ((List.range u).any fun v => decide (get (levels N G [u]) v < N)) = false := by
      simpa using hb
    have hfil := Luks.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (c := 2)
      (xs := List.range N)
      (P := fun v => decide (get (levels N G [u]) v < N)) fun v _ =>
        RunsWithin.levLtProg _ N v
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.levelsProg hG _)
      run_step (RunsWithin.prim _ _)
      run_step hany
      run_with RunsWithin.ite_neg hb' _
      run_step (RunsWithin.prim _ _)
      run_step hfil
      exact RunsWithin.prim_le (by simp only [Prim.eval, compStep, hb']; rfl) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_cons,
        List.length_nil, compStepCost]
      nlinarith

/-- The cost bound of the components. -/
def compsCost (N : ℕ) : ℕ := N * (compStepCost N + 1) + 2 * N + 4

theorem length_comps_le {N : ℕ} {G : GraphData} : (comps N G).length ≤ N := by
  rw [comps, List.length_map, reps]
  exact (List.length_filter_le _ _).trans (by simp)

theorem RunsWithin.compsProg {N : ℕ} {G : GraphData} (hG : G.Valid N) :
    RunsWithin X body (Graph.compsProg N G) (comps N G) (compsCost N) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.list .nat)) (cf := fun _ => compStepCost N) (F := compStep N G)
    (List.range N) [] fun acc u hu =>
      RunsWithin.compStepProg hG acc (Nat.le_of_lt (List.mem_range.1 hu))
  rw [sum_map_const, List.length_range] at hfold
  have hlen : ((List.range N).foldl (compStep N G) []).length ≤ N := by
    rw [← List.length_reverse, comps_eq_fold]
    exact length_comps_le
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le (comps_eq_fold N G) le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, compsCost]
    omega

theorem RunsWithin.subRowProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (cs : List ℕ) (u : ℕ) :
    RunsWithin X body (Graph.subRowProg G cs u) ((nbrs G u).map cs.idxOf)
      (27 * cs.length + 24) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := nbrs G u)
    (c := 9 * cs.length + 4) (F := cs.idxOf) fun w _ => RunsWithin.idxOfProg cs w
  have := hG3 u
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hmap
  case hc =>
    simp only [Prim.cost]
    nlinarith

/-- The cost bound of the component data on `k` points. -/
def subGCost (k : ℕ) : ℕ := k * (27 * k + 28) + 4

theorem RunsWithin.subGProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (cs : List ℕ) :
    RunsWithin X body (Graph.subGProg G cs) (subG G cs) (subGCost cs.length) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := cs)
    (c := 27 * cs.length + 24) (F := fun u => (nbrs G u).map cs.idxOf) fun u _ =>
      RunsWithin.subRowProg hG3 cs u
  apply RunsWithin.mono
  case h =>
    run_step hmap
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_map, subGCost]
    nlinarith

theorem RunsWithin.writeProg (t : List ℕ × List ℕ × Array ℕ) (acc : List (ℕ × ℕ)) (i : ℕ) :
    RunsWithin X body (Graph.writeProg t.1 t.2.1 t.2.2 acc i) (writeStep t acc i)
      (11 * t.1.length + 11 * t.2.1.length + 13) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.getDProg _ _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.getDProg _ _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.glueStepProg (acc : List (ℕ × ℕ)) (t : List ℕ × List ℕ × Array ℕ) :
    RunsWithin X body (Graph.glueStepProg acc t) (glueStep acc t)
      (t.1.length * (11 * t.1.length + 11 * t.2.1.length + 14) + 2 * t.1.length + 8) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.prod .nat .nat)) (cf := fun _ => 11 * t.1.length + 11 * t.2.1.length + 13)
    (F := writeStep t) (List.range t.1.length) acc fun acc i _ => RunsWithin.writeProg t acc i
  rw [sum_map_const, List.length_range] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons, Prim.eval]
    nlinarith

/-- The cost bound of gluing on `n` points. -/
def glueCost (n : ℕ) : ℕ := n * (n * (22 * n + 16) + 9) + n * n + 2 * n + 8

theorem length_glueStep (acc : List (ℕ × ℕ)) (t : List ℕ × List ℕ × Array ℕ) :
    (glueStep acc t).length = t.1.length + acc.length := by
  simp [glueStep_eq, glueWrites]

theorem RunsWithin.glueProg {n : ℕ} {M : List (List ℕ × List ℕ × Array ℕ)}
    (hM : ∀ t ∈ M, t.1.length ≤ n ∧ t.2.1.length ≤ n) (hlen : M.length ≤ n) :
    RunsWithin X body (Graph.glueProg n M) (glue n (M.foldl glueStep [])) (glueCost n) := by
  have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := Ty.cmatch)
    (b' := .list (.prod .nat .nat)) (f := fun acc t => Graph.glueStepProg acc t)
    (F := glueStep) (I := fun _ => True) (c := n * (22 * n + 14) + 2 * n + 8) M []
    (fun acc _ t ht => ⟨(RunsWithin.glueStepProg acc t).mono (by
      obtain ⟨h₁, h₂⟩ := hM t ht
      nlinarith), trivial⟩) trivial).1
  have hws : (M.foldl glueStep []).length ≤ n * n := by
    rw [(perm_foldl_glueStep M []).length_eq, List.append_nil, List.length_flatMap]
    have hle : ∀ x ∈ M.map fun t => (glueWrites t).length, x ≤ n := by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      simpa [glueWrites] using (hM t ht).1
    have := List.sum_le_length_nsmul _ _ hle
    simp only [List.length_map, smul_eq_mul] at this
    nlinarith
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate,
      glueCost]
    nlinarith

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_compStepProg {N₁ u₁ : var₁ .nat} {N₂ u₂ : var₂ .nat} {G₁ : var₁ Ty.graph}
    {G₂ : var₂ Ty.graph} {acc₁ : var₁ (.list (.list .nat))} {acc₂ : var₂ (.list (.list .nat))}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ)
    (hacc : ⟨.list (.list .nat), acc₁, acc₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (compStepProg N₁ G₁ acc₁ u₁)
      (compStepProg N₂ G₂ acc₂ u₂) := by
  unfold compStepProg
  refine .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hu]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (wf_levelsProg (by simp [hN]) (by simp [hG]) (List.Mem.head _)) fun _ _ => ?_
  unfold anyList levLtProg Luks.filterList
  prog_wf

theorem wf_compsProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {G₁ : var₁ Ty.graph}
    {G₂ : var₂ Ty.graph} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (compsProg N₁ G₁) (compsProg N₂ G₂) := by
  unfold compsProg
  exact .bind (.prim _ (.cons hN .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.foldList (by simp) (List.Mem.head _) fun _ _ _ _ =>
      wf_compStepProg (by simp [hN]) (by simp [hG]) (List.Mem.head _) (by simp)) fun _ _ =>
    .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_subGProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {cs₁ : var₁ (.list .nat)}
    {cs₂ : var₂ (.list .nat)} (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ)
    (hcs : ⟨.list .nat, cs₁, cs₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (subGProg G₁ cs₁) (subGProg G₂ cs₂) := by
  unfold subGProg subRowProg
  exact .bind (wf_mapList hcs fun Γ' hΓ _ _ hu =>
      .bind (.prim _ (.cons (hΓ hG) (.cons hu .nil))) fun _ _ =>
      wf_mapList (List.Mem.head _) fun Γ'' hΓ' _ _ hw =>
        wf_idxOfProg (hΓ' (List.mem_cons_of_mem _ (hΓ hcs))) hw) fun _ _ =>
    .prim _ (.cons (List.Mem.head _) .nil)

theorem wf_writeProg {cs₁ ds₁ : var₁ (.list .nat)} {cs₂ ds₂ : var₂ (.list .nat)}
    {iso₁ : var₁ (.array .nat)} {iso₂ : var₂ (.array .nat)}
    {acc₁ : var₁ (.list (.prod .nat .nat))} {acc₂ : var₂ (.list (.prod .nat .nat))}
    {i₁ : var₁ .nat} {i₂ : var₂ .nat} (hcs : ⟨.list .nat, cs₁, cs₂⟩ ∈ Γ)
    (hds : ⟨.list .nat, ds₁, ds₂⟩ ∈ Γ) (hiso : ⟨.array .nat, iso₁, iso₂⟩ ∈ Γ)
    (hacc : ⟨.list (.prod .nat .nat), acc₁, acc₂⟩ ∈ Γ) (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (writeProg cs₁ ds₁ iso₁ acc₁ i₁)
      (writeProg cs₂ ds₂ iso₂ acc₂ i₂) := by
  unfold writeProg
  exact .bind (.prim _ .nil) fun _ _ =>
    .bind (wf_getDProg (by simp [hcs]) (by simp [hi]) (List.Mem.head _)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hiso]) (.cons (by simp [hi]) .nil))) fun _ _ =>
    .bind (wf_getDProg (by simp [hds]) (List.Mem.head _) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .prim _ (.cons (List.Mem.head _) (.cons (by simp [hacc]) .nil))

theorem wf_glueProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {M₁ : var₁ (.list Ty.cmatch)}
    {M₂ : var₂ (.list Ty.cmatch)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hM : ⟨.list Ty.cmatch, M₁, M₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (glueProg n₁ M₁) (glueProg n₂ M₂) := by
  unfold glueProg glueStepProg
  exact .bind (.prim _ .nil) fun _ _ =>
    .bind (.foldList (by simp [hM]) (List.Mem.head _) fun _ _ _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
      .foldList (List.Mem.head _) (by simp) fun _ _ _ _ =>
        wf_writeProg (by simp) (by simp) (by simp) (List.Mem.head _) (by simp)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hn]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil))

end Wf

end GraphIso.Graph
