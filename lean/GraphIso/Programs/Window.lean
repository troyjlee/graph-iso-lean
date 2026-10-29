module

public import GraphIso.Programs.Perm

/-!
# Building windows

`mkWindow n pts` materializes the represented window with point list `pts` in degree `n`: a
fresh mask of length `n` with the listed positions set. Its functional model is
`WinData.ofPoints n pts`; it is valid when `pts` has no duplicates and all points are below
`n` (`WinData.valid_ofPoints`), and it denotes `{u | u.val ∈ pts}`. Cost `2 n + 5 |pts| + 7`:
the mask is charged in full, so a window of size `m` costs `Θ(n + m)` to build, not `Θ(m)`.
-/

@[expose] public section

namespace GraphIso

open Cost

/-- The window with point list `pts` in degree `n`. -/
def WinData.ofPoints (n : ℕ) (pts : List ℕ) : WinData :=
  (pts, Prim.applyWrites (a := .bool) (Array.replicate n false) (pts.map fun i => (i, true)))

theorem size_applyWrites_true (arr : Array Bool) (l : List ℕ) :
    (Prim.applyWrites (a := .bool) arr (l.map fun i => (i, true))).size = arr.size := by
  induction l generalizing arr with
  | nil => rfl
  | cons j l ih =>
    simp only [Prim.applyWrites, List.map_cons, List.foldl_cons] at ih ⊢
    rw [ih, Array.size_setIfInBounds]

theorem getB_applyWrites_true (arr : Array Bool) (l : List ℕ) {i : ℕ} (hi : i < arr.size) :
    getB (Prim.applyWrites (a := .bool) arr (l.map fun i => (i, true))) i =
      (getB arr i || decide (i ∈ l)) := by
  induction l generalizing arr with
  | nil => simp [Prim.applyWrites]
  | cons j l ih =>
    have h := ih (arr.setIfInBounds j true) (by rwa [Array.size_setIfInBounds])
    simp only [Prim.applyWrites, List.map_cons, List.foldl_cons] at h ⊢
    rw [h]
    simp only [getB, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, List.mem_cons]
    by_cases hji : j = i
    · subst hji
      simp [hi]
    · simp [hji, Ne.symm hji]

theorem WinData.valid_ofPoints {n : ℕ} {pts : List ℕ} (hnd : pts.Nodup)
    (hlt : ∀ i ∈ pts, i < n) : (WinData.ofPoints n pts).Valid n := by
  refine ⟨(size_applyWrites_true _ _).trans Array.size_replicate, hnd, hlt, fun i hi => ?_⟩
  simp only [WinData.ofPoints]
  rw [getB_applyWrites_true _ _ (by simpa using hi)]
  simp [getB, Array.getD_eq_getD_getElem?, hi]

@[simp] theorem WinData.ofPoints_fst (n : ℕ) (pts : List ℕ) : (WinData.ofPoints n pts).1 = pts :=
  rfl

theorem WinData.denote_ofPoints (n : ℕ) (pts : List ℕ) :
    (WinData.ofPoints n pts).denote n = {u : Fin n | u.val ∈ pts} := rfl

end GraphIso

namespace GraphIso.Programs

open Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Materialize the window with point list `pts` in degree `n`. -/
def mkWindow (n : var .nat) (pts : var (.list .nat)) : Prog S rec var Ty.win :=
  .bind (.op0 (.boolLit false)) fun ff =>
  .bind (.op2 .arrayMk n ff) fun blank =>
  .bind (.op0 (.boolLit true)) fun tt =>
  .bind (mapList pts fun i => .op2 .pair i tt) fun ws =>
  .bind (.prim .arrayUpdate (.cons blank (.cons ws .nil))) fun mask =>
  .op2 .pair pts mask

section Specs

variable {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.mkWindow (n : ℕ) (pts : List ℕ) :
    RunsWithin X body (Programs.mkWindow n pts) (WinData.ofPoints n pts)
      (2 * n + 5 * pts.length + 7) := by
  refine RunsWithin.bind_le (c₂ := 2 * n + 5 * pts.length + 6) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := n + 5 * pts.length + 5) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := n + 5 * pts.length + 4) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .bool) (xs := pts) (c := 1) (F := fun i => (i, true))
    (f := fun i => .op2 .pair i true) fun i _ => RunsWithin.prim_le rfl le_rfl
  refine RunsWithin.bind_le (c₂ := n + pts.length + 2) hm ?_ (by omega)
  refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ ?_
  · exact RunsWithin.prim_le rfl le_rfl
  · simp [Prim.cost, Prim.eval]

end Specs

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_mkWindow {n₁ : var₁ .nat} {n₂ : var₂ .nat} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (mkWindow n₁ p₁) (mkWindow n₂ p₂) := by
  unfold mkWindow mapList
  prog_wf

end Wf

end GraphIso.Programs
