module

public import GraphIso.Programs.List
public import GraphIso.GroupOps.Interface

/-!
# Permutation operations in the cost language

The elementary operations on represented permutations, as programs, with proofs that they
compute the functional models of `GraphIso.Representation.Permutation` and with explicit cost
bounds for degree `n`. This validates the accounting choices of the plan for the selected
implementation (forward and inverse arrays):

| program | result | cost |
|---|---|---|
| `permApply g i` | `get g.1 i` | `2` (one lookup and one projection) |
| `permInv g` | `PermData.inv g` | `3` (the arrays are swapped, not copied) |
| `permMul g h` | `PermData.mul g h` | `12 n + 13` |
| `permOne n` | `PermData.one n` | `2 n + 3` |
| `arrayNatBeq x y` | `x == y` | `6 n + 8` for arrays of length `n` |
| `permBeq g h` | `PermData.beq g h` | `6 n + 10` |

All of them are well-formed (`wf_permApply`, …, `wf_permBeq`).
-/

@[expose] public section

namespace GraphIso.Programs

open Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- Evaluate a permutation at a point: one array read. -/
def permApply (g : var Ty.perm) (i : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .fst g) fun f => .op2 .arrayGet f i

/-- Inverse: swap the forward and inverse arrays. -/
def permInv (g : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun f => .bind (.op1 .snd g) fun b => .op2 .pair b f

/-- Composition `g * h`: forward array `h.1` read through `g.1`, inverse array `g.2` read
through `h.2`. -/
def permMul (g h : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun gf => .bind (.op1 .snd g) fun gb =>
  .bind (.op1 .fst h) fun hf => .bind (.op1 .snd h) fun hb =>
  .bind (mapArray hf fun j => .op2 .arrayGet gf j) fun f =>
  .bind (mapArray gb fun j => .op2 .arrayGet hb j) fun b =>
  .op2 .pair f b

/-- The identity of degree `n`. -/
def permOne (n : var .nat) : Prog S rec var Ty.perm :=
  .bind (.op1 .range n) fun l => .bind (.op1 .arrayOfList l) fun arr => .op2 .pair arr arr

/-- Equality of arrays of naturals: compare sizes, then every entry. -/
def arrayNatBeq (x y : var (.array .nat)) : Prog S rec var .bool :=
  .bind (.op1 .arraySize x) fun nx => .bind (.op1 .arraySize y) fun ny =>
  .bind (.op2 .natEq nx ny) fun same =>
  .ite same
    (.bind (.op1 .range nx) fun is => allList is fun i =>
      .bind (.op2 .arrayGet x i) fun xi => .bind (.op2 .arrayGet y i) fun yi => .op2 .natEq xi yi)
    (.op0 (.boolLit false))

/-- Equality test of represented permutations, on forward arrays. -/
def permBeq (g h : var Ty.perm) : Prog S rec var .bool :=
  .bind (.op1 .fst g) fun gf => .bind (.op1 .fst h) fun hf => arrayNatBeq gf hf

section Specs

variable {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.permApply (g : PermData) (i : ℕ) :
    RunsWithin X body (Programs.permApply g i) (get g.1 i) 2 :=
  RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl

theorem RunsWithin.permInv (g : PermData) :
    RunsWithin X body (Programs.permInv g) (PermData.inv g) 3 :=
  RunsWithin.bind_le (c₂ := 2) (RunsWithin.prim _ _)
    (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl) le_rfl

theorem RunsWithin.permMul {n : ℕ} {g h : PermData} (hg : g.Valid n) (hh : h.Valid n) :
    RunsWithin X body (Programs.permMul g h) (PermData.mul g h) (12 * n + 13) := by
  have m₁ : RunsWithin X body
      (Programs.mapArray (a' := .nat) (b' := .nat) h.1 fun j => .op2 .arrayGet g.1 j)
      (amap (get g.1) h.1)
      (n * (1 + 5) + 4) := by
    rw [← hh.size_fwd]
    exact RunsWithin.mapArray fun j _ => RunsWithin.prim_le rfl le_rfl
  have m₂ : RunsWithin X body
      (Programs.mapArray (a' := .nat) (b' := .nat) g.2 fun j => .op2 .arrayGet h.2 j)
      (amap (get h.2) g.2)
      (n * (1 + 5) + 4) := by
    rw [← hg.size_inv]
    exact RunsWithin.mapArray fun j _ => RunsWithin.prim_le rfl le_rfl
  refine RunsWithin.bind_le (c₂ := 12 * n + 12) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 12 * n + 11) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 12 * n + 10) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 12 * n + 9) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 6 * n + 5) m₁ ?_ (by omega)
  refine RunsWithin.bind_le (c₂ := 1) m₂ ?_ (by omega)
  exact RunsWithin.prim_le rfl le_rfl

theorem RunsWithin.permOne (n : ℕ) :
    RunsWithin X body (Programs.permOne n) (PermData.one n) (2 * n + 3) := by
  refine RunsWithin.bind_le (c₂ := n + 2) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost, Prim.eval])
  exact RunsWithin.prim_le (by simp [Prim.eval, PermData.one]) le_rfl

theorem arrayNat_beq_iff (x y : Array ℕ) :
    (x == y) = (decide (x.size = y.size) &&
      (List.range x.size).all fun i => get x i == get y i) := by
  by_cases hs : x.size = y.size
  · simp only [hs, decide_true, Bool.true_and]
    rw [Bool.eq_iff_iff, beq_iff_eq, List.all_eq_true]
    simp only [List.mem_range, beq_iff_eq]
    constructor
    · rintro rfl i _
      rfl
    · intro h
      refine Array.ext hs fun i hi₁ hi₂ => ?_
      have := h i (hs ▸ hi₂)
      rwa [get_eq_getElem hi₁, get_eq_getElem hi₂] at this
  · simp only [hs, decide_false, Bool.false_and]
    rw [Bool.eq_false_iff]
    intro h
    exact hs (congrArg Array.size (beq_iff_eq.1 h))

theorem RunsWithin.arrayNatBeq (x y : Array ℕ) :
    RunsWithin X body (Programs.arrayNatBeq x y) (x == y) (6 * x.size + 8) := by
  rw [arrayNat_beq_iff]
  refine RunsWithin.bind_le (c₂ := 6 * x.size + 7) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 6 * x.size + 6) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 6 * x.size + 5) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  by_cases hs : x.size = y.size
  · have hb : (x.size == y.size) = true := by simp [hs]
    have hd : decide (x.size = y.size) = true := decide_eq_true hs
    simp only [Prim.eval]
    rw [hb, hd, Bool.true_and]
    refine (RunsWithin.ite_true (k := 6 * x.size + 4) ?_).mono (by omega)
    refine RunsWithin.bind_le (c₂ := 5 * x.size + 1) (RunsWithin.prim _ _) ?_
      (by simp [Prim.cost]; omega)
    have := RunsWithin.allList_le (X := X) (body := body) (c := 3) (a' := .nat)
      (xs := List.range x.size)
      (p := fun i => .bind (.op2 .arrayGet x i) fun xi => .bind (.op2 .arrayGet y i) fun yi =>
        .op2 .natEq xi yi)
      (P := fun i => get x i == get y i) fun i _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _)
          (RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl) le_rfl) le_rfl
    simp only [Prim.eval] at this ⊢
    refine this.mono ?_
    simp only [List.length_range]
    omega
  · have hb : (x.size == y.size) = false := by simp [hs]
    simp only [Prim.eval, hb, hs, decide_false, Bool.false_and]
    exact (RunsWithin.ite_false (RunsWithin.prim _ _)).mono (by simp [Prim.cost])

theorem RunsWithin.permBeq {n : ℕ} {g h : PermData} (hg : g.Valid n) :
    RunsWithin X body (Programs.permBeq g h) (PermData.beq g h) (6 * n + 10) := by
  refine RunsWithin.bind_le (c₂ := 6 * n + 9) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  refine RunsWithin.bind_le (c₂ := 6 * n + 8) (RunsWithin.prim _ _) ?_
    (by simp [Prim.cost]; omega)
  have := RunsWithin.arrayNatBeq (X := X) (body := body) g.1 h.1
  rw [hg.size_fwd] at this
  exact this

end Specs

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_permApply {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm} {i₁ : var₁ .nat} {i₂ : var₂ .nat}
    (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permApply g₁ i₁) (permApply g₂ i₂) := by
  unfold permApply
  prog_wf

theorem wf_permInv {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm} (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permInv g₁) (permInv g₂) := by
  unfold permInv
  prog_wf

theorem wf_permMul {g₁ h₁ : var₁ Ty.perm} {g₂ h₂ : var₂ Ty.perm} (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ)
    (hh : ⟨Ty.perm, h₁, h₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permMul g₁ h₁) (permMul g₂ h₂) := by
  unfold permMul mapArray mapList
  prog_wf

theorem wf_permOne {n₁ : var₁ .nat} {n₂ : var₂ .nat} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permOne n₁) (permOne n₂) := by
  unfold permOne
  prog_wf

theorem wf_arrayNatBeq {x₁ y₁ : var₁ (.array .nat)} {x₂ y₂ : var₂ (.array .nat)}
    (hx : ⟨.array .nat, x₁, x₂⟩ ∈ Γ) (hy : ⟨.array .nat, y₁, y₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (arrayNatBeq x₁ y₁) (arrayNatBeq x₂ y₂) := by
  unfold arrayNatBeq allList
  prog_wf

theorem wf_permBeq {g₁ h₁ : var₁ Ty.perm} {g₂ h₂ : var₂ Ty.perm} (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ)
    (hh : ⟨Ty.perm, h₁, h₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (permBeq g₁ h₁) (permBeq g₂ h₂) := by
  unfold permBeq arrayNatBeq allList
  prog_wf

end Wf

end GraphIso.Programs
