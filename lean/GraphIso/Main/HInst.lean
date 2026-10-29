module

public import GraphIso.Toolkit.Extend
public import GraphIso.Reductions.Data

/-!
# Hinted instances as data

Stage 14j-1, item 1 (`PLAN-14.md` §14.1). The main recursion works on *hinted instances*: an
instance `(x, y, W, σ • G)` of degree `N`, the original size `n₀` (for the thresholds), the
number `n` of string positions — the base of the hint is `[n, N)` — and optional labels.

* `hinstTy D`, `HInstData D`: the type and its values; `HInstData.inst`, `.n₀`, `.n`, `.lab`.
* `HInstValid DV I`: the representation invariant. The instance is valid, the string positions
  `[0, n)` contain the window, the base `[n, N)` is invariant, and the group acts faithfully on
  the string positions (the hypothesis of `rebase_faithful`). When labels are present they are
  valid hint data (`HintValid`) and the group is transitive on the window: the invariant of
  `PLAN-14.md` §2.1 (an instance carries a hint only if its group is transitive on its window).
* `HInstValid.isHint`, `HInstValid.transitive`: the bridge to stage 14a's `IsHint` and
  `Transitive` for the base action `baseHom`.
* `hmeasure`: the pair `(n, m)` the potential charges, with `m := N − n` for a hinted instance
  and `m := 2 n + 1` without a hint (`pot0`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Toolkit GraphIso.Recursion

variable {D : Ty}

/-- The type of hinted instances: an instance, `n₀`, the number `n` of string positions, and
optional labels. -/
abbrev hinstTy (D : Ty) : Ty :=
  .prod (Ty.inst D) (.prod .nat (.prod .nat (.option (.array (.list .nat)))))

/-- Hinted instances as data. -/
abbrev HInstData (D : Ty) := InstData D × (ℕ × (ℕ × Option LabelData))

namespace HInstData

variable (I : HInstData D)

/-- The underlying instance. -/
def inst : InstData D := I.1
/-- The original size, for the thresholds. -/
def n₀ : ℕ := I.2.1
/-- The number of string positions; the base is `[n, N)`. -/
def n : ℕ := I.2.2.1
/-- The labels, if any. -/
def lab : Option LabelData := I.2.2.2

end HInstData

/-- The group of an instance is transitive on its window. -/
def IsTransOn {N : ℕ} (G : Subgroup (Perm (Fin N))) (W : Set (Fin N)) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, ∃ g ∈ G, g u = v

/-- **Valid hinted instances.** -/
structure HInstValid (DV : ℕ → GensData → D.denote → Prop) (I : HInstData D) : Prop where
  valid : I.inst.Valid DV
  le : I.n ≤ I.inst.degree
  base_inv : IsInvariant I.inst.G (baseSet I.n I.inst.degree)
  win_lt : ∀ i ∈ I.inst.2.1.1, i < I.n
  faithful : ∀ g ∈ I.inst.G, (∀ j : Fin I.inst.degree, j.val < I.n → g j = j) → g = 1
  hint : ∀ L, I.lab = some L →
    HintValid I.n I.inst.degree I.inst.2.2.2.gens I.inst.2.1 L ∧ IsTransOn I.inst.G I.inst.W

namespace HInstValid

variable {DV : ℕ → GensData → D.denote → Prop} {I : HInstData D}

/-- **The bridge to stage 14a**: valid labels denote a hint for the base action. -/
theorem isHint (h : HInstValid DV I) {L : LabelData} (hL : I.lab = some L) :
    IsHint (baseHom I.inst.G I.n h.base_inv) (winFinset I.inst.degree I.inst.2.1)
      (labOf I.n I.inst.degree L) :=
  (h.hint L hL).1.isHint h.valid.group.1 h.valid.win h.valid.invariant

/-- **Transitivity in stage 14a's form.** -/
theorem transitive (h : HInstValid DV I) {L : LabelData} (hL : I.lab = some L) :
    Transitive ↥I.inst.G (winFinset I.inst.degree I.inst.2.1) := by
  intro u hu v hv
  rw [mem_winFinset] at hu hv
  obtain ⟨g, hg, hgu⟩ := (h.hint L hL).2 u hu v hv
  exact ⟨⟨g, hg⟩, hgu⟩

end HInstValid

/-- The window size of a hinted instance. -/
def HInstData.winSize (I : HInstData D) : ℕ := I.inst.2.1.1.length

/-- **The measure the potential charges**: the window size, and the base size of the hint, or
`2 n + 1` without a hint. -/
def hmeasure (I : HInstData D) : ℕ × ℕ :=
  (I.winSize, match I.lab with
    | some _ => I.inst.degree - I.n
    | none => 2 * I.winSize + 1)

theorem hmeasure_some {I : HInstData D} {L : LabelData} (h : I.lab = some L) :
    hmeasure I = (I.winSize, I.inst.degree - I.n) := by
  simp [hmeasure, h]

theorem hmeasure_none {I : HInstData D} (h : I.lab = none) :
    hmeasure I = (I.winSize, 2 * I.winSize + 1) := by
  simp [hmeasure, h]

end GraphIso.Main
