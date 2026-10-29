module

public import GraphIso.Representation.Group
public import GraphIso.Semantics.StringIso

/-!
# Represented strings and instances

* `StrData`: an array of naturals; `StrData.Valid n q x` says it has length `n` and symbols
  below `q`. It denotes `Fin n → ℕ`. The bound `q` is part of the input contract: it is what
  justifies charging one word operation per symbol comparison in the cost model.
* `matchesB w g x y` checks `Matches` on the listed window points without inverting `g`.
* `StrData.comp y σ` is the normalized target `y ∘ σ` (forward array of `σ` mapped through
  `y`), used by coset normalization.
* `InstanceData`: a full represented instance. `InstanceData.validB` checks every invariant,
  including invariance of the window under the supplied generators, and `InstanceData.Valid`
  provides the semantic hypothesis `IsInvariant` needed for coset-valued answers.
-/

@[expose] public section

namespace GraphIso

open Equiv

/-- A represented string. -/
abbrev StrData := Array ℕ

namespace StrData

/-- The interpreted string over the alphabet `ℕ`. -/
def denote (n : ℕ) (x : StrData) : Fin n → ℕ := fun u => get x u

/-- Valid string data: length `n`, symbols below `q`. -/
structure Valid (n q : ℕ) (x : StrData) : Prop where
  size : x.size = n
  lt : ∀ i < n, get x i < q

/-- Executable validity check. -/
def validB (n q : ℕ) (x : StrData) : Bool :=
  x.size == n && (List.range n).all fun i => decide (get x i < q)

theorem validB_iff {n q : ℕ} {x : StrData} : validB n q x = true ↔ Valid n q x := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.size, h.lt⟩⟩

/-- The normalized target `y ∘ σ`. -/
def comp (y : StrData) (σ : PermData) : StrData := amap (get y) σ.1

theorem denote_comp {n : ℕ} {σ : PermData} (hσ : σ.Valid n) (y : StrData) :
    (y.comp σ).denote n = fun u => y.denote n (σ.denote n u) := by
  funext u
  simp only [denote, comp]
  rw [get_amap (by rw [hσ.size_fwd]; exact u.2), PermData.val_denote_apply hσ]

theorem Valid.comp {n q : ℕ} {y : StrData} {σ : PermData} (hy : Valid n q y) (hσ : σ.Valid n) :
    Valid n q (y.comp σ) := by
  refine ⟨by simp [StrData.comp, hσ.size_fwd], fun i hi => ?_⟩
  rw [StrData.comp, get_amap (by rw [hσ.size_fwd]; exact hi)]
  exact hy.lt _ (hσ.fwd_lt i hi)

end StrData

/-- Check `x u = y (g u)` at every listed window point. -/
def matchesB (w : WinData) (g : PermData) (x y : StrData) : Bool :=
  w.1.all fun u => get x u == get y (get g.1 u)

theorem matchesB_iff {n : ℕ} {w : WinData} {g : PermData} (hw : w.Valid n) (hg : g.Valid n)
    (x y : StrData) :
    matchesB w g x y = true ↔ Matches (w.denote n) (g.denote n) (x.denote n) (y.denote n) := by
  simp only [matchesB, List.all_eq_true, beq_iff_eq, Matches]
  rw [WinData.forall_mem_denote hw]
  simp only [StrData.denote, PermData.val_denote_apply hg]

/-! ### Instances -/

/-- A represented instance of windowed string isomorphism: strings `x` and `y`, a window, a
coset representative and generators of the group, together with backend data of type `D`. -/
structure InstanceData (D : Type) where
  /-- Source string. -/
  x : StrData
  /-- Target string. -/
  y : StrData
  /-- Window. -/
  win : WinData
  /-- Coset representative. -/
  rep : PermData
  /-- Group generators. -/
  gens : GensData
  /-- Backend data attached to the group. -/
  data : D

namespace InstanceData

variable {D : Type}

/-- The degree is the length of the source string. -/
def degree (I : InstanceData D) : ℕ := I.x.size

/-- All representation invariants for alphabet bound `q`, including the window's invariance
under the generators. -/
structure Valid (q : ℕ) (I : InstanceData D) : Prop where
  x_valid : I.x.Valid I.degree q
  y_valid : I.y.Valid I.degree q
  win_valid : I.win.Valid I.degree
  rep_valid : I.rep.Valid I.degree
  gens_valid : I.gens.AllValid I.degree
  invariant : I.gens.invariantB I.win = true

/-- Executable validity check. -/
def validB (q : ℕ) (I : InstanceData D) : Bool :=
  I.x.validB I.degree q && I.y.validB I.degree q && I.win.validB I.degree &&
    I.rep.validB I.degree && I.gens.allValidB I.degree && I.gens.invariantB I.win

theorem validB_iff {q : ℕ} {I : InstanceData D} : I.validB q = true ↔ I.Valid q := by
  simp only [validB, Bool.and_eq_true, StrData.validB_iff, WinData.validB_iff,
    PermData.validB_iff, GensData.allValidB_iff]
  exact ⟨fun ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩,
    fun h => ⟨⟨⟨⟨⟨h.x_valid, h.y_valid⟩, h.win_valid⟩, h.rep_valid⟩, h.gens_valid⟩, h.invariant⟩⟩

/-! Decoded semantic objects. -/

/-- The decoded window. -/
def W (I : InstanceData D) : Set (Fin I.degree) := I.win.denote I.degree
/-- The decoded coset representative. -/
def σ (I : InstanceData D) : Perm (Fin I.degree) := I.rep.denote I.degree
/-- The decoded group. -/
def G (I : InstanceData D) : Subgroup (Perm (Fin I.degree)) := I.gens.denote I.degree
/-- The decoded source string. -/
def xs (I : InstanceData D) : Fin I.degree → ℕ := I.x.denote I.degree
/-- The decoded target string. -/
def ys (I : InstanceData D) : Fin I.degree → ℕ := I.y.denote I.degree

/-- A valid instance decodes to a window that is invariant under the decoded group. -/
theorem Valid.isInvariant {q : ℕ} {I : InstanceData D} (h : I.Valid q) : IsInvariant I.G I.W :=
  (GensData.invariantB_iff h.gens_valid h.win_valid).1 h.invariant

/-- The solution set of the decoded instance. -/
def solutions (I : InstanceData D) : Set (Perm (Fin I.degree)) := iso I.W I.σ I.G I.xs I.ys

end InstanceData

end GraphIso
