module

public import GraphIso.Cost.Program
public import GraphIso.TM.Heap

/-!
# Values in the heap

Stage 17c (`PLAN-17.md` §6).

* **`Rep h t v p`**: the cell at index `p` of the heap `h`, with the cells it points to, stands
  for the value `v : t.denote`. This covers every `Ty`:
  - the unit, Booleans and `none` and `nil` are cells with no fields;
  - a natural is a cell with one field, its bits;
  - a pair is a cell with two pointers;
  - `some` is a cell with one pointer, and `cons` a cell with two (head and tail);
  - an array is a cell with one pointer per element.
  Fields are read as numbers through `ofBits`, so pointers need not be canonical.
* **`Rep.mono`**: appending cells keeps every representation, as allocation does.
* **`Rep.lt`**: a representation points into the heap. **`Rep.nat_inv`** inverts the case of
  naturals.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost

/-- The cell at index `p` has tag `t` and fields `fs`. -/
def CellAt (h : List Cell) (p : ℕ) (t : Tag) (fs : List (List Bool)) : Prop :=
  ∃ hp : p < h.length, h[p].tag = t ∧ h[p].fields = fs

/-- **Representation**: the cell at index `p` of the heap `h`, with the cells it points to,
stands for the value `v` of type `t`. Fields are read as numbers through `ofBits`. -/
inductive Rep (h : List Cell) : (t : Ty) → t.denote → ℕ → Prop
  | unit {p : ℕ} : CellAt h p .unit [] → Rep h .unit () p
  | bool {p : ℕ} (b : Bool) : CellAt h p (if b then .tt else .ff) [] → Rep h .bool b p
  | nat {p : ℕ} {l : List Bool} : CellAt h p .nat [l] → Rep h .nat (ofBits l) p
  | pair {a b : Ty} {x : a.denote} {y : b.denote} {p : ℕ} {l₁ l₂ : List Bool} :
      CellAt h p .pair [l₁, l₂] → Rep h a x (ofBits l₁) → Rep h b y (ofBits l₂) →
      Rep h (.prod a b) (x, y) p
  | none {a : Ty} {p : ℕ} : CellAt h p .none [] → Rep h (.option a) Option.none p
  | some {a : Ty} {x : a.denote} {p : ℕ} {l : List Bool} : CellAt h p .some [l] →
      Rep h a x (ofBits l) → Rep h (.option a) (Option.some x) p
  | nil {a : Ty} {p : ℕ} : CellAt h p .nil [] → Rep h (.list a) [] p
  | cons {a : Ty} {x : a.denote} {xs : List a.denote} {p : ℕ} {l₁ l₂ : List Bool} :
      CellAt h p .cons [l₁, l₂] → Rep h a x (ofBits l₁) → Rep h (.list a) xs (ofBits l₂) →
      Rep h (.list a) (x :: xs) p
  | arr {a : Ty} {v : Array a.denote} {p : ℕ} {ls : List (List Bool)} :
      CellAt h p .arr ls → ls.length = v.size →
      (∀ i (hi : i < ls.length) (hv : i < v.size), Rep h a v[i] (ofBits ls[i])) →
      Rep h (.array a) v p

theorem CellAt.mono {h h' : List Cell} {p : ℕ} {t : Tag} {fs : List (List Bool)}
    (hc : CellAt h p t fs) : CellAt (h ++ h') p t fs := by
  obtain ⟨hp, ht, hf⟩ := hc
  refine ⟨by simp; omega, ?_, ?_⟩ <;> rw [List.getElem_append_left hp] <;> assumption

/-- **Monotonicity**: allocation keeps every representation. -/
theorem Rep.mono {h h' : List Cell} {t : Ty} {v : t.denote} {p : ℕ} (hr : Rep h t v p) :
    Rep (h ++ h') t v p := by
  induction hr with
  | unit hc => exact .unit hc.mono
  | bool b hc => exact .bool b hc.mono
  | nat hc => exact .nat hc.mono
  | pair hc _ _ ih₁ ih₂ => exact .pair hc.mono ih₁ ih₂
  | none hc => exact .none hc.mono
  | some hc _ ih => exact .some hc.mono ih
  | nil hc => exact .nil hc.mono
  | cons hc _ _ ih₁ ih₂ => exact .cons hc.mono ih₁ ih₂
  | arr hc hl _ ih => exact .arr hc.mono hl ih

/-- Inversion at the type of naturals: the value is read from the cell's one field. -/
theorem Rep.nat_inv {h : List Cell} {v p : ℕ} (hr : Rep h .nat v p) :
    ∃ l, CellAt h p .nat [l] ∧ ofBits l = v := by
  cases hr with
  | nat hc => exact ⟨_, hc, rfl⟩

/-- A representation points into the heap. -/
theorem Rep.lt {h : List Cell} {t : Ty} {v : t.denote} {p : ℕ} : Rep h t v p → p < h.length
  | .unit hc | .bool _ hc | .nat hc | .pair hc _ _ | .none hc | .some hc _ | .nil hc
  | .cons hc _ _ | .arr hc _ _ => hc.1

end GraphIso.TM
