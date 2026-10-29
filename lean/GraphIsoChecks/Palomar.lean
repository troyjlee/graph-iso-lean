module

public import GraphIso.Palomar.Bridge
public import GraphIsoChecks.TMVertices
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stages 19c and 19d: the Palomar statements

`PLAN-19.md` §5–§6. Kernel `decide` on small fixtures, and the theorems instantiated; no machine
is run.

* **The words**: `natWord` on `0` and `6` (least significant digit first); `Nat.bits = toBits`
  on `0, …, 64`; the input words of the empty pairs at `n = 0, 1`, of the two paths and of a
  path and the triangle (`GraphIsoChecks.TMGI`) map to the input tapes `encodeIn p.enc` of the
  single-tape machine; the output words map to `encodeOut (ser .bool b)`.
* **The theorem** (`gi_singleTape_proof`) on the two paths and on a path and the triangle: the
  machine halts with `output true` on the first pair and with `output false` on the second
  within `2 ^ (c 2⁸)` transitions (`⌊log₂ 3⌋ = 1`).
* **Negative controls**: the two output words differ under every injective map; the words of a
  path and of the triangle differ; `graphWord` lists the vertices from `n - 1` down to `0`, not
  upwards.
* **The coset words**: the word of the 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` (the images of `2, 1, 0`, then
  the inverse images); the output words of the 3-cycle with the generators `[swap, 3-cycle]`,
  and of `none`, map to the output tapes `encodeOut (ser Ty.giCoset r)` of the data.
* **The coset theorem** (`gi_coset_singleTape_proof`) on the two paths and on a path and the
  triangle: the machine halts with `cosetWord (some (τ, gs))` on the first pair, where `τ`
  underlies an isomorphism, and with `cosetWord none` on the second, within `2 ^ (c 2⁸)`
  transitions.
* **Negative controls**: the images listed from `0` upwards give another word; the word of
  `none` is not the word of any `some`.
-/

@[expose] public section

namespace GraphIsoChecks.Palomar

open Equiv GraphIso GraphIso.TM GraphIso.Cost GraphIso.Main GraphIsoPalomar GraphIsoChecks.TMGI
  GraphIsoChecks.TMVertices

-- the statement's symbols have no `DecidableEq` (`PLAN-19.md`, Appendix A); the checks derive it
deriving instance DecidableEq for GraphIsoPalomar.Sym

/-! ### The words -/

example : natWord 0 = [.endNum] ∧
    natWord 6 = [.digit false, .digit true, .digit true, .endNum] := by
  decide +kernel

example : ∀ k < 65, Nat.bits k = toBits k := by
  decide +kernel

section WordEq

variable {W : Type}

/-- Tape symbols compared: marks, input and output symbols. Work symbols have no decidable
equality here and do not occur in the words. -/
def symEq : SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym →
    SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym → Bool
  | .lmark, .lmark => true
  | .rmark, .rmark => true
  | .inp a, .inp b => a == b
  | .out a, .out b => a == b
  | _, _ => false

theorem eq_of_symEq {a b : SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym}
    (h : symEq a b = true) : a = b := by
  cases a <;> cases b <;> simp_all [symEq]

/-- Two words of tape symbols, compared symbol by symbol. -/
def wordEq : List (SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym) →
    List (SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym) → Bool
  | [], [] => true
  | a :: l, b :: l' => symEq a b && wordEq l l'
  | _, _ => false

theorem eq_of_wordEq :
    ∀ {l l' : List (SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym)}, wordEq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [wordEq, Bool.and_eq_true] at h
    rw [eq_of_symEq h.1, eq_of_wordEq h.2]

end WordEq

/-- The input words of the empty pairs, of the two paths and of a path and the triangle are the
machine's input tapes. -/
example : (input (⊥ : SimpleGraph (Fin 0)) ⊥).map symbolEmbedding =
      SingleTape.encodeIn (emptyPair 0).enc ∧
    (input (⊥ : SimpleGraph (Fin 1)) ⊥).map symbolEmbedding =
      SingleTape.encodeIn (emptyPair 1).enc ∧
    (input path₁ path₂).map symbolEmbedding = SingleTape.encodeIn pp.enc ∧
    (input path₁ tri).map symbolEmbedding = SingleTape.encodeIn pt.enc :=
  ⟨eq_of_wordEq (by decide +kernel), eq_of_wordEq (by decide +kernel),
    eq_of_wordEq (by decide +kernel), eq_of_wordEq (by decide +kernel)⟩

example : (output true).map symbolEmbedding = SingleTape.encodeOut (ser .bool true) ∧
    (output false).map symbolEmbedding = SingleTape.encodeOut (ser .bool false) :=
  ⟨eq_of_wordEq (by decide +kernel), eq_of_wordEq (by decide +kernel)⟩

/-! ### The theorem -/

/-- **The theorem on the two paths and on a path and the triangle**: the machine halts with the
output `yes` on the first pair and `no` on the second within `2 ^ (c 2⁸)` transitions. -/
example : ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ) (M : Turing.TM0.Machine Γ Λ)
    (ι : GraphIsoPalomar.Sym ↪ Γ) (c : ℕ),
    (∃ k ≤ 2 ^ (c * 2 ^ 8), ∃ q : Λ, (flip bind (Turing.TM0.step M))^[k]
        (some (Turing.TM0.init ((input path₁ path₂).map ι))) =
      some ⟨q, Turing.Tape.mk₁ ((output true).map ι)⟩ ∧
      Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((output true).map ι)⟩ = none) ∧
    (∃ k ≤ 2 ^ (c * 2 ^ 8), ∃ q : Λ, (flip bind (Turing.TM0.step M))^[k]
        (some (Turing.TM0.init ((input path₁ tri).map ι))) =
      some ⟨q, Turing.Tape.mk₁ ((output false).map ι)⟩ ∧
      Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((output false).map ι)⟩ = none) := by
  obtain ⟨Γ, Λ, i₁, i₂, -, -, M, ι, c, -, h⟩ := gi_singleTape_proof
  have hl : Nat.log 2 3 = 1 := by
    decide +kernel
  obtain ⟨b, hb, k, hk, q, hr, hh⟩ := h 3 path₁ path₂
  obtain ⟨b', hb', k', hk', q', hr', hh'⟩ := h 3 path₁ tri
  have e : b = true := hb.2 ((isoDecide_iff pp).1 pp_iso)
  have e' : b' = false := by
    rw [← Bool.not_eq_true, hb']
    exact fun hi => Bool.false_ne_true (pt_not_iso.symm.trans ((isoDecide_iff pt).2 hi))
  subst e e'
  rw [hl] at hk hk'
  exact ⟨Γ, Λ, i₁, i₂, M, ι, c, ⟨k, hk, q, hr, hh⟩, ⟨k', hk', q', hr', hh'⟩⟩

/-! ### Negative controls -/

/-- The two output words differ under every injective map. -/
example {Γ : Type} (ι : GraphIsoPalomar.Sym ↪ Γ) : (output true).map ι ≠ (output false).map ι := by
  simp [output]

/-- A path and the triangle have different words. -/
example : graphWord path₁ ≠ graphWord tri := by
  decide +kernel

/-- The graph on `Fin 3` with the single edge `0 - 1`. -/
abbrev edge01 : SimpleGraph (Fin 3) := ofAdj 3 fun u v => u.val == 0 && v.val == 1

/-- `graphWord` lists the neighbour lists of the vertices `2, 1, 0`, in that order. -/
example : graphWord edge01 = listWord [listWord [], listWord [natWord 0], listWord [natWord 1]] ∧
    graphWord edge01 ≠ listWord [listWord [natWord 1], listWord [natWord 0], listWord []] := by
  decide +kernel

/-! ### The coset words -/

/-- The 3-cycle `0 ↦ 1 ↦ 2 ↦ 0` as data: forward and inverse images. -/
def c3d : PermData := (#[1, 2, 0], #[2, 0, 1])

/-- The transposition of `0` and `1` as data. -/
def swd : PermData := (#[1, 0, 2], #[1, 0, 2])

/-- The 3-cycle's word: the images of `2, 1, 0`, then their inverse images. -/
example : permWord (PermData.denote 3 c3d) =
    listWord [natWord 0, natWord 2, natWord 1] ++ listWord [natWord 1, natWord 0, natWord 2] := by
  decide +kernel

/-- The output words of the 3-cycle with the generators `[swap, 3-cycle]`, and of `none`, are
the machine's output tapes. -/
example : (cosetWord (cosetData 3 (some (c3d, [swd, c3d])))).map cosetOut =
      SingleTape.encodeOut (ser Ty.giCoset (some (c3d, [swd, c3d]))) ∧
    (cosetWord (cosetData 3 none)).map cosetOut = SingleTape.encodeOut (ser Ty.giCoset none) :=
  ⟨eq_of_wordEq (by decide +kernel), eq_of_wordEq (by decide +kernel)⟩

/-- **The coset theorem on the two paths and on a path and the triangle**: the machine halts with
a coset answer whose `τ` underlies an isomorphism on the first pair, and with `none` on the
second, within `2 ^ (c 2⁸)` transitions. -/
example : ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ) (M : Turing.TM0.Machine Γ Λ)
    (ιin ιout : GraphIsoPalomar.Sym ↪ Γ) (c : ℕ),
    (∃ (τ : Perm (Fin 3)) (gs : List (Perm (Fin 3))), (∃ e : path₁ ≃g path₂, e.toEquiv = τ) ∧
      ∃ k ≤ 2 ^ (c * 2 ^ 8), ∃ q : Λ, (flip bind (Turing.TM0.step M))^[k]
        (some (Turing.TM0.init ((input path₁ path₂).map ιin))) =
      some ⟨q, Turing.Tape.mk₁ ((cosetWord (some (τ, gs))).map ιout)⟩) ∧
    (∃ k ≤ 2 ^ (c * 2 ^ 8), ∃ q : Λ, (flip bind (Turing.TM0.step M))^[k]
        (some (Turing.TM0.init ((input path₁ tri).map ιin))) =
      some ⟨q, Turing.Tape.mk₁ ((cosetWord (n := 3) none).map ιout)⟩) := by
  obtain ⟨Γ, Λ, i₁, i₂, -, -, M, ιin, ιout, c, -, -, h⟩ := gi_coset_singleTape_proof
  have hl : Nat.log 2 3 = 1 := by
    decide +kernel
  obtain ⟨r, hr, hiso, k, hk, q, hrun, -⟩ := h 3 path₁ path₂
  obtain ⟨r', hr', -, k', hk', q', hrun', -⟩ := h 3 path₁ tri
  rw [hl] at hk hk'
  have hne : Nonempty (path₁ ≃g path₂) := (isoDecide_iff pp).1 pp_iso
  have hemp : IsEmpty (path₁ ≃g tri) := not_nonempty_iff.1 fun hi =>
    Bool.false_ne_true (pt_not_iso.symm.trans ((isoDecide_iff pt).2 hi))
  obtain rfl : r' = none := hr'.2 hemp
  rcases r with _ | ⟨τ, gs⟩
  · exact absurd (hr.1 rfl) (not_isEmpty_iff.2 hne)
  · have hτ : ∃ e : path₁ ≃g path₂, e.toEquiv = τ :=
      (hiso τ gs rfl τ).2 (by rw [inv_mul_cancel]; exact Subgroup.one_mem _)
    exact ⟨Γ, Λ, i₁, i₂, M, ιin, ιout, c, ⟨τ, gs, hτ, k, hk, q, hrun⟩, ⟨k', hk', q', hrun'⟩⟩

/-! ### Negative controls for the coset words -/

/-- Listing the images from `0` upwards gives another word. -/
example : permWord (PermData.denote 3 c3d) ≠
    listWord ((List.finRange 3).map fun i => natWord (PermData.denote 3 c3d i)) ++
      listWord ((List.finRange 3).map fun i => natWord ((PermData.denote 3 c3d).symm i)) := by
  decide +kernel

/-- The word of `none` is not the word of any `some`. -/
example {n : ℕ} (x : Perm (Fin n) × List (Perm (Fin n))) :
    cosetWord (n := n) none ≠ cosetWord (some x) := by
  simp [cosetWord]

end GraphIsoChecks.Palomar
