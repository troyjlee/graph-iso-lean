module

public import GraphIso.Pyber.Theorem7
public import GraphIsoChecks.PyberPerm
public import Mathlib.Data.Finite.Perm
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 15c: Theorem 7

`PLAN-15.md` §5 item 5. As in stages 15a and 15b, the checks are instantiations of the library,
with kernel `decide` for the numbers.

* **Wielandt's lemma and its corollary on `Sym(3)`** at the self-paired orbital of `(0, 1)`.
* **Theorem 7 on `Sym(4)`:** `|compA G_0| ≤ 2 λ(4)² + 1 = 9` and `|compA G| ≤ 11`.
* **A negative control:** core-freeness is needed. In `Sym(3)`, `⊤` has index `1`, and
  `|compA ⊤| = 2 > 2 λ(1)² + 1 = 1`.
* **The dichotomy of Lemma 10, both alternatives:** `Alt(3)` on `Fin 3` satisfies
  `|G| ≤ |Ω|^(λ(|Ω|)+1)`; `Sym(8)` on `Fin 8` does not (`8! > 8^4`), so the dichotomy gives
  `compA Sym(8) ⊆ compA G_0`.
* **Numbers:** the inequalities of the induction, for small values, by kernel `decide`.
-/

@[expose] public section

namespace GraphIsoChecks.PyberThm7

open GraphIso.Pyber GraphIsoChecks.Pyber GraphIsoChecks.PyberPerm MulAction Subgroup Equiv
  Equiv.Perm

/-! ### Wielandt's lemma and its corollary on `Sym(3)` -/

/-- **Wielandt's lemma on `Sym(3)`:** `compA T(0) ⊆ compA (G_{01} ⧸ T(0))`. -/
example : compA (suborbitKer (Perm (Fin 3)) (0 : Fin 3) 1 0) ⊆
    compA (↥(stabilizer (Perm (Fin 3)) (0 : Fin 3) ⊓ stabilizer (Perm (Fin 3)) (1 : Fin 3)) ⧸
      (suborbitKer (Perm (Fin 3)) (0 : Fin 3) 1 0).subgroupOf
        (stabilizer (Perm (Fin 3)) (0 : Fin 3) ⊓ stabilizer (Perm (Fin 3)) (1 : Fin 3))) :=
  compA_suborbitKer_subset faithful_perm3 (by decide) selfPaired_perm3

/-- **Wielandt's corollary on `Sym(3)`:** `compA G_0 ⊆ compA P ∪ compA P_1`. -/
example : compA (stabilizer (Perm (Fin 3)) (0 : Fin 3)) ⊆
    compA (toPermHom (stabilizer (Perm (Fin 3)) (0 : Fin 3))
      (orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3))).range ∪
    compA (stabilizer (toPermHom (stabilizer (Perm (Fin 3)) (0 : Fin 3))
      (orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3))).range
      (⟨1, mem_orbit_self 1⟩ : orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3))) :=
  compA_stabilizer_subset faithful_perm3 (by decide) selfPaired_perm3

/-! ### Theorem 7 on `Sym(4)` -/

theorem faithful_perm4 : Faithful (Perm (Fin 4)) (Fin 4) :=
  fun _ h => Equiv.ext h

/-- **Theorem 7 on `Sym(4)`:** `|compA G_0| ≤ 2 λ(4)² + 1 = 9`. -/
example : (compA (stabilizer (Perm (Fin 4)) (0 : Fin 4))).ncard ≤ 9 := by
  have h := ncard_compA_stabilizer_le faithful_perm4 (0 : Fin 4)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.log 2 4 = 2 by decide +kernel] at h

/-- **The corollary on `Sym(4)`:** `|compA G| ≤ 2 λ(4)² + λ(4) + 1 = 11`. -/
example : (compA (Perm (Fin 4))).ncard ≤ 11 := by
  have h := ncard_compA_le_of_transitive faithful_perm4
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, show Nat.log 2 4 = 2 by decide +kernel] at h

/-- **A negative control:** without core-freeness the bound fails. In `Sym(3)`, `⊤` has index
`1` and `|compA ⊤| = |{2, 3}| = 2 > 2 λ(1)² + 1 = 1`. -/
example : ¬(compA (⊤ : Subgroup (Perm (Fin 3)))).ncard ≤
    2 * Nat.log 2 (⊤ : Subgroup (Perm (Fin 3))).index ^ 2 + 1 := by
  rw [compA_eq_of_mulEquiv Subgroup.topEquiv, compA_perm3, index_top,
    Set.ncard_pair (by decide)]
  decide +kernel

/-! ### The dichotomy of Lemma 10 -/

instance isPreprimitive_alt3 : IsPreprimitive (alternatingGroup (Fin 3)) (Fin 3) :=
  alternatingGroup.isPreprimitive_of_three_le_card (Fin 3) (by simp)

instance nontrivial_alt3 : Nontrivial (alternatingGroup (Fin 3)) :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [card_alt3]; decide)

/-- **The first alternative on `Alt(3)`:** `|G| ≤ 3^(λ(3) + 1)` or `compA G ⊆ compA G_0`; here
the first holds, `3 ≤ 9`. -/
example : Nat.card (alternatingGroup (Fin 3)) ≤ 3 ^ (Nat.log 2 3 + 1) ∨
    compA (alternatingGroup (Fin 3)) ⊆
      compA (stabilizer (alternatingGroup (Fin 3)) (0 : Fin 3)) := by
  have h := card_le_or_compA_subset (faithful_perm (alternatingGroup (Fin 3))) (0 : Fin 3)
  rwa [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h

example : Nat.card (alternatingGroup (Fin 3)) ≤ 3 ^ (Nat.log 2 3 + 1) := by
  rw [card_alt3, show Nat.log 2 3 = 1 by decide +kernel]
  decide +kernel

/-- **The second alternative on `Sym(8)`:** `|G| = 8! > 8^(λ(8) + 1) = 4096`, so the dichotomy
gives `compA Sym(8) ⊆ compA G_0`. -/
example : compA (Perm (Fin 8)) ⊆ compA (stabilizer (Perm (Fin 8)) (0 : Fin 8)) := by
  refine (card_le_or_compA_subset (fun _ h => Equiv.ext h) (0 : Fin 8)).resolve_left ?_
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin,
    show Nat.log 2 8 = 3 by decide +kernel]
  decide +kernel

/-! ### Numbers -/

/-- Lemma 8's step: `F(t) + F(b) + λ(b) ≤ F(t b)` for `t, b ≥ 2`, with `F(m) = 2 λ(m)² + 1`. -/
example : ∀ t < 24, ∀ b < 24, 2 ≤ t → 2 ≤ b →
    (2 * Nat.log 2 t ^ 2 + 1) + (2 * Nat.log 2 b ^ 2 + 1) + Nat.log 2 b ≤
      2 * Nat.log 2 (t * b) ^ 2 + 1 := by
  decide +kernel

/-- The imprimitive `P`: `F(t) + F(b) + λ(b) + λ(t b) ≤ F(t b + 1)`, the worst case `n = d + 1`
of `d = t b < n`. -/
example : ∀ t < 16, ∀ b < 16, 2 ≤ t → 2 ≤ b →
    (2 * Nat.log 2 t ^ 2 + 1) + (2 * Nat.log 2 b ^ 2 + 1) + Nat.log 2 b + Nat.log 2 (t * b) ≤
      2 * Nat.log 2 (t * b + 1) ^ 2 + 1 := by
  decide +kernel

/-- The abelian case: `λ(d^(λ(d) + 1)) ≤ F(d)`. -/
example : ∀ d < 64, Nat.log 2 (d ^ (Nat.log 2 d + 1)) ≤ 2 * Nat.log 2 d ^ 2 + 1 := by
  decide +kernel

end GraphIsoChecks.PyberThm7
