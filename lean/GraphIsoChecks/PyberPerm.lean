module

public import GraphIso.Pyber.OddOrder
public import GraphIsoChecks.Pyber
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 15b: permutation groups and the odd-order bound

`PLAN-15.md` §4 item 7. As in stage 15a, the checks are instantiations of the library, with
kernel `decide` for the numbers.

* **`Sym(3)` on `Fin 3`:** the orbital of `(0, 1)` is self-paired (by the involution
  `swap 0 1`), and `Δ(0) = {1, 2}`. So `2 |Δ(0)| + 1 = 5 > 3`: the suborbit bound fails without
  odd order (a negative control). Jordan's lemma: `2` divides `|G_0| = 2`, hence `|P|`.
* **`Alt(3)` on `Fin 3`** (order `3`, odd): the orbital of `(0, 1)` is not self-paired,
  `2 |Δ(0)| + 1 ≤ 3`, and the odd-order bound gives `ω(3) ≤ 1`.
* **A negative control for connectivity:** the rotations of `Fin 4` act transitively, and
  `{0, 2}` is closed along the orbital of `(0, 2)` but is not everything. So the connectivity
  lemma needs primitivity, not just transitivity.
* **Numbers:** the two inequalities of the induction, for small values, by kernel `decide`.
-/

@[expose] public section

namespace GraphIsoChecks.PyberPerm

open GraphIso.Pyber GraphIsoChecks.Pyber MulAction Subgroup Equiv Equiv.Perm

/-! ### `Sym(3)` on `Fin 3` -/

theorem faithful_perm3 : Faithful (Perm (Fin 3)) (Fin 3) :=
  fun _ h => Equiv.ext h

/-- The orbital of `(0, 1)` is self-paired: `swap 0 1` exchanges the two points. -/
theorem selfPaired_perm3 :
    ((1 : Fin 3), (0 : Fin 3)) ∈ orbit (Perm (Fin 3)) ((0 : Fin 3), (1 : Fin 3)) := by
  have h := swap_mem_orbit_of_mul_self (G := Perm (Fin 3)) (swap_mul_self (0 : Fin 3) 1)
    (0 : Fin 3)
  rwa [Perm.smul_def, swap_apply_left] at h

/-- `Δ(0) = {1, 2}` in `Sym(3)`. -/
theorem suborbit_perm3 :
    orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3) = {1, 2} := by
  ext b
  constructor
  · rintro ⟨h, rfl⟩
    have h0 : (h : Perm (Fin 3)) 0 = 0 := h.2
    have h1 : (h : Perm (Fin 3)) 1 ≠ 0 := fun e =>
      absurd ((h : Perm (Fin 3)).injective (e.trans h0.symm)) (by decide)
    have hc : ∀ c : Fin 3, c ≠ 0 → c = 1 ∨ c = 2 := by decide
    exact hc _ h1
  · rintro (rfl | rfl)
    · exact mem_orbit_self _
    · refine ⟨⟨swap 1 2, ?_⟩, ?_⟩
      · exact swap_apply_of_ne_of_ne (by decide) (by decide)
      · exact swap_apply_left 1 2

theorem ncard_suborbit_perm3 :
    (orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3)).ncard = 2 := by
  rw [suborbit_perm3, Set.ncard_pair (by decide)]

/-- **A negative control:** without odd order, `2 |Δ(x)| + 1 ≤ |Ω|` fails. -/
example : ¬2 * (orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3)).ncard + 1 ≤
    Nat.card (Fin 3) := by
  rw [ncard_suborbit_perm3, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_stabilizer_perm3 : Nat.card (stabilizer (Perm (Fin 3)) (0 : Fin 3)) = 2 := by
  have h := card_mul_index (stabilizer (Perm (Fin 3)) (0 : Fin 3))
  rw [index_stabilizer_of_transitive, card_perm3, show Nat.card (Fin 3) = 3 by simp] at h
  omega

/-- **Jordan's lemma on `Sym(3)`:** `2` divides `|G_0|`, hence the order of its image in
`Perm Δ(0)`. -/
example : 2 ∣ Nat.card (toPermHom (stabilizer (Perm (Fin 3)) (0 : Fin 3))
    (orbit (stabilizer (Perm (Fin 3)) (0 : Fin 3)) (1 : Fin 3))).range :=
  prime_dvd_card_range faithful_perm3 (by decide) Nat.prime_two (by rw [card_stabilizer_perm3])

/-! ### `Alt(3)` on `Fin 3`: odd order -/

instance isPretransitive_alt3 : IsPretransitive (alternatingGroup (Fin 3)) (Fin 3) :=
  alternatingGroup.isPretransitive_of_three_le_card (Fin 3) (by simp)

theorem odd_alt3 : Odd (Nat.card (alternatingGroup (Fin 3))) := by
  rw [card_alt3]
  decide

/-- The orbital of `(0, 1)` under `Alt(3)` is not self-paired. -/
example :
    ((1 : Fin 3), (0 : Fin 3)) ∉ orbit (alternatingGroup (Fin 3)) ((0 : Fin 3), (1 : Fin 3)) :=
  swap_notMem_orbit odd_alt3 (by decide)

example : 2 * (orbit (stabilizer (alternatingGroup (Fin 3)) (0 : Fin 3)) (1 : Fin 3)).ncard + 1 ≤
    3 := by
  have h := two_mul_ncard_suborbit_add_one_le odd_alt3 (show (0 : Fin 3) ≠ 1 by decide)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h

/-- **The odd-order bound on `Alt(3)`:** `ω(3) ≤ λ(3) (λ(3) + 1) / 2 = 1`. -/
example : (Nat.card (alternatingGroup (Fin 3))).primeFactors.card ≤ 1 := by
  have h := card_primeFactors_le_of_odd_action (faithful_perm (alternatingGroup (Fin 3))) odd_alt3
  rwa [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin,
    show Nat.log 2 3 = 1 by decide +kernel] at h

/-! ### The rotations of `Fin 4`: transitive, not primitive -/

theorem rot_add_two (g : Perm (Fin 4)) (hg : g ∈ zpowers (finRotate 4)) (c : Fin 4) :
    g (c + 2) = g c + 2 := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
  clear hg
  have h1 : ∀ c : Fin 4, finRotate 4 (c + 2) = finRotate 4 c + 2 := by decide +kernel
  have h2 : ∀ c : Fin 4, (finRotate 4)⁻¹ (c + 2) = (finRotate 4)⁻¹ c + 2 := by decide +kernel
  induction k using Int.induction_on generalizing c with
  | zero => rfl
  | succ k ih => rw [zpow_add_one, Perm.mul_apply, Perm.mul_apply, h1, ih]
  | pred k ih => rw [zpow_sub_one, Perm.mul_apply, Perm.mul_apply, h2, ih]

instance isPretransitive_rot4 : IsPretransitive (zpowers (finRotate 4)) (Fin 4) :=
  ⟨fun a b => by
    have h : ∀ a b : Fin 4, ∃ k : Fin 4, (finRotate 4 ^ (k : ℕ)) a = b := by decide +kernel
    obtain ⟨k, hk⟩ := h a b
    exact ⟨⟨finRotate 4 ^ (k : ℕ), pow_mem (mem_zpowers _) _⟩, hk⟩⟩

/-- **A negative control for connectivity:** `{0, 2}` contains `0`, is closed along the orbital
of `(0, 2)` under the (transitive) rotations, and is not everything. -/
example : ∃ F : Set (Fin 4), (0 : Fin 4) ∈ F ∧
    (∀ a b, a ∈ F → (a, b) ∈ orbit (zpowers (finRotate 4)) ((0 : Fin 4), (2 : Fin 4)) →
      b ∈ F) ∧ F ≠ Set.univ := by
  refine ⟨{0, 2}, Or.inl rfl, ?_, ?_⟩
  · rintro a b ha ⟨g, hg⟩
    have h1 : (g : Perm (Fin 4)) 0 = a := (Prod.ext_iff.mp hg).1
    have h2 : (g : Perm (Fin 4)) 2 = b := (Prod.ext_iff.mp hg).2
    have h3 := rot_add_two g g.2 0
    rw [zero_add, h1, h2] at h3
    rw [h3]
    have hc : ∀ a : Fin 4, a ∈ ({0, 2} : Set (Fin 4)) → a + 2 ∈ ({0, 2} : Set (Fin 4)) := by
      intro a ha
      rcases ha with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    exact hc a ha
  · intro h
    have h1 : (1 : Fin 4) ∈ ({0, 2} : Set (Fin 4)) := h ▸ Set.mem_univ 1
    rcases h1 with h1 | h1 <;> exact absurd h1 (by decide)

/-! ### Numbers -/

/-- The primitive case: `λ(n) + T(λ(d)) ≤ T(λ(n))` when `2 d < n`, with `T(L) = L(L+1)/2`. -/
example : ∀ n < 64, ∀ d < n, d ≠ 0 → 2 * d < n →
    Nat.log 2 n + Nat.log 2 d * (Nat.log 2 d + 1) / 2 ≤ Nat.log 2 n * (Nat.log 2 n + 1) / 2 := by
  decide +kernel

/-- The imprimitive case: `T(λ(t)) + T(λ(b)) ≤ T(λ(t b))`. -/
example : ∀ t < 24, ∀ b < 24, t ≠ 0 → b ≠ 0 →
    Nat.log 2 t * (Nat.log 2 t + 1) / 2 + Nat.log 2 b * (Nat.log 2 b + 1) / 2 ≤
      Nat.log 2 (t * b) * (Nat.log 2 (t * b) + 1) / 2 := by
  decide +kernel

end GraphIsoChecks.PyberPerm
