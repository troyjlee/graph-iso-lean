module

public import GraphIso.Pyber.Discharge
public import GraphIsoChecks.PyberThm7
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Checks of stage 15d: Lemma 12 and the discharge

`PLAN-15.md` §6 item 4. As in stages 15a–15c, the checks are instantiations of the library, with
kernel `decide` for the numbers.

* **The prime count at `L = 1`:** `π(64) = 18`, and `card_primesLE_ge` gives `3 ≤ π(64)`.
* **The permutation** for the odd primes `{3, 5, 7}` (sum `15`) in `Alt(15)`: its order is
  divisible by `3`, `5` and `7`.
* **A negative control for the threshold:** `Sym(3)` on `Fin 3` is primitive and maps onto the
  trivial group `Alt(2)`, not injectively; here `|Λ| = 2 < Kpy 3 = 6144`.
* **Numbers:** `Kpy 1 = 192`, `Kpy 3 = 6144`, and the arithmetic of Lemma 12 for small `ℓ`.
-/

@[expose] public section

namespace GraphIsoChecks.PyberLemma12

open GraphIso.Pyber GraphIsoChecks.Pyber GraphIsoChecks.PyberPerm MulAction Subgroup Equiv
  Equiv.Perm Finset

/-! ### The primes -/

theorem card_primesLE_64 : #(Nat.primesLE 64) = 18 := by
  decide +kernel

/-- `card_primesLE_ge` at `L = 1`: `3 ≤ π(64)`. -/
example : 3 ≤ #(Nat.primesLE 64) :=
  card_primesLE_ge (L := 1) le_rfl

/-- **The permutation for `{3, 5, 7}`:** an even permutation of `Fin 15` whose order is
divisible by `3`, `5` and `7`. -/
example : ∃ σ ∈ alternatingGroup (Fin 15), ∀ p ∈ ({3, 5, 7} : Finset ℕ), p ∣ orderOf σ :=
  exists_mem_alternatingGroup _ (by decide +kernel) (by rw [Fintype.card_fin]; decide +kernel)

/-! ### A negative control for the threshold -/

theorem subsingleton_alt2 : Subsingleton (alternatingGroup (Fin 2)) := by
  rw [← Finite.card_le_one_iff_subsingleton, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide +kernel

/-- **Without the threshold, Lemma 12 fails:** `Sym(3)` on `Fin 3` is faithful and primitive,
the trivial homomorphism onto `Alt(2)` is surjective, and it is not injective. -/
example : Function.Surjective (1 : Perm (Fin 3) →* alternatingGroup (Fin 2)) ∧
    ¬Function.Injective (1 : Perm (Fin 3) →* alternatingGroup (Fin 2)) ∧
    Fintype.card (Fin 2) < Kpy (Nat.card (Fin 3)) := by
  refine ⟨fun q => ⟨1, subsingleton_alt2.elim _ _⟩, fun h => ?_, ?_⟩
  · have := h (a₁ := swap 0 1) (a₂ := 1) rfl
    exact absurd (congrArg (fun σ : Perm (Fin 3) => σ 0) this) (by decide)
  · rw [Fintype.card_fin, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide +kernel

/-! ### Numbers -/

example : Kpy 1 = 192 ∧ Kpy 3 = 6144 := by
  decide +kernel

/-- The arithmetic of Lemma 12: `R · 64 (ℓ + 1)³ ≤ 192 (ℓ + 1)⁵` with `R = 2 ℓ² + ℓ + 2`, and
`R ≤ 2 (ℓ + 1)²`. -/
example : ∀ l < 32, (2 * l ^ 2 + l + 2) * (64 * (l + 1) ^ 3) ≤ 192 * (l + 1) ^ 5 ∧
    2 * l ^ 2 + l + 2 ≤ 2 * (l + 1) ^ 2 := by
  decide +kernel

end GraphIsoChecks.PyberLemma12
