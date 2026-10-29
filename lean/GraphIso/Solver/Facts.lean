module

public import GraphIso.Reductions.SubgroupProg

/-!
# Facts used by the solver

* `IsLeftTransversal.card_eq`: a left transversal of `K ≤ G` with `k` representatives gives
  `|G| = k |K|`. Applied to the point stabilizer this is the orbit–stabilizer count; it is what
  makes the branching step decrease the group order.
* Consequences of an exact orbit partition (`IsOrbitPartition`) of a nonempty window: it is
  nonempty; with one orbit the window is transitive; with several orbits each is strictly
  smaller than the window and their sizes add up to it.
* A one-point invariant window is fixed pointwise, so a window that is transitive but not
  fixed pointwise has at least two points.
* An orbit transversal of a transitive window has one pair per window point.
-/

@[expose] public section

namespace GraphIso

open Equiv

/-- A left transversal with `k` representatives: `|G| = k |K|`. -/
theorem IsLeftTransversal.card_eq {M : Type*} [Group M] {G K : Subgroup M} {k : ℕ}
    {r : Fin k → M} (hr : IsLeftTransversal G K r) (hK : K ≤ G) :
    Nat.card G = k * Nat.card K := by
  let f : Fin k × K → G := fun p => ⟨r p.1 * p.2, mul_mem (hr.mem p.1) (hK p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, κ⟩ ⟨j, κ'⟩ h
      simp only [f, Subtype.mk.injEq] at h
      have hij : (r i)⁻¹ * r j ∈ K := by
        have e : (r i)⁻¹ * r j = (κ : M) * (κ' : M)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
        rw [e]
        exact mul_mem κ.2 (inv_mem κ'.2)
      obtain rfl := hr.distinct i j hij
      have : κ = κ' := Subtype.ext (mul_left_cancel h)
      rw [this]
    · rintro ⟨g, hg⟩
      obtain ⟨i, hi⟩ := hr.cover g hg
      exact ⟨(i, ⟨_, hi⟩), Subtype.ext (by simp [f])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_eq_fintype_card,
    Fintype.card_fin]

theorem le_sum_of_mem_nat {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h
      simp only [List.sum_cons]
      omega

section OrbitPartition

variable {n : ℕ} {G : Subgroup (Perm (Fin n))} {w : WinData} {os : List (List ℕ)}

theorem IsOrbitPartition.length_sum (h : IsOrbitPartition G w os) :
    (os.map List.length).sum = w.1.length := by
  rw [← List.length_flatten]
  exact h.1.length_eq

theorem IsOrbitPartition.ne_nil (h : IsOrbitPartition G w os) (hw : w.1 ≠ []) : os ≠ [] := by
  rintro rfl
  exact hw (List.Perm.eq_nil h.1.symm)

theorem IsOrbitPartition.length_pos (h : IsOrbitPartition G w os) {o : List ℕ} (ho : o ∈ os) :
    0 < o.length :=
  List.length_pos_of_ne_nil (h.2 o ho).1

/-- With a single orbit, the window is transitive. -/
theorem IsOrbitPartition.transitive_of_singleton {o : List ℕ}
    (h : IsOrbitPartition G w [o]) {i : ℕ} (hi : i ∈ w.1) :
    ∀ j, j ∈ w.1 ↔ SameOrbit G i j := by
  have hmem : ∀ j, j ∈ o ↔ j ∈ w.1 := fun j => by
    have := h.1.mem_iff (a := j)
    simpa using this
  intro j
  rw [← hmem, ((h.2 o List.mem_cons_self).2 i ((hmem i).2 hi) j)]

/-- With several orbits, each is strictly smaller than the window. -/
theorem IsOrbitPartition.length_lt {o₀ o₁ : List ℕ} {rest : List (List ℕ)}
    (h : IsOrbitPartition G w (o₀ :: o₁ :: rest)) {o : List ℕ} (ho : o ∈ o₀ :: o₁ :: rest) :
    o.length < w.1.length := by
  have hsum := h.length_sum
  have hpos := fun o (ho : o ∈ o₀ :: o₁ :: rest) => h.length_pos ho
  have h₀ := hpos o₀ List.mem_cons_self
  have h₁ := hpos o₁ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [List.map_cons, List.sum_cons] at hsum
  rcases List.mem_cons.1 ho with rfl | ho
  · omega
  rcases List.mem_cons.1 ho with rfl | ho
  · omega
  have : o.length ≤ (rest.map List.length).sum :=
    le_sum_of_mem_nat (List.mem_map_of_mem ho)
  omega

end OrbitPartition

/-- A one-point invariant window is fixed pointwise. -/
theorem fixesPointwise_of_singleton {n : ℕ} {G : Subgroup (Perm (Fin n))} {w : WinData} {u : ℕ}
    (hw1 : w.1 = [u]) (hinv : IsInvariant G (w.denote n)) : FixesPointwise G (w.denote n) := by
  intro g hg v hv
  have hv' : v.val ∈ w.1 := hv
  have hgv : (g v).val ∈ w.1 := hinv g hg v hv
  rw [hw1, List.mem_singleton] at hv' hgv
  exact Fin.ext (hgv.trans hv'.symm)

/-- An orbit transversal of a transitive window has one pair per window point. -/
theorem length_orbitTransversal {n : ℕ} {G : Subgroup (Perm (Fin n))} {w : WinData}
    (hw : w.Valid n) {u : ℕ} (htrans : ∀ j, j ∈ w.1 ↔ SameOrbit G u j)
    {trs : List (ℕ × PermData)} (hnd : (trs.map Prod.fst).Nodup)
    (horb : ∀ j, j ∈ trs.map Prod.fst ↔ SameOrbit G u j) : trs.length = w.1.length := by
  have hperm : (trs.map Prod.fst).Perm w.1 :=
    (List.perm_ext_iff_of_nodup hnd hw.nodup).2 fun j => (horb j).trans (htrans j).symm
  simpa using hperm.length_eq

end GraphIso
