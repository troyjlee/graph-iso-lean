module

public import GraphIso.Graph.Swap

/-!
# Small subsets as canonical triples

A set of at most three numbers is represented by its **canonical triple**: the elements in
increasing order, with a missing element replaced by the least one, so `{a}` is `(a, a, a)`,
`{a < c}` is `(a, a, c)` and `{a < b < c}` is `(a, b, c)`.

* `canon t`: the canonical triple of the set of the entries of `t`, computed by sorting
  (`sort3`) and padding. It is canonical with the same set (`canon_spec`), and a canonical
  triple is determined by its set (`canonical_unique`); so `canon` depends only on the set
  (`canon_eq_of_tset`).
* `tripsL ℓ`: the triples of `0, …, ℓ − 1` in lexicographic order; `subsL ℓ`: the canonical
  ones, one for each nonempty subset of at most three elements.
-/

@[expose] public section

namespace GraphIso.Graph

/-! ### Sorting -/

/-- Two numbers in increasing order. -/
def sort2 (a b : ℕ) : ℕ × ℕ := if a ≤ b then (a, b) else (b, a)

/-- Three numbers in increasing order. -/
def sort3 (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  ((sort2 (sort2 t.1 t.2.1).1 (sort2 (sort2 t.1 t.2.1).2 t.2.2).1).1,
    (sort2 (sort2 t.1 t.2.1).1 (sort2 (sort2 t.1 t.2.1).2 t.2.2).1).2,
    (sort2 (sort2 t.1 t.2.1).2 t.2.2).2)

/-- The set of the entries of a triple. -/
def tset (t : ℕ × ℕ × ℕ) : Finset ℕ := {t.1, t.2.1, t.2.2}

theorem mem_tset {t : ℕ × ℕ × ℕ} {x : ℕ} : x ∈ tset t ↔ x = t.1 ∨ x = t.2.1 ∨ x = t.2.2 := by
  simp [tset]

theorem sort3_spec (t : ℕ × ℕ × ℕ) :
    (sort3 t).1 ≤ (sort3 t).2.1 ∧ (sort3 t).2.1 ≤ (sort3 t).2.2 ∧
      ∀ x, x ∈ tset (sort3 t) ↔ x ∈ tset t := by
  obtain ⟨a, b, c⟩ := t
  simp only [sort3, sort2, mem_tset]
  split_ifs <;> (try dsimp only) <;>
    refine ⟨by omega, by omega, fun x => ⟨fun h => by omega, fun h => by omega⟩⟩

/-- A canonical triple: increasing, with a repeated last pair only for a singleton. -/
def Canonical (t : ℕ × ℕ × ℕ) : Prop :=
  t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ (t.2.1 = t.2.2 → t.1 = t.2.1)

instance (t : ℕ × ℕ × ℕ) : Decidable (Canonical t) := by unfold Canonical; infer_instance

/-- The canonical triple of the set of the entries of `t`. -/
def canon (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if (sort3 t).2.1 = (sort3 t).2.2 then ((sort3 t).1, (sort3 t).1, (sort3 t).2.2) else sort3 t

theorem canon_spec (t : ℕ × ℕ × ℕ) : Canonical (canon t) ∧ tset (canon t) = tset t := by
  obtain ⟨h₁, h₂, h₃⟩ := sort3_spec t
  unfold canon Canonical
  split
  · rename_i h
    refine ⟨⟨le_refl _, show (sort3 t).1 ≤ (sort3 t).2.2 by omega, fun _ => rfl⟩,
      Finset.ext fun x => ?_⟩
    rw [← h₃ x, mem_tset, mem_tset]
    simp only
    constructor <;> intro h' <;> omega
  · rename_i h
    exact ⟨⟨h₁, h₂, fun e => absurd e h⟩, Finset.ext h₃⟩

/-- **A canonical triple is determined by its set.** -/
theorem canonical_unique {u v : ℕ × ℕ × ℕ} (hu : Canonical u) (hv : Canonical v)
    (h : tset u = tset v) : u = v := by
  obtain ⟨a, b, c⟩ := u
  obtain ⟨a', b', c'⟩ := v
  obtain ⟨hu₁, hu₂, hu₃⟩ := hu
  obtain ⟨hv₁, hv₂, hv₃⟩ := hv
  simp only at hu₁ hu₂ hu₃ hv₁ hv₂ hv₃
  have m : ∀ x, (x = a ∨ x = b ∨ x = c) ↔ (x = a' ∨ x = b' ∨ x = c') := fun x => by
    have := congrArg (x ∈ ·) h
    simpa [mem_tset] using this
  have ma := (m a).1 (Or.inl rfl)
  have mb := (m b).1 (Or.inr (Or.inl rfl))
  have mc := (m c).1 (Or.inr (Or.inr rfl))
  have ma' := (m a').2 (Or.inl rfl)
  have mb' := (m b').2 (Or.inr (Or.inl rfl))
  have mc' := (m c').2 (Or.inr (Or.inr rfl))
  have e₁ : a = a' := by omega
  have e₃ : c = c' := by omega
  have e₂ : b = b' := by omega
  rw [e₁, e₂, e₃]

theorem canon_eq_of_tset {t t' : ℕ × ℕ × ℕ} (h : tset t = tset t') : canon t = canon t' :=
  canonical_unique (canon_spec t).1 (canon_spec t').1
    (by rw [(canon_spec t).2, (canon_spec t').2, h])

theorem canon_of_canonical {t : ℕ × ℕ × ℕ} (h : Canonical t) : canon t = t :=
  canonical_unique (canon_spec t).1 h (canon_spec t).2

/-- Apply `f` to each entry. -/
def tmap (f : ℕ → ℕ) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (f t.1, f t.2.1, f t.2.2)

theorem tset_tmap (f : ℕ → ℕ) (t : ℕ × ℕ × ℕ) : tset (tmap f t) = (tset t).image f := by
  simp [tset, tmap, Finset.image_insert]

/-! ### Triples and canonical triples of `0, …, ℓ − 1` -/

/-- The triples in lexicographic order. -/
def tripsL (ℓ : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range ℓ).flatMap fun i =>
    (List.range ℓ).flatMap fun j => (List.range ℓ).map fun k => (i, j, k)

theorem mem_tripsL {ℓ : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ tripsL ℓ ↔ t.1 < ℓ ∧ t.2.1 < ℓ ∧ t.2.2 < ℓ := by
  obtain ⟨i, j, k⟩ := t
  simp [tripsL]

theorem nodup_tripsL (ℓ : ℕ) : (tripsL ℓ).Nodup := by
  unfold tripsL
  refine List.nodup_flatMap.2 ⟨fun i _ => List.nodup_flatMap.2 ⟨fun j _ =>
    List.nodup_range.map fun k k' h => by simpa using h, ?_⟩, ?_⟩
  · exact List.nodup_range.pairwise_of_forall_ne fun j _ j' _ hne =>
      List.disjoint_left.2 fun t ht ht' => by
        simp only [List.mem_map, List.mem_range] at ht ht'
        obtain ⟨k, -, rfl⟩ := ht
        obtain ⟨k', -, he⟩ := ht'
        simp only [Prod.mk.injEq] at he
        exact hne he.2.1.symm
  · exact List.nodup_range.pairwise_of_forall_ne fun i _ i' _ hne =>
      List.disjoint_left.2 fun t ht ht' => by
        simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ht ht'
        obtain ⟨j, -, k, -, rfl⟩ := ht
        obtain ⟨j', -, k', -, he⟩ := ht'
        simp only [Prod.mk.injEq] at he
        exact hne he.1.symm

theorem length_tripsL (ℓ : ℕ) : (tripsL ℓ).length = ℓ * ℓ * ℓ := by
  simp [tripsL, List.length_flatMap, List.sum_replicate, Nat.mul_assoc]

/-- The canonical triples: one for each nonempty subset of at most three elements. -/
def subsL (ℓ : ℕ) : List (ℕ × ℕ × ℕ) := (tripsL ℓ).filter fun t => decide (Canonical t)

theorem mem_subsL {ℓ : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ subsL ℓ ↔ (t.1 < ℓ ∧ t.2.1 < ℓ ∧ t.2.2 < ℓ) ∧ Canonical t := by
  simp [subsL, mem_tripsL]

theorem nodup_subsL (ℓ : ℕ) : (subsL ℓ).Nodup := (nodup_tripsL ℓ).filter _

theorem length_subsL_le (ℓ : ℕ) : (subsL ℓ).length ≤ ℓ * ℓ * ℓ :=
  (List.length_filter_le _ _).trans (length_tripsL ℓ).le

/-- The canonical triple of a triple of numbers below `ℓ` is listed. -/
theorem canon_mem_subsL {ℓ : ℕ} {t : ℕ × ℕ × ℕ} (h : t.1 < ℓ ∧ t.2.1 < ℓ ∧ t.2.2 < ℓ) :
    canon t ∈ subsL ℓ := by
  obtain ⟨hc, hs⟩ := canon_spec t
  refine mem_subsL.2 ⟨?_, hc⟩
  have hm : ∀ x ∈ tset (canon t), x < ℓ := fun x hx => by
    rw [hs, mem_tset] at hx
    omega
  exact ⟨hm _ (mem_tset.2 (Or.inl rfl)), hm _ (mem_tset.2 (Or.inr (Or.inl rfl))),
    hm _ (mem_tset.2 (Or.inr (Or.inr rfl)))⟩

end GraphIso.Graph
