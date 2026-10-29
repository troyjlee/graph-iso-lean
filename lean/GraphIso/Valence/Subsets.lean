module

public import GraphIso.Graph.StepModel
public import Mathlib.Data.List.Sort

/-!
# Subsets of at most `Δ` points as sublists

For maximum degree `Δ`, a layer step reads the layer string on the subsets of a level with at
most `Δ` points. A subset of the increasing list `l` of the level's points is represented by
the sublist of `l` with its elements (`subsR Δ l`):

* `subsR Δ l`: the sublists of `l` with at most `Δ` elements, the empty one first. It is
  computed by one pass over `l` from the right, extending each sublist of fewer than `Δ`
  elements by the new head; the cost-language program follows the same recursion.
* `mem_subsR`: its members are exactly the sublists of `l` of length at most `Δ`; it has no
  repetition (`nodup_subsR`).
* For an increasing list `l`, a sublist is determined by its elements (`eq_of_toFinset_eq`),
  and every set of at most `Δ` points of `l` is the set of a member (`exists_subsR`).
* `length_subsR_le`: there are at most `(|l| + 1)^Δ` of them.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

/-- The sublists of `l` with at most `Δ` elements. -/
def subsR (Δ : ℕ) : List ℕ → List (List ℕ)
  | [] => [[]]
  | x :: l => subsR Δ l ++ ((subsR Δ l).filter fun s => decide (s.length < Δ)).map (x :: ·)

theorem subsR_cons (Δ x : ℕ) (l : List ℕ) :
    subsR Δ (x :: l) =
      subsR Δ l ++ ((subsR Δ l).filter fun s => decide (s.length < Δ)).map (x :: ·) := rfl

/-- **The members of `subsR Δ l`**: the sublists of `l` with at most `Δ` elements. -/
theorem mem_subsR {Δ : ℕ} : ∀ {l s : List ℕ}, s ∈ subsR Δ l ↔ s.Sublist l ∧ s.length ≤ Δ
  | [], s => by
    simp only [subsR, List.mem_singleton, List.sublist_nil]
    constructor
    · rintro rfl
      exact ⟨rfl, by simp⟩
    · exact fun h => h.1
  | x :: l, s => by
    rw [subsR_cons, List.mem_append, List.mem_map, List.sublist_cons_iff, mem_subsR]
    simp only [List.mem_filter, mem_subsR, decide_eq_true_eq]
    constructor
    · rintro (⟨h₁, h₂⟩ | ⟨t, ⟨⟨h₁, -⟩, h₂⟩, rfl⟩)
      · exact ⟨Or.inl h₁, h₂⟩
      · exact ⟨Or.inr ⟨t, rfl, h₁⟩, by simp only [List.length_cons]; omega⟩
    · rintro ⟨h₁ | ⟨t, rfl, h₁⟩, h₂⟩
      · exact Or.inl ⟨h₁, h₂⟩
      · simp only [List.length_cons] at h₂
        exact Or.inr ⟨t, ⟨⟨h₁, by omega⟩, by omega⟩, rfl⟩

/-- The empty list is the first member. -/
theorem subsR_head (Δ : ℕ) : ∀ l : List ℕ, ∃ rest, subsR Δ l = [] :: rest
  | [] => ⟨[], rfl⟩
  | x :: l => by
    obtain ⟨rest, h⟩ := subsR_head Δ l
    exact ⟨rest ++ _, by rw [subsR_cons, h, List.cons_append]⟩

theorem nodup_subsR (Δ : ℕ) : ∀ {l : List ℕ}, l.Nodup → (subsR Δ l).Nodup
  | [], _ => List.nodup_singleton _
  | x :: l, h => by
    rw [List.nodup_cons] at h
    rw [subsR_cons, List.nodup_append]
    refine ⟨nodup_subsR Δ h.2, ((nodup_subsR Δ h.2).filter _).map fun _ _ e => by
      simpa using e, fun s hs t ht => ?_⟩
    rintro rfl
    obtain ⟨t', -, rfl⟩ := List.mem_map.1 ht
    exact h.1 ((mem_subsR.1 hs).1.subset List.mem_cons_self)

/-- **A sublist of an increasing list is determined by its elements.** -/
theorem eq_of_toFinset_eq {l s t : List ℕ} (hl : l.Pairwise (· < ·)) (hs : s.Sublist l)
    (ht : t.Sublist l) (h : s.toFinset = t.toFinset) : s = t :=
  List.SortedLT.eq_of_mem_iff (hl.sublist hs).sortedLT (hl.sublist ht).sortedLT fun a => by
    rw [← List.mem_toFinset, h, List.mem_toFinset]

/-- **Every set of at most `Δ` points of `l` is the set of a member.** -/
theorem exists_subsR {Δ : ℕ} {l : List ℕ} (hl : l.Nodup) {T : Finset ℕ}
    (hT : ∀ x ∈ T, x ∈ l) (hc : T.card ≤ Δ) : ∃ s ∈ subsR Δ l, s.toFinset = T := by
  have hset : (l.filter fun x => decide (x ∈ T)).toFinset = T := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hT x h, h⟩⟩
  refine ⟨l.filter fun x => decide (x ∈ T), mem_subsR.2 ⟨List.filter_sublist, ?_⟩, hset⟩
  rw [← List.toFinset_card_of_nodup (hl.filter _), hset]
  exact hc

theorem length_filter_subsR_le {Δ : ℕ} {l : List ℕ} (hl : l.Nodup) :
    ((subsR (Δ + 1) l).filter fun s => decide (s.length < Δ + 1)).length ≤ (subsR Δ l).length := by
  refine (List.subperm_of_subset ((nodup_subsR _ hl).filter _) fun s hs => ?_).length_le
  obtain ⟨hs₁, hs₂⟩ := List.mem_filter.1 hs
  refine mem_subsR.2 ⟨(mem_subsR.1 hs₁).1, ?_⟩
  simp only [decide_eq_true_eq] at hs₂
  omega

/-- **There are at most `(|l| + 1)^Δ` sublists of at most `Δ` elements.** -/
theorem length_subsR_le : ∀ (Δ : ℕ) {l : List ℕ}, l.Nodup →
    (subsR Δ l).length ≤ (l.length + 1) ^ Δ
  | Δ, [], _ => by simp [subsR]
  | 0, x :: l, h => by
    rw [List.nodup_cons] at h
    have e : ((subsR 0 l).filter fun s => decide (s.length < 0)) = [] := by simp
    rw [subsR_cons, e, List.map_nil, List.append_nil]
    have := length_subsR_le 0 h.2
    simpa using this
  | Δ + 1, x :: l, h => by
    rw [List.nodup_cons] at h
    rw [subsR_cons, List.length_append, List.length_map, List.length_cons]
    have h₁ := length_subsR_le (Δ + 1) h.2
    have h₂ := (length_filter_subsR_le (Δ := Δ) h.2).trans (length_subsR_le Δ h.2)
    have h₃ : (l.length + 1) ^ Δ ≤ (l.length + 1 + 1) ^ Δ := Nat.pow_le_pow_left (by omega) _
    calc _ ≤ (l.length + 1) ^ (Δ + 1) + (l.length + 1) ^ Δ := Nat.add_le_add h₁ h₂
      _ = (l.length + 1) ^ Δ * (l.length + 1 + 1) := by ring
      _ ≤ (l.length + 1 + 1) ^ Δ * (l.length + 1 + 1) := Nat.mul_le_mul_right _ h₃
      _ = (l.length + 1 + 1) ^ (Δ + 1) := by ring

end GraphIso.Graph.Valence
