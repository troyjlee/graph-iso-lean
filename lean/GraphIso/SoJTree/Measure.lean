module

public import GraphIso.SplitJohnson.Main

/-!
# Leaf multisets, sizes and heights of choice trees

Stage 14d, item 1 (`PLAN-14.md` §8), at the level of milestone 11's model
(`GraphIso/SplitJohnson/CTree.lean`).

* `CTree.leafMs`: the multiset of the leaves of all root-to-leaf paths. Its cardinality is the
  count (`card_leafMs`) and its elements are the reachable leaves (`mem_leafMs`). This is what
  the tree programs of stage 14d enumerate.
* `CTree.size`: the vertices and the edges of a tree. The tree programs' costs are bounded by a
  polynomial times the size, and for a live tree the size is at most `2 (height + 1) · count`
  (`size_le_of_live`).
* `CTree.height`, with the height bounds of `bsoj` (`height_bsoj_le`) and `soj`
  (`height_soj_le`).
* **The index bound of macro-step M4** (`card_orbit_le_count`): if a group preserves the
  colouring, the orbit of a reachable leaf of `soj` consists of reachable leaves, so it has at
  most `count` elements.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset

namespace CTree

variable {C C' O O' : Type*}

/-- The multiset of the leaves of all root-to-leaf paths. -/
def leafMs : CTree C O → Multiset O
  | leaf o => {o}
  | node S k => ∑ c ∈ S, (k c).leafMs

/-- The vertices and the edges of a tree: `1` for a leaf; for a node, `1` plus, for every
choice, its edge and its subtree. -/
def size : CTree C O → ℕ
  | leaf _ => 1
  | node S k => 1 + ∑ c ∈ S, ((k c).size + 1)

/-- The height of a tree. -/
def height : CTree C O → ℕ
  | leaf _ => 0
  | node S k => 1 + S.sup fun c => (k c).height

/-- **The leaf multiset has the count as cardinality.** -/
theorem card_leafMs (t : CTree C O) : Multiset.card t.leafMs = t.count := by
  induction t with
  | leaf o => rfl
  | node S k ih =>
    simp only [leafMs, count, Multiset.card_sum]
    exact sum_congr rfl fun c _ => ih c

/-- **The elements of the leaf multiset are the reachable leaves.** -/
theorem mem_leafMs {t : CTree C O} {o : O} : o ∈ t.leafMs ↔ t.Reach o := by
  induction t with
  | leaf o' => simp [leafMs, Reach, eq_comm]
  | node S k ih => simp only [leafMs, Reach, Multiset.mem_sum, ih]

theorem meas_sum_bind {ι : Type*} (S : Finset ι) (g : ι → Multiset O)
    (f : O → Multiset O') : (∑ c ∈ S, g c).bind f = ∑ c ∈ S, (g c).bind f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, Multiset.add_bind, ih]

theorem meas_sum_map {ι : Type*} (S : Finset ι) (g : ι → Multiset O) (f : O → O') :
    (∑ c ∈ S, g c).map f = ∑ c ∈ S, (g c).map f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, Multiset.map_add, ih]

theorem leafMs_bind (t : CTree C O) (f : O → CTree C O') :
    (t.bind f).leafMs = t.leafMs.bind fun o => (f o).leafMs := by
  induction t with
  | leaf o => simp [bind, leafMs]
  | node S k ih =>
    simp only [bind, leafMs, meas_sum_bind]
    exact sum_congr rfl fun c _ => ih c

theorem leafMs_trans [DecidableEq C'] (f : C → C') (r : C' → C) (h : O → O')
    (hr : ∀ c, r (f c) = c) (t : CTree C O) : (t.trans f r h).leafMs = t.leafMs.map h := by
  have hf : Function.Injective f := fun a b e => by rw [← hr a, e, hr]
  induction t with
  | leaf o => simp [trans, leafMs]
  | node S k ih =>
    simp only [trans, leafMs, meas_sum_map]
    rw [sum_image fun a _ b _ e => hf e]
    exact sum_congr rfl fun c _ => by rw [hr, ih]

theorem one_le_size (t : CTree C O) : 1 ≤ t.size := by
  cases t with
  | leaf o => exact le_refl 1
  | node S k => exact Nat.le_add_right 1 _

theorem size_bind_leaf (t : CTree C O) (g : O → O') :
    (t.bind fun o => leaf (g o)).size = t.size := by
  induction t with
  | leaf o => rfl
  | node S k ih =>
    simp only [bind, size]
    exact congrArg (1 + ·) (sum_congr rfl fun c _ => by rw [ih c])

theorem height_bind_le (t : CTree C O) (f : O → CTree C O') (h : ℕ)
    (hf : ∀ o, t.Reach o → (f o).height ≤ h) : (t.bind f).height ≤ t.height + h := by
  induction t with
  | leaf o => simpa [bind, height] using hf o rfl
  | node S k ih =>
    simp only [bind, height]
    have : (S.sup fun c => ((k c).bind f).height) ≤ (S.sup fun c => (k c).height) + h := by
      refine Finset.sup_le fun c hc => (ih c fun o ho => hf o ⟨c, hc, ho⟩).trans ?_
      exact Nat.add_le_add_right (le_sup (f := fun c => (k c).height) hc) h
    omega

/-- The size bound of a live tree, with one to spare, and its positive count. -/
theorem meas_size_live {t : CTree C O} (ht : t.Live) :
    t.size + 1 ≤ 2 * (t.height + 1) * t.count ∧ 1 ≤ t.count := by
  induction t with
  | leaf o => exact ⟨le_refl 2, le_refl 1⟩
  | node S k ih =>
    obtain ⟨⟨c₀, hc₀⟩, hk⟩ := ht
    simp only [size, height, count]
    set H := S.sup fun c => (k c).height
    have hch : ∀ c ∈ S, (k c).size + 1 ≤ 2 * (H + 1) * (k c).count := fun c hc =>
      (ih c (hk c hc)).1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.add_le_add_right (le_sup (f := fun c => (k c).height) hc) 1)))
    have hsum : ∑ c ∈ S, ((k c).size + 1) ≤ 2 * (H + 1) * ∑ c ∈ S, (k c).count := by
      rw [mul_sum]
      exact sum_le_sum hch
    have hc1 : 1 ≤ ∑ c ∈ S, (k c).count :=
      (ih c₀ (hk c₀ hc₀)).2.trans (single_le_sum (f := fun c => (k c).count)
        (fun _ _ => Nat.zero_le _) hc₀)
    refine ⟨?_, hc1⟩
    have e : 2 * (1 + H + 1) * ∑ c ∈ S, (k c).count =
        2 * (H + 1) * ∑ c ∈ S, (k c).count + 2 * ∑ c ∈ S, (k c).count := by ring
    rw [e]
    omega

/-- **The size of a live tree** is at most `2 (height + 1)` times its count. -/
theorem size_le_of_live {t : CTree C O} (ht : t.Live) :
    t.size ≤ 2 * (t.height + 1) * t.count :=
  (Nat.le_succ _).trans (meas_size_live ht).1

theorem meas_height_bind_leaf (t : CTree C O) (g : O → O') :
    (t.bind fun o => leaf (g o)).height = t.height := by
  induction t with
  | leaf o => rfl
  | node S k ih =>
    simp only [bind, height]
    exact congrArg (1 + ·) (Finset.sup_congr rfl fun c _ => ih c)

theorem meas_height_trans [DecidableEq C'] (f : C → C') (r : C' → C) (h : O → O')
    (hr : ∀ c, r (f c) = c) (t : CTree C O) : (t.trans f r h).height = t.height := by
  induction t with
  | leaf o => rfl
  | node S k ih =>
    simp only [trans, height]
    rw [Finset.sup_image]
    exact congrArg (1 + ·) (Finset.sup_congr rfl fun c _ => by
      simp only [Function.comp, hr, ih])

theorem meas_height_node_le (S : Finset C) (k : C → CTree C O) {h : ℕ}
    (hk : ∀ c ∈ S, (k c).height ≤ h) : (node S k).height ≤ 1 + h := by
  simp only [height]
  exact Nat.add_le_add_left (Finset.sup_le hk) 1

theorem meas_height_ite_le {p : Prop} [Decidable p] {a b : CTree C O} {h : ℕ}
    (ha : a.height ≤ h) (hb : b.height ≤ h) : (if p then a else b).height ≤ h := by
  split_ifs
  · exact ha
  · exact hb

end CTree

section Bsoj

variable {α : Type*} [DecidableEq α]

theorem leafMs_withPiece (D : Finset α) (t : STree α) :
    (withPiece D t).leafMs = t.leafMs.map (addPieceOut D) := by
  rw [withPiece, CTree.leafMs_bind]
  exact Multiset.bind_singleton _ _

theorem size_withPiece (D : Finset α) (t : STree α) : (withPiece D t).size = t.size :=
  CTree.size_bind_leaf _ _

theorem meas_height_withPiece (D : Finset α) (t : STree α) :
    (withPiece D t).height = t.height :=
  CTree.meas_height_bind_leaf _ _

omit [DecidableEq α] in
theorem meas_height_cohSoj {R : Type*} [DecidableEq R] (C₁ C₂ : Finset R) (c : R → R → ℕ) :
    (cohSoj C₁ C₂ c).height ≤ 1 := by
  unfold cohSoj
  dsimp only
  split_ifs
  all_goals first
    | exact Nat.zero_le 1
    | exact CTree.meas_height_node_le _ _ (h := 0) fun _ _ => le_refl 0
    | refine CTree.meas_height_node_le _ _ (h := 0) fun _ _ => ?_
      split_ifs <;> exact le_refl 0

omit [DecidableEq α] in
theorem meas_height_shrink {V₂ : Finset (Finset α)}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α} {h : ℕ}
    (hrec : ∀ V₁' V₂' A', (rec V₁' V₂' A').height ≤ h) (V₁' : Finset α)
    (V₂' : Finset (Finset α)) (A' : α → Finset α → Bool) :
    (shrink V₂ rec V₁' V₂' A').height ≤ h := by
  unfold shrink
  split_ifs
  · exact hrec _ _ _
  · exact Nat.zero_le _

theorem meas_height_cohCont {t : ℕ} {V₁ V₁' C₁ : Finset α}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α} {h : ℕ}
    (hrec : ∀ V₁'' V₂'' A'', (rec V₁'' V₂'' A'').height ≤ h)
    (o : Option (CohOut (α ⊕ Finset α))) : (cohCont t V₁ V₁' C₁ rec o).height ≤ h := by
  rcases o with _ | (p | ⟨W₁, W₂, A'⟩)
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · simp only [cohCont]
    split_ifs
    · exact Nat.zero_le _
    · rw [meas_height_withPiece, meas_height_withPiece, meas_height_withPiece]
      exact hrec _ _ _

theorem meas_height_dlCont {t : ℕ} {V₁ V₁' : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} {d : ℕ} (W : (Fin d → V₂) → ℕ)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α} {h : ℕ}
    (hrec : ∀ V₁'' V₂'' A'', (rec V₁'' V₂'' A'').height ≤ h) (x : List V₂) :
    (dlCont t V₁ V₁' V₂ A W rec x).height ≤ h + 1 := by
  have hsh : ∀ V₁'' V₂'' A'', (shrink V₂ rec V₁'' V₂'' A'').height ≤ h :=
    meas_height_shrink hrec
  unfold dlCont
  dsimp only
  split_ifs
  all_goals first
    | exact (Nat.zero_le _)
    | (rw [meas_height_withPiece]; exact (hsh _ _ _).trans (Nat.le_succ _))
    | refine CTree.meas_height_ite_le ?_ ?_
      · rw [meas_height_withPiece]
        exact (hsh _ _ _).trans (Nat.le_succ _)
      · refine (CTree.height_bind_le _ _ h fun o _ => meas_height_cohCont hsh o).trans ?_
        refine (Nat.add_le_add_right ((CTree.meas_height_trans _ _ _ ?_ _).le.trans
          (meas_height_cohSoj _ _ _)) h).trans (by omega)
        intro q
        rfl

theorem meas_height_bstep {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁' V₂' A', (rec V₁' V₂' A').height ≤ 2 * V₂.card - 1) :
    (bstep t V₁ V₂ A rec).height ≤ 2 * V₂.card + 1 := by
  unfold bstep
  dsimp only
  split_ifs with hd hJ hb hS
  · exact Nat.zero_le _
  · exact (CTree.meas_height_node_le _ _ (h := 0) fun _ _ => le_refl 0).trans (by omega)
  · rw [meas_height_withPiece]
    exact (hrec _ _ _).trans (by omega)
  · have hv : 1 ≤ V₂.card := by
      by_contra h0
      apply hb
      rw [IsBase, show V₂.card = 0 by omega]
      simp
    refine (CTree.meas_height_node_le _ _ (h := 2 * V₂.card - 1 + 1) fun _ _ =>
      meas_height_dlCont _ hrec _).trans (by omega)
  · exact Nat.zero_le _

/-- **The height of Bipartite Split-or-Johnson** is at most `2 |V₂| + 1`. -/
theorem height_bsoj_le (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) : (bsoj t V₁ V₂ A).height ≤ 2 * V₂.card + 1 := by
  suffices h : ∀ n (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool),
      V₂.card = n → (bsoj t V₁ V₂ A).height ≤ 2 * V₂.card + 1 from h _ V₁ V₂ A rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V₁ V₂ A hn
    rw [bsoj]
    refine meas_height_bstep fun V₁' V₂' A' => ?_
    split_ifs with hlt
    · exact (ih _ (hn ▸ hlt) V₁' V₂' A' rfl).trans (by omega)
    · exact Nat.zero_le _

end Bsoj

section Soj

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- **The height of Split-or-Johnson** is at most `2 |Γ| + 2`. -/
theorem height_soj_le (c : Γ → Γ → ℕ) (t : ℕ) :
    (soj c t).height ≤ 2 * Fintype.card Γ + 2 := by
  unfold soj
  refine (CTree.meas_height_node_le _ _ (h := 2 * Fintype.card Γ + 1) fun ch _ => ?_).trans
    (by omega)
  split
  · unfold sojAt
    dsimp only
    split_ifs
    · exact Nat.zero_le _
    · rw [CTree.meas_height_bind_leaf]
      refine (height_bsoj_le _ _ _ _).trans ?_
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (card_image_le.trans (card_le_univ _))) 1
    · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- **The index bound of macro-step M4.** If every element of `G` preserves the colouring `c`,
the orbit of a reachable leaf of `soj c t` under `G` has at most `(soj c t).count` elements. -/
theorem card_orbit_le_count {G : Subgroup (Equiv.Perm Γ)} {c : Γ → Γ → ℕ} {t : ℕ}
    (hG : ∀ σ ∈ G, relab2 σ c = c) {o : Option (Out Γ)} (ho : (soj c t).Reach o) :
    Nat.card (MulAction.orbit G o) ≤ (soj c t).count := by
  classical
  have hsub : MulAction.orbit G o ⊆ ((soj c t).leafMs.toFinset : Set (Option (Out Γ))) := by
    rintro _ ⟨g, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, CTree.mem_leafMs]
    have h := (split_or_johnson_reach (g : Equiv.Perm Γ) c t o).2 ho
    rwa [hG g g.2] at h
  calc Nat.card (MulAction.orbit G o) = (MulAction.orbit G o).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ ((soj c t).leafMs.toFinset : Set (Option (Out Γ))).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (soj c t).leafMs.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card (soj c t).leafMs := Multiset.toFinset_card_le _
    _ = (soj c t).count := CTree.card_leafMs _

end Soj

end GraphIso.SplitJohnson
