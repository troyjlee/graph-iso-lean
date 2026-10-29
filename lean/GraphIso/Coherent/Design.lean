module

public import GraphIso.Coherent.Skeleton
public import GraphIso.Coherent.LargeClique

/-!
# The Design Lemma

**The Design Lemma** (Helfgott, *Graph isomorphisms in quasi-polynomial time*, Prop. 5.1;
Babai, Thm. 6.1.1), with a natural threshold `t` in place of `α |Γ|`: a class of a vertex
colouring is *dominant* if it has more than `t` points. It is proved for every `t` with
`|V| ≤ 2t + 1` (`design_lemma_of_le_succ`): a class has more than `α |V|` points exactly when it
has more than `⌊α |V|⌋`, and `|V| ≤ 2 ⌊α |V|⌋ + 1` for every `α ≥ 1/2`, so this is Helfgott's
whole range. `design_lemma` is the case `|V| ≤ 2t`. Let `c` be a `k`-ary coherent
configuration, `k ≥ 2`, with no set of more than `t` pairwise twins. Then some list `x` of fewer
than `k` points satisfies one of:

* (a) the vertex colouring individualized at `x` has no dominant class; or
* (b) `x` has fewer than `k − 1` points, the vertex colouring has a dominant class `C`, and the
  individualized 2-skeleton is not a clique on `C`.

The proof follows Helfgott. Suppose not: every individualization at fewer than `k` points has a
dominant class `D(x)`, and for fewer than `k − 1` points the 2-skeleton is a clique on it.

* A point is a set of pairwise twins, so `t ≥ 1`; two classes of more than `t ≥ (|V| − 1)/2`
  points meet, and a dominant class has at least two points and more than half of `V`.
* `D(x ++ [z]) = D(x) \ {z}`: by the large clique lemma (`isTwin2_of_large_clique`) the points
  of `D(x)` are twins of the 2-skeleton, so the colouring individualized at `x ++ [z]` is
  constant on `D(x) \ {z}`; it refines the colouring at `x` (`skel1_refine`) and separates `z`
  from every other point (`skel1_append_ne`), and two dominant classes meet.
* So `D(x) = D([]) \ x`. Since `D([])` has more than `t` points, it contains non-twins `u`, `v`,
  and some tuple `w` has `c (w^{(u v)}) ≠ c w`. Listing the entries of `w` other than `u` and
  `v` as `xs`, the tuple `w` is `ŵ ∘ σ` for `ŵ` one of `(xs, u, …, u)`, `(xs, v, …, v)`,
  `(xs, u, v, …, v)` (`exists_comp`), so `ŵ` is also moved: the colouring at `xs` separates `u`
  from `v`, contradicting `u, v ∈ D(xs)`, or the 2-skeleton at `xs` is not a clique on `D(xs)`.
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

omit [Fintype V] [DecidableEq V] in
/-- The colouring individualized at `y ++ [z]` refines the colouring individualized at `y`. -/
theorem skel1_refine {c : (Fin k → V) → ℕ} (hc : IsConfig c) {y : List V}
    (hy : y.length + 2 ≤ k) (z : V) {a b : V}
    (h : skel1 c (y ++ [z]) a = skel1 c (y ++ [z]) b) : skel1 c y a = skel1 c y b := by
  let τ : Fin k → Fin k := fun i => if i.val < y.length then i else ⟨y.length + 1, by omega⟩
  have e : ∀ a, pad1 k (y ++ [z]) a ∘ τ = pad1 k y a := fun a => by
    funext i
    simp only [comp_apply, τ, pad1, List.length_append, List.length_singleton]
    by_cases hi : i.val < y.length
    · have hi' : i.val < y.length + 1 := by omega
      simp [hi, hi', List.getElem_append_left hi]
    · simp [hi]
  have := hc.comp h τ
  unfold skel1
  rwa [e, e] at this

omit [Fintype V] [DecidableEq V] in
/-- The colouring individualized at `y ++ [z]` separates `z` from every other point. -/
theorem skel1_append_ne {c : (Fin k → V) → ℕ} (hc : IsConfig c) {y : List V}
    (hy : y.length + 2 ≤ k) {z w : V} (hw : w ≠ z) :
    skel1 c (y ++ [z]) z ≠ skel1 c (y ++ [z]) w := by
  intro h
  have := hc.eq_iff h ⟨y.length, by omega⟩ ⟨y.length + 1, by omega⟩
  simp [pad1] at this
  exact hw this.symm

omit [Fintype V] [DecidableEq V] in
/-- A tuple whose entries are all entries of `ŵ` is `ŵ` composed with a map of positions. -/
theorem exists_comp {ŵ w : Fin k → V} (h : ∀ i, ∃ j, ŵ j = w i) :
    ∃ σ : Fin k → Fin k, w = ŵ ∘ σ := by
  choose σ hσ using h
  exact ⟨σ, funext fun i => (hσ i).symm⟩

omit [Fintype V] in
/-- If `ŵ` is not moved by `(u v)`, neither is `ŵ ∘ σ`. -/
theorem comp_swap_eq {c : (Fin k → V) → ℕ} (hc : IsConfig c) {u v : V} {ŵ : Fin k → V}
    (h : c (⇑(Equiv.swap u v) ∘ ŵ) = c ŵ) (σ : Fin k → Fin k) :
    c (⇑(Equiv.swap u v) ∘ (ŵ ∘ σ)) = c (ŵ ∘ σ) :=
  hc.comp h σ

omit [Fintype V] in
theorem swap_comp_pad1 {u v : V} {xs : List V} (hxs : ∀ a ∈ xs, a ≠ u ∧ a ≠ v) (a : V) :
    ⇑(Equiv.swap u v) ∘ pad1 k xs a = pad1 k xs (Equiv.swap u v a) := by
  funext i
  simp only [comp_apply, pad1]
  by_cases hi : i.val < xs.length
  · simp only [hi, ↓reduceDIte]
    have := hxs _ (List.getElem_mem hi)
    exact Equiv.swap_apply_of_ne_of_ne this.1 this.2
  · simp only [hi, ↓reduceDIte]

omit [Fintype V] in
theorem swap_comp_pad2 {u v : V} {xs : List V} (hxs : ∀ a ∈ xs, a ≠ u ∧ a ≠ v) :
    ⇑(Equiv.swap u v) ∘ pad2 k xs u v = pad2 k xs v u := by
  funext i
  simp only [comp_apply, pad2]
  by_cases hi : i.val < xs.length
  · simp only [hi, ↓reduceDIte]
    have := hxs _ (List.getElem_mem hi)
    exact Equiv.swap_apply_of_ne_of_ne this.1 this.2
  · by_cases hi' : i.val = xs.length <;> simp [hi, hi']

/-- **The Design Lemma for every threshold `t ≥ (|V| − 1)/2`**: Helfgott's Prop. 5.1 with
`|V| ≤ 2t + 1`, which holds for `t = ⌊α |V|⌋` whenever `α ≥ 1/2` (a class has more than `α |V|`
points exactly when it has more than `⌊α |V|⌋`). Let `c` be a `k`-ary coherent configuration,
`k ≥ 2`, with no set of more than `t` pairwise twins. Then some list `x` of fewer than `k` points
satisfies one of: (a) the vertex colouring individualized at `x` has no class of more than `t`
points; or (b) `x` has fewer than `k − 1` points, the vertex colouring has a class `C` of more
than `t` points, and the individualized 2-skeleton is not a clique on `C`. -/
theorem design_lemma_of_le_succ {t : ℕ} (hk : 2 ≤ k) {c : (Fin k → V) → ℕ}
    (hc : IsCoherent c) (ht : Fintype.card V ≤ 2 * t + 1)
    (htw : ∀ T : Finset V, (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ t) :
    ∃ x : List V, x.length < k ∧
      ((∀ u, (cls1 c x u).card ≤ t) ∨
        (x.length + 2 ≤ k ∧ ∃ u, t < (cls1 c x u).card ∧
          ¬ IsClique (skel2 c x) (cls1 c x u))) := by
  classical
  by_contra hcon
  have hdom : ∀ x : List V, x.length < k → ∃ u, t < (cls1 c x u).card := by
    intro x hx
    by_contra h
    push Not at h
    exact hcon ⟨x, hx, Or.inl h⟩
  have hcl : ∀ x : List V, x.length + 2 ≤ k → ∀ u, t < (cls1 c x u).card →
      IsClique (skel2 c x) (cls1 c x u) := by
    intro x hx u hu
    by_contra h
    exact hcon ⟨x, by omega, Or.inr ⟨hx, u, hu, h⟩⟩
  have hmem : ∀ x u w, w ∈ cls1 c x u ↔ skel1 c x w = skel1 c x u := fun x u w => by
    simp [cls1]
  -- two sets of more than `t` points meet
  have hmeet : ∀ A B : Finset V, t < A.card → t < B.card → (A ∩ B).Nonempty := by
    intro A B hA hB
    rw [← Finset.card_pos]
    have h1 := Finset.card_union_add_card_inter A B
    have h2 : (A ∪ B).card ≤ Fintype.card V := Finset.card_le_univ _
    omega
  have huniq : ∀ x u u', t < (cls1 c x u).card → t < (cls1 c x u').card →
      cls1 c x u = cls1 c x u' := by
    intro x u u' hu hu'
    obtain ⟨a, ha⟩ := hmeet _ _ hu hu'
    rw [mem_inter, hmem, hmem] at ha
    ext w
    rw [hmem, hmem, ← ha.1, ha.2]
  obtain ⟨u₀, hu₀⟩ := hdom [] (by simp; omega)
  -- a point is a set of pairwise twins, so `t ≥ 1`
  have ht1 : 1 ≤ t := by
    have := htw {u₀} fun u hu v hv => by
      rw [mem_singleton] at hu hv
      subst hu hv
      intro x
      simp
    simpa using this
  set C := cls1 c [] u₀ with hC
  -- the dominant class individualized at `x` is `C \ x`
  have hmain : ∀ x : List V, x.length < k → ∀ u, t < (cls1 c x u).card →
      cls1 c x u = C \ x.toFinset := by
    intro x
    induction x using List.reverseRecOn with
    | nil =>
      intro _ u hu
      simp only [List.toFinset_nil, sdiff_empty]
      exact huniq _ _ _ hu hu₀
    | append_singleton y z ih =>
      intro hx u hu
      have hy : y.length + 2 ≤ k := by simp at hx; omega
      obtain ⟨u', hu'⟩ := hdom y (by omega)
      have ihy := ih (by omega) u' hu'
      set Dy := cls1 c y u' with hDy
      have hc2 := isCoherent2_skel2 hc hy
      have hfilt : (univ.filter fun w => skel2 c y w w = skel1 c y u') = Dy := by
        ext w
        simp [hDy, cls1, skel2_self]
      -- the points of `Dy` are twins of the 2-skeleton
      have htwin : ∀ a ∈ Dy, ∀ b ∈ Dy, IsTwin2 (skel2 c y) a b := by
        intro a ha b hb
        refine isTwin2_of_large_clique hc2 (κ := skel1 c y u') ?_ ?_ ?_ ?_
        · rw [hfilt]
          omega
        · rw [hfilt]
          exact hcl y hy u' hu'
        · rw [skel2_self]
          exact (hmem _ _ _).1 ha
        · rw [skel2_self]
          exact (hmem _ _ _).1 hb
      -- so the colouring at `y ++ [z]` is constant on `Dy \ {z}`
      have hconst : ∀ a ∈ Dy, ∀ b ∈ Dy, a ≠ z → b ≠ z →
          skel1 c (y ++ [z]) a = skel1 c (y ++ [z]) b := by
        intro a ha b hb haz hbz
        rw [skel1_append c hy, skel1_append c hy]
        have := htwin a ha b hb z a
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm haz) (Ne.symm hbz),
          Equiv.swap_apply_left] at this
        exact this.symm
      set Dx := cls1 c (y ++ [z]) u with hDx
      have hDxV : Dx.card ≤ Fintype.card V := card_le_univ _
      have hsub : Dx ⊆ Dy := by
        intro w hw
        obtain ⟨a, ha⟩ := hmeet _ _ hu hu'
        rw [mem_inter] at ha
        have h1 : skel1 c (y ++ [z]) w = skel1 c (y ++ [z]) a := by
          rw [(hmem _ _ _).1 hw, (hmem _ _ _).1 ha.1]
        rw [hmem, skel1_refine hc.config hy z h1]
        exact (hmem _ _ _).1 ha.2
      have hzx : z ∉ Dx := by
        intro hz
        obtain ⟨w, hw, hwz⟩ := Finset.exists_mem_ne (show 1 < Dx.card by omega) z
        apply skel1_append_ne hc.config hy hwz
        rw [(hmem _ _ _).1 hz, (hmem _ _ _).1 hw]
      have hDxe : Dx = Dy.erase z := by
        obtain ⟨w₀, hw₀⟩ : Dx.Nonempty := card_pos.1 (by omega)
        have hw₀z : w₀ ≠ z := fun h => hzx (h ▸ hw₀)
        ext w
        rw [mem_erase]
        constructor
        · intro hw
          exact ⟨fun h => hzx (h ▸ hw), hsub hw⟩
        · rintro ⟨hwz, hw⟩
          rw [hmem, hconst w hw w₀ (hsub hw₀) hwz hw₀z]
          exact (hmem _ _ _).1 hw₀
      rw [hDxe, ihy]
      ext w
      simp only [mem_erase, mem_sdiff, List.mem_toFinset, List.mem_append, List.mem_singleton]
      tauto
  -- `C` contains two points that are not twins
  have hnt : ¬ ∀ u ∈ C, ∀ v ∈ C, IsTwin c u v := fun h => by
    have := htw C h
    omega
  push Not at hnt
  obtain ⟨u, hu, v, hv, huv⟩ := hnt
  simp only [IsTwin, not_forall] at huv
  obtain ⟨w, hw⟩ := huv
  have huv' : u ≠ v := by
    rintro rfl
    simp at hw
  -- individualizing points outside `{u, v}` keeps `u` and `v` in one class
  have hsame : ∀ xs : List V, xs.length < k → u ∉ xs → v ∉ xs →
      skel1 c xs u = skel1 c xs v := by
    intro xs hxs hux hvx
    obtain ⟨u'', hu''⟩ := hdom xs hxs
    have e := hmain xs hxs u'' hu''
    have h1 : u ∈ cls1 c xs u'' := by rw [e]; simp [hu, hux]
    have h2 : v ∈ cls1 c xs u'' := by rw [e]; simp [hv, hvx]
    rw [(hmem _ _ _).1 h1, (hmem _ _ _).1 h2]
  have hclq : ∀ xs : List V, xs.length + 2 ≤ k → u ∉ xs → v ∉ xs →
      skel2 c xs u v = skel2 c xs v u := by
    intro xs hxs hux hvx
    obtain ⟨u'', hu''⟩ := hdom xs (by omega)
    have e := hmain xs (by omega) u'' hu''
    have h1 : u ∈ cls1 c xs u'' := by rw [e]; simp [hu, hux]
    have h2 : v ∈ cls1 c xs u'' := by rw [e]; simp [hv, hvx]
    exact hcl xs hxs u'' hu'' u h1 v h2 v h2 u h1 huv' (Ne.symm huv')
  -- the entries of `w` other than `u` and `v`
  set F := (univ.image w).filter fun a => a ≠ u ∧ a ≠ v with hF
  set xs := F.toList with hxs
  have hxsmem : ∀ a, a ∈ xs ↔ a ∈ univ.image w ∧ a ≠ u ∧ a ≠ v := fun a => by
    simp [hxs, hF]
  have hxsne : ∀ a ∈ xs, a ≠ u ∧ a ≠ v := fun a ha => ((hxsmem a).1 ha).2
  have hux : u ∉ xs := fun h => ((hxsmem u).1 h).2.1 rfl
  have hvx : v ∉ xs := fun h => ((hxsmem v).1 h).2.2 rfl
  have hlen : xs.length = F.card := Finset.length_toList F
  have himg : (univ.image w).card ≤ k := card_image_le.trans (by simp)
  have hFsub : F ⊆ univ.image w := filter_subset _ _
  have hunF : u ∉ F := fun h => (mem_filter.1 h).2.1 rfl
  have hvnF : v ∉ F := fun h => (mem_filter.1 h).2.2 rfl
  -- positions of the entries of `xs`
  have hidx : ∀ a ∈ xs, ∀ (hk' : xs.length < k), ∃ j : Fin k, pad1 k xs u j = a ∧
      pad1 k xs v j = a ∧ ∀ b d, pad2 k xs b d j = a := by
    intro a ha hk'
    have hj := List.idxOf_lt_length_iff.2 ha
    refine ⟨⟨xs.idxOf a, by omega⟩, ?_, ?_, fun b d => ?_⟩ <;>
      simp [pad1, pad2, hj, List.getElem_idxOf hj]
  -- `w` is not moved when it is a rearrangement of an unmoved tuple
  have hcontra : ∀ ŵ : Fin k → V, (∀ i, ∃ j, ŵ j = w i) →
      c (⇑(Equiv.swap u v) ∘ ŵ) = c ŵ → False := by
    intro ŵ hŵ h
    obtain ⟨σ, rfl⟩ := exists_comp hŵ
    exact hw (comp_swap_eq hc.config h σ)
  by_cases hui : u ∈ univ.image w <;> by_cases hvi : v ∈ univ.image w
  · -- both occur: the 2-skeleton at `xs`
    have hcard : F.card + 2 ≤ k := by
      have hs : insert u (insert v F) ⊆ univ.image w := by
        intro a ha
        simp only [mem_insert] at ha
        rcases ha with rfl | rfl | ha
        · exact hui
        · exact hvi
        · exact hFsub ha
      have := card_le_card hs
      rw [card_insert_of_notMem (by simp [hunF, huv']), card_insert_of_notMem hvnF] at this
      omega
    have hk' : xs.length < k := by omega
    refine hcontra (pad2 k xs u v) (fun i => ?_) ?_
    · by_cases hiu : w i = u
      · exact ⟨⟨xs.length, by omega⟩, by simp [pad2, hiu]⟩
      · by_cases hiv : w i = v
        · exact ⟨⟨xs.length + 1, by omega⟩, by simp [pad2, hiv]⟩
        · obtain ⟨j, -, -, hj⟩ := hidx (w i) ((hxsmem _).2 ⟨by simp, hiu, hiv⟩) hk'
          exact ⟨j, hj u v⟩
    · rw [swap_comp_pad2 hxsne]
      exact (hclq xs (by omega) hux hvx).symm
  · -- only `u` occurs
    have hcard : F.card + 1 ≤ k := by
      have hs : insert u F ⊆ univ.image w := by
        intro a ha
        simp only [mem_insert] at ha
        rcases ha with rfl | ha
        · exact hui
        · exact hFsub ha
      have := card_le_card hs
      rw [card_insert_of_notMem hunF] at this
      omega
    have hk' : xs.length < k := by omega
    refine hcontra (pad1 k xs u) (fun i => ?_) ?_
    · by_cases hiu : w i = u
      · exact ⟨⟨xs.length, by omega⟩, by simp [pad1, hiu]⟩
      · have hiv : w i ≠ v := fun e => hvi (e ▸ by simp)
        obtain ⟨j, hj, -, -⟩ := hidx (w i) ((hxsmem _).2 ⟨by simp, hiu, hiv⟩) hk'
        exact ⟨j, hj⟩
    · rw [swap_comp_pad1 hxsne u, Equiv.swap_apply_left]
      exact (hsame xs hk' hux hvx).symm
  · -- only `v` occurs
    have hcard : F.card + 1 ≤ k := by
      have hs : insert v F ⊆ univ.image w := by
        intro a ha
        simp only [mem_insert] at ha
        rcases ha with rfl | ha
        · exact hvi
        · exact hFsub ha
      have := card_le_card hs
      rw [card_insert_of_notMem hvnF] at this
      omega
    have hk' : xs.length < k := by omega
    refine hcontra (pad1 k xs v) (fun i => ?_) ?_
    · by_cases hiv : w i = v
      · exact ⟨⟨xs.length, by omega⟩, by simp [pad1, hiv]⟩
      · have hiu : w i ≠ u := fun e => hui (e ▸ by simp)
        obtain ⟨j, -, hj, -⟩ := hidx (w i) ((hxsmem _).2 ⟨by simp, hiu, hiv⟩) hk'
        exact ⟨j, hj⟩
    · rw [swap_comp_pad1 hxsne v, Equiv.swap_apply_right]
      exact hsame xs hk' hux hvx
  · -- neither occurs: `w` is fixed by `(u v)`
    apply hw
    congr 1
    funext i
    have hiu : w i ≠ u := fun e => hui (e ▸ by simp)
    have hiv : w i ≠ v := fun e => hvi (e ▸ by simp)
    exact Equiv.swap_apply_of_ne_of_ne hiu hiv

/-- **The Design Lemma** (Helfgott, Prop. 5.1; Babai, Thm. 6.1.1), with a threshold `t ≥ |V|/2`
in place of `α |Γ|`; `design_lemma_of_le_succ` allows `t ≥ (|V| − 1)/2`. Let `c` be a `k`-ary
coherent configuration, `k ≥ 2`, with no set of more than `t` pairwise twins. Then some list `x`
of fewer than `k` points satisfies one of: (a) the vertex colouring individualized at `x` has no
class of more than `t` points; or (b) `x` has fewer than `k − 1` points, the vertex colouring has
a class `C` of more than `t` points, and the individualized 2-skeleton is not a clique on
`C`. -/
theorem design_lemma {t : ℕ} (hk : 2 ≤ k) {c : (Fin k → V) → ℕ} (hc : IsCoherent c)
    (ht : Fintype.card V ≤ 2 * t)
    (htw : ∀ T : Finset V, (∀ u ∈ T, ∀ v ∈ T, IsTwin c u v) → T.card ≤ t) :
    ∃ x : List V, x.length < k ∧
      ((∀ u, (cls1 c x u).card ≤ t) ∨
        (x.length + 2 ≤ k ∧ ∃ u, t < (cls1 c x u).card ∧
          ¬ IsClique (skel2 c x) (cls1 c x u))) :=
  design_lemma_of_le_succ hk hc (by omega) htw

end GraphIso.Coherent
