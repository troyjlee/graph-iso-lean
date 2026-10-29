module

public import GraphIso.Recursion.Primitive
public import GraphIso.Recursion.Align
public import GraphIso.Align.Trim
public import GraphIso.SoJTree.Measure

/-!
# Case 2b: the choice tree

Stage 14h, item 1 (`PLAN-14.md` §12), at the level of the model. Case 2b of the giant
macro-step: `P = ψ(F)` has an orbit `Φ` on which it is not a giant, with degree of transitivity
`d`. The choice tree `case2bTree P Φ d` on the base `Γ`:

* a node over the `(d - 1)`-tuples `S` of distinct points of `Φ` (`tuplesOf`);
* a node over the pairs `(a, b)` of distinct points of `Φ ∖ S` (`pairsOf`);
* `Φ ∖ S` is numbered by `Fin m'` in increasing order (`e`, `Finset.orderEmbOfFin`), and the
  orbital of `(a, b)` under the elements of `P` fixing `S` pointwise is the relation
  `orbRel P S a b e` on `Fin m'`; its 2-ary Weisfeiler–Leman refinement is `wlRel`;
* if some colour graph of the refinement is disconnected, the leaf is the partition into the
  components of the least such colour (milestone 11's `⟨fun _ => 0, comp univ c r⟩`),
  extended to `Γ` (`extPart`); otherwise Split-or-Johnson with `t = (m' + 3) / 2`, its leaves
  trimmed (`trimOut`) and extended (`extOut`).

The extension of a structure on `Fin m'` along an embedding `e : Fin m' ↪ Γ`:

* `extPart e p`: colour `p.col i + 1` at `e i`, `0` off the range; blocks `(p.blk i).map e` at
  `e i`, and the complement of the range as one block;
* `extJohn e J`: points, cells and `f` carried by `e`, `f` empty off the range.

The tree is defined for a base with a linear order (the programs use `Fin m`), and the orbital
relation is decided through `[DecidablePred (· ∈ P)]`; the tree does not depend on that instance
(`case2bTree_congr`).

Results:

* `case2bTree_relabel`: **canonicity**,
  `case2bTree (P.map (MulAut.conj σ)) (σ • Φ) d = (case2bTree P Φ d).act σ`
  (`case2bTree_relabel'` for any `P'` with `g ∈ P' ↔ σ⁻¹ g σ ∈ P`). Relabelling `Φ ∖ S` changes
  its increasing numbering by a permutation `π` of `Fin m'` (`e' ∘ π = σ ∘ e`), and
  Split-or-Johnson moves with `π` (`split_or_johnson_relabel`); `cb_act_trans` carries this
  through the extension (`leafTree_relabel`).
* `Case2bHyp P Φ d`: `P` maps `Φ` into itself, `|Φ| ≥ d + 3`, and after fixing any `d − 1`
  points of `Φ` the elements of `P` act on the rest transitively and not doubly transitively.
  `case2bHyp_of_degree` derives it when `d` is the degree of transitivity (`P` moves any `d`
  distinct points of `Φ` to any other `d`, and not so for `d + 1`).
* `case2bTree_valid` (`ValidLeaf`): under `Case2bHyp`, every reachable leaf is a colored
  partition of `Γ`, or a trimmed Johnson embedding of `Γ` whose cells are disjoint from its
  points (the model-level conditions of `jvalid_of_isJohnson`).
* `case2bTree_live`, `case2bTree_count_le`: the tree is live with count at most
  `|Φ|^(d+1) · 2^(129 (⌈log₂ |Φ|⌉ + 2)²)` (`leafTree_spec` at one leaf: Split-or-Johnson's count).
* `case2b_reach`: for `P` and `Φ` given canonically by the string, every isomorphism carries a
  reachable leaf for `x` to a reachable leaf for `y` (`iso_reach`), the alignment hypothesis
  of `alignProg`.
* **The size of the partitions** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 1): `PartLe b`, a
  partition leaf is a colored `t`-partition with `t ≤ b`. Every partition leaf of the leaf tree
  has `t ≤ max ((m + 3) / 2) (|Γ| − m)` for `m` numbered points (`leafTree_partLe`): the
  components' `m / 2`, Split-or-Johnson's `(m + 3) / 2`, and the extension's complement block
  (`extPart_partLe`). So under `Case2bHyp` the tree's partition leaves have
  `t ≤ max ((|Φ| − (d − 1) + 3) / 2) (|Γ| − (|Φ| − (d − 1)))` (`case2bTree_partLe`).
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv MulAction Pointwise Finset GraphIso.SplitJohnson GraphIso.Coherent GraphIso.Recursion
  GraphIso.Align

/-! ### Two embeddings related by permutations -/

section Ext

variable {Γ : Type*} [DecidableEq Γ] {m : ℕ}

/-- The preimage of a point under `e`, if any. -/
def epre (e : Fin m ↪ Γ) (v : Γ) : Option (Fin m) := (List.finRange m).find? fun i => e i = v

theorem epre_eq_some {e : Fin m ↪ Γ} {v : Γ} {i : Fin m} : epre e v = some i ↔ e i = v := by
  unfold epre
  constructor
  · intro h
    have := List.find?_some h
    simpa using this
  · intro h
    rcases hf : (List.finRange m).find? (fun i => e i = v) with _ | j
    · rw [List.find?_eq_none] at hf
      exact absurd (by simpa using h) (hf i (List.mem_finRange i))
    · have hj := List.find?_some hf
      simp only [decide_eq_true_eq] at hj
      rw [e.injective (hj.trans h.symm)]

theorem epre_apply (e : Fin m ↪ Γ) (i : Fin m) : epre e (e i) = some i :=
  epre_eq_some.2 rfl

theorem epre_eq_none {e : Fin m ↪ Γ} {v : Γ} : epre e v = none ↔ ∀ i, e i ≠ v := by
  unfold epre
  rw [List.find?_eq_none]
  simp

variable (σ : Perm Γ) (π : Perm (Fin m)) {e e' : Fin m ↪ Γ}

theorem epre_relabel (he : ∀ i, e' (π i) = σ (e i)) (v : Γ) :
    epre e' (σ v) = (epre e v).map π := by
  rcases h : epre e v with _ | i
  · rw [Option.map_none, epre_eq_none]
    intro j hj
    have := he (π⁻¹ j)
    rw [perm_apply_inv_self] at this
    rw [this] at hj
    exact (epre_eq_none.1 h) _ (σ.injective hj)
  · rw [Option.map_some, epre_eq_some, he, (epre_eq_some.1 h)]

theorem epre_relabel' (he : ∀ i, e' (π i) = σ (e i)) (v : Γ) :
    epre e' v = (epre e (σ⁻¹ v)).map π := by
  rw [← epre_relabel σ π he, perm_apply_inv_self]

theorem map_relabel (he : ∀ i, e' (π i) = σ (e i)) (B : Finset (Fin m)) :
    (π • B).map e' = σ • B.map e := by
  ext v
  simp only [mem_map, mem_smul_finset, Perm.smul_def]
  constructor
  · rintro ⟨j, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨e i, ⟨i, hi, rfl⟩, (he i).symm⟩
  · rintro ⟨w, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨π i, ⟨i, hi, rfl⟩, he i⟩

end Ext

section Extend

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {m : ℕ}

/-- **A colored partition of `Fin m` extended to `Γ` along `e`**: colours shifted by one on the
range, `0` off it; the blocks carried by `e`, and the complement of the range as one block. -/
def extPart (e : Fin m ↪ Γ) (p : CPart (Fin m)) : CPart Γ :=
  ⟨fun v => match epre e v with
    | some i => p.col i + 1
    | none => 0,
   fun v => match epre e v with
    | some i => (p.blk i).map e
    | none => univ \ univ.map e⟩

/-- **A Johnson embedding of `Fin m` carried to `Γ` along `e`**, `f` empty off the range. -/
def extJohn (e : Fin m ↪ Γ) (J : JEmb (Fin m)) : JEmb Γ :=
  ⟨J.V0.map e, J.Λ.image (·.map e), J.s, fun v => match epre e v with
    | some i => (J.f i).image (·.map e)
    | none => ∅⟩

/-- The extension of a leaf. -/
def extOut (e : Fin m ↪ Γ) : Option (Out (Fin m)) → Option (Out Γ)
  | some (.inl p) => some (.inl (extPart e p))
  | some (.inr J) => some (.inr (extJohn e J))
  | none => none

variable (σ : Perm Γ) (π : Perm (Fin m)) {e e' : Fin m ↪ Γ}

omit [Fintype Γ] in
theorem univ_map_relabel (he : ∀ i, e' (π i) = σ (e i)) :
    (univ : Finset (Fin m)).map e' = σ • (univ : Finset (Fin m)).map e := by
  rw [← map_relabel σ π he, Finset.smul_finset_univ]

theorem extPart_relabel (he : ∀ i, e' (π i) = σ (e i)) (p : CPart (Fin m)) :
    extPart e' (π • p) = σ • extPart e p := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  · funext v
    show (match epre e' v with | some i => (π • p).col i + 1 | none => 0) =
      (match epre e (σ⁻¹ v) with | some i => p.col i + 1 | none => 0)
    rw [epre_relabel' σ π he v]
    rcases epre e (σ⁻¹ v) with _ | i
    · rfl
    · show (π • p).col (π i) + 1 = p.col i + 1
      rw [CPart.smul_col, Perm.smul_def, perm_inv_apply_self]
  · funext v
    show (match epre e' v with | some i => ((π • p).blk i).map e' | none => univ \ univ.map e') =
      σ • (match epre e (σ⁻¹ v) with | some i => (p.blk i).map e | none => univ \ univ.map e)
    rw [epre_relabel' σ π he v]
    rcases epre e (σ⁻¹ v) with _ | i
    · show univ \ univ.map e' = σ • (univ \ univ.map e)
      rw [smul_finset_sdiff, Finset.smul_finset_univ, univ_map_relabel σ π he]
    · show ((π • p).blk (π i)).map e' = σ • (p.blk i).map e
      rw [CPart.smul_blk, Perm.smul_def, perm_inv_apply_self, map_relabel σ π he]

omit [Fintype Γ] in
theorem image_map_relabel (he : ∀ i, e' (π i) = σ (e i)) (L : Finset (Finset (Fin m))) :
    (π • L).image (fun A : Finset (Fin m) => A.map e') =
      σ • L.image (fun A : Finset (Fin m) => A.map e) := by
  ext B
  simp only [mem_image, mem_smul_finset]
  constructor
  · rintro ⟨A, ⟨A₀, hA₀, rfl⟩, rfl⟩
    exact ⟨A₀.map e, ⟨A₀, hA₀, rfl⟩, (map_relabel σ π he A₀).symm⟩
  · rintro ⟨B₀, ⟨A₀, hA₀, rfl⟩, rfl⟩
    exact ⟨π • A₀, ⟨A₀, hA₀, rfl⟩, map_relabel σ π he A₀⟩

omit [Fintype Γ] in
theorem extJohn_relabel (he : ∀ i, e' (π i) = σ (e i)) (J : JEmb (Fin m)) :
    extJohn e' (π • J) = σ • extJohn e J := by
  show JEmb.mk _ _ _ _ = JEmb.mk _ _ _ _
  congr 1
  · exact map_relabel σ π he J.V0
  · exact image_map_relabel σ π he J.Λ
  · funext v
    show (match epre e' v with
        | some i => ((π • J).f i).image (fun A : Finset (Fin m) => A.map e')
        | none => ∅) =
      σ • (match epre e (σ⁻¹ v) with
        | some i => (J.f i).image (fun A : Finset (Fin m) => A.map e)
        | none => ∅)
    rw [epre_relabel' σ π he v]
    rcases epre e (σ⁻¹ v) with _ | i
    · exact (Finset.smul_finset_empty σ).symm
    · show ((π • J).f (π i)).image (fun A : Finset (Fin m) => A.map e') =
        σ • (J.f i).image (fun A : Finset (Fin m) => A.map e)
      rw [JEmb.smul_f, Perm.smul_def, perm_inv_apply_self]
      exact image_map_relabel σ π he (J.f i)

theorem extOut_relabel (he : ∀ i, e' (π i) = σ (e i)) (o : Option (Out (Fin m))) :
    extOut e' (π • o) = σ • extOut e o := by
  rcases o with _ | p | J
  · rfl
  · show some (Sum.inl (extPart e' (π • p))) = some (Sum.inl (σ • extPart e p))
    rw [extPart_relabel σ π he]
  · show some (Sum.inr (extJohn e' (π • J))) = some (Sum.inr (σ • extJohn e J))
    rw [extJohn_relabel σ π he]

end Extend

/-! ### Validity of the extensions -/

section ExtValid

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {m : ℕ} (e : Fin m ↪ Γ)

theorem extPart_col_e (p : CPart (Fin m)) (i : Fin m) : (extPart e p).col (e i) = p.col i + 1 := by
  show (match epre e (e i) with | some i => p.col i + 1 | none => 0) = _
  rw [epre_apply]

theorem extPart_blk_e (p : CPart (Fin m)) (i : Fin m) :
    (extPart e p).blk (e i) = (p.blk i).map e := by
  show (match epre e (e i) with | some i => (p.blk i).map e | none => univ \ univ.map e) = _
  rw [epre_apply]

theorem extPart_col_off (p : CPart (Fin m)) {v : Γ} (hv : ∀ i, e i ≠ v) :
    (extPart e p).col v = 0 := by
  show (match epre e v with | some i => p.col i + 1 | none => 0) = _
  rw [epre_eq_none.2 hv]

theorem extPart_blk_off (p : CPart (Fin m)) {v : Γ} (hv : ∀ i, e i ≠ v) :
    (extPart e p).blk v = univ \ univ.map e := by
  show (match epre e v with | some i => (p.blk i).map e | none => univ \ univ.map e) = _
  rw [epre_eq_none.2 hv]

theorem mem_rest {v : Γ} : v ∈ univ \ univ.map e ↔ ∀ i, e i ≠ v := by
  simp

/-- **The extension of a colored partition is a colored partition.** -/
theorem extPart_valid {t : ℕ} {p : CPart (Fin m)} (hp : IsColPart univ t p) :
    IsColPart univ (max t (univ \ univ.map e).card) (extPart e p) := by
  have hcases : ∀ v : Γ, (∃ i, e i = v) ∨ ∀ i, e i ≠ v := fun v => by
    by_cases h : ∃ i, e i = v
    · exact Or.inl h
    · exact Or.inr fun i hi => h ⟨i, hi⟩
  refine ⟨fun v _ => ?_, fun v _ => subset_univ _, fun v _ w hw => ?_, fun v _ w hw => ?_,
    fun v _ w _ hvw => ?_, fun v _ h1 w _ hvw => ?_, fun v _ => ?_⟩
  · rcases hcases v with ⟨i, rfl⟩ | hv
    · rw [extPart_blk_e]
      exact mem_map_of_mem e (hp.mem_blk i (mem_univ _))
    · rw [extPart_blk_off e p hv, mem_rest]
      exact hv
  · rcases hcases v with ⟨i, rfl⟩ | hv
    · rw [extPart_blk_e] at hw ⊢
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hw
      rw [extPart_blk_e, hp.blk_eq i (mem_univ _) j hj]
    · rw [extPart_blk_off e p hv, mem_rest] at hw
      rw [extPart_blk_off e p hv, extPart_blk_off e p hw]
  · rcases hcases v with ⟨i, rfl⟩ | hv
    · rw [extPart_blk_e] at hw
      obtain ⟨j, hj, rfl⟩ := mem_map.1 hw
      rw [extPart_col_e, extPart_col_e, hp.col_eq i (mem_univ _) j hj]
    · rw [extPart_blk_off e p hv, mem_rest] at hw
      rw [extPart_col_off e p hv, extPart_col_off e p hw]
  · rcases hcases v with ⟨i, rfl⟩ | hv <;> rcases hcases w with ⟨j, rfl⟩ | hw
    · rw [extPart_col_e, extPart_col_e] at hvw
      rw [extPart_blk_e, extPart_blk_e, card_map, card_map]
      exact hp.card_eq i (mem_univ _) j (mem_univ _) (by omega)
    · rw [extPart_col_e, extPart_col_off e p hw] at hvw
      omega
    · rw [extPart_col_e, extPart_col_off e p hv] at hvw
      omega
    · rw [extPart_blk_off e p hv, extPart_blk_off e p hw]
  · rcases hcases v with ⟨i, rfl⟩ | hv <;> rcases hcases w with ⟨j, rfl⟩ | hw
    · rw [extPart_blk_e, card_map] at h1
      rw [extPart_col_e, extPart_col_e] at hvw
      rw [hp.admissible i (mem_univ _) h1 j (mem_univ _) (by omega)]
    · rw [extPart_col_e, extPart_col_off e p hw] at hvw
      omega
    · rw [extPart_col_e, extPart_col_off e p hv] at hvw
      omega
    · rw [extPart_blk_off e p hv] at h1
      obtain ⟨x, hx⟩ := card_eq_one.1 h1
      have hv' : v ∈ univ \ univ.map e := (mem_rest e).2 hv
      have hw' : w ∈ univ \ univ.map e := (mem_rest e).2 hw
      rw [hx, mem_singleton] at hv' hw'
      rw [hv', hw']
  · rcases hcases v with ⟨i, rfl⟩ | hv
    · rw [extPart_blk_e, card_map]
      exact (hp.card_le i (mem_univ _)).trans (le_max_left _ _)
    · rw [extPart_blk_off e p hv]
      exact le_max_right _ _

omit [Fintype Γ] in
theorem extJohn_f_e (J : JEmb (Fin m)) (i : Fin m) :
    (extJohn e J).f (e i) = (J.f i).image (fun A : Finset (Fin m) => A.map e) := by
  show (match epre e (e i) with
    | some i => (J.f i).image (fun A : Finset (Fin m) => A.map e) | none => ∅) = _
  rw [epre_apply]

omit [Fintype Γ] in
theorem extJohn_f_off (J : JEmb (Fin m)) {v : Γ} (hv : ∀ i, e i ≠ v) :
    (extJohn e J).f v = ∅ := by
  show (match epre e v with
    | some i => (J.f i).image (fun A : Finset (Fin m) => A.map e) | none => ∅) = _
  rw [epre_eq_none.2 hv]

omit [Fintype Γ] [DecidableEq Γ] in
theorem mapE_injective : Function.Injective fun A : Finset (Fin m) => A.map e :=
  fun _ _ h => Finset.map_injective e h

/-- **The extension of a Johnson embedding is a Johnson embedding.** -/
theorem extJohn_valid {t : ℕ} {J : JEmb (Fin m)} (hJ : IsJohnson univ t J) :
    IsJohnson univ t (extJohn e J) := by
  have hinj := mapE_injective e
  refine ⟨subset_univ _, ?_, hJ.two_le, ?_, fun A hA => ?_, fun A hA B hB hAB => ?_,
    fun v hv => ?_, fun v hv w hw hvw => ?_, fun T hT => ?_⟩
  · show t < (J.V0.map e).card
    rw [card_map]
    exact hJ.card_gt
  · show 2 * J.s ≤ (J.Λ.image fun A : Finset (Fin m) => A.map e).card
    rw [card_image_of_injective _ hinj]
    exact hJ.le_half
  · obtain ⟨A₀, hA₀, rfl⟩ := mem_image.1 hA
    exact (hJ.cells_ne A₀ hA₀).map
  · obtain ⟨A₀, hA₀, rfl⟩ := mem_image.1 hA
    obtain ⟨B₀, hB₀, rfl⟩ := mem_image.1 hB
    rw [disjoint_map]
    exact hJ.cells_disj A₀ hA₀ B₀ hB₀ fun h => hAB (by rw [h])
  · obtain ⟨i, hi, rfl⟩ := mem_map.1 hv
    rw [extJohn_f_e]
    have h := hJ.maps_to i hi
    rw [mem_powersetCard] at h ⊢
    exact ⟨image_subset_image h.1, by rw [card_image_of_injective _ hinj, h.2]; rfl⟩
  · obtain ⟨i, hi, rfl⟩ := mem_map.1 hv
    obtain ⟨j, hj, rfl⟩ := mem_map.1 hw
    rw [extJohn_f_e, extJohn_f_e] at hvw
    rw [hJ.inj i hi j hj (image_injective hinj hvw)]
  · rw [mem_powersetCard] at hT
    set T₀ := J.Λ.filter fun A => A.map e ∈ T with hT₀
    have himg : T₀.image (fun A : Finset (Fin m) => A.map e) = T := by
      ext B
      simp only [hT₀, mem_image, mem_filter]
      constructor
      · rintro ⟨A, ⟨-, hA⟩, rfl⟩
        exact hA
      · intro hB
        obtain ⟨A, hA, rfl⟩ := mem_image.1 (hT.1 hB)
        exact ⟨A, ⟨hA, hB⟩, rfl⟩
    have hcard : T₀.card = J.s := by
      rw [← card_image_of_injective T₀ hinj, himg, hT.2]
      rfl
    obtain ⟨i, hi, hfi⟩ := hJ.surj T₀ (mem_powersetCard.2 ⟨filter_subset _ _, hcard⟩)
    exact ⟨e i, mem_map_of_mem e hi, by rw [extJohn_f_e, hfi, himg]⟩

omit [Fintype Γ] in
theorem extJohn_trim {J : JEmb (Fin m)} (h : ∀ i, i ∉ J.V0 → J.f i = ∅) (v : Γ)
    (hv : v ∉ (extJohn e J).V0) : (extJohn e J).f v = ∅ := by
  by_cases hr : ∃ i, e i = v
  · obtain ⟨i, rfl⟩ := hr
    have hi : i ∉ J.V0 := fun hi => hv (mem_map_of_mem e hi)
    rw [extJohn_f_e, h i hi, image_empty]
  · exact extJohn_f_off e J fun i hi => hr ⟨i, hi⟩

omit [Fintype Γ] in
theorem extJohn_disj {J : JEmb (Fin m)} (h : ∀ A ∈ J.Λ, Disjoint A J.V0) :
    ∀ A ∈ (extJohn e J).Λ, Disjoint A (extJohn e J).V0 := by
  intro A hA
  obtain ⟨A₀, hA₀, rfl⟩ := mem_image.1 hA
  exact (disjoint_map e).2 (h A₀ hA₀)

end ExtValid

/-! ### Choices carried along an embedding -/

section Choices

variable {Γ : Type*} [DecidableEq Γ] {m : ℕ}

/-- A choice on `Fin m` carried to `Γ` along `e`. -/
def chMap (e : Fin m ↪ Γ) (c : Choice (Fin m)) : Choice Γ :=
  (show List (Fin m ⊕ Finset (Fin m)) from c).map (Sum.map e fun s => s.map e)

/-- One entry of a choice on `Γ` pulled back along `e` (a point off the range becomes the empty
cell). -/
def chBackQ (e : Fin m ↪ Γ) : Γ ⊕ Finset Γ → Fin m ⊕ Finset (Fin m)
  | .inl v => match epre e v with
    | some i => .inl i
    | none => .inr ∅
  | .inr s => .inr (univ.filter fun i => e i ∈ s)

/-- A choice on `Γ` pulled back along `e`. -/
def chBack (e : Fin m ↪ Γ) (c : Choice Γ) : Choice (Fin m) :=
  (show List (Γ ⊕ Finset Γ) from c).map (chBackQ e)

theorem chBack_chMap (e : Fin m ↪ Γ) (c : Choice (Fin m)) : chBack e (chMap e c) = c := by
  show List.map _ (List.map _ _) = (c : List (Fin m ⊕ Finset (Fin m)))
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (c : List (Fin m ⊕ Finset (Fin m)))]
  refine List.map_congr_left fun q _ => ?_
  rcases q with i | s
  · simp [chBackQ, epre_apply]
  · simp only [Function.comp, Sum.map_inr, chBackQ, id, Sum.inr.injEq]
    ext i
    simp

variable (σ : Perm Γ) (π : Perm (Fin m)) {e e' : Fin m ↪ Γ}

theorem chMap_relabel (he : ∀ i, e' (π i) = σ (e i)) (c : Choice (Fin m)) :
    chMap e' (π • c) = σ • chMap e c := by
  show List.map _ (List.map _ _) = List.map _ (List.map _ _)
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun q _ => ?_
  rcases q with i | s
  · simp only [Function.comp, Sum.smul_inl, Sum.map_inl, Perm.smul_def, he]
  · simp only [Function.comp, Sum.smul_inr, Sum.map_inr, map_relabel σ π he]

theorem chBack_relabel (he : ∀ i, e' (π i) = σ (e i)) (c : Choice Γ) :
    chBack e' (σ • c) = π • chBack e c := by
  show List.map _ (List.map _ _) = List.map _ (List.map _ _)
  rw [List.map_map, List.map_map]
  refine List.map_congr_left fun q _ => ?_
  rcases q with v | s
  · simp only [Function.comp, Sum.smul_inl, Perm.smul_def, chBackQ]
    rw [epre_relabel σ π he v]
    rcases epre e v with _ | i
    · simp
    · simp [Perm.smul_def]
  · simp only [Function.comp, Sum.smul_inr, chBackQ, Sum.inr.injEq]
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_smul_finset, Perm.smul_def]
    constructor
    · intro h
      obtain ⟨w, hw, hwi⟩ := h
      refine ⟨π⁻¹ i, ?_, perm_apply_inv_self π i⟩
      have := he (π⁻¹ i)
      rw [perm_apply_inv_self] at this
      rw [this] at hwi
      rwa [← σ.injective hwi]
    · rintro ⟨j, hj, rfl⟩
      exact ⟨e j, hj, (he j).symm⟩

end Choices

/-! ### Trees carried along two related maps -/

section TreeMaps

namespace CTree

open GraphIso.SplitJohnson.CTree

variable {C C' O O' G G' : Type*} [Group G] [Group G'] [MulAction G C] [MulAction G O]
  [MulAction G' C'] [MulAction G' O'] [DecidableEq C] [DecidableEq C']

/-- **Moving a tree, then carrying it**: if `f'`, `r'`, `h'` after `g` agree with `f`, `r`, `h`
before `g'`, carrying the moved tree along the primed maps is moving the carried tree. -/
theorem cb_act_trans (g : G) (g' : G') {f f' : C → C'} {r r' : C' → C} {h h' : O → O'}
    (hf : ∀ c, f' (g • c) = g' • f c) (hr : ∀ c', r' (g' • c') = g • r c')
    (hh : ∀ o, h' (g • o) = g' • h o) (t : SplitJohnson.CTree C O) :
    (t.act g).trans f' r' h' = (t.trans f r h).act g' := by
  induction t with
  | leaf o => simp only [SplitJohnson.CTree.act, SplitJohnson.CTree.trans, hh]
  | node S k ih =>
    simp only [SplitJohnson.CTree.act, SplitJohnson.CTree.trans]
    congr 1
    · ext c'
      simp only [mem_image, mem_smul_finset]
      constructor
      · rintro ⟨c, ⟨c₀, hc₀, rfl⟩, rfl⟩
        exact ⟨f c₀, ⟨c₀, hc₀, rfl⟩, (hf c₀).symm⟩
      · rintro ⟨c₁, ⟨c₀, hc₀, rfl⟩, rfl⟩
        exact ⟨g • c₀, ⟨c₀, hc₀, rfl⟩, hf c₀⟩
    · funext c'
      have hr' : g⁻¹ • r' c' = r (g'⁻¹ • c') := by
        have := hr (g'⁻¹ • c')
        rw [smul_inv_smul] at this
        rw [this, inv_smul_smul]
      rw [hr', ih]

end CTree

namespace CTree

open GraphIso.SplitJohnson.CTree

variable {C C' O O' : Type*} [DecidableEq C']

/-- The reachable leaves of a carried tree. -/
theorem cb_reach_trans {f : C → C'} {r : C' → C} {h : O → O'} (hr : ∀ c, r (f c) = c)
    {t : SplitJohnson.CTree C O} {o : O'} :
    (t.trans f r h).Reach o ↔ ∃ o₀, t.Reach o₀ ∧ h o₀ = o := by
  rw [← mem_leafMs, leafMs_trans f r h hr, Multiset.mem_map]
  simp only [mem_leafMs]

theorem cb_count_trans {f : C → C'} {r : C' → C} {h : O → O'} (hr : ∀ c, r (f c) = c)
    (t : SplitJohnson.CTree C O) : (t.trans f r h).count = t.count := by
  rw [← card_leafMs, leafMs_trans f r h hr, Multiset.card_map, card_leafMs]

theorem cb_live_trans {f : C → C'} {r : C' → C} {h : O → O'} (hr : ∀ c, r (f c) = c)
    {t : SplitJohnson.CTree C O} (ht : t.Live) : (t.trans f r h).Live := by
  induction t with
  | leaf o => trivial
  | node S k ih =>
    obtain ⟨hS, hk⟩ := ht
    refine ⟨hS.image f, fun c' hc' => ?_⟩
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hc'
    show (SplitJohnson.CTree.trans f r h (k (r (f c)))).Live
    rw [hr]
    exact ih c (hk c hc)

end CTree

end TreeMaps

/-! ### The leaf at given choices -/

section Leaf

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {m : ℕ}

/-- **The orbital of `(a, b)`** under the elements of `P` fixing `S` pointwise, on `Fin m`
through `e`. -/
def orbRel (P : Subgroup (Perm Γ)) (S : Finset Γ) (a b : Γ) (e : Fin m ↪ Γ) (u v : Fin m) :
    Prop :=
  ∃ g ∈ P, (∀ s ∈ S, g s = s) ∧ g a = e u ∧ g b = e v

instance (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (S : Finset Γ) (a b : Γ)
    (e : Fin m ↪ Γ) : DecidableRel (orbRel P S a b e) := fun u v => by
  unfold orbRel
  infer_instance

/-- **The leaf tree at the choices `S` and `(a, b)`**, with `Φ ∖ S` numbered by `e`: the
partition into the components of the least disconnected colour of the refined orbital, or
Split-or-Johnson on it, extended to `Γ`. -/
def leafTree (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (S : Finset Γ) (a b : Γ)
    (e : Fin m ↪ Γ) : STree Γ :=
  if h : (disconn univ (wlRel (orbRel P S a b e))).Nonempty then
    .leaf (some (.inl (extPart e ⟨fun _ => 0, comp univ (wlRel (orbRel P S a b e))
      ((disconn univ (wlRel (orbRel P S a b e))).min' h)⟩)))
  else
    (soj (wlRel (orbRel P S a b e)) ((m + 3) / 2)).trans (chMap e) (chBack e)
      fun o => extOut e (trimOut o)

omit [Fintype Γ] in
/-- The orbital relation moves with the choices. -/
theorem orbRel_relabel (σ : Perm Γ) {P P' : Subgroup (Perm Γ)}
    (hP : ∀ g, g ∈ P' ↔ σ⁻¹ * g * σ ∈ P) (S : Finset Γ) (a b : Γ) (π : Perm (Fin m))
    {e e' : Fin m ↪ Γ} (he : ∀ i, e' (π i) = σ (e i)) (u v : Fin m) :
    orbRel P' (σ • S) (σ a) (σ b) e' (π u) (π v) ↔ orbRel P S a b e u v := by
  unfold orbRel
  rw [he, he]
  constructor
  · rintro ⟨g', hg', hS, ha, hb⟩
    refine ⟨σ⁻¹ * g' * σ, (hP g').1 hg', fun s hs => ?_, ?_, ?_⟩
    · have := hS (σ s) (Finset.smul_mem_smul_finset (a := σ) hs)
      simp only [Perm.mul_apply, this, perm_inv_apply_self]
    · simp only [Perm.mul_apply, ha, perm_inv_apply_self]
    · simp only [Perm.mul_apply, hb, perm_inv_apply_self]
  · rintro ⟨g, hg, hS, ha, hb⟩
    refine ⟨σ * g * σ⁻¹, (hP _).2 (by simpa [mul_assoc] using hg), fun s hs => ?_, ?_, ?_⟩
    · obtain ⟨s₀, hs₀, rfl⟩ := Finset.mem_smul_finset.1 hs
      simp only [Perm.smul_def, Perm.mul_apply, perm_inv_apply_self, hS s₀ hs₀]
    · simp only [Perm.mul_apply, perm_inv_apply_self, ha]
    · simp only [Perm.mul_apply, perm_inv_apply_self, hb]

/-- The refined orbital is relabelled by `π`. -/
theorem wlRel_orbRel_relabel (σ : Perm Γ) {P P' : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P')] (hP : ∀ g, g ∈ P' ↔ σ⁻¹ * g * σ ∈ P) (S : Finset Γ) (a b : Γ)
    (π : Perm (Fin m)) {e e' : Fin m ↪ Γ} (he : ∀ i, e' (π i) = σ (e i)) :
    wlRel (orbRel P' (σ • S) (σ a) (σ b) e') = relab2 π (wlRel (orbRel P S a b e)) := by
  funext x y
  have h := Recursion.wlRel_natural (π : Fin m ≃ Fin m) (orbRel P S a b e)
    (orbRel P' (σ • S) (σ a) (σ b) e') (orbRel_relabel σ hP S a b π he) (π⁻¹ x) (π⁻¹ y)
  rw [show (π : Fin m ≃ Fin m) (π⁻¹ x) = x from perm_apply_inv_self π x,
    show (π : Fin m ≃ Fin m) (π⁻¹ y) = y from perm_apply_inv_self π y] at h
  rw [h]
  rfl

theorem cb_cpart_smul {α : Type*} [DecidableEq α] (π : Perm α) (p : CPart α) :
    π • p = ⟨fun v => p.col (π⁻¹ • v), fun v => π • p.blk (π⁻¹ • v)⟩ := rfl

omit [Fintype Γ] in
theorem cb_act_leaf (σ : Perm Γ) (o : Option (Out Γ)) :
    (SplitJohnson.CTree.leaf o : STree Γ).act σ = .leaf (σ • o) := rfl

omit [Fintype Γ] in
theorem cb_smul_inl (σ : Perm Γ) (p : CPart Γ) :
    σ • (some (Sum.inl p) : Option (Out Γ)) = some (Sum.inl (σ • p)) := rfl

omit [Fintype Γ] [DecidableEq Γ] in
/-- The partition into components moves with the colouring. -/
theorem compPart_relabel (π : Perm (Fin m)) (c : Fin m → Fin m → ℕ)
    (h : (disconn univ c).Nonempty) (h' : (disconn univ (relab2 π c)).Nonempty)
    (hdis : disconn univ (relab2 π c) = disconn univ c) :
    (⟨fun _ => 0, comp univ (relab2 π c) ((disconn univ (relab2 π c)).min' h')⟩ :
        CPart (Fin m)) = π • ⟨fun _ => 0, comp univ c ((disconn univ c).min' h)⟩ := by
  rw [cb_cpart_smul]
  congr 1
  funext x
  have hmin : (disconn univ (relab2 π c)).min' h' = (disconn univ c).min' h := by
    simp only [hdis]
  rw [hmin, ← comp_smul' π univ c, Finset.smul_finset_univ]

/-- **The leaf tree is canonical**: relabelling the group, the choices and the numbering (any
numbering of the image, related by a permutation of `Fin m`) moves the tree. -/
theorem leafTree_relabel (σ : Perm Γ) {P P' : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P')] (hP : ∀ g, g ∈ P' ↔ σ⁻¹ * g * σ ∈ P) (S : Finset Γ) (a b : Γ)
    {m₂ : ℕ} (e : Fin m ↪ Γ) (e' : Fin m₂ ↪ Γ) (hm : m₂ = m)
    (hrange : ∀ v, (∃ j, e' j = v) ↔ ∃ i, e i = σ⁻¹ v) :
    leafTree P' (σ • S) (σ a) (σ b) e' = (leafTree P S a b e).act σ := by
  subst hm
  -- the permutation of `Fin m₂` relating the numberings
  have hex : ∀ i, ∃ j, e' j = σ (e i) := fun i =>
    (hrange (σ (e i))).2 ⟨i, by rw [perm_inv_apply_self]⟩
  choose fπ hfπ using hex
  have hinj : Function.Injective fπ := fun i j hij => by
    have := congrArg e' hij
    rw [hfπ, hfπ] at this
    exact e.injective (σ.injective this)
  set π : Perm (Fin m₂) := Equiv.ofBijective fπ (Finite.injective_iff_bijective.1 hinj)
  have he : ∀ i, e' (π i) = σ (e i) := fun i => hfπ i
  have hc := wlRel_orbRel_relabel σ hP S a b π he
  unfold leafTree
  rw [hc]
  generalize wlRel (orbRel P S a b e) = c
  have hdis : disconn univ (relab2 π c) = disconn univ c := by
    rw [← disconn_smul π univ c, Finset.smul_finset_univ]
  by_cases hd : (disconn univ c).Nonempty
  · have hd' : (disconn univ (relab2 π c)).Nonempty := hdis ▸ hd
    rw [dite_eq_left hd', dite_eq_left hd, cb_act_leaf, cb_smul_inl, ← extPart_relabel σ π he,
      compPart_relabel π c hd hd' hdis]
  · have hd' : ¬ (disconn univ (relab2 π c)).Nonempty := hdis ▸ hd
    rw [dite_eq_right hd', dite_eq_right hd, split_or_johnson_relabel]
    exact CTree.cb_act_trans π σ (chMap_relabel σ π he) (chBack_relabel σ π he)
      (fun o => by rw [trimOut_smul, extOut_relabel σ π he]) _

/-! #### The group acting on the numbered rest, and the leaf's properties -/

/-- The permutations of `Fin m` induced through `e` by the elements of `P` fixing `S`
pointwise. -/
def fixGroup (P : Subgroup (Perm Γ)) (S : Finset Γ) (e : Fin m ↪ Γ) : Subgroup (Perm (Fin m))
    where
  carrier := {h | ∃ g ∈ P, (∀ s ∈ S, g s = s) ∧ ∀ i, g (e i) = e (h i)}
  one_mem' := ⟨1, P.one_mem, fun _ _ => rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro h₁ h₂ ⟨g₁, hg₁, hS₁, he₁⟩ ⟨g₂, hg₂, hS₂, he₂⟩
    exact ⟨g₁ * g₂, P.mul_mem hg₁ hg₂, fun s hs => by
      rw [Perm.mul_apply, hS₂ s hs, hS₁ s hs], fun i => by
      rw [Perm.mul_apply, Perm.mul_apply, he₂, he₁]⟩
  inv_mem' := by
    rintro h ⟨g, hg, hS, he⟩
    refine ⟨g⁻¹, P.inv_mem hg, fun s hs => ?_, fun i => ?_⟩
    · conv_lhs => rw [← hS s hs]
      exact perm_inv_apply_self g s
    · have := he (h⁻¹ i)
      rw [perm_apply_inv_self] at this
      rw [← this, perm_inv_apply_self]

omit [Fintype Γ] [DecidableEq Γ] in
/-- An element of `P` fixing `S` and preserving the range of `e` induces an element of the
group. -/
theorem cb_realize {P : Subgroup (Perm Γ)} {S : Finset Γ} {e : Fin m ↪ Γ} {g : Perm Γ}
    (hg : g ∈ P) (hS : ∀ s ∈ S, g s = s) (hmaps : ∀ i, ∃ j, g (e i) = e j) :
    ∃ h ∈ fixGroup P S e, ∀ i, g (e i) = e (h i) := by
  choose f hf using hmaps
  have hinj : Function.Injective f := fun i j hij => by
    have := congrArg e hij
    rw [← hf, ← hf] at this
    exact e.injective (g.injective this)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), ⟨g, hg, hS, hf⟩, hf⟩

omit [Fintype Γ] [DecidableEq Γ] in
/-- The orbital is the orbital of the induced group. -/
theorem orbRel_iff {P : Subgroup (Perm Γ)} {S : Finset Γ} {e : Fin m ↪ Γ} {a' b' : Fin m}
    (hmaps : ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (e i) = e j) (u v : Fin m) :
    orbRel P S (e a') (e b') e u v ↔ ∃ h : fixGroup P S e, h • a' = u ∧ h • b' = v := by
  constructor
  · rintro ⟨g, hg, hS, ha, hb⟩
    obtain ⟨h, hh, he⟩ := cb_realize hg hS (hmaps g hg hS)
    refine ⟨⟨h, hh⟩, e.injective ?_, e.injective ?_⟩
    · rw [← ha, he]
      rfl
    · rw [← hb, he]
      rfl
  · rintro ⟨⟨h, g, hg, hS, he⟩, ha, hb⟩
    refine ⟨g, hg, hS, ?_, ?_⟩
    · rw [he, ← ha]
      rfl
    · rw [he, ← hb]
      rfl

/-- A valid leaf: a colored partition of `Γ`, or a trimmed Johnson embedding of `Γ` whose
cells are disjoint from its points. -/
def ValidLeaf (o : Option (Out Γ)) : Prop :=
  (∃ p t, o = some (Sum.inl p) ∧ IsColPart univ t p) ∨
    ∃ J t, o = some (Sum.inr J) ∧ IsJohnson univ t J ∧ (∀ v, v ∉ J.V0 → J.f v = ∅) ∧
      ∀ A ∈ J.Λ, Disjoint A J.V0

/-- **The leaf tree is live and valid, with Split-or-Johnson's count**, when the elements of
`P` fixing `S` act on the numbered rest transitively and not doubly transitively. -/
theorem leafTree_spec (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (S : Finset Γ)
    (e : Fin m ↪ Γ) {a' b' : Fin m} (hab : a' ≠ b') (hm : 4 ≤ m)
    (hmaps : ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (e i) = e j)
    (htr : IsPretransitive (fixGroup P S e) (Fin m))
    (h2 : ¬ IsMultiplyPretransitive (fixGroup P S e) (Fin m) 2) :
    (leafTree P S (e a') (e b') e).Live ∧
      (leafTree P S (e a') (e b') e).count ≤ 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2) ∧
      (leafTree P S (e a') (e b') e).AllLeaves ValidLeaf := by
  have hR := orbRel_iff (a' := a') (b' := b') hmaps
  obtain ⟨hcoh, hhom, -, -⟩ := Recursion.wlRel_spec h2 hab _ hR
  unfold leafTree
  by_cases hd : (disconn univ (wlRel (orbRel P S (e a') (e b') e))).Nonempty
  · rw [dite_eq_left hd]
    exact ⟨trivial, Nat.one_le_two_pow, Or.inl ⟨_, _, rfl, extPart_valid e
      (GraphIso.SplitJohnson.isColPart_comp (GraphIso.SplitJohnson.isCoh2On_univ hcoh) hhom
        ((disconn univ _).min'_mem hd))⟩⟩
  · rw [dite_eq_right hd]
    have hu : IsUniprimitive univ (wlRel (orbRel P S (e a') (e b') e)) := by
      rcases Recursion.wlRel_split_or_uniprimitive h2 hab _ hR with ⟨h, -⟩ | hu
      · exact absurd h hd
      · exact hu
    obtain ⟨hlive, hcount, hvalid⟩ := split_or_johnson hcoh hu
      (t := (m + 3) / 2) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
    rw [Fintype.card_fin] at hcount
    refine ⟨CTree.cb_live_trans (chBack_chMap e) hlive,
      (CTree.cb_count_trans (chBack_chMap e) _).trans_le hcount, ?_⟩
    rw [SplitJohnson.CTree.allLeaves_iff_reach]
    intro o ho
    obtain ⟨o₀, ho₀, rfl⟩ := (CTree.cb_reach_trans (chBack_chMap e)).1 ho
    have hv := (SplitJohnson.CTree.allLeaves_iff_reach.1 hvalid) o₀ ho₀
    rcases o₀ with _ | p | J
    · exact hv.elim
    · exact Or.inl ⟨_, _, rfl, extPart_valid e hv⟩
    · have hdisj := soj_johnson_disjoint _ _ ho₀
      refine Or.inr ⟨_, _, rfl, extJohn_valid e (isJohnson_trimJ hv),
        extJohn_trim e (fun i hi => ?_), extJohn_disj e hdisj⟩
      show (if i ∈ J.V0 then J.f i else ∅) = ∅
      exact ite_eq_right_iff.2 fun h => absurd h hi

/-- **The partition leaves have blocks of at most `b` points** (stage 14j-6b-1): a leaf that is
a colored partition is a colored `t`-partition for some `t ≤ b`. -/
def PartLe (b : ℕ) (o : Option (Out Γ)) : Prop :=
  ∀ p, o = some (Sum.inl p) → ∃ t ≤ b, IsColPart univ t p

/-- **The extension of a small colored partition is small**: blocks of at most
`max t (|Γ| − m)` points, the complement of the range being one block. -/
theorem extPart_partLe (e : Fin m ↪ Γ) {t b : ℕ} {p : CPart (Fin m)} (hp : IsColPart univ t p)
    (ht : t ≤ b) : ∃ t' ≤ max b (Fintype.card Γ - m), IsColPart univ t' (extPart e p) := by
  refine ⟨_, ?_, extPart_valid e hp⟩
  have hc : (univ \ univ.map e).card = Fintype.card Γ - m := by
    rw [card_univ_sdiff, card_map, card_univ, Fintype.card_fin]
  rw [hc]
  exact max_le_max ht le_rfl

/-- **The size of the leaf tree's partitions**: under the hypotheses of `leafTree_spec`, every
partition leaf is a colored `t`-partition with `t ≤ max ((m + 3) / 2) (|Γ| − m)`, from
Split-or-Johnson's `(m + 3) / 2`, the components' `m / 2` (`isColPart_comp`) and the complement
block of the extension (`extPart_partLe`). -/
theorem leafTree_partLe (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (S : Finset Γ)
    (e : Fin m ↪ Γ) {a' b' : Fin m} (hab : a' ≠ b') (hm : 4 ≤ m)
    (hmaps : ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (e i) = e j)
    (htr : IsPretransitive (fixGroup P S e) (Fin m))
    (h2 : ¬ IsMultiplyPretransitive (fixGroup P S e) (Fin m) 2) :
    (leafTree P S (e a') (e b') e).AllLeaves
      (PartLe (max ((m + 3) / 2) (Fintype.card Γ - m))) := by
  have hR := orbRel_iff (a' := a') (b' := b') hmaps
  obtain ⟨hcoh, hhom, -, -⟩ := Recursion.wlRel_spec h2 hab _ hR
  unfold leafTree
  by_cases hd : (disconn univ (wlRel (orbRel P S (e a') (e b') e))).Nonempty
  · rw [dite_eq_left hd]
    intro p hp
    cases Sum.inl.inj (Option.some.inj hp)
    refine extPart_partLe e (GraphIso.SplitJohnson.isColPart_comp
      (GraphIso.SplitJohnson.isCoh2On_univ hcoh) hhom ((disconn univ _).min'_mem hd)) ?_
    rw [card_univ, Fintype.card_fin]
    omega
  · rw [dite_eq_right hd]
    have hu : IsUniprimitive univ (wlRel (orbRel P S (e a') (e b') e)) := by
      rcases Recursion.wlRel_split_or_uniprimitive h2 hab _ hR with ⟨h, -⟩ | hu
      · exact absurd h hd
      · exact hu
    obtain ⟨-, -, hvalid⟩ := split_or_johnson hcoh hu
      (t := (m + 3) / 2) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
    rw [SplitJohnson.CTree.allLeaves_iff_reach]
    intro o ho
    obtain ⟨o₀, ho₀, rfl⟩ := (CTree.cb_reach_trans (chBack_chMap e)).1 ho
    have hv := (SplitJohnson.CTree.allLeaves_iff_reach.1 hvalid) o₀ ho₀
    rcases o₀ with _ | p | J
    · intro p hp
      cases hp
    · intro p' hp'
      cases Sum.inl.inj (Option.some.inj hp')
      exact extPart_partLe e hv le_rfl
    · intro p hp
      cases hp

end Leaf

/-! ### The tree -/

section Tree

variable {Γ : Type*} [Fintype Γ] [LinearOrder Γ]

/-- The points of a choice. -/
def ptsOf (c : Choice Γ) : List Γ := (show List (Γ ⊕ Finset Γ) from c).filterMap Sum.getLeft?

/-- The `k`-tuples of distinct points of `Φ`, as choices. -/
def tuplesOf (Φ : Finset Γ) (k : ℕ) : Finset (Choice Γ) :=
  ((univ : Finset (Fin k → Γ)).filter fun T => Function.Injective T ∧ ∀ i, T i ∈ Φ).image
    fun T => (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) : Choice Γ)

/-- The pairs of distinct points of `X`, as choices. -/
def pairsOf (X : Finset Γ) : Finset (Choice Γ) :=
  ((X ×ˢ X).filter fun p => p.1 ≠ p.2).image fun p =>
    ([Sum.inl p.1, Sum.inl p.2] : Choice Γ)

/-- The increasing numbering of a finite set. -/
def eOf (X : Finset Γ) : Fin X.card ↪ Γ := (X.orderEmbOfFin rfl).toEmbedding

/-- The node over the pairs of `Φ ∖ S`, after individualizing `S`. -/
def pairNode (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (Φ S : Finset Γ) : STree Γ :=
  .node (pairsOf (Φ \ S)) fun ch => match ptsOf ch with
    | [a, b] => leafTree P S a b (eOf (Φ \ S))
    | _ => .leaf none

/-- **The choice tree of Case 2b.** -/
def case2bTree (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (Φ : Finset Γ) (d : ℕ) :
    STree Γ :=
  .node (tuplesOf Φ (d - 1)) fun ch => pairNode P Φ (ptsOf ch).toFinset

/-! #### Canonicity -/

omit [Fintype Γ] in
theorem ptsOf_smul (σ : Perm Γ) (c : Choice Γ) : ptsOf (σ • c) = (ptsOf c).map σ := by
  show List.filterMap _ (List.map _ _) = List.map _ (List.filterMap _ _)
  induction (show List (Γ ⊕ Finset Γ) from c) with
  | nil => rfl
  | cons q l ih =>
    rcases q with v | t
    · simp only [List.map_cons, Sum.smul_inl, List.filterMap_cons, Sum.getLeft?_inl, ih,
        Perm.smul_def]
    · simp only [List.map_cons, Sum.smul_inr, List.filterMap_cons, Sum.getLeft?_inr, ih]

omit [Fintype Γ] in
theorem mem_eOf_range (X : Finset Γ) (v : Γ) : (∃ j, eOf X j = v) ↔ v ∈ X := by
  rw [← Set.mem_range]
  unfold eOf
  rw [show (⇑(X.orderEmbOfFin rfl).toEmbedding) = ⇑(X.orderEmbOfFin rfl) from rfl,
    Finset.range_orderEmbOfFin]
  rfl

theorem tuplesOf_smul (σ : Perm Γ) (Φ : Finset Γ) (k : ℕ) :
    tuplesOf (σ • Φ) k = σ • tuplesOf Φ k := by
  ext ch
  constructor
  · intro h
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨-, hinj, hΦ⟩ := Finset.mem_filter.1 hT
    refine Finset.mem_smul_finset.2 ⟨_, Finset.mem_image.2 ⟨fun i => σ⁻¹ (T i),
      Finset.mem_filter.2 ⟨mem_univ _, fun i j hij => hinj (σ⁻¹.injective hij), fun i => ?_⟩,
      rfl⟩, ?_⟩
    · show σ⁻¹ (T i) ∈ Φ
      obtain ⟨w, hw, hwi⟩ := mem_smul_finset.1 (hΦ i)
      rw [← hwi, Perm.smul_def, perm_inv_apply_self]
      exact hw
    · show List.map _ (List.ofFn _) = List.ofFn _
      rw [List.map_ofFn]
      congr 1
      funext i
      simp [Function.comp, Perm.smul_def]
  · intro h
    obtain ⟨_, h₁, rfl⟩ := Finset.mem_smul_finset.1 h
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨-, hinj, hΦ⟩ := Finset.mem_filter.1 hT
    refine Finset.mem_image.2 ⟨fun i => σ (T i), Finset.mem_filter.2 ⟨mem_univ _,
      fun i j hij => hinj (σ.injective hij), fun i =>
        Finset.smul_mem_smul_finset (a := σ) (hΦ i)⟩, ?_⟩
    show List.ofFn _ = List.map _ (List.ofFn _)
    rw [List.map_ofFn]
    congr 1

omit [Fintype Γ] in
theorem pairsOf_smul (σ : Perm Γ) (X : Finset Γ) : pairsOf (σ • X) = σ • pairsOf X := by
  ext ch
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨huv₁, hne⟩ := Finset.mem_filter.1 huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.1 huv₁
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_smul_finset.1 hu
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_smul_finset.1 hv
    refine Finset.mem_smul_finset.2 ⟨_, Finset.mem_image.2 ⟨(u₀, v₀), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hu₀, hv₀⟩, fun h => hne (by simp only at h ⊢; rw [h])⟩, rfl⟩, rfl⟩
  · intro h
    obtain ⟨_, h₁, rfl⟩ := Finset.mem_smul_finset.1 h
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 h₁
    obtain ⟨huv₁, hne⟩ := Finset.mem_filter.1 huv
    obtain ⟨hu, hv⟩ := Finset.mem_product.1 huv₁
    exact Finset.mem_image.2 ⟨(σ u, σ v), Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨Finset.smul_mem_smul_finset (a := σ) hu, Finset.smul_mem_smul_finset (a := σ) hv⟩,
      fun h => hne (σ.injective h)⟩, rfl⟩

theorem pairNode_relabel (σ : Perm Γ) {P P' : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P')] (hP : ∀ g, g ∈ P' ↔ σ⁻¹ * g * σ ∈ P) (Φ S : Finset Γ) :
    pairNode P' (σ • Φ) (σ • S) = (pairNode P Φ S).act σ := by
  have hsd : σ • Φ \ σ • S = σ • (Φ \ S) := Finset.smul_finset_sdiff.symm
  unfold pairNode
  show SplitJohnson.CTree.node _ _ = SplitJohnson.CTree.node _ _
  congr 1
  · rw [hsd, pairsOf_smul]
  · funext ch
    have hp : ptsOf (σ⁻¹ • ch) = (ptsOf ch).map ⇑σ⁻¹ := ptsOf_smul σ⁻¹ ch
    beta_reduce
    rw [hp]
    rcases h : ptsOf ch with _ | ⟨a, _ | ⟨b, _ | ⟨w, l⟩⟩⟩
    · rfl
    · rfl
    · show leafTree P' (σ • S) a b (eOf (σ • Φ \ σ • S)) =
        (leafTree P S (σ⁻¹ a) (σ⁻¹ b) (eOf (Φ \ S))).act σ
      have ha : a = σ (σ⁻¹ a) := (perm_apply_inv_self σ a).symm
      have hb : b = σ (σ⁻¹ b) := (perm_apply_inv_self σ b).symm
      conv_lhs => rw [ha, hb]
      refine leafTree_relabel σ hP S _ _ _ _ (by rw [hsd, Finset.card_smul_finset]) fun v => ?_
      rw [mem_eOf_range, mem_eOf_range, hsd, mem_smul_finset]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rwa [Perm.smul_def, perm_inv_apply_self]
      · intro hv
        exact ⟨σ⁻¹ v, hv, by rw [Perm.smul_def, perm_apply_inv_self]⟩
    · rfl

/-- **Canonicity of the choice tree of Case 2b.** -/
theorem case2bTree_relabel' (σ : Perm Γ) {P P' : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P')] (hP : ∀ g, g ∈ P' ↔ σ⁻¹ * g * σ ∈ P) (Φ : Finset Γ) (d : ℕ) :
    case2bTree P' (σ • Φ) d = (case2bTree P Φ d).act σ := by
  unfold case2bTree
  show SplitJohnson.CTree.node _ _ = SplitJohnson.CTree.node _ _
  congr 1
  · exact tuplesOf_smul σ Φ (d - 1)
  · funext ch
    have hS : (ptsOf ch).toFinset = σ • (ptsOf (σ⁻¹ • ch)).toFinset := by
      rw [ptsOf_smul σ⁻¹ ch]
      ext v
      simp only [List.mem_toFinset, mem_smul_finset, List.mem_map, Perm.smul_def]
      constructor
      · intro hv
        exact ⟨σ⁻¹ v, ⟨v, hv, rfl⟩, perm_apply_inv_self σ v⟩
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        rwa [perm_apply_inv_self]
    rw [hS]
    exact pairNode_relabel σ hP Φ _

/-! #### Validity, liveness and the count -/

/-- **The hypotheses of Case 2b** on `P` and `Φ` at degree `d`: `P` maps `Φ` into itself, `Φ`
has at least `d + 3` points, and after fixing any `d − 1` points of `Φ` the elements of `P`
act on the rest of `Φ` transitively and not doubly transitively (milestone 13's
`fixing_transitive_not_two`, for `d` the degree of transitivity). -/
structure Case2bHyp (P : Subgroup (Perm Γ)) (Φ : Finset Γ) (d : ℕ) : Prop where
  pres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ
  size : d - 1 + 4 ≤ Φ.card
  trans : ∀ S : Finset Γ, S ⊆ Φ → S.card = d - 1 → ∀ x ∈ Φ \ S, ∀ y ∈ Φ \ S,
    ∃ g ∈ P, (∀ s ∈ S, g s = s) ∧ g x = y
  notTwo : ∀ S : Finset Γ, S ⊆ Φ → S.card = d - 1 →
    ¬ ∀ x₁ ∈ Φ \ S, ∀ x₂ ∈ Φ \ S, ∀ y₁ ∈ Φ \ S, ∀ y₂ ∈ Φ \ S, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g ∈ P, (∀ s ∈ S, g s = s) ∧ g x₁ = y₁ ∧ g x₂ = y₂

omit [Fintype Γ] [LinearOrder Γ] in
theorem ptsOf_ofFn {k : ℕ} (T : Fin k → Γ) :
    ptsOf (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) : Choice Γ) = List.ofFn T := by
  show List.filterMap _ (List.ofFn _) = _
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.filterMap_cons, Sum.getLeft?_inl]
    exact congrArg _ (ih fun i => T i.succ)

omit [Fintype Γ] in
/-- **The hypotheses of `leafTree_spec` at valid choices** `S`, for the increasing numbering of
`Φ ∖ S`. -/
theorem cb_choice_facts {P : Subgroup (Perm Γ)} {Φ : Finset Γ} {d : ℕ} (H : Case2bHyp P Φ d)
    {S : Finset Γ} (hSΦ : S ⊆ Φ) (hS : S.card = d - 1) :
    4 ≤ (Φ \ S).card ∧
      (∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (eOf (Φ \ S) i) = eOf (Φ \ S) j) ∧
      IsPretransitive (fixGroup P S (eOf (Φ \ S))) (Fin (Φ \ S).card) ∧
      ¬ IsMultiplyPretransitive (fixGroup P S (eOf (Φ \ S))) (Fin (Φ \ S).card) 2 := by
  set e := eOf (Φ \ S)
  have hcard : 4 ≤ (Φ \ S).card := by
    rw [card_sdiff_of_subset hSΦ]
    have := H.size
    omega
  have hmaps : ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, e j = g (e i) := by
    intro g hg hgS i
    have hi : e i ∈ Φ \ S := (mem_eOf_range (Φ \ S) _).1 ⟨i, rfl⟩
    rw [mem_sdiff] at hi
    refine (mem_eOf_range (Φ \ S) _).2 (mem_sdiff.2 ⟨H.pres g hg _ hi.1, fun hs => hi.2 ?_⟩)
    have := hgS _ hs
    rw [← g.injective this]
    exact hs
  have hmaps' : ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (e i) = e j := fun g hg hgS i => by
    obtain ⟨j, hj⟩ := hmaps g hg hgS i
    exact ⟨j, hj.symm⟩
  refine ⟨hcard, hmaps', ?_, ?_⟩
  · refine ⟨fun u v => ?_⟩
    obtain ⟨g, hg, hgS, hgu⟩ := H.trans S hSΦ hS (e u) ((mem_eOf_range _ _).1 ⟨u, rfl⟩)
      (e v) ((mem_eOf_range _ _).1 ⟨v, rfl⟩)
    obtain ⟨h, hh, he⟩ := cb_realize hg hgS (hmaps' g hg hgS)
    exact ⟨⟨h, hh⟩, e.injective (by rw [← hgu, he]; rfl)⟩
  · intro h2
    rw [is_two_pretransitive_iff] at h2
    refine H.notTwo S hSΦ hS fun x₁ hx₁ x₂ hx₂ y₁ hy₁ y₂ hy₂ hx hy => ?_
    obtain ⟨u₁, rfl⟩ := (mem_eOf_range _ _).2 hx₁
    obtain ⟨u₂, rfl⟩ := (mem_eOf_range _ _).2 hx₂
    obtain ⟨v₁, rfl⟩ := (mem_eOf_range _ _).2 hy₁
    obtain ⟨v₂, rfl⟩ := (mem_eOf_range _ _).2 hy₂
    obtain ⟨⟨h, g, hg, hgS, he⟩, h₁, h₂⟩ :=
      h2 (a := u₁) (b := u₂) (c := v₁) (d := v₂) (fun h => hx (by rw [h]))
        (fun h => hy (by rw [h]))
    refine ⟨g, hg, hgS, ?_, ?_⟩
    · rw [he]
      exact congrArg e h₁
    · rw [he]
      exact congrArg e h₂

/-- The leaf at valid choices satisfies the hypotheses of `leafTree_spec`. -/
theorem cb_choice_spec {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ} {d : ℕ}
    (H : Case2bHyp P Φ d) {S : Finset Γ} (hSΦ : S ⊆ Φ) (hS : S.card = d - 1) {a b : Γ}
    (ha : a ∈ Φ \ S) (hb : b ∈ Φ \ S) (hab : a ≠ b) :
    (leafTree P S a b (eOf (Φ \ S))).Live ∧
      (leafTree P S a b (eOf (Φ \ S))).count ≤
        2 ^ (129 * (Nat.clog 2 (Φ \ S).card + 2) ^ 2) ∧
      (leafTree P S a b (eOf (Φ \ S))).AllLeaves ValidLeaf := by
  obtain ⟨a', rfl⟩ := (mem_eOf_range (Φ \ S) a).2 ha
  obtain ⟨b', rfl⟩ := (mem_eOf_range (Φ \ S) b).2 hb
  obtain ⟨hcard, hmaps', htr, h2⟩ := cb_choice_facts H hSΦ hS
  exact leafTree_spec P S _ (fun h => hab (by rw [h])) hcard hmaps' htr h2

/-- **The partition leaves at valid choices are small** (stage 14j-6b-1): blocks of at most
`max ((|Φ| − (d − 1) + 3) / 2) (|Γ| − (|Φ| − (d − 1)))` points (`leafTree_partLe`). -/
theorem cb_choice_partLe {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ} {d : ℕ}
    (H : Case2bHyp P Φ d) {S : Finset Γ} (hSΦ : S ⊆ Φ) (hS : S.card = d - 1) {a b : Γ}
    (ha : a ∈ Φ \ S) (hb : b ∈ Φ \ S) (hab : a ≠ b) :
    (leafTree P S a b (eOf (Φ \ S))).AllLeaves
      (PartLe (max ((Φ.card - (d - 1) + 3) / 2) (Fintype.card Γ - (Φ.card - (d - 1))))) := by
  obtain ⟨a', rfl⟩ := (mem_eOf_range (Φ \ S) a).2 ha
  obtain ⟨b', rfl⟩ := (mem_eOf_range (Φ \ S) b).2 hb
  obtain ⟨hcard, hmaps', htr, h2⟩ := cb_choice_facts H hSΦ hS
  have hc : (Φ \ S).card = Φ.card - (d - 1) := by rw [card_sdiff_of_subset hSΦ, hS]
  have h := leafTree_partLe P S (eOf (Φ \ S)) (a' := a') (b' := b') (fun h => hab (by rw [h]))
    hcard hmaps' htr h2
  exact h.mono fun o ho => by rwa [hc] at ho

/-- **Every reachable leaf of the Case 2b tree is valid.** -/
theorem case2bTree_valid {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ}
    {d : ℕ} (H : Case2bHyp P Φ d) : (case2bTree P Φ d).AllLeaves ValidLeaf := by
  intro ch hch
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hch
  obtain ⟨-, hinj, hTΦ⟩ := mem_filter.1 hT
  show (pairNode P Φ (ptsOf (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) :
    Choice Γ)).toFinset).AllLeaves ValidLeaf
  rw [ptsOf_ofFn]
  have hSΦ : (List.ofFn T).toFinset ⊆ Φ := fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (List.mem_toFinset.1 hx)
    exact hTΦ i
  have hS : (List.ofFn T).toFinset.card = d - 1 := by
    rw [List.toFinset_card_of_nodup (List.nodup_ofFn.2 hinj), List.length_ofFn]
  intro ch₂ hch₂
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hch₂
  obtain ⟨habΦ, hne⟩ := mem_filter.1 hab
  obtain ⟨ha, hb⟩ := mem_product.1 habΦ
  exact (cb_choice_spec H hSΦ hS ha hb hne).2.2

/-- **The partition leaves of the Case 2b tree are small** (stage 14j-6b-1): under `Case2bHyp`,
every reachable partition leaf is a colored `t`-partition with
`t ≤ max ((|Φ| − (d − 1) + 3) / 2) (|Γ| − (|Φ| − (d − 1)))`. -/
theorem case2bTree_partLe {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ}
    {d : ℕ} (H : Case2bHyp P Φ d) :
    (case2bTree P Φ d).AllLeaves
      (PartLe (max ((Φ.card - (d - 1) + 3) / 2) (Fintype.card Γ - (Φ.card - (d - 1))))) := by
  intro ch hch
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hch
  obtain ⟨-, hinj, hTΦ⟩ := mem_filter.1 hT
  show (pairNode P Φ (ptsOf (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) :
    Choice Γ)).toFinset).AllLeaves _
  rw [ptsOf_ofFn]
  have hSΦ : (List.ofFn T).toFinset ⊆ Φ := fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (List.mem_toFinset.1 hx)
    exact hTΦ i
  have hS : (List.ofFn T).toFinset.card = d - 1 := by
    rw [List.toFinset_card_of_nodup (List.nodup_ofFn.2 hinj), List.length_ofFn]
  intro ch₂ hch₂
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hch₂
  obtain ⟨habΦ, hne⟩ := mem_filter.1 hab
  obtain ⟨ha, hb⟩ := mem_product.1 habΦ
  exact cb_choice_partLe H hSΦ hS ha hb hne

theorem cb_tuple_of_mem {Φ : Finset Γ} {k : ℕ} {ch : Choice Γ} (hch : ch ∈ tuplesOf Φ k) :
    ∃ T : Fin k → Γ, Function.Injective T ∧ (∀ i, T i ∈ Φ) ∧
      ch = (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) : Choice Γ) := by
  obtain ⟨T, hT, rfl⟩ := mem_image.1 hch
  obtain ⟨-, hinj, hTΦ⟩ := mem_filter.1 hT
  exact ⟨T, hinj, hTΦ, rfl⟩

omit [Fintype Γ] in
theorem cb_set_of_tuple {Φ : Finset Γ} {k : ℕ} {T : Fin k → Γ} (hinj : Function.Injective T)
    (hTΦ : ∀ i, T i ∈ Φ) : (List.ofFn T).toFinset ⊆ Φ ∧ (List.ofFn T).toFinset.card = k := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 (List.mem_toFinset.1 hx)
    exact hTΦ i
  · rw [List.toFinset_card_of_nodup (List.nodup_ofFn.2 hinj), List.length_ofFn]

/-- The spec of the pair node after valid individualizations. -/
theorem pairNode_spec {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ} {d : ℕ}
    (H : Case2bHyp P Φ d) {S : Finset Γ} (hSΦ : S ⊆ Φ) (hS : S.card = d - 1) :
    (pairNode P Φ S).Live ∧
      (pairNode P Φ S).count ≤ Φ.card ^ 2 * 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2) := by
  have hcard : 4 ≤ (Φ \ S).card := by
    rw [card_sdiff_of_subset hSΦ]
    have := H.size
    omega
  have hleaf : ∀ ch ∈ pairsOf (Φ \ S), (match ptsOf ch with
      | [a, b] => leafTree P S a b (eOf (Φ \ S))
      | _ => .leaf none : STree Γ).Live ∧
      (match ptsOf ch with
      | [a, b] => leafTree P S a b (eOf (Φ \ S))
      | _ => .leaf none : STree Γ).count ≤ 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2) := by
    intro ch hch
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := mem_image.1 hch
    obtain ⟨habΦ, hne⟩ := mem_filter.1 hab
    obtain ⟨ha, hb⟩ := mem_product.1 habΦ
    have hpts : ptsOf ([Sum.inl a, Sum.inl b] : Choice Γ) = [a, b] := rfl
    show (match ptsOf ([Sum.inl a, Sum.inl b] : Choice Γ) with
      | [a, b] => leafTree P S a b (eOf (Φ \ S))
      | _ => .leaf none : STree Γ).Live ∧ _
    rw [hpts]
    obtain ⟨hl, hc, -⟩ := cb_choice_spec H hSΦ hS ha hb hne
    refine ⟨hl, hc.trans (Nat.pow_le_pow_right two_pos ?_)⟩
    have : Nat.clog 2 (Φ \ S).card ≤ Nat.clog 2 Φ.card :=
      Nat.clog_mono_right 2 (card_le_card sdiff_subset)
    have h2 : (Nat.clog 2 (Φ \ S).card + 2) ^ 2 ≤ (Nat.clog 2 Φ.card + 2) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    omega
  refine ⟨⟨?_, fun ch hch => (hleaf ch hch).1⟩, ?_⟩
  · obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (show 1 < (Φ \ S).card by omega)
    exact ⟨_, mem_image.2 ⟨(a, b), mem_filter.2 ⟨mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩⟩
  · show ∑ ch ∈ pairsOf (Φ \ S), _ ≤ _
    refine (sum_le_card_nsmul _ _ _ fun ch hch => (hleaf ch hch).2).trans ?_
    rw [smul_eq_mul]
    refine Nat.mul_le_mul_right _ ?_
    calc (pairsOf (Φ \ S)).card ≤ ((Φ \ S) ×ˢ (Φ \ S)).card :=
          card_image_le.trans (card_filter_le _ _)
      _ = (Φ \ S).card ^ 2 := by rw [card_product, sq]
      _ ≤ Φ.card ^ 2 := Nat.pow_le_pow_left (card_le_card sdiff_subset) 2

/-- **The Case 2b tree is live.** -/
theorem case2bTree_live {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ}
    {d : ℕ} (H : Case2bHyp P Φ d) : (case2bTree P Φ d).Live := by
  refine ⟨?_, fun ch hch => ?_⟩
  · have hk : d - 1 < Φ.card := by
      have := H.size
      omega
    refine ⟨_, mem_image.2 ⟨fun i : Fin (d - 1) => Φ.orderEmbOfFin rfl ⟨i, by omega⟩,
      mem_filter.2 ⟨mem_univ _, fun i j hij => ?_, fun i => Φ.orderEmbOfFin_mem rfl _⟩, rfl⟩⟩
    have := (Φ.orderEmbOfFin rfl).injective hij
    exact Fin.ext (by simpa using this)
  · obtain ⟨T, hinj, hTΦ, rfl⟩ := cb_tuple_of_mem hch
    show (pairNode P Φ (ptsOf (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) :
      Choice Γ)).toFinset).Live
    rw [ptsOf_ofFn]
    obtain ⟨hSΦ, hS⟩ := cb_set_of_tuple hinj hTΦ
    exact (pairNode_spec H hSΦ hS).1

/-- **The count of the Case 2b tree**: at most `|Φ|^(d+1) · 2^(129 (⌈log₂ |Φ|⌉ + 2)²)`. -/
theorem case2bTree_count_le {P : Subgroup (Perm Γ)} [DecidablePred (· ∈ P)] {Φ : Finset Γ}
    {d : ℕ} (H : Case2bHyp P Φ d) (hd : 1 ≤ d) :
    (case2bTree P Φ d).count ≤ Φ.card ^ (d + 1) * 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2) := by
  have hpair : ∀ ch ∈ tuplesOf Φ (d - 1), (pairNode P Φ (ptsOf ch).toFinset).count ≤
      Φ.card ^ 2 * 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2) := by
    intro ch hch
    obtain ⟨T, hinj, hTΦ, rfl⟩ := cb_tuple_of_mem hch
    show (pairNode P Φ (ptsOf (List.ofFn fun i => (Sum.inl (T i) : Γ ⊕ Finset Γ) :
      Choice Γ)).toFinset).count ≤ _
    rw [ptsOf_ofFn]
    obtain ⟨hSΦ, hS⟩ := cb_set_of_tuple hinj hTΦ
    exact (pairNode_spec H hSΦ hS).2
  show ∑ ch ∈ tuplesOf Φ (d - 1), _ ≤ _
  refine (sum_le_card_nsmul _ _ _ hpair).trans ?_
  rw [smul_eq_mul]
  have htup : (tuplesOf Φ (d - 1)).card ≤ Φ.card ^ (d - 1) := by
    refine card_image_le.trans ?_
    calc ((univ : Finset (Fin (d - 1) → Γ)).filter
          fun T => Function.Injective T ∧ ∀ i, T i ∈ Φ).card
        ≤ (Fintype.piFinset fun _ : Fin (d - 1) => Φ).card := by
          refine card_le_card fun T hT => Fintype.mem_piFinset.2 fun i => ?_
          exact (mem_filter.1 hT).2.2 i
      _ = Φ.card ^ (d - 1) := by rw [Fintype.card_piFinset, prod_const, card_univ,
          Fintype.card_fin]
  calc (tuplesOf Φ (d - 1)).card * (Φ.card ^ 2 * 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2))
      ≤ Φ.card ^ (d - 1) * (Φ.card ^ 2 * 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2)) :=
        Nat.mul_le_mul_right _ htup
    _ = Φ.card ^ (d + 1) * 2 ^ (129 * (Nat.clog 2 Φ.card + 2) ^ 2) := by
        rw [← mul_assoc, ← pow_add, show d - 1 + 2 = d + 1 by omega]

/-! #### The hypotheses from the degree of transitivity -/

omit [Fintype Γ] in
/-- An enumeration of a finite set of `k` points. -/
theorem cb_enum {S : Finset Γ} {k : ℕ} (hS : S.card = k) :
    ∃ U : Fin k → Γ, Function.Injective U ∧ ∀ v, v ∈ S ↔ ∃ i, U i = v := by
  refine ⟨S.orderEmbOfFin hS, (S.orderEmbOfFin hS).injective, fun v => ?_⟩
  rw [← Set.mem_range, Finset.range_orderEmbOfFin]
  rfl

omit [Fintype Γ] [LinearOrder Γ] in
theorem cb_snoc_inj {k : ℕ} {U : Fin k → Γ} (hU : Function.Injective U) {x : Γ}
    (hx : ∀ i, U i ≠ x) : Function.Injective (Fin.snoc (α := fun _ => Γ) U x) :=
  Fin.snoc_injective_iff.2 ⟨hU, fun ⟨i, hi⟩ => hx i hi⟩

omit [Fintype Γ] in
/-- **The hypotheses of Case 2b from the degree of transitivity**: if `P` maps `Φ` into itself,
moves any `d` distinct points of `Φ` to any `d` distinct points (`d = (d - 1) + 1`), cannot do
so for `d + 1` points, and `|Φ| ≥ d + 3`, then after fixing `d − 1` points it acts on the rest
of `Φ` transitively and not doubly transitively. -/
theorem case2bHyp_of_degree {P : Subgroup (Perm Γ)} {Φ : Finset Γ} {d : ℕ}
    (hpres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ) (hsize : d - 1 + 4 ≤ Φ.card)
    (htr : ∀ T T' : Fin (d - 1 + 1) → Γ, Function.Injective T → Function.Injective T' →
      (∀ i, T i ∈ Φ) → (∀ i, T' i ∈ Φ) → ∃ g ∈ P, ∀ i, g (T i) = T' i)
    (hnot : ¬ ∀ T T' : Fin (d - 1 + 2) → Γ, Function.Injective T → Function.Injective T' →
      (∀ i, T i ∈ Φ) → (∀ i, T' i ∈ Φ) → ∃ g ∈ P, ∀ i, g (T i) = T' i) :
    Case2bHyp P Φ d := by
  refine ⟨hpres, hsize, fun S hSΦ hS x hx y hy => ?_, fun S hSΦ hS h2 => ?_⟩
  · obtain ⟨U, hU, hUS⟩ := cb_enum hS
    have hxS : ∀ i, U i ≠ x := fun i hi => (mem_sdiff.1 hx).2 ((hUS x).2 ⟨i, hi⟩)
    have hyS : ∀ i, U i ≠ y := fun i hi => (mem_sdiff.1 hy).2 ((hUS y).2 ⟨i, hi⟩)
    have hUΦ : ∀ i, U i ∈ Φ := fun i => hSΦ ((hUS _).2 ⟨i, rfl⟩)
    obtain ⟨g, hg, hgT⟩ := htr _ _ (cb_snoc_inj hU hxS) (cb_snoc_inj hU hyS)
      (fun i => Fin.lastCases (by simpa using (mem_sdiff.1 hx).1)
        (fun j => by simpa using hUΦ j) i)
      (fun i => Fin.lastCases (by simpa using (mem_sdiff.1 hy).1)
        (fun j => by simpa using hUΦ j) i)
    refine ⟨g, hg, fun s hs => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := (hUS s).1 hs
      have := hgT (Fin.castSucc i)
      simpa using this
    · have := hgT (Fin.last _)
      simpa using this
  · -- the double transitivity on the rest would give `(d + 1)`-transitivity
    apply hnot
    intro T T' hT hT' hTΦ hT'Φ
    obtain ⟨U, hU, hUS⟩ := cb_enum hS
    have hUΦ : ∀ i, U i ∈ Φ := fun i => hSΦ ((hUS _).2 ⟨i, rfl⟩)
    have hcard : 1 < (Φ \ S).card := by
      rw [card_sdiff_of_subset hSΦ]
      omega
    obtain ⟨z, hz, -⟩ := one_lt_card.1 hcard
    have hzS : ∀ i, U i ≠ z := fun i hi => (mem_sdiff.1 hz).2 ((hUS z).2 ⟨i, hi⟩)
    have hB := cb_snoc_inj hU hzS
    have hBΦ : ∀ i, (Fin.snoc (α := fun _ => Γ) U z : Fin (d - 1 + 1) → Γ) i ∈ Φ := fun i =>
      Fin.lastCases (by simpa using (mem_sdiff.1 hz).1) (fun j => by simpa using hUΦ j) i
    -- move the first `d` points of `T` and of `T'` to `U` followed by `z`
    have hpre : ∀ T : Fin (d - 1 + 2) → Γ, Function.Injective T → (∀ i, T i ∈ Φ) →
        ∃ g ∈ P, ∀ i : Fin (d - 1 + 1), g (T (Fin.castSucc i)) =
          (Fin.snoc (α := fun _ => Γ) U z : Fin (d - 1 + 1) → Γ) i :=
      fun T hT hTΦ => htr _ _ (hT.comp (Fin.castSucc_injective _)) hB
        (fun i => hTΦ _) hBΦ
    obtain ⟨g₁, hg₁, he₁⟩ := hpre T hT hTΦ
    obtain ⟨g₂, hg₂, he₂⟩ := hpre T' hT' hT'Φ
    -- the last points land in the rest, away from `z`
    have hrest : ∀ (T : Fin (d - 1 + 2) → Γ) (g : Perm Γ), Function.Injective T →
        (∀ i, T i ∈ Φ) → g ∈ P → (∀ i : Fin (d - 1 + 1), g (T (Fin.castSucc i)) =
          (Fin.snoc (α := fun _ => Γ) U z : Fin (d - 1 + 1) → Γ) i) →
        g (T (Fin.last _)) ∈ Φ \ S ∧ z ≠ g (T (Fin.last _)) := by
      intro T g hT hTΦ hg he
      refine ⟨mem_sdiff.2 ⟨hpres g hg _ (hTΦ _), fun hs => ?_⟩, fun hz' => ?_⟩
      · obtain ⟨j, hj⟩ := (hUS _).1 hs
        have h1 := he (Fin.castSucc j)
        rw [Fin.snoc_castSucc, hj] at h1
        have := hT (g.injective h1)
        exact absurd this (Fin.ne_of_lt (Fin.castSucc_lt_last _))
      · have h1 := he (Fin.last _)
        rw [Fin.snoc_last, hz'] at h1
        have := hT (g.injective h1)
        exact absurd this (Fin.ne_of_lt (Fin.castSucc_lt_last _))
    obtain ⟨hx₂, hzx⟩ := hrest T g₁ hT hTΦ hg₁ he₁
    obtain ⟨hy₂, hzy⟩ := hrest T' g₂ hT' hT'Φ hg₂ he₂
    obtain ⟨g, hg, hgS, hgz, hgx⟩ := h2 z hz _ hx₂ z hz _ hy₂ hzx hzy
    refine ⟨g₂⁻¹ * g * g₁, P.mul_mem (P.mul_mem (P.inv_mem hg₂) hg) hg₁, fun i => ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq]
    induction i using Fin.lastCases with
    | last => exact hgx
    | cast i =>
      induction i using Fin.lastCases with
      | last =>
        simp only [he₁, he₂, Fin.snoc_last]
        exact hgz
      | cast j =>
        simp only [he₁, he₂, Fin.snoc_castSucc]
        exact hgS _ ((hUS _).2 ⟨j, rfl⟩)

/-! #### The canonicity in the forms the recursion uses -/

/-- **Canonicity**, for the conjugate subgroup. -/
theorem case2bTree_relabel (σ : Perm Γ) (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P.map (MulAut.conj σ).toMonoidHom)] (Φ : Finset Γ) (d : ℕ) :
    case2bTree (P.map (MulAut.conj σ).toMonoidHom) (σ • Φ) d = (case2bTree P Φ d).act σ := by
  refine case2bTree_relabel' σ (fun g => ?_) Φ d
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hh
  · intro hg
    exact ⟨σ⁻¹ * g * σ, hg, by simp [mul_assoc]⟩

/-- The tree depends on the subgroup, not on how its membership is decided. -/
theorem case2bTree_congr {P P' : Subgroup (Perm Γ)} (hP : P = P') [DecidablePred (· ∈ P)]
    [DecidablePred (· ∈ P')] (Φ : Finset Γ) (d : ℕ) :
    case2bTree P Φ d = case2bTree P' Φ d := by
  subst hP
  congr

/-- **The alignment hypothesis of Case 2b**: for `P` and `Φ` given canonically by the string,
every isomorphism carries a reachable leaf of the tree for `x` to a reachable leaf of the tree
for `y` (milestone 14a's `iso_reach`). -/
theorem case2b_reach {Ω α : Type*} {G : Subgroup (Perm Ω)} {W : Set Ω} {ψ : G →* Perm Γ}
    (hW : IsInvariant G W) (Pm : (Ω → α) → Subgroup (Perm Γ)) [∀ x, DecidablePred (· ∈ Pm x)]
    (Φm : (Ω → α) → Finset Γ) (d : ℕ)
    (hlocP : ∀ x x' : Ω → α, (∀ u ∈ W, x u = x' u) → Pm x = Pm x')
    (hlocΦ : ∀ x x' : Ω → α, (∀ u ∈ W, x u = x' u) → Φm x = Φm x')
    (heqP : ∀ (g : G) (x : Ω → α) (h : Perm Γ),
      h ∈ Pm (relabel (g : Perm Ω) x) ↔ (ψ g)⁻¹ * h * ψ g ∈ Pm x)
    (heqΦ : ∀ (g : G) (x : Ω → α), Φm (relabel (g : Perm Ω) x) = ψ g • Φm x)
    {x y : Ω → α} {o : Option (Out Γ)} (ho : (case2bTree (Pm x) (Φm x) d).Reach o)
    {g : Perm Ω} (hg : g ∈ iso W 1 G x y) :
    (case2bTree (Pm y) (Φm y) d).Reach (ψ ⟨g, (mem_iso_one.1 hg).1⟩ • o) := by
  refine iso_reach (ψ := ψ) hW (fun x => case2bTree (Pm x) (Φm x) d) (fun x x' h => ?_)
    (fun g x => ?_) ho hg
  · show case2bTree (Pm x) (Φm x) d = case2bTree (Pm x') (Φm x') d
    rw [hlocΦ x x' h]
    exact case2bTree_congr (hlocP x x' h) _ d
  · show case2bTree (Pm (relabel (g : Perm Ω) x)) (Φm (relabel (g : Perm Ω) x)) d = _
    rw [heqΦ g x]
    exact case2bTree_relabel' (ψ g) (heqP g x) (Φm x) d

end Tree

end GraphIso.Case2b
