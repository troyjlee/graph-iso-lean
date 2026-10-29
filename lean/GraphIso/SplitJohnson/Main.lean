module

public import GraphIso.SplitJohnson.MainDef
public import GraphIso.SplitJohnson.Bipartite

/-!
# Split-or-Johnson

**Split-or-Johnson** (Helfgott, Thm. 5.3; Babai, §7): for a uniprimitive classical coherent
configuration `c` on a finite type `Γ` and a threshold `t` with `|Γ| + 2 ≤ 2t` and `t < |Γ|`
(Helfgott's `α` is the case `t = ⌊α|Γ|⌋`, covered when `|Γ| + 2 ≤ 2⌊α|Γ|⌋`), the choice tree
`soj c t` is live, has at most `2^{129 (⌈log₂ |Γ|⌉ + 2)²}` paths — a multiplicative cost
`|Γ|^{O(log |Γ|)}` — and every reachable leaf is a colored `t`-partition of `Γ` or a Johnson
scheme embedded in `Γ` on more than `t` points (`split_or_johnson`). It is canonical under
`Sym(Γ)` (`split_or_johnson_relabel`), so a relabelling carries the reachable leaves onto those
of the relabelled input (`split_or_johnson_reach`).

The choice of `x` costs `|Γ|`. Exercise B.7 gives the colours `beige` and `cyan`; the bipartite
graph `(C_aqua, C_beige; cyan)` is semiregular, nonempty and not complete (its degrees on
`C_beige` are below `|Γ| − t < |C_aqua|`), so by Exercise 5.4 its twin classes are at most half
of `C_aqua`, and Bipartite Split-or-Johnson applies with the same threshold
(`MainValid.main_case`); its colored partitions extend to `Γ` by the classes of `c x ·`
(`MainValid.extendPart_valid`). Canonicity is `MainRelabel.sojAt_relabel` at each `x`.
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

namespace MainRelabel

/-! ### Relabelling -/

theorem filter_inv_smul (σ : Equiv.Perm Γ) (P : Γ → Prop) [DecidablePred P] :
    (univ.filter fun z => P (σ⁻¹ • z)) = σ • univ.filter P := by
  ext z
  simp only [mem_filter, mem_univ, true_and, ← inv_smul_mem_iff]

theorem smul_colPart_univ (σ : Equiv.Perm Γ) (f : Γ → ℕ) :
    σ • colPart univ f = colPart univ fun z => f (σ⁻¹ • z) := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  funext v
  exact (filter_inv_smul σ fun y => f y = f (σ⁻¹ • v)).symm

theorem smul_extendOut (σ : Equiv.Perm Γ) (V₁ : Finset Γ) (col : Γ → ℕ)
    (o : Option (Out Γ)) :
    σ • extendOut V₁ col o = extendOut (σ • V₁) (fun z => col (σ⁻¹ • z)) (σ • o) := by
  match o with
  | none => rfl
  | some (Sum.inr J) => rfl
  | some (Sum.inl p) =>
    show some (Sum.inl (σ • extendPart V₁ col p)) =
      some (Sum.inl (extendPart (σ • V₁) (fun z => col (σ⁻¹ • z)) (σ • p)))
    congr 2
    show CPart.mk _ _ = CPart.mk _ _
    congr 1
    · funext v
      show (if σ⁻¹ • v ∈ V₁ then _ else _) = if v ∈ σ • V₁ then _ else _
      simp only [inv_smul_mem_iff]
      rfl
    · funext v
      show σ • (if σ⁻¹ • v ∈ V₁ then _ else _) = if v ∈ σ • V₁ then _ else _
      simp only [inv_smul_mem_iff]
      split_ifs with h
      · rfl
      · rw [← filter_inv_smul]
        refine filter_congr fun z _ => ?_
        rw [inv_smul_mem_iff]

omit [Fintype Γ] in
/-- Binding commutes with the action when the continuations correspond. -/
theorem bind_act (σ : Equiv.Perm Γ) (T : STree Γ) {f f' : Option (Out Γ) → STree Γ}
    (hf : ∀ o, f' (σ • o) = (f o).act σ) : (T.act σ).bind f' = (T.bind f).act σ := by
  induction T with
  | leaf o => exact hf o
  | node S k ih => simp only [CTree.act, CTree.bind, ih]

omit [Fintype Γ] in
theorem image_smul_aqua (σ : Equiv.Perm Γ) (c : Γ → Γ → ℕ) (x : Γ) (B : Finset Γ) :
    (σ • B).image (fun z => c x (σ⁻¹ • z)) = B.image (c x) := by
  ext a
  simp only [mem_image, mem_smul_finset]
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by rw [inv_smul_smul]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨σ • w, ⟨w, hw, rfl⟩, by rw [inv_smul_smul]⟩

theorem pairs_smul (σ : Equiv.Perm Γ) (c : Γ → Γ → ℕ) (x : Γ) (B : Finset Γ) (aq : Finset ℕ) :
    (((σ • B) ×ˢ univ).filter fun q => c x (σ⁻¹ • q.2) ∉ aq ∧
        c (σ⁻¹ • q.1) (σ⁻¹ • q.2) ∉ aq).image
      (fun p => Nat.pair (c x (σ⁻¹ • p.2)) (c (σ⁻¹ • p.1) (σ⁻¹ • p.2))) =
    ((B ×ˢ univ).filter fun p => c x p.2 ∉ aq ∧ c p.1 p.2 ∉ aq).image
      fun p => Nat.pair (c x p.2) (c p.1 p.2) := by
  ext m
  simp only [mem_image, mem_filter, mem_product, mem_univ, and_true, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, h₁, h₂⟩, rfl⟩
    exact ⟨σ⁻¹ • a, σ⁻¹ • b, ⟨inv_smul_mem_iff.2 ha, h₁, h₂⟩, rfl⟩
  · rintro ⟨a, b, ⟨ha, h₁, h₂⟩, rfl⟩
    refine ⟨σ • a, σ • b, ⟨smul_mem_smul_finset ha, ?_, ?_⟩, ?_⟩ <;>
      simp only [inv_smul_smul] <;> assumption

omit [Fintype Γ] in
theorem image_singleton_smul (σ : Equiv.Perm Γ) (F : Finset Γ) :
    (σ • F).image (singleton : Γ → Finset Γ) = σ • F.image (singleton : Γ → Finset Γ) := by
  rw [smul_finset_def, smul_finset_def, image_image, image_image]
  refine image_congr fun y _ => ?_
  simp only [Function.comp_apply, smul_finset_singleton]

/-- **`sojAt` is canonical.** -/
theorem sojAt_relabel (σ : Equiv.Perm Γ) (c : Γ → Γ → ℕ) (t : ℕ) (x : Γ) :
    sojAt (relab2 σ c) t (σ • x) = (sojAt c t x).act σ := by
  have hr : ∀ a b, relab2 σ c a b = c (σ⁻¹ • a) (σ⁻¹ • b) := fun _ _ => rfl
  have hx : relab2 σ c (σ • x) = fun z => c x (σ⁻¹ • z) := by
    funext z
    rw [hr, inv_smul_smul]
  have hcls : ∀ y, (univ.filter fun z => c x (σ⁻¹ • z) = c x (σ⁻¹ • y)).card =
      (univ.filter fun z => c x z = c x (σ⁻¹ • y)).card := fun y => by
    rw [filter_inv_smul σ fun z => c x z = c x (σ⁻¹ • y), card_smul_finset]
  have hbig : (univ.filter fun y => t < (univ.filter fun z => c x z = c x (σ⁻¹ • y)).card) =
      σ • univ.filter fun y => t < (univ.filter fun z => c x z = c x y).card :=
    filter_inv_smul σ fun y => t < (univ.filter fun z => c x z = c x y).card
  unfold sojAt
  simp only [hx, hr, inv_smul_smul, hcls, hbig, smul_finset_eq_empty, image_smul_aqua,
    pairs_smul]
  set B := univ.filter fun y => t < (univ.filter fun z => c x z = c x y).card with hBd
  set P := ((B ×ˢ univ).filter fun p => c x p.2 ∉ B.image (c x) ∧
    c p.1 p.2 ∉ B.image (c x)).image (fun p => Nat.pair (c x p.2) (c p.1 p.2)) with hPd
  by_cases hB : B = ∅
  · rw [ite_eq_left hB, ite_eq_left hB]
    simp only [CTree.act, Option.smul_some, Sum.smul_inl, smul_colPart_univ]
  rw [ite_eq_right hB, ite_eq_right hB]
  by_cases hP : P.Nonempty
  · rw [dite_eq_left hP, dite_eq_left hP]
    generalize Nat.unpair (P.min' hP) = k
    have hV₂ : (univ.filter fun y => c x (σ⁻¹ • y) = k.1).image (singleton : Γ → Finset Γ) =
        σ • (univ.filter fun y => c x y = k.1).image (singleton : Γ → Finset Γ) := by
      rw [filter_inv_smul σ fun y => c x y = k.1, image_singleton_smul]
    have hA : (fun z (s : Finset Γ) => decide (∃ y ∈ s, c (σ⁻¹ • z) (σ⁻¹ • y) = k.2)) =
        relabA σ fun z s => decide (∃ y ∈ s, c z y = k.2) := by
      funext z s
      simp only [relabA, decide_eq_decide]
      constructor
      · rintro ⟨y, hy, h⟩
        exact ⟨σ⁻¹ • y, smul_mem_smul_finset hy, h⟩
      · rintro ⟨y, hy, h⟩
        obtain ⟨y', hy', rfl⟩ := mem_smul_finset.1 hy
        exact ⟨y', hy', h⟩
    rw [hV₂, hA, bipartite_split_or_johnson_relabel]
    refine bind_act σ _ fun o => ?_
    simp only [CTree.act, smul_extendOut]
  · rw [dite_eq_right hP, dite_eq_right hP]
    rfl

/-- **`soj` is canonical.** -/
theorem soj_relabel (σ : Equiv.Perm Γ) (c : Γ → Γ → ℕ) (t : ℕ) :
    soj (relab2 σ c) t = (soj c t).act σ := by
  unfold soj
  simp only [CTree.act]
  congr 1
  · apply Finset.ext
    intro ch
    rw [mem_smul_finset]
    constructor
    · intro h
      obtain ⟨x, -, rfl⟩ := mem_image.1 h
      refine ⟨[Sum.inl (σ⁻¹ • x)], mem_image.2 ⟨σ⁻¹ • x, mem_univ _, rfl⟩, ?_⟩
      show [σ • (Sum.inl (σ⁻¹ • x) : Γ ⊕ Finset Γ)] = _
      rw [Sum.smul_inl, smul_inv_smul]
    · rintro ⟨_, h, rfl⟩
      obtain ⟨x, -, rfl⟩ := mem_image.1 h
      exact mem_image.2 ⟨σ • x, mem_univ _, rfl⟩
  · funext ch
    match ch with
    | [] => rfl
    | [Sum.inr s] => rfl
    | a :: _ :: _ => rcases a with a | a <;> rfl
    | [Sum.inl x] =>
      show sojAt (relab2 σ c) t x = (sojAt c t (σ⁻¹ • x)).act σ
      rw [← sojAt_relabel, smul_inv_smul]

end MainRelabel

namespace MainValid

/-! ### Validity -/

omit [DecidableEq Γ] in
/-- A classical coherent configuration on `Γ` is one on `univ`. -/
theorem isCoh2On_univ {c : Γ → Γ → ℕ} (hc : IsCoherent2 c) : IsCoh2On univ c := by
  refine ⟨fun x y x' y' h => ?_, fun x y x' y' h r s => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hc.config h
    exact ⟨by rw [Subtype.ext_iff, Subtype.ext_iff]; exact h1, h2, h3, h4⟩
  · have e := fun a b : Γ =>
      card_univ_filter_val (univ : Finset Γ) fun z => c a z = r ∧ c z b = s
    dsimp only
    rw [e, e]
    exact hc.2 x y x' y' h r s

/-- At most one colour class of `c x ·` has more than `t` points. -/
theorem big_eq {c : Γ → Γ → ℕ} {t : ℕ} (ht : Fintype.card Γ + 2 ≤ 2 * t) (x : Γ) {z₀ : Γ}
    (hz₀ : t < (univ.filter fun z => c x z = c x z₀).card) :
    (univ.filter fun y => t < (univ.filter fun z => c x z = c x y).card) =
      univ.filter fun z => c x z = c x z₀ := by
  ext w
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro hw
    by_contra hne
    have hdisj : Disjoint (univ.filter fun z => c x z = c x w)
        (univ.filter fun z => c x z = c x z₀) := by
      rw [disjoint_filter]
      intro z _ h1 h2
      exact hne (h1.symm.trans h2)
    have h1 := card_union_of_disjoint hdisj
    have h2 := card_le_univ ((univ.filter fun z => c x z = c x w) ∪
      univ.filter fun z => c x z = c x z₀)
    omega
  · intro hw
    have e : (univ.filter fun z => c x z = c x w) = univ.filter fun z => c x z = c x z₀ := by
      simp only [hw]
    rwa [e]

/-- Extending a colored partition of `B` by the classes of `col` outside `B`. -/
theorem extendPart_valid {B : Finset Γ} {t : ℕ} {col : Γ → ℕ}
    (hcol : ∀ y, y ∉ B → (univ.filter fun z => col z = col y).card ≤ t) {p : CPart Γ}
    (hp : IsColPart B t p) : IsColPart univ t (extendPart B col p) where
  mem_blk v _ := by
    by_cases hv : v ∈ B
    · simp only [extendPart, hv, ↓reduceIte]
      exact hp.mem_blk v hv
    · simp [extendPart, hv]
  blk_sub v _ := subset_univ _
  blk_eq v _ w hw := by
    by_cases hv : v ∈ B
    · simp only [extendPart, hv, ↓reduceIte] at hw ⊢
      have hwB : w ∈ B := hp.blk_sub v hv hw
      simp only [hwB, ↓reduceIte]
      exact hp.blk_eq v hv w hw
    · simp only [extendPart, hv, ↓reduceIte, mem_filter, mem_univ, true_and] at hw ⊢
      simp only [hw.1, ↓reduceIte, hw.2]
  col_eq v _ w hw := by
    by_cases hv : v ∈ B
    · simp only [extendPart, hv, ↓reduceIte] at hw ⊢
      have hwB : w ∈ B := hp.blk_sub v hv hw
      simp only [hwB, ↓reduceIte, hp.col_eq v hv w hw]
    · simp only [extendPart, hv, ↓reduceIte, mem_filter, mem_univ, true_and] at hw ⊢
      simp only [hw.1, ↓reduceIte, hw.2]
  card_eq v _ w _ h := by
    by_cases hv : v ∈ B <;> by_cases hw : w ∈ B <;>
      simp only [extendPart, hv, hw, ↓reduceIte] at h ⊢
    · exact hp.card_eq v hv w hw (by omega)
    · omega
    · omega
    · have h' : col v = col w := by omega
      simp only [h']
  admissible v _ h1 w _ h := by
    by_cases hv : v ∈ B <;> by_cases hw : w ∈ B <;>
      simp only [extendPart, hv, hw, ↓reduceIte] at h h1
    · exact hp.admissible v hv h1 w hw (by omega)
    · omega
    · omega
    · obtain ⟨a, ha⟩ := card_eq_one.1 h1
      have hva : v ∈ ({a} : Finset Γ) := by
        rw [← ha]
        simp [hv]
      have hwa : w ∈ ({a} : Finset Γ) := by
        rw [← ha]
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨hw, by omega⟩
      rw [mem_singleton] at hva hwa
      rw [hva, hwa]
  card_le v _ := by
    by_cases hv : v ∈ B
    · simp only [extendPart, hv, ↓reduceIte]
      exact hp.card_le v hv
    · simp only [extendPart, hv, ↓reduceIte]
      refine (card_le_card fun z hz => ?_).trans (hcol v hv)
      simp only [mem_filter, mem_univ, true_and] at hz ⊢
      exact hz.2

/-- Extending a valid leaf. -/
theorem extendOut_valid {B : Finset Γ} {t : ℕ} {col : Γ → ℕ}
    (hcol : ∀ y, y ∉ B → (univ.filter fun z => col z = col y).card ≤ t)
    {o : Option (Out Γ)} (ho : ValidOut B t o) : ValidOut univ t (extendOut B col o) := by
  match o, ho with
  | some (Sum.inl p), hp => exact extendPart_valid hcol hp
  | some (Sum.inr J), hJ =>
    have hJ' : IsJohnson B t J := hJ
    exact { hJ' with sub := subset_univ _ }

/-- **The main case of `sojAt`**: `c x z₁ = aqua` is the colour of the class `B` of more than
`t` points, `c x y₁ = beige` and `c z₁ y₁ = cyan` differ from `aqua`. -/
theorem main_case {c : Γ → Γ → ℕ} {t : ℕ} (hc : IsCoherent2 c) (hu : IsUniprimitive univ c)
    (ht : Fintype.card Γ + 2 ≤ 2 * t) {x z₁ y₁ : Γ}
    (hBt : t < (univ.filter fun z => c x z = c x z₁).card)
    (hy₁ : c x y₁ ≠ c x z₁) (hzy : c z₁ y₁ ≠ c x z₁) (T : STree Γ)
    (hT : T = (bsoj t (univ.filter fun z => c x z = c x z₁)
        ((univ.filter fun y => c x y = c x y₁).image singleton)
          fun z s => decide (∃ y ∈ s, c z y = c z₁ y₁)).bind
        fun o => .leaf (extendOut (univ.filter fun z => c x z = c x z₁) (c x) o)) :
    T.Live ∧ T.AllLeaves (ValidOut univ t) ∧ T.count ≤ 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) := by
  have hcU := isCoh2On_univ hc
  have hh : IsHomog univ c := hu.1.1
  set B := univ.filter fun z => c x z = c x z₁ with hB
  set F := univ.filter fun y => c x y = c x y₁ with hF
  set V₂ := F.image (singleton : Γ → Finset Γ) with hV₂
  set A : Γ → Finset Γ → Bool := fun z s => decide (∃ y ∈ s, c z y = c z₁ y₁) with hA
  have hn : (univ : Finset Γ).card = Fintype.card Γ := card_univ
  have hFB : Disjoint F B := by
    rw [hF, hB, disjoint_filter]
    intro y _ h1 h2
    exact hy₁ (h1.symm.trans h2)
  have hBn : B.card ≤ Fintype.card Γ := hn ▸ card_le_univ B
  have hFn : F.card + B.card ≤ Fintype.card Γ := by
    rw [← card_union_of_disjoint hFB]
    exact hn ▸ card_le_univ _
  have hv : V₂.card ≤ t := card_image_le.trans (by omega)
  have hz₁ : z₁ ∈ B := mem_filter.2 ⟨mem_univ _, rfl⟩
  have hy₁F : y₁ ∈ F := mem_filter.2 ⟨mem_univ _, rfl⟩
  -- degrees on the side of the points
  have hdeg : ∀ z, (V₂.filter fun s => A z s).card =
      (univ.filter fun y => c x y = c x y₁ ∧ c z y = c z₁ y₁).card := by
    intro z
    have e : V₂.filter (fun s => A z s) =
        (univ.filter fun y => c x y = c x y₁ ∧ c z y = c z₁ y₁).image singleton := by
      ext s
      simp only [hV₂, hF, hA, mem_filter, mem_image, mem_univ, true_and, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, y', hy', h⟩
        rw [mem_singleton] at hy'
        subst hy'
        exact ⟨y', ⟨hy, h⟩, rfl⟩
      · rintro ⟨y, ⟨hy, h⟩, rfl⟩
        exact ⟨⟨y, hy, rfl⟩, y, mem_singleton_self y, h⟩
    rw [e, card_image_of_injective _ singleton_injective]
  have h₁ : ∀ z ∈ B, (V₂.filter fun s => A z s).card = (V₂.filter fun s => A z₁ s).card := by
    intro z hz
    rw [hdeg, hdeg]
    have hz' : c x z = c x z₁ := (mem_filter.1 hz).2
    have key : ∀ w : Γ, (univ.filter fun y => c x y = c x y₁ ∧ c w y = c z₁ y₁) =
        univ.filter fun y => (fun a b => a = c x y₁ ∧ ∃ u v, c u v = b ∧ c v u = c z₁ y₁)
          (c x y) (c y w) := by
      intro w
      refine filter_congr fun y _ => ?_
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, y, w, rfl, h2⟩
      · rintro ⟨h1, u, v, h2, h3⟩
        exact ⟨h1, by rw [← (hc.config h2).2.1]; exact h3⟩
    rw [key z, key z₁]
    exact hc.card_filter_pred hz'
      (fun a b => a = c x y₁ ∧ ∃ u v, c u v = b ∧ c v u = c z₁ y₁)
  -- degrees on the side of the cells
  have h₂ : ∀ s ∈ V₂, (B.filter fun z => A z s).card = (B.filter fun z => A z {y₁}).card := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hs
    have e : ∀ y', (B.filter fun z => A z {y'}) =
        univ.filter fun z => c x z = c x z₁ ∧ c z y' = c z₁ y₁ := by
      intro y'
      ext z
      simp [hB, hA]
    rw [e, e]
    exact hc.card_filter_pred (show c x y = c x y₁ from (mem_filter.1 hy).2)
      (fun a b => a = c x z₁ ∧ b = c z₁ y₁)
  have hne : ∃ z ∈ B, ∃ s ∈ V₂, A z s = true :=
    ⟨z₁, hz₁, {y₁}, mem_image_of_mem _ hy₁F, by simp [hA]⟩
  have hnc : ∃ z ∈ B, ∃ s ∈ V₂, A z s = false := by
    by_contra hno
    push Not at hno
    have hall : ∀ z ∈ B, c z y₁ = c z₁ y₁ := by
      intro z hz
      have := hno z hz {y₁} (mem_image_of_mem _ hy₁F)
      simpa [hA] using this
    have hsub : B ⊆ univ.filter fun z => c z y₁ = c z₁ y₁ := fun z hz =>
      mem_filter.2 ⟨mem_univ _, hall z hz⟩
    have e1 := hcU.card_in_eq_out hh (mem_univ y₁) (mem_univ y₁) (c z₁ y₁)
    have e2 := hcU.outdeg (mem_univ y₁) (mem_univ x) (hh y₁ (mem_univ _) x (mem_univ _))
      (c x z₁)
    have hd : Disjoint (univ.filter fun w => c y₁ w = c z₁ y₁)
        (univ.filter fun w => c y₁ w = c x z₁) := by
      rw [disjoint_filter]
      intro w _ h1 h2
      exact hzy (h1.symm.trans h2)
    have h3 := card_union_of_disjoint hd
    have h4 := card_le_univ ((univ.filter fun w => c y₁ w = c z₁ y₁) ∪
      univ.filter fun w => c y₁ w = c x z₁)
    have h5 := card_le_card hsub
    rw [hB] at hBt h5
    omega
  have htw : ∀ z ∈ B, (twinCls B V₂ A z).card ≤ t := fun z hz => by
    have := two_mul_card_twinCls_le h₁ h₂ hne hnc hz
    omega
  have hcells : ∀ s ∈ V₂, s.Nonempty := fun s hs => by
    obtain ⟨y, -, rfl⟩ := mem_image.1 hs
    exact singleton_nonempty y
  have hdisj : ∀ s ∈ V₂, ∀ s' ∈ V₂, s ≠ s' → Disjoint s s' := fun s hs s' hs' hne' => by
    obtain ⟨y, -, rfl⟩ := mem_image.1 hs
    obtain ⟨y', -, rfl⟩ := mem_image.1 hs'
    exact disjoint_singleton.2 fun e => hne' (by rw [e])
  obtain ⟨hlive, hcount, hall⟩ :=
    bipartite_split_or_johnson hcells hdisj hv (by omega) hBt htw
  have hcol : ∀ y, y ∉ B → (univ.filter fun z => c x z = c x y).card ≤ t := by
    intro y hy
    by_contra hlt
    push Not at hlt
    have hyB : c x y ≠ c x z₁ := fun e => hy (mem_filter.2 ⟨mem_univ _, e⟩)
    have hd : Disjoint (univ.filter fun z => c x z = c x y) B := by
      rw [hB, disjoint_filter]
      intro z _ h1 h2
      exact hyB (h1.symm.trans h2)
    have h3 := card_union_of_disjoint hd
    have h4 := card_le_univ ((univ.filter fun z => c x z = c x y) ∪ B)
    omega
  subst hT
  refine ⟨CTree.live_bind hlive (hall.mono fun _ _ => trivial),
    CTree.allLeaves_bind (hall.mono fun o ho => extendOut_valid hcol ho), ?_⟩
  calc _ ≤ (bsoj t B V₂ A).count * 1 := CTree.count_bind_le (hall.mono fun _ _ => le_rfl)
    _ ≤ _ := by rw [mul_one]; exact hcount

/-- **`sojAt` is valid**, with its multiplicative cost. -/
theorem sojAt_spec {c : Γ → Γ → ℕ} {t : ℕ} (hc : IsCoherent2 c) (hu : IsUniprimitive univ c)
    (ht : Fintype.card Γ + 2 ≤ 2 * t) (x : Γ) :
    (sojAt c t x).Live ∧ (sojAt c t x).AllLeaves (ValidOut univ t) ∧
      (sojAt c t x).count ≤ 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) := by
  have hcU := isCoh2On_univ hc
  have hh : IsHomog univ c := hu.1.1
  unfold sojAt
  dsimp only
  by_cases hB : (univ.filter fun y => t < (univ.filter fun z => c x z = c x y).card) = ∅
  · rw [ite_eq_left hB]
    refine ⟨trivial, ?_, Nat.one_le_two_pow⟩
    refine colPart_valid fun y _ => ?_
    have : y ∉ univ.filter fun y => t < (univ.filter fun z => c x z = c x y).card := by
      rw [hB]
      exact notMem_empty y
    simpa using this
  rw [ite_eq_right hB]
  obtain ⟨z₀, hz₀⟩ := nonempty_iff_ne_empty.2 hB
  have hz₀' : t < (univ.filter fun z => c x z = c x z₀).card := (mem_filter.1 hz₀).2
  rw [big_eq ht x hz₀']
  have hAq : ∀ a, a ∈ (univ.filter fun z => c x z = c x z₀).image (c x) ↔ a = c x z₀ := by
    intro a
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · rintro rfl
      exact ⟨z₀, rfl, rfl⟩
  have hxz : x ≠ z₀ := by
    rintro rfl
    have hsub : (univ.filter fun z => c x z = c x x) ⊆ {x} := fun z hz => by
      have := (mem_filter.1 hz).2
      rw [mem_singleton]
      exact ((hc.config this).1.2 rfl).symm
    have := card_le_card hsub
    rw [card_singleton] at this
    omega
  obtain ⟨y, -, hy1, hy2⟩ := hu.exists_common hcU (mem_univ x) (mem_univ z₀) hxz
  have ha : (univ : Finset Γ).card < 2 * (univ.filter fun z => c x z = c x z₀).card := by
    rw [card_univ]
    omega
  have hy3 : c z₀ y ≠ c x z₀ := fun h =>
    hy2 (hcU.symm_of_large hh (mem_univ x) ha (mem_univ z₀) (mem_univ y) h)
  have hP : (((univ.filter fun z => c x z = c x z₀) ×ˢ univ).filter fun p =>
      c x p.2 ∉ (univ.filter fun z => c x z = c x z₀).image (c x) ∧
        c p.1 p.2 ∉ (univ.filter fun z => c x z = c x z₀).image (c x)).image
      (fun p => Nat.pair (c x p.2) (c p.1 p.2)) |>.Nonempty := by
    refine ⟨Nat.pair (c x y) (c z₀ y), mem_image.2 ⟨(z₀, y), ?_, rfl⟩⟩
    simp only [mem_filter, mem_product, mem_univ, true_and, and_true, hAq]
    exact ⟨hy1, hy3⟩
  rw [dite_eq_left hP]
  obtain ⟨⟨z₁, y₁⟩, hmem, hpair⟩ := mem_image.1 (min'_mem _ hP)
  simp only [mem_filter, mem_product, mem_univ, true_and, and_true, hAq] at hmem
  obtain ⟨hz₁', hy₁, hzy⟩ := hmem
  rw [← hpair, Nat.unpair_pair]
  have e : (univ.filter fun z => c x z = c x z₀) = univ.filter fun z => c x z = c x z₁ := by
    rw [hz₁']
  rw [e]
  exact main_case hc hu ht (e ▸ hz₀') (hz₁' ▸ hy₁) (hz₁' ▸ hzy) _ rfl

end MainValid

/-- **Split-or-Johnson** (Helfgott, Thm. 5.3). -/
theorem split_or_johnson {c : Γ → Γ → ℕ} {t : ℕ} (hc : IsCoherent2 c)
    (hu : IsUniprimitive univ c) (ht : Fintype.card Γ + 2 ≤ 2 * t)
    (ht' : t < Fintype.card Γ) :
    (soj c t).Live ∧ (soj c t).count ≤ 2 ^ (129 * (Nat.clog 2 (Fintype.card Γ) + 2) ^ 2) ∧
      (soj c t).AllLeaves (ValidOut univ t) := by
  have hS := fun x => MainValid.sojAt_spec hc hu ht x
  obtain ⟨x₀⟩ : Nonempty Γ := Fintype.card_pos_iff.1 (by omega)
  refine ⟨⟨⟨_, mem_image_of_mem _ (mem_univ x₀)⟩, fun ch hch => ?_⟩, ?_, fun ch hch => ?_⟩
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hch
    exact (hS x).1
  · show ∑ ch ∈ univ.image fun x => ([.inl x] : List (Γ ⊕ Finset Γ)), _ ≤ _
    rw [sum_image fun a _ b _ e => by simpa using e]
    set L := Nat.clog 2 (Fintype.card Γ)
    have hnL : Fintype.card Γ ≤ 2 ^ L := Nat.le_pow_clog one_lt_two _
    have htL : Nat.clog 2 t ≤ L := Nat.clog_mono_right 2 ht'.le
    calc ∑ x, (sojAt c t x).count ≤ ∑ _x : Γ, 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) :=
          sum_le_sum fun x _ => (hS x).2.2
      _ = Fintype.card Γ * 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) := by
          rw [sum_const, card_univ, smul_eq_mul]
      _ ≤ 2 ^ L * 2 ^ (128 * (L + 2) ^ 2) := by
          refine Nat.mul_le_mul hnL (Nat.pow_le_pow_right two_pos ?_)
          have : (Nat.clog 2 t + 2) ^ 2 ≤ (L + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          omega
      _ ≤ 2 ^ (129 * (L + 2) ^ 2) := by
          rw [← pow_add]
          refine Nat.pow_le_pow_right two_pos ?_
          nlinarith
  · obtain ⟨x, -, rfl⟩ := mem_image.1 hch
    exact (hS x).2.1

/-- **Split-or-Johnson is canonical.** -/
theorem split_or_johnson_relabel (σ : Equiv.Perm Γ) (c : Γ → Γ → ℕ) (t : ℕ) :
    soj (relab2 σ c) t = (soj c t).act σ :=
  MainRelabel.soj_relabel σ c t

/-- **Isomorphism transfer**: `σ` carries the reachable leaves of `soj c t` onto those of the
relabelled input. So if `σ` maps `c` to `d = relab2 σ c`, every leaf of `soj d t` is the
`σ`-image of a leaf of `soj c t`, and conversely. -/
theorem split_or_johnson_reach (σ : Equiv.Perm Γ) (c : Γ → Γ → ℕ) (t : ℕ)
    (o : Option (Out Γ)) : (soj (relab2 σ c) t).Reach (σ • o) ↔ (soj c t).Reach o := by
  rw [split_or_johnson_relabel]
  exact CTree.reach_act σ

end GraphIso.SplitJohnson
