module

public import GraphIso.SplitJohnson.BipartiteDef

/-!
# Canonicity of Bipartite Split-or-Johnson: the pieces

Relabelling lemmas for the steps of `bstep` (BipartiteDef.lean): for `σ ∈ Sym(α)`, every
quantity computed from `(σ • V₁, σ • V₂, relabA σ A)` is the image under `σ` of the one computed
from `(V₁, V₂, A)`. Structures on `↥V₂` are transported along `eσ σ V₂ : ↥V₂ ≃ ↥(σ • V₂)`.
Tree-level lemmas: `act_bind'` (binding with a relabelled continuation) and `trans_bind_act`
(changing the type of choices and binding commute with the actions).
-/

@[expose] public section

namespace GraphIso.SplitJohnson.BipRelabel

open Finset Pointwise GraphIso.Coherent GraphIso.SplitJohnson

/-! ### General facts -/

theorem mem_smul_iff {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] {g : G}
    {S : Finset β} {b : β} : b ∈ g • S ↔ g⁻¹ • b ∈ S :=
  inv_smul_mem_iff.symm

theorem min'_eq_of_eq {s t : Finset ℕ} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty) :
    s.min' hs = t.min' ht := by
  subst h
  rfl

/-- Binding with a relabelled continuation commutes with the action. -/
theorem act_bind' {G C O O' : Type*} [Group G] [MulAction G C] [MulAction G O]
    [MulAction G O'] [DecidableEq C] (g : G) (t : CTree C O) {f f' : O → CTree C O'}
    (hf : ∀ o, f' (g • o) = (f o).act g) : (t.act g).bind f' = (t.bind f).act g := by
  induction t with
  | leaf o => exact hf o
  | node S k ih => simp only [CTree.bind, CTree.act, ih]

/-- Changing the type of choices and binding commute with the actions. -/
theorem trans_bind_act {G G' C C' O O'' : Type*} [Group G] [Group G'] [MulAction G C]
    [MulAction G O] [MulAction G' C'] [MulAction G' O''] [DecidableEq C] [DecidableEq C']
    (g : G) (g' : G') {f : C → C'} {r : C' → C} (hf : ∀ c, f (g • c) = g' • f c)
    (hr : ∀ c', r (g'⁻¹ • c') = g⁻¹ • r c') {k k' : O → CTree C' O''}
    (hk : ∀ o, k' (g • o) = (k o).act g') (T : CTree C O) :
    ((T.act g).trans f r id).bind k' = ((T.trans f r id).bind k).act g' := by
  induction T with
  | leaf o => exact hk o
  | node S k₀ ih =>
    simp only [CTree.act, CTree.trans, CTree.bind]
    congr 1
    · ext c'
      simp only [mem_image, mem_smul_finset]
      constructor
      · rintro ⟨c, ⟨c₀, hc₀, rfl⟩, rfl⟩
        exact ⟨f c₀, ⟨c₀, hc₀, rfl⟩, (hf c₀).symm⟩
      · rintro ⟨c₁, ⟨c₀, hc₀, rfl⟩, rfl⟩
        exact ⟨g • c₀, ⟨c₀, hc₀, rfl⟩, hf c₀⟩
    · funext c'
      rw [ih, hr]

/-- `selThird` commutes with embeddings that preserve the colouring. -/
theorem selThird_map {β γ : Type*} [DecidableEq β] [DecidableEq γ] (S : Finset β)
    (col : β → ℕ) (col' : γ → ℕ) (f : β ↪ γ) (hc : ∀ x, col' (f x) = col x) :
    selThird (S.map f) col' = (selThird S col).map f := by
  have himg : (S.map f).image col' = S.image col := by
    ext k
    simp [hc]
  have hfilt : ∀ P : ℕ → Prop, [DecidablePred P] →
      ((S.map f).filter fun x => P (col' x)) = (S.filter fun x => P (col x)).map f := by
    intro P _
    ext y
    simp only [mem_filter, mem_map]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hP⟩
      exact ⟨x, ⟨hx, by rwa [hc] at hP⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hP⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rwa [hc]⟩
  have hcard : ∀ P : ℕ → Prop, [DecidablePred P] →
      ((S.map f).filter fun x => P (col' x)).card = (S.filter fun x => P (col x)).card := by
    intro P _
    rw [hfilt P, card_map]
  unfold selThird
  simp only [card_map, himg]
  have e1 : ∀ k, ((S.map f).filter fun x => col' x = k).card =
      (S.filter fun x => col x = k).card := fun k => hcard (fun j => j = k)
  have e2 : ∀ l : List ℕ, ((S.map f).filter fun x => col' x ∈ l).card =
      (S.filter fun x => col x ∈ l).card := fun l => hcard (fun j => j ∈ l)
  simp only [e1, e2]
  generalize List.find? _ _ = o
  cases o with
  | some k => exact hfilt (fun j => j = k)
  | none =>
    have hl : ∀ l : List ℕ, ((S.map f).filter fun x => col' x ∈ l) =
        (S.filter fun x => col x ∈ l).map f := fun l => hfilt (fun j => j ∈ l)
    exact hl _


/-- A predicate filter of a moved set. -/
theorem filter_smul_eq {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G)
    (S : Finset β) {p q : β → Prop} [DecidablePred p] [DecidablePred q]
    (h : ∀ b, p (g • b) ↔ q b) : (g • S).filter p = g • S.filter q := by
  ext b
  rw [mem_filter, mem_smul_iff, mem_smul_iff, mem_filter, ← h, smul_inv_smul]

/-- A moved set is a mapped set. -/
theorem smul_eq_map {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G)
    (S : Finset β) : g • S = S.map (MulAction.toPerm g : Equiv.Perm β).toEmbedding := by
  rw [map_eq_image, smul_finset_def]
  rfl

/-- The equivalence `↥S ≃ ↥(g • S)` given by `g`. -/
def eS {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G) (S : Finset β) :
    S ≃ ↥(g • S) where
  toFun u := ⟨g • u.val, smul_mem_smul_finset u.2⟩
  invFun u := ⟨g⁻¹ • u.val, mem_smul_iff.1 u.2⟩
  left_inv u := Subtype.ext (inv_smul_smul g u.val)
  right_inv u := Subtype.ext (smul_inv_smul g u.val)

@[simp] theorem eS_val {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G)
    (S : Finset β) (u : S) : (eS g S u).val = g • u.val := rfl

/-- Mapping a subset of `↥S` to `↥(g • S)` and then into `β` is moving it by `g`. -/
theorem map_eS_subtype {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G)
    (S : Finset β) (T : Finset S) :
    (T.map (eS g S).toEmbedding).map (Function.Embedding.subtype _) =
      g • T.map (Function.Embedding.subtype _) := by
  ext b
  simp only [mem_map, Equiv.coe_toEmbedding, Function.Embedding.coe_subtype, mem_smul_finset]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u.val, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨eS g S u, ⟨u, hu, rfl⟩, rfl⟩

/-- A filter of `univ` transported along `eS`. -/
theorem filter_univ_eS {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G)
    (S : Finset β) {p : S → Prop} {p' : ↥(g • S) → Prop} [DecidablePred p] [DecidablePred p']
    (h : ∀ u, p' (eS g S u) ↔ p u) :
    (univ.filter p') = (univ.filter p).map (eS g S).toEmbedding := by
  ext u'
  simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hu
    refine ⟨(eS g S).symm u', ?_, by simp⟩
    rw [← h]
    simpa using hu
  · rintro ⟨u, hu, rfl⟩
    exact (h u).2 hu

/-! ### Relabelling the steps of `bstep` -/

variable {α : Type*} [DecidableEq α]

theorem relabA_smul (σ : Equiv.Perm α) (A : α → Finset α → Bool) (x : α) (s : Finset α) :
    relabA σ A (σ • x) (σ • s) = A x s := by
  simp [relabA]

theorem twinCls_smul (σ : Equiv.Perm α) (V₁ : Finset α) (S : Finset (Finset α))
    (A : α → Finset α → Bool) (x : α) :
    twinCls (σ • V₁) (σ • S) (relabA σ A) (σ • x) = σ • twinCls V₁ S A x := by
  ext y
  rw [mem_smul_iff, mem_twinCls, mem_twinCls, mem_smul_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h s hs
    have := h (σ • s) (smul_mem_smul_finset hs)
    simpa [relabA] using this
  · intro h s hs
    have := h (σ⁻¹ • s) (mem_smul_iff.1 hs)
    simpa [relabA] using this

theorem deg_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool)
    (x : α) : deg (σ • V₂) (relabA σ A) (σ • x) = deg V₂ A x := by
  unfold deg
  rw [filter_smul_eq σ V₂ (q := fun s => A x s = true) fun s => by rw [relabA_smul],
    card_smul_finset]

theorem nbr_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool)
    (x : α) : nbr (σ • V₂) (relabA σ A) (σ • x) = σ • nbr V₂ A x := by
  unfold nbr
  exact filter_smul_eq σ V₂ fun s => by rw [relabA_smul]

theorem tw_smul (σ : Equiv.Perm α) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) (x : α) :
    tw (σ • V₁) (σ • V₂) (relabA σ A) (σ • x) = tw V₁ V₂ A x := by
  unfold tw
  rw [twinCls_smul, card_smul_finset]

theorem tfDeg_smul (σ : Equiv.Perm α) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) (d : ℕ) :
    tfDeg (σ • V₁) (σ • V₂) (relabA σ A) d = σ • tfDeg V₁ V₂ A d := by
  unfold tfDeg
  exact filter_smul_eq σ V₁ fun x => by rw [tw_smul, deg_smul]

theorem bigDegs_smul (σ : Equiv.Perm α) (t : ℕ) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) :
    bigDegs t (σ • V₁) (σ • V₂) (relabA σ A) = bigDegs t V₁ V₂ A := by
  unfold bigDegs
  have : (σ • V₁).image (deg (σ • V₂) (relabA σ A)) = V₁.image (deg V₂ A) := by
    ext k
    simp only [mem_image, mem_smul_finset]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (deg_smul σ V₂ A x).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨σ • x, ⟨x, hx, rfl⟩, deg_smul σ V₂ A x⟩
  rw [this]
  refine filter_congr fun d _ => ?_
  rw [tfDeg_smul, card_smul_finset]

omit [DecidableEq α] in
theorem exists_smul_eq (σ : Equiv.Perm α) {β : Type*} [MulAction (Equiv.Perm α) β] (b : β) :
    ∃ b₀, b = σ • b₀ :=
  ⟨σ⁻¹ • b, (smul_inv_smul σ b).symm⟩

theorem twinPart_smul (σ : Equiv.Perm α) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) :
    twinPart (σ • V₁) (σ • V₂) (relabA σ A) = σ • twinPart V₁ V₂ A := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  · funext x
    obtain ⟨y, rfl⟩ := exists_smul_eq σ x
    rw [inv_smul_smul, tw_smul, deg_smul]
    rfl
  · funext x
    obtain ⟨y, rfl⟩ := exists_smul_eq σ x
    simp only [twinPart, inv_smul_smul, tw_smul, deg_smul, tfDeg_smul, twinCls_smul]
    split_ifs <;> rfl

/-- `colPart` of a moved set and a moved colouring. -/
theorem colPart_smul (σ : Equiv.Perm α) (V : Finset α) {f f' : α → ℕ}
    (hf : ∀ y, f' (σ • y) = f y) : colPart (σ • V) f' = σ • colPart V f := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  · funext x
    obtain ⟨y, rfl⟩ := exists_smul_eq σ x
    rw [inv_smul_smul, hf]
    rfl
  · funext x
    obtain ⟨y, rfl⟩ := exists_smul_eq σ x
    rw [inv_smul_smul]
    exact filter_smul_eq σ V fun z => by rw [hf, hf]

theorem choiceCells_smul (σ : Equiv.Perm α) (ch : Choice α) :
    choiceCells (σ • ch) = (choiceCells ch).map (σ • ·) := by
  let l : List (α ⊕ Finset α) := ch
  show List.filterMap _ (List.map _ l) = List.map _ (List.filterMap _ l)
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext q
  cases q <;> rfl

theorem nbrCode_smul (σ : Equiv.Perm α) (A : α → Finset α → Bool) (e : List (Finset α))
    (x : α) : nbrCode (relabA σ A) (e.map (σ • ·)) (σ • x) = nbrCode A e x := by
  unfold nbrCode
  rw [List.map_map]
  congr 2
  funext s
  simp only [Function.comp_apply, relabA_smul]

theorem smul_val {G β : Type*} [Group G] [MulAction G β] [DecidableEq β] (g : G)
    (S : Finset β) : (g • S).val = S.val.map (g • ·) := by
  rw [smul_finset_def, image_val_of_injOn fun a _ b _ h => smul_left_cancel g h]

theorem mem_enums {V₂ : Finset (Finset α)} {c : Choice α} :
    c ∈ enums V₂ ↔ ∃ l : List (Finset α), V₂.val = ↑l ∧ c = l.map Sum.inr := by
  refine Finset.mem_image.trans ?_
  simp only [Multiset.mem_toFinset, Multiset.mem_lists_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

theorem smul_map_inr (σ : Equiv.Perm α) (l : List (Finset α)) :
    σ • (show Choice α from l.map Sum.inr) =
      (show Choice α from (l.map (σ • ·)).map Sum.inr) := by
  show List.map _ (List.map _ l) = _
  rw [List.map_map, List.map_map]
  rfl

theorem enums_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) :
    enums (σ • V₂) = σ • enums V₂ := by
  ext c
  rw [mem_smul_iff, mem_enums, mem_enums, smul_val]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l.map (σ⁻¹ • ·), ?_, smul_map_inr σ⁻¹ l⟩
    rw [← Multiset.map_coe, ← hl, Multiset.map_map]
    simp
  · rintro ⟨l, hl, hc⟩
    refine ⟨l.map (σ • ·), ?_, ?_⟩
    · rw [hl, Multiset.map_coe]
    · rw [← smul_inv_smul σ c, hc]
      exact smul_map_inr σ l

theorem fOf_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool)
    (d₁ : ℕ) (x : α) : fOf (σ • V₂) (relabA σ A) d₁ (σ • x) = σ • fOf V₂ A d₁ x := by
  unfold fOf
  rw [card_smul_finset, nbr_smul]
  split_ifs
  · rw [smul_finset_sdiff]
  · rfl

theorem image_fOf_smul (σ : Equiv.Perm α) (V₁ : Finset α) (V₂ : Finset (Finset α))
    (A : α → Finset α → Bool) (d₁ : ℕ) :
    (σ • V₁).image (fOf (σ • V₂) (relabA σ A) d₁) = σ • V₁.image (fOf V₂ A d₁) := by
  ext F
  simp only [mem_image, mem_smul_finset]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨fOf V₂ A d₁ x, ⟨x, hx, rfl⟩, (fOf_smul σ V₂ A d₁ x).symm⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨σ • x, ⟨x, hx, rfl⟩, fOf_smul σ V₂ A d₁ x⟩

/-- The `d`-ary structure transported along `eS σ V₂`. -/
theorem daryCol_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α))
    (H : Finset (Finset (Finset α))) (d : ℕ) (y : Fin d → V₂) :
    daryCol (σ • V₂) (σ • H) d (⇑(eS σ V₂) ∘ y) = daryCol V₂ H d y := by
  unfold daryCol
  have himg : (univ.image fun i => ((⇑(eS σ V₂) ∘ y) i).val) =
      σ • univ.image fun i => (y i).val := by
    ext s
    simp only [mem_image, mem_univ, true_and, mem_smul_finset, Function.comp_apply, eS_val]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [himg, card_smul_finset,
    filter_smul_eq σ H (q := fun e => (univ.image fun i => (y i).val) ⊆ e)
      fun e => smul_finset_subset_smul_finset_iff, card_smul_finset]

/-- Twins transported along `eS σ V₂`. -/
theorem bigTwins_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) {d : ℕ}
    (cd : (Fin d → V₂) → ℕ) (cd' : (Fin d → ↥(σ • V₂)) → ℕ)
    (hcd : ∀ y, cd' (⇑(eS σ V₂) ∘ y) = cd y) : bigTwins (σ • V₂) cd' = σ • bigTwins V₂ cd := by
  unfold bigTwins
  have htw : ∀ u w : V₂, IsTwin cd' (eS σ V₂ u) (eS σ V₂ w) ↔ IsTwin cd u w := by
    intro u w
    rw [← isTwin_comp_equiv_iff cd' (eS σ V₂)]
    have : (fun x : Fin d → V₂ => cd' (⇑(eS σ V₂) ∘ x)) = cd := funext hcd
    rw [this]
  have hcnt : ∀ u : V₂, (univ.filter fun w => IsTwin cd' (eS σ V₂ u) w).card =
      (univ.filter fun w => IsTwin cd u w).card := by
    intro u
    rw [← card_filter_comp_equiv (eS σ V₂)]
    exact congrArg card (filter_congr fun w _ => htw u w)
  rw [filter_univ_eS σ V₂ (p := fun u : V₂ =>
      V₂.card < 2 * (univ.filter fun w => IsTwin cd u w).card)
    fun u => by rw [hcnt, card_smul_finset], map_eS_subtype]

theorem pickSide_smul (σ : Equiv.Perm α) (V₁ : Finset α) (V₂ S : Finset (Finset α))
    (A : α → Finset α → Bool) :
    pickSide (σ • V₁) (σ • V₂) (σ • S) (relabA σ A) = σ • pickSide V₁ V₂ S A := by
  unfold pickSide
  have hc : (∀ x ∈ σ • V₁, 2 * (twinCls (σ • V₁) (σ • S) (relabA σ A) x).card <
      (σ • V₁).card + 2) ↔ ∀ x ∈ V₁, 2 * (twinCls V₁ S A x).card < V₁.card + 2 := by
    rw [card_smul_finset]
    constructor
    · intro h x hx
      have := h (σ • x) (smul_mem_smul_finset hx)
      rwa [twinCls_smul, card_smul_finset] at this
    · intro h x hx
      obtain ⟨y, rfl⟩ := exists_smul_eq σ x
      rw [twinCls_smul, card_smul_finset]
      exact h y ((smul_mem_smul_finset_iff σ).1 hx)
  by_cases h : ∀ x ∈ V₁, 2 * (twinCls V₁ S A x).card < V₁.card + 2
  · rw [ite_eq_left (hc.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hc.1 h')), ite_eq_right h, smul_finset_sdiff]


/-! ### Structures on `↥V₂` transported along an equivalence -/

section Transport

variable {V V' : Type*} [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] {k : ℕ}

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
theorem pad1_map (e : V ≃ V') (x : List V) (u : V) :
    pad1 k (x.map e) (e u) = ⇑e ∘ pad1 k x u := by
  funext i
  simp only [pad1, List.length_map, Function.comp_apply]
  split_ifs <;> simp

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
theorem pad2_map (e : V ≃ V') (x : List V) (u v : V) :
    pad2 k (x.map e) (e u) (e v) = ⇑e ∘ pad2 k x u v := by
  funext i
  simp only [pad2, List.length_map, Function.comp_apply]
  split_ifs <;> simp

variable {W : (Fin k → V) → ℕ} {W' : (Fin k → V') → ℕ}

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
theorem skel1_map (e : V ≃ V') (hW : ∀ y, W' (⇑e ∘ y) = W y) (x : List V) (u : V) :
    skel1 W' (x.map e) (e u) = skel1 W x u := by
  unfold skel1
  rw [pad1_map, hW]

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
theorem skel2_map (e : V ≃ V') (hW : ∀ y, W' (⇑e ∘ y) = W y) (x : List V) (u v : V) :
    skel2 W' (x.map e) (e u) (e v) = skel2 W x u v := by
  unfold skel2
  rw [pad2_map, hW]

omit [DecidableEq V] [DecidableEq V'] in
theorem cls1_map (e : V ≃ V') (hW : ∀ y, W' (⇑e ∘ y) = W y) (x : List V) (u : V) :
    cls1 W' (x.map e) (e u) = (cls1 W x u).map e.toEmbedding := by
  ext w'
  rw [mem_map_equiv]
  simp only [cls1, mem_filter, mem_univ, true_and]
  rw [← skel1_map e hW x (e.symm w'), ← skel1_map e hW x u, Equiv.apply_symm_apply]

omit [Fintype V] [Fintype V'] [DecidableEq V] [DecidableEq V'] in
theorem isClique_map (e : V ≃ V') (hW : ∀ y, W' (⇑e ∘ y) = W y) (x : List V)
    (C : Finset V) :
    IsClique (skel2 W' (x.map e)) (C.map e.toEmbedding) ↔ IsClique (skel2 W x) C := by
  unfold IsClique
  simp only [forall_mem_map, Equiv.coe_toEmbedding, ne_eq, EmbeddingLike.apply_eq_iff_eq,
    skel2_map e hW]

theorem dlGood_map (e : V ≃ V') (hW : ∀ y, W' (⇑e ∘ y) = W y) (t₂ : ℕ) (x : List V) :
    DLGood W' t₂ (x.map e) ↔ DLGood W t₂ x := by
  unfold DLGood
  rw [List.length_map]
  refine or_congr ⟨fun h u => ?_, fun h u' => ?_⟩ (and_congr_right fun _ => ⟨?_, ?_⟩)
  · have := h (e u)
    rwa [cls1_map e hW, card_map] at this
  · obtain ⟨u, rfl⟩ := e.surjective u'
    rw [cls1_map e hW, card_map]
    exact h u
  · rintro ⟨u', hu', hc⟩
    obtain ⟨u, rfl⟩ := e.surjective u'
    rw [cls1_map e hW, card_map] at hu'
    rw [cls1_map e hW, isClique_map e hW] at hc
    exact ⟨u, hu', hc⟩
  · rintro ⟨u, hu, hc⟩
    refine ⟨e u, ?_, ?_⟩
    · rwa [cls1_map e hW, card_map]
    · rwa [cls1_map e hW, isClique_map e hW]

end Transport

theorem mem_tuples {β : Type*} [DecidableEq β] {S : Finset β} :
    ∀ {n : ℕ} {x : List β}, x ∈ tuples S n ↔ x.length = n ∧ ∀ a ∈ x, a ∈ S
  | 0, x => by cases x <;> simp [tuples]
  | n + 1, x => by
    cases x with
    | nil => simp [tuples]
    | cons a x =>
      simp only [tuples, mem_image, mem_product, Prod.exists, List.cons.injEq,
        List.length_cons, List.mem_cons, forall_eq_or_imp, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨b, y, ⟨hb, hy⟩, rfl, rfl⟩
        exact ⟨(mem_tuples.1 hy).1, hb, (mem_tuples.1 hy).2⟩
      · rintro ⟨hl, ha, hx⟩
        exact ⟨a, x, ⟨ha, mem_tuples.2 ⟨hl, hx⟩⟩, rfl, rfl⟩

theorem mem_tuplesLt {β : Type*} [DecidableEq β] {S : Finset β} {d : ℕ} {x : List β} :
    x ∈ tuplesLt S d ↔ x.length < d ∧ ∀ a ∈ x, a ∈ S := by
  simp only [tuplesLt, mem_biUnion, mem_range, mem_tuples]
  constructor
  · rintro ⟨n, hn, rfl, h⟩
    exact ⟨hn, h⟩
  · rintro ⟨hn, h⟩
    exact ⟨_, hn, rfl, h⟩

theorem smul_map_val (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) (x : List V₂) :
    σ • (show Choice α from x.map fun u => Sum.inr u.val) =
      (show Choice α from (x.map (eS σ V₂)).map fun u => Sum.inr u.val) := by
  show List.map _ (List.map _ x) = _
  rw [List.map_map, List.map_map]
  rfl

/-- The node set of the Design Lemma's choice, transported. -/
theorem nodeSet_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) {d : ℕ}
    (W : (Fin d → V₂) → ℕ) (W' : (Fin d → ↥(σ • V₂)) → ℕ)
    (hW : ∀ y, W' (⇑(eS σ V₂) ∘ y) = W y) (t₂ : ℕ) :
    ((tuplesLt univ d).filter (DLGood W' t₂)).image (β := Choice α)
        (fun x => x.map fun u => (Sum.inr u.val : α ⊕ Finset α)) =
      σ • ((tuplesLt univ d).filter (DLGood W t₂)).image (β := Choice α)
        (fun x => x.map fun u => (Sum.inr u.val : α ⊕ Finset α)) := by
  ext c
  constructor
  · intro hc
    obtain ⟨x', hx', rfl⟩ := mem_image.1 hc
    rw [mem_filter, mem_tuplesLt] at hx'
    obtain ⟨x, rfl⟩ : ∃ x, x' = x.map (eS σ V₂) :=
      ⟨x'.map (eS σ V₂).symm, by rw [List.map_map]; simp⟩
    rw [List.length_map, dlGood_map _ hW] at hx'
    have hmem : (show Choice α from x.map fun u => Sum.inr u.val) ∈
        ((tuplesLt univ d).filter (DLGood W t₂)).image (β := Choice α)
          (fun x => x.map fun u => (Sum.inr u.val : α ⊕ Finset α)) :=
      mem_image.2 ⟨x, mem_filter.2 ⟨mem_tuplesLt.2 ⟨hx'.1.1, fun _ _ => mem_univ _⟩, hx'.2⟩,
        rfl⟩
    have := smul_mem_smul_finset (a := σ) hmem
    rwa [smul_map_val] at this
  · intro hc
    obtain ⟨c₀, hc₀, rfl⟩ := mem_smul_finset.1 hc
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hc₀
    rw [mem_filter, mem_tuplesLt] at hx
    rw [smul_map_val]
    refine mem_image.2 ⟨x.map (eS σ V₂), mem_filter.2 ⟨mem_tuplesLt.2 ⟨?_, fun _ _ =>
      mem_univ _⟩, ?_⟩, rfl⟩
    · rw [List.length_map]
      exact hx.1.1
    · rw [dlGood_map _ hW]
      exact hx.2

theorem decodeV₂_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) (ch : Choice α) :
    decodeV₂ (σ • V₂) (σ • ch) = (decodeV₂ V₂ ch).map (eS σ V₂) := by
  unfold decodeV₂
  rw [choiceCells_smul, List.filterMap_map, List.map_filterMap]
  congr 1
  funext s
  by_cases hs : s ∈ V₂
  · have hs' : σ • s ∈ σ • V₂ := smul_mem_smul_finset hs
    simp only [Function.comp_apply, hs, hs', dite_true, Option.map_some]
    rfl
  · have hs' : σ • s ∉ σ • V₂ := fun h => hs ((smul_mem_smul_finset_iff σ).1 h)
    simp only [Function.comp_apply, hs, hs', dite_false, Option.map_none]

/-! ### Dropped pieces and guards -/

theorem addPiece_smul (σ : Equiv.Perm α) (D : Finset α) (p : CPart α) :
    σ • addPiece D p = addPiece (σ • D) (σ • p) := by
  show CPart.mk _ _ = CPart.mk _ _
  congr 1
  · funext x
    simp only [addPiece, mem_smul_iff]
    rfl
  · funext x
    simp only [addPiece, mem_smul_iff]
    split_ifs <;> rfl

theorem addPieceOut_smul (σ : Equiv.Perm α) (D : Finset α) (o : Option (Out α)) :
    σ • addPieceOut D o = addPieceOut (σ • D) (σ • o) := by
  rcases o with _ | p | J
  · rfl
  · show some (Sum.inl (σ • addPiece D p)) = _
    rw [addPiece_smul]
    rfl
  · rfl

theorem withPiece_act (σ : Equiv.Perm α) (D : Finset α) (T : STree α) :
    (withPiece D T).act σ = withPiece (σ • D) (T.act σ) := by
  unfold withPiece
  refine (act_bind' σ T fun o => ?_).symm
  show CTree.leaf _ = CTree.leaf _
  rw [addPieceOut_smul]

theorem shrink_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α))
    {rec rec' : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ a b c, rec' (σ • a) (σ • b) (relabA σ c) = (rec a b c).act σ)
    (a : Finset α) (b : Finset (Finset α)) (c : α → Finset α → Bool) :
    shrink (σ • V₂) rec' (σ • a) (σ • b) (relabA σ c) = (shrink V₂ rec a b c).act σ := by
  unfold shrink
  rw [card_smul_finset, card_smul_finset]
  split_ifs
  · exact hrec a b c
  · rfl

/-! ### The classical structure on `V₁' ⊔ V₂` -/

theorem disjSum_smul (σ : Equiv.Perm α) (V₁' : Finset α) (V₂ : Finset (Finset α)) :
    σ • V₁'.disjSum V₂ = (σ • V₁').disjSum (σ • V₂) := by
  ext q
  rw [mem_smul_iff]
  cases q with
  | inl a => rw [Sum.smul_inl, inl_mem_disjSum, inl_mem_disjSum, mem_smul_iff]
  | inr s => rw [Sum.smul_inr, inr_mem_disjSum, inr_mem_disjSum, mem_smul_iff]

theorem code_smul (σ : Equiv.Perm α) (A : α → Finset α → Bool)
    {Y Y' : Finset α → Finset α → ℕ} (hY : ∀ s s', Y' (σ • s) (σ • s') = Y s s')
    (a b : α ⊕ Finset α) : code (relabA σ A) Y' (σ • a) (σ • b) = code A Y a b := by
  cases a <;> cases b <;> simp only [Sum.smul_inl, Sum.smul_inr, code, relabA_smul, hY]

theorem extCells_smul (σ : Equiv.Perm α) (V₂ : Finset (Finset α)) {Y : V₂ → V₂ → ℕ}
    {Y' : ↥(σ • V₂) → ↥(σ • V₂) → ℕ} (hY : ∀ u v, Y' (eS σ V₂ u) (eS σ V₂ v) = Y u v)
    (s s' : Finset α) : extCells (σ • V₂) Y' (σ • s) (σ • s') = extCells V₂ Y s s' := by
  unfold extCells
  by_cases h : s ∈ V₂ ∧ s' ∈ V₂
  · have h' : σ • s ∈ σ • V₂ ∧ σ • s' ∈ σ • V₂ :=
      ⟨smul_mem_smul_finset h.1, smul_mem_smul_finset h.2⟩
    rw [dite_eq_left h', dite_eq_left h]
    exact hY ⟨s, h.1⟩ ⟨s', h.2⟩
  · have h' : ¬ (σ • s ∈ σ • V₂ ∧ σ • s' ∈ σ • V₂) := by
      rwa [smul_mem_smul_finset_iff, smul_mem_smul_finset_iff]
    rw [dite_eq_right h', dite_eq_right h]

theorem cohOn_smul (σ : Equiv.Perm α) (SQ : Finset (α ⊕ Finset α))
    {c₀ c₀' : α ⊕ Finset α → α ⊕ Finset α → ℕ} (hc : ∀ a b, c₀' (σ • a) (σ • b) = c₀ a b)
    (a b : α ⊕ Finset α) : cohOn (σ • SQ) c₀' (σ • a) (σ • b) = cohOn SQ c₀ a b := by
  unfold cohOn
  by_cases h : a ∈ SQ ∧ b ∈ SQ
  · have h' : σ • a ∈ σ • SQ ∧ σ • b ∈ σ • SQ :=
      ⟨smul_mem_smul_finset h.1, smul_mem_smul_finset h.2⟩
    rw [dite_eq_left h', dite_eq_left h]
    have hn := wlOn_natural (k := 2) (eS σ SQ)
      (fun p : Fin 2 → ↥(σ • SQ) => c₀' (p 0).val (p 1).val)
    have hfun : (fun x : Fin 2 → SQ =>
        (fun p : Fin 2 → ↥(σ • SQ) => c₀' (p 0).val (p 1).val) (⇑(eS σ SQ) ∘ x)) =
        fun p : Fin 2 → SQ => c₀ (p 0).val (p 1).val := by
      funext x
      exact hc _ _
    rw [hfun] at hn
    rw [hn]
    congr 1
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  · have h' : ¬ (σ • a ∈ σ • SQ ∧ σ • b ∈ σ • SQ) := by
      rwa [smul_mem_smul_finset_iff, smul_mem_smul_finset_iff]
    rw [dite_eq_right h', dite_eq_right h]

theorem toLeft_smul (σ : Equiv.Perm α) (B : Finset (α ⊕ Finset α)) :
    (σ • B).toLeft = σ • B.toLeft := by
  ext a
  rw [mem_toLeft, mem_smul_iff, mem_smul_iff, mem_toLeft, Sum.smul_inl]

theorem cellOf_smul (σ : Equiv.Perm α) (B : Finset (α ⊕ Finset α)) :
    cellOf (σ • B) = σ • cellOf B := by
  ext a
  simp only [cellOf, mem_sup, mem_toRight, id, mem_smul_iff]
  constructor
  · rintro ⟨s, hs, ha⟩
    rw [Sum.smul_inr] at hs
    exact ⟨σ⁻¹ • s, hs, smul_mem_smul_finset ha⟩
  · rintro ⟨s, hs, ha⟩
    refine ⟨σ • s, ?_, ?_⟩
    · rw [Sum.smul_inr, inv_smul_smul]
      exact hs
    · rw [mem_smul_iff]
      exact ha


/-! ### The permutation of `α ⊕ Finset α` induced by `σ` -/

/-- The permutation of `α ⊕ Finset α` given by the action of `σ`. -/
def τ (σ : Equiv.Perm α) : Equiv.Perm (α ⊕ Finset α) := MulAction.toPerm σ

theorem τ_smul (σ : Equiv.Perm α) (q : α ⊕ Finset α) : τ σ • q = σ • q := rfl

theorem τ_inv_smul (σ : Equiv.Perm α) (q : α ⊕ Finset α) : (τ σ)⁻¹ • q = σ⁻¹ • q := rfl

theorem τ_smul_finset (σ : Equiv.Perm α) (S : Finset (α ⊕ Finset α)) : τ σ • S = σ • S := rfl

theorem τ_inv_smul_finset (σ : Equiv.Perm α) (S : Finset (α ⊕ Finset α)) :
    (τ σ)⁻¹ • S = σ⁻¹ • S := rfl

theorem τ_smul_finset₂ (σ : Equiv.Perm α) (W : Finset (Finset (α ⊕ Finset α))) :
    τ σ • W = σ • W := rfl

theorem image_cellOf_smul (σ : Equiv.Perm α) (W : Finset (Finset (α ⊕ Finset α))) :
    (σ • W).image cellOf = σ • W.image cellOf := by
  rw [smul_finset_def, smul_finset_def, image_image, image_image]
  exact image_congr fun B _ => cellOf_smul σ B

/-- **`cohCont` is canonical.** -/
theorem cohCont_smul (σ : Equiv.Perm α) (t : ℕ) (V₁ V₁' C₁ : Finset α)
    {rc rc' : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrc : ∀ a b c, rc' (σ • a) (σ • b) (relabA σ c) = (rc a b c).act σ)
    (o : Option (CohOut (α ⊕ Finset α))) :
    cohCont t (σ • V₁) (σ • V₁') (σ • C₁) rc' (τ σ • o) =
      (cohCont t V₁ V₁' C₁ rc o).act σ := by
  rcases o with _ | p | ⟨W₁, W₂, A'⟩
  · rfl
  · have hP : (⟨fun x => (τ σ • p).col (.inl x), fun x => ((τ σ • p).blk (.inl x)).toLeft⟩ :
        CPart α) = σ • (⟨fun x => p.col (.inl x), fun x => (p.blk (.inl x)).toLeft⟩ : CPart α) := by
      show CPart.mk _ _ = CPart.mk _ _
      congr 1
      funext x
      show ((τ σ • p.blk ((τ σ)⁻¹ • Sum.inl x))).toLeft = σ • (p.blk (Sum.inl (σ⁻¹ • x))).toLeft
      rw [τ_smul_finset, toLeft_smul]
      rfl
    show CTree.leaf (some (Sum.inl (addPiece (σ • V₁ \ σ • V₁') (addPiece (σ • V₁' \ σ • C₁)
      ⟨fun x => (τ σ • p).col (.inl x), fun x => ((τ σ • p).blk (.inl x)).toLeft⟩)))) =
      CTree.leaf (σ • some (Sum.inl (addPiece (V₁ \ V₁') (addPiece (V₁' \ C₁)
      ⟨fun x => p.col (.inl x), fun x => (p.blk (.inl x)).toLeft⟩))))
    rw [hP, ← smul_finset_sdiff, ← smul_finset_sdiff, ← addPiece_smul, ← addPiece_smul]
    rfl
  · have hW : (τ σ • W₁).toLeft = σ • W₁.toLeft := by
      rw [τ_smul_finset, toLeft_smul]
    have hA : (fun x s => decide (∃ B ∈ τ σ • W₂, cellOf B = s ∧
        (fun x B => A' ((τ σ)⁻¹ • x) ((τ σ)⁻¹ • B)) (Sum.inl x) B = true)) =
        relabA σ fun x s => decide (∃ B ∈ W₂, cellOf B = s ∧ A' (Sum.inl x) B = true) := by
      funext x s
      simp only [relabA, τ_smul_finset₂, τ_inv_smul, τ_inv_smul_finset, Sum.smul_inl]
      congr 1
      apply propext
      constructor
      · rintro ⟨B, hB, hc, hA⟩
        obtain ⟨B₀, hB₀, rfl⟩ := mem_smul_finset.1 hB
        rw [inv_smul_smul] at hA
        exact ⟨B₀, hB₀, by rw [← hc, cellOf_smul, inv_smul_smul], hA⟩
      · rintro ⟨B₀, hB₀, hc, hA⟩
        refine ⟨σ • B₀, smul_mem_smul_finset hB₀, ?_, by rwa [inv_smul_smul]⟩
        rw [cellOf_smul, hc, smul_inv_smul]
    show cohCont t (σ • V₁) (σ • V₁') (σ • C₁) rc'
        (some (CohOut.bip (τ σ • W₁) (τ σ • W₂) fun x B => A' ((τ σ)⁻¹ • x) ((τ σ)⁻¹ • B))) =
      (cohCont t V₁ V₁' C₁ rc (some (CohOut.bip W₁ W₂ A'))).act σ
    simp only [cohCont]
    rw [hW, card_smul_finset]
    by_cases hc : W₁.toLeft.card ≤ t
    · rw [ite_eq_left hc, ite_eq_left hc]
      have hcp : colPart (σ • W₁.toLeft) (fun _ => 0) = σ • colPart W₁.toLeft fun _ => 0 :=
        colPart_smul σ _ fun _ => rfl
      rw [hcp, ← smul_finset_sdiff, ← smul_finset_sdiff, ← smul_finset_sdiff, ← addPiece_smul,
        ← addPiece_smul, ← addPiece_smul]
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc, withPiece_act, withPiece_act, withPiece_act,
        ← hrc, hA, τ_smul_finset₂, image_cellOf_smul, smul_finset_sdiff, smul_finset_sdiff,
        smul_finset_sdiff]

end GraphIso.SplitJohnson.BipRelabel
