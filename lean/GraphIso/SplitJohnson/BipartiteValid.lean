module

public import GraphIso.SplitJohnson.BipartiteDary
public import GraphIso.SplitJohnson.BipartiteDL

/-!
# Bipartite Split-or-Johnson: validity

`bsoj_valid`: under the invariant `BInv`, `bsoj t V₁ V₂ A` is live and every reachable leaf is a
colored `t`-partition of `V₁` or a Johnson embedding in `V₁` on more than `t` points. The proof
is by strong induction on `|V₂|`, through the branches of `bstep` (`bstep_valid`):
* the base case: a colouring by neighbourhoods along an enumeration of `V₂` has the twin
  classes as colour classes (`base_valid`);
* no large class without twins: `twinPart` is valid (`twinPart_valid`);
* the Johnson case (`johnson_valid`);
* a large twin class on `V₂`: Exercise 5.5 (`twin_split`) gives the invariant for the side that
  `pickSide` keeps, which has fewer cells (`bigTwins_card_lt`);
* the Design Lemma's choice (`exists_dlGood`, `dlCont_valid`).
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset Pointwise GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

/-! ### The base case -/

/-- Binary numbers are injective on `0/1` digit lists of one length. -/
theorem ofDigits_two_inj : ∀ {L₁ L₂ : List ℕ}, L₁.length = L₂.length → (∀ a ∈ L₁, a < 2) →
    (∀ a ∈ L₂, a < 2) → Nat.ofDigits 2 L₁ = Nat.ofDigits 2 L₂ → L₁ = L₂
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | a :: L₁, b :: L₂, hl, h₁, h₂, he => by
    simp only [Nat.ofDigits_cons] at he
    have ha := h₁ a (by simp)
    have hb := h₂ b (by simp)
    have hab : a = b := by omega
    subst hab
    have he' : Nat.ofDigits 2 L₁ = Nat.ofDigits 2 L₂ := by omega
    rw [ofDigits_two_inj (by simpa using hl) (fun x hx => h₁ x (by simp [hx]))
      (fun x hx => h₂ x (by simp [hx])) he']

omit [DecidableEq α] in
theorem choiceCells_map_inr (l : List (Finset α)) :
    choiceCells (l.map Sum.inr : List (α ⊕ Finset α)) = l := by
  unfold choiceCells
  induction l with
  | nil => rfl
  | cons a l ih => simpa using ih

theorem mem_enums {V₂ : Finset (Finset α)} {e : Choice α} :
    e ∈ enums V₂ ↔ ∃ l : List (Finset α), V₂.val = ↑l ∧ l.map Sum.inr = e := by
  unfold enums
  constructor
  · intro he
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 he
    exact ⟨l, (Multiset.mem_lists_iff _ _).1 (Multiset.mem_toFinset.1 hl), rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact Finset.mem_image.2 ⟨l, Multiset.mem_toFinset.2 ((Multiset.mem_lists_iff _ _).2 hl), rfl⟩

theorem enums_nonempty (V₂ : Finset (Finset α)) : (enums V₂).Nonempty := by
  obtain ⟨l, hl⟩ := Quot.exists_rep V₂.val
  exact ⟨_, mem_enums.2 ⟨l, hl.symm, rfl⟩⟩

omit [DecidableEq α] in
/-- Equal neighbourhood codes along an enumeration of `V₂` mean equal neighbourhoods. -/
theorem nbrCode_eq {V₂ : Finset (Finset α)} {A : α → Finset α → Bool} {l : List (Finset α)}
    (hl : V₂.val = ↑l) {x y : α} (h : nbrCode A l x = nbrCode A l y) :
    ∀ s ∈ V₂, A x s = A y s := by
  have hd := ofDigits_two_inj (by simp) (fun a ha => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
      split <;> omega) (fun a ha => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
      split <;> omega) h
  intro s hs
  have hsl : s ∈ l := by
    rw [← Finset.mem_val, hl] at hs
    exact hs
  have := (List.map_inj_left.1 hd) s hsl
  by_cases hx : A x s <;> by_cases hy : A y s <;> simp_all

/-- **The base case**: colouring by neighbourhoods along an enumeration. -/
theorem base_valid {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) {e : Choice α} (he : e ∈ enums V₂) :
    IsColPart V₁ t (colPart V₁ (nbrCode A (choiceCells e))) := by
  obtain ⟨l, hl, rfl⟩ := mem_enums.1 he
  rw [choiceCells_map_inr]
  refine colPart_valid fun x hx => (card_le_card fun y hy => ?_).trans (h.twin_le x hx)
  rw [mem_filter] at hy
  exact mem_twinCls.2 ⟨hy.1, nbrCode_eq hl hy.2.symm⟩

/-! ### Twins and degrees -/

omit [DecidableEq α] in
theorem tw_eq_of_mem {V₁ : Finset α} {V₂ : Finset (Finset α)} {A : α → Finset α → Bool}
    {x y : α} (hy : y ∈ twinCls V₁ V₂ A x) : tw V₁ V₂ A y = tw V₁ V₂ A x := by
  unfold tw
  rw [twinCls_eq_of_mem hy]

omit [DecidableEq α] in
theorem deg_eq_of_mem {V₁ : Finset α} {V₂ : Finset (Finset α)} {A : α → Finset α → Bool}
    {x y : α} (hy : y ∈ twinCls V₁ V₂ A x) : deg V₂ A y = deg V₂ A x := by
  unfold deg
  congr 1
  exact filter_congr fun s hs => by rw [(mem_twinCls.1 hy).2 s hs]

omit [DecidableEq α] in
/-- **No large class without twins**: `twinPart` is valid. -/
theorem twinPart_valid {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hb : ¬ (bigDegs t V₁ V₂ A).Nonempty) :
    IsColPart V₁ t (twinPart V₁ V₂ A) := by
  have hcol : ∀ v w, (twinPart V₁ V₂ A).col v = (twinPart V₁ V₂ A).col w →
      tw V₁ V₂ A v = tw V₁ V₂ A w ∧ deg V₂ A v = deg V₂ A w := fun v w e =>
    Nat.pair_eq_pair.1 e
  have hblk : ∀ v ∈ V₁, ∀ w ∈ (twinPart V₁ V₂ A).blk v,
      tw V₁ V₂ A w = tw V₁ V₂ A v ∧ deg V₂ A w = deg V₂ A v := by
    intro v hv w hw
    simp only [twinPart] at hw
    split_ifs at hw with h1
    · simp only [tfDeg, mem_filter] at hw
      exact ⟨hw.2.1.trans h1.symm, hw.2.2⟩
    · exact ⟨tw_eq_of_mem hw, deg_eq_of_mem hw⟩
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv w hw => ?_, fun v hv w hw => ?_,
    fun v hv w hw hvw => ?_, fun v hv h1 w hw hwv => ?_, fun v hv => ?_⟩
  · simp only [twinPart]
    split_ifs with h1
    · exact mem_filter.2 ⟨hv, h1, rfl⟩
    · exact self_mem_twinCls hv
  · simp only [twinPart]
    split_ifs
    · exact filter_subset _ _
    · exact filter_subset _ _
  · obtain ⟨e1, e2⟩ := hblk v hv w hw
    simp only [twinPart] at hw ⊢
    rw [e1, e2]
    split_ifs at hw ⊢ with h1
    · rfl
    · exact twinCls_eq_of_mem hw
  · obtain ⟨e1, e2⟩ := hblk v hv w hw
    show Nat.pair _ _ = Nat.pair _ _
    rw [e1, e2]
  · obtain ⟨e1, e2⟩ := hcol v w hvw
    simp only [twinPart]
    rw [← e1, ← e2]
    split_ifs
    · rfl
    · exact e1
  · obtain ⟨e1, e2⟩ := hcol w v hwv
    simp only [twinPart] at h1
    split_ifs at h1 with htv
    · have hwm : w ∈ tfDeg V₁ V₂ A (deg V₂ A v) := mem_filter.2 ⟨hw, e1.trans htv, e2⟩
      have hvm : v ∈ tfDeg V₁ V₂ A (deg V₂ A v) := mem_filter.2 ⟨hv, htv, rfl⟩
      exact card_le_one.1 h1.le w hwm v hvm
    · exact absurd h1 htv
  · simp only [twinPart]
    split_ifs with h1
    · by_contra hlt
      exact hb ⟨deg V₂ A v, mem_filter.2 ⟨mem_image_of_mem _ hv, by omega⟩⟩
    · exact h.twin_le v hv

omit [DecidableEq α] in
/-- The points without twins of one degree have no twins among themselves. -/
theorem twinCls_tfDeg {V₁ : Finset α} {V₂ : Finset (Finset α)} {A : α → Finset α → Bool}
    {d : ℕ} {x : α} (hx : x ∈ tfDeg V₁ V₂ A d) : twinCls (tfDeg V₁ V₂ A d) V₂ A x = {x} := by
  have hx' := mem_filter.1 hx
  obtain ⟨a, ha⟩ := card_eq_one.1 (show (twinCls V₁ V₂ A x).card = 1 from hx'.2.1)
  have hxa : x ∈ twinCls V₁ V₂ A x := self_mem_twinCls hx'.1
  rw [ha, mem_singleton] at hxa
  refine Finset.Subset.antisymm (fun y hy => ?_) (singleton_subset_iff.2 (self_mem_twinCls hx))
  have hy' := mem_twinCls.1 hy
  have hy₁ : y ∈ twinCls V₁ V₂ A x := mem_twinCls.2 ⟨(mem_filter.1 hy'.1).1, hy'.2⟩
  rw [ha, mem_singleton] at hy₁
  rw [mem_singleton, hy₁, hxa]

/-! ### The large twin class on `V₂` -/

theorem bigTwins_subset (V₂ : Finset (Finset α)) {d : ℕ} (c : (Fin d → V₂) → ℕ) :
    bigTwins V₂ c ⊆ V₂ := by
  intro s hs
  obtain ⟨u, -, rfl⟩ := mem_map.1 hs
  exact u.2

theorem pickSide_sub_V₂ {V₁ : Finset α} {V₂ S : Finset (Finset α)} {A : α → Finset α → Bool}
    (hS : S ⊆ V₂) : pickSide V₁ V₂ S A ⊆ V₂ := by
  unfold pickSide
  split_ifs
  · exact hS
  · exact sdiff_subset

theorem pickSide_card_lt {V₁ : Finset α} {V₂ S : Finset (Finset α)}
    {A : α → Finset α → Bool} (hS : S ⊆ V₂) (hlt : S.card < V₂.card) (hne : S.Nonempty) :
    (pickSide V₁ V₂ S A).card < V₂.card := by
  unfold pickSide
  split_ifs
  · exact hlt
  · rw [card_sdiff_of_subset hS]
    have := hne.card_pos
    omega

/-- **Exercise 5.5 for the kept side.** -/
theorem pickSide_twin_lt {V₁' : Finset α} {V₂ S : Finset (Finset α)} {A : α → Finset α → Bool}
    (hS : S ⊆ V₂) (htf : ∀ x ∈ V₁', twinCls V₁' V₂ A x = {x}) :
    ∀ x ∈ V₁', 2 * (twinCls V₁' (pickSide V₁' V₂ S A) A x).card < V₁'.card + 2 := by
  have htf' : ∀ x ∈ V₁', twinCls V₁' (S ∪ (V₂ \ S)) A x = {x} := by
    rw [union_sdiff_of_subset hS]
    exact htf
  unfold pickSide
  split_ifs with h1
  · exact h1
  · exact (twin_split htf').resolve_left h1

/-! ### The Design Lemma's choice -/

omit [DecidableEq α] in
theorem six_le_of_not_base {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) (hb : ¬ IsBase t V₂.card) :
    6 ≤ V₂.card := by
  unfold IsBase at hb
  have ht : 1 ≤ t := by
    have := h.v₁_le
    have := h.t_lt
    omega
  have hc : 0 < Nat.clog 2 (2 * t) := Nat.clog_pos (by norm_num) (by omega)
  rcases Nat.lt_or_ge V₂.card 6 with hlt | hge
  · exfalso
    apply hb
    have h25 : V₂.card ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h1 : 1 ≤ Nat.clog 2 (2 * t) ^ 3 := Nat.one_le_pow _ _ hc
    omega
  · exact hge

theorem decodeV₂_map (V₂ : Finset (Finset α)) (x : List V₂) :
    decodeV₂ V₂ (x.map fun u => (Sum.inr u.val : α ⊕ Finset α)) = x := by
  unfold decodeV₂
  rw [show (x.map fun u => (Sum.inr u.val : α ⊕ Finset α)) = (x.map Subtype.val).map Sum.inr by
    simp, choiceCells_map_inr]
  induction x with
  | nil => rfl
  | cons u x ih => simpa [u.2] using ih

/-! ### One level and the recursion -/

/-- **One level is valid**, given valid recursive calls on fewer cells. -/
theorem bstep_valid {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hrec : ∀ V₁'' V₂'' A'', V₂''.card < V₂.card → BInv t V₁'' V₂'' A'' →
      (rec V₁'' V₂'' A'').Live ∧ (rec V₁'' V₂'' A'').AllLeaves (ValidOut V₁'' t)) :
    (bstep t V₁ V₂ A rec).Live ∧ (bstep t V₁ V₂ A rec).AllLeaves (ValidOut V₁ t) := by
  unfold bstep
  by_cases hd : (bigDegs t V₁ V₂ A).Nonempty
  swap
  · rw [dite_eq_right hd]
    exact ⟨trivial, twinPart_valid h hd⟩
  rw [dite_eq_left hd]
  dsimp only
  have hd₁ := min'_mem _ hd
  generalize (bigDegs t V₁ V₂ A).min' hd = d₁ at hd₁ ⊢
  have hV₁' : tfDeg V₁ V₂ A d₁ ⊆ V₁ := filter_subset _ _
  have htV₁' : t < (tfDeg V₁ V₂ A d₁).card := (mem_filter.1 hd₁).2
  have htf : ∀ x ∈ tfDeg V₁ V₂ A d₁, twinCls (tfDeg V₁ V₂ A d₁) V₂ A x = {x} :=
    fun x hx => twinCls_tfDeg hx
  have hDt : (V₁ \ tfDeg V₁ V₂ A d₁).card ≤ t := by
    rw [card_sdiff_of_subset hV₁']
    have := h.v₁_le
    omega
  have hunion : V₁ \ tfDeg V₁ V₂ A d₁ ∪ tfDeg V₁ V₂ A d₁ = V₁ := sdiff_union_of_subset hV₁'
  have hdisj : Disjoint (V₁ \ tfDeg V₁ V₂ A d₁) (tfDeg V₁ V₂ A d₁) := sdiff_disjoint
  by_cases hJ : (tfDeg V₁ V₂ A d₁).card = V₂.card.choose (sOf V₂.card d₁)
  · rw [ite_eq_left hJ]
    exact ⟨trivial, johnson_valid h hd₁ hJ⟩
  rw [ite_eq_right hJ]
  by_cases hb : IsBase t V₂.card
  · rw [ite_eq_left hb]
    exact ⟨⟨enums_nonempty V₂, fun _ _ => trivial⟩, fun e he => base_valid h he⟩
  rw [ite_eq_right hb]
  set cd := daryCol V₂ ((tfDeg V₁ V₂ A d₁).image (fOf V₂ A d₁))
    (arity V₂.card (sOf V₂.card d₁) (tfDeg V₁ V₂ A d₁).card) with hcd
  have hSsub := bigTwins_subset V₂ cd
  by_cases hS : (bigTwins V₂ cd).Nonempty
  · rw [ite_eq_left hS]
    have hsub : pickSide (tfDeg V₁ V₂ A d₁) V₂ (bigTwins V₂ cd) A ⊆ V₂ := pickSide_sub_V₂ hSsub
    have hlt := pickSide_card_lt (V₁ := tfDeg V₁ V₂ A d₁) (A := A) hSsub
      (bigTwins_card_lt h hb hd₁ hJ) hS
    have hcV₁' := card_le_card hV₁'
    have hv₁ := h.v₁_le
    have hI : BInv t (tfDeg V₁ V₂ A d₁) (pickSide (tfDeg V₁ V₂ A d₁) V₂ (bigTwins V₂ cd) A) A :=
      ⟨fun s hs => h.cells_ne s (hsub hs),
        fun s hs s' hs' => h.cells_disj s (hsub hs) s' (hsub hs'),
        (card_le_card hsub).trans h.v_le, by omega, htV₁', fun x hx => by
          have := pickSide_twin_lt (A := A) hSsub htf x hx
          omega⟩
    have := withPiece_valid (hrec _ _ _ hlt hI) hdisj hDt
    rwa [hunion] at this
  · rw [ite_eq_right hS]
    have hS0 : bigTwins V₂ cd = ∅ := not_nonempty_iff_eq_empty.1 hS
    have hv6 : 6 ≤ V₂.card := six_le_of_not_base h hb
    have hd2 := two_le_arity h hb hd₁
    obtain ⟨x₀, hx₀, hg₀⟩ := exists_dlGood hd2 (by omega) cd hS0
    refine ⟨⟨⟨_, mem_image_of_mem _ (mem_filter.2 ⟨hx₀, hg₀⟩)⟩, fun ch hch => ?_⟩,
      fun ch hch => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hch
      dsimp only
      rw [decodeV₂_map]
      exact (dlCont_valid h hV₁' htV₁' htf hv6 cd (mem_filter.1 hx).2 hrec).1
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hch
      dsimp only
      rw [decodeV₂_map]
      exact (dlCont_valid h hV₁' htV₁' htf hv6 cd (mem_filter.1 hx).2 hrec).2

/-- **Bipartite Split-or-Johnson is valid.** -/
theorem bsoj_valid {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (h : BInv t V₁ V₂ A) :
    (bsoj t V₁ V₂ A).Live ∧ (bsoj t V₁ V₂ A).AllLeaves (ValidOut V₁ t) := by
  induction hn : V₂.card using Nat.strong_induction_on generalizing V₁ V₂ A with
  | _ n ih =>
    rw [bsoj]
    refine bstep_valid h fun V₁'' V₂'' A'' hlt hI => ?_
    rw [dite_eq_left hlt]
    exact ih _ (hn ▸ hlt) hI rfl

end GraphIso.SplitJohnson
