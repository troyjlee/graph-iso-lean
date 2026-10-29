module

public import GraphIso.SplitJohnson.BipartiteBasic

/-!
# Bipartite Split-or-Johnson: the multiplicative cost

`bsoj_count_le`: if `|V₂| ≤ t` and `|V₁| ≤ 2t`, the choice tree has at most
`2^{128 (⌈log₂ t⌉ + 2)²}` paths. No validity hypotheses are needed: the `shrink` guard makes
every recursive call after a choice have at most two thirds of the cells.

* `BCount.cntF t v = M^{lvl v} · vb^vb` bounds the count for `|V₂| = v`
  (`BCount.count_bsoj_le_cntF`, strong induction on `v` through `BCount.count_bstep_le`):
  * `M = 64 (t + 1)^13` is the cost of a level that makes choices: the Design Lemma's lists
    (`|tuplesLt| ≤ v^d ≤ 64 t^12`, `BCount.pow_arity_le`, since `v^j < v n₁` for
    `j = ⌈log_v n₁⌉`) times one point of Coherent Split-or-Johnson (`BCount.count_cohSoj_le`);
  * `lvl v` counts the shrinkings to two thirds (`BCount.lvl`);
  * `vb = ⌊√(27 L³)⌋`, `L = ⌈log₂ 2t⌉`, bounds the base case, whose `|enums V₂| ≤ v^v`.
* The closed form (`BCount.cntF_le`): `lvl t ≤ 2 ⌈log₂ t⌉ + 1`, `M ≤ 2^{13L + 19}` and
  `vb^vb ≤ 2^{94 (L + 1)²}` (`BCount.pow_self_le`).
-/

@[expose] public section

namespace GraphIso.SplitJohnson

open Finset GraphIso.Coherent

variable {α : Type*} [DecidableEq α]

namespace BCount

/-! ### Arithmetic -/

/-- The number of levels that shrink by two thirds before reaching one cell. -/
def lvl (v : ℕ) : ℕ := if v ≤ 1 then 0 else lvl (2 * v / 3) + 1
termination_by v
decreasing_by omega

theorem lvl_of_le_one {v : ℕ} (h : v ≤ 1) : lvl v = 0 := by
  rw [lvl]
  simp only [h, ↓reduceIte]

theorem lvl_of_two_le {v : ℕ} (h : 2 ≤ v) : lvl v = lvl (2 * v / 3) + 1 := by
  rw [lvl]
  simp only [show ¬ v ≤ 1 by omega, ↓reduceIte]

/-- `lvl` is monotone. -/
theorem lvl_mono : ∀ {a b : ℕ}, a ≤ b → lvl a ≤ lvl b := by
  intro a b
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    intro hab
    by_cases ha : a ≤ 1
    · rw [lvl_of_le_one ha]
      exact Nat.zero_le _
    · rw [lvl_of_two_le (by omega : 2 ≤ a), lvl_of_two_le (by omega : 2 ≤ b)]
      exact Nat.succ_le_succ (ih _ (by omega) (by omega))

/-- Two shrinkings at least halve. -/
theorem lvl_le_half_add_two (v : ℕ) : lvl v ≤ lvl (v / 2) + 2 := by
  by_cases hv : v ≤ 1
  · rw [lvl_of_le_one hv]
    exact Nat.zero_le _
  rw [lvl_of_two_le (by omega : 2 ≤ v)]
  by_cases hx : 2 * v / 3 ≤ 1
  · rw [lvl_of_le_one hx]
    omega
  rw [lvl_of_two_le (by omega : 2 ≤ 2 * v / 3)]
  have := lvl_mono (show 2 * (2 * v / 3) / 3 ≤ v / 2 by omega)
  omega

/-- `lvl v ≤ 2k + 1` for `v ≤ 2^k`. -/
theorem lvl_le_of_le_pow : ∀ k v : ℕ, v ≤ 2 ^ k → lvl v ≤ 2 * k + 1 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    rw [lvl_of_le_one (by simpa using hv)]
    omega
  | succ k ih =>
    intro v hv
    have h := ih (v / 2) (by rw [pow_succ] at hv; omega)
    have := lvl_le_half_add_two v
    omega

/-- `Σ_{ℓ < d} v^ℓ ≤ v^d` for `v ≥ 2`. -/
theorem sum_range_pow_le {v : ℕ} (hv : 2 ≤ v) (d : ℕ) : ∑ l ∈ range d, v ^ l ≤ v ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, pow_succ]
    nlinarith [pow_pos (show 0 < v by omega) d]

/-- The base cost: `x^x ≤ 2^{94 K²}` when `x² ≤ 27 K³` and `K ≥ 1`. -/
theorem pow_self_le {x K : ℕ} (hK : 1 ≤ K) (hx : x ^ 2 ≤ 27 * K ^ 3) :
    x ^ x ≤ 2 ^ (94 * K ^ 2) := by
  set r := Nat.sqrt K with hr
  have hr2 : r ^ 2 ≤ K := Nat.sqrt_le' K
  have hKq : K < (r + 1) ^ 2 := Nat.lt_succ_sqrt' K
  have hr1 : 1 ≤ r := Nat.sqrt_pos.2 hK
  set q := r + 1 with hq
  have hq2 : q ^ 2 ≤ 4 * K := by nlinarith
  have hqK : q ≤ 2 * K := by nlinarith
  -- `x < 8 q³ < 2^(3q + 3)`
  have hK3 : K ^ 3 ≤ K ^ 2 * q ^ 2 := by
    rw [show K ^ 3 = K ^ 2 * K by ring]
    exact Nat.mul_le_mul_left _ hKq.le
  have h8 : x < 8 * q ^ 3 := by
    have : x ^ 2 < (8 * q ^ 3) ^ 2 := by
      have hKq' : K ^ 3 < (q ^ 2) ^ 3 := Nat.pow_lt_pow_left hKq (by norm_num)
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) this
  have hpow : x ≤ 2 ^ (3 * q + 3) := by
    have hq' : q < 2 ^ q := q.lt_two_pow_self
    have : q ^ 3 < (2 ^ q) ^ 3 := Nat.pow_lt_pow_left hq' (by norm_num)
    have e : 2 ^ (3 * q + 3) = 8 * (2 ^ q) ^ 3 := by ring
    omega
  -- `5x ≤ 26 K q`
  have h5 : 5 * x ≤ 26 * K * q := by
    have : (5 * x) ^ 2 ≤ (26 * K * q) ^ 2 := by nlinarith
    exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
  have hexp : (3 * q + 3) * x ≤ 94 * K ^ 2 := by nlinarith
  calc x ^ x ≤ (2 ^ (3 * q + 3)) ^ x := Nat.pow_le_pow_left hpow x
    _ = 2 ^ ((3 * q + 3) * x) := by rw [← pow_mul]
    _ ≤ 2 ^ (94 * K ^ 2) := Nat.pow_le_pow_right (by norm_num) hexp


/-! ### Trees -/


/-- A node whose children have at most `B` paths has at most `|S| B`. -/
theorem count_node_le {C O : Type*} (S : Finset C) (k : C → CTree C O) {B : ℕ}
    (h : ∀ c ∈ S, (k c).count ≤ B) : (CTree.node S k).count ≤ S.card * B := by
  show ∑ c ∈ S, (k c).count ≤ S.card * B
  calc ∑ c ∈ S, (k c).count ≤ ∑ _c ∈ S, B := sum_le_sum h
    _ = S.card * B := by rw [sum_const, smul_eq_mul]

/-- Dropped pieces do not add paths. -/
theorem count_withPiece_le (D : Finset α) (T : STree α) : (withPiece D T).count ≤ T.count := by
  have := CTree.count_bind_le (t := T) (f := fun o => (.leaf (addPieceOut D o) : STree α))
    (B := 1) ((CTree.allLeaves_iff_reach).2 fun _ _ => le_refl 1)
  simpa [withPiece] using this

/-- The lists of length `n` over `S`. -/
theorem mem_tuples {β : Type*} [DecidableEq β] {S : Finset β} :
    ∀ {n : ℕ} {l : List β}, l ∈ tuples S n ↔ l.length = n ∧ ∀ a ∈ l, a ∈ S
  | 0, l => by cases l <;> simp [tuples]
  | n + 1, [] => by simp [tuples]
  | n + 1, a :: l => by
    simp only [tuples, mem_image, mem_product, Prod.exists, List.cons.injEq,
      List.length_cons, Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨b, l', ⟨hb, hl'⟩, rfl, rfl⟩
      exact ⟨(mem_tuples.1 hl').1, hb, (mem_tuples.1 hl').2⟩
    · rintro ⟨hl, ha, hl'⟩
      exact ⟨a, l, ⟨ha, mem_tuples.2 ⟨hl, hl'⟩⟩, rfl, rfl⟩

/-- There are at most `|S|^n` lists of length `n` over `S`. -/
theorem card_tuples_le {β : Type*} [DecidableEq β] (S : Finset β) :
    ∀ n, (tuples S n).card ≤ S.card ^ n
  | 0 => by simp [tuples]
  | n + 1 => by
    rw [tuples, pow_succ']
    refine card_image_le.trans ?_
    rw [card_product]
    exact Nat.mul_le_mul_left _ (card_tuples_le S n)

/-- There are at most `|S|^d` lists of length less than `d`, for `|S| ≥ 2`. -/
theorem card_tuplesLt_le {β : Type*} [DecidableEq β] (S : Finset β) (hS : 2 ≤ S.card)
    (d : ℕ) : (tuplesLt S d).card ≤ S.card ^ d :=
  card_biUnion_le.trans ((sum_le_sum fun l _ => card_tuples_le S l).trans
    (sum_range_pow_le hS d))

/-- An enumeration of `V₂` is a list of length `|V₂|` over `V₂`. -/
theorem card_enums_le (V₂ : Finset (Finset α)) : (enums V₂).card ≤ V₂.card ^ V₂.card := by
  refine card_image_le.trans ((card_le_card fun l hl => ?_).trans (card_tuples_le V₂ V₂.card))
  rw [Multiset.mem_toFinset, Multiset.mem_lists_iff] at hl
  refine mem_tuples.2 ⟨?_, fun a ha => ?_⟩
  · have := congrArg Multiset.card hl
    simpa using this.symm
  · rw [← Finset.mem_val, hl]
    exact Multiset.mem_coe.2 ha

/-- `v^d ≤ 64 t^12` for the arity `d` of the `d`-ary structure. -/
theorem pow_arity_le {v s n t : ℕ} (hv : 2 ≤ v) (hvt : v ≤ t) (hn : n ≤ 2 * t) :
    v ^ arity v s n ≤ 64 * t ^ 12 := by
  have hj : v ^ Nat.clog v n ≤ 2 * t ^ 2 := by
    by_cases hn1 : n ≤ 1
    · rw [Nat.clog_of_right_le_one hn1, pow_zero]
      nlinarith
    · have hpos := Nat.clog_pos (by omega : 1 < v) (by omega : 1 < n)
      have hlt := Nat.pow_pred_clog_lt_self (by omega : 1 < v) (by omega : 1 < n)
      rw [Nat.pred_eq_sub_one] at hlt
      have e : v ^ Nat.clog v n = v * v ^ (Nat.clog v n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [e]
      nlinarith
  calc v ^ arity v s n ≤ v ^ (6 * Nat.clog v n) :=
        Nat.pow_le_pow_right (by omega) (min_le_right _ _)
    _ = (v ^ Nat.clog v n) ^ 6 := by rw [mul_comm, pow_mul]
    _ ≤ (2 * t ^ 2) ^ 6 := Nat.pow_le_pow_left hj 6
    _ = 64 * t ^ 12 := by ring

/-- Coherent Split-or-Johnson makes at most one choice, a point of `C₂`. -/
theorem count_cohSoj_le {R : Type*} [DecidableEq R] (C₁ C₂ : Finset R) (c : R → R → ℕ) :
    (cohSoj C₁ C₂ c).count ≤ max 1 C₂.card := by
  have hleaf : ∀ {o : Option (CohOut R)}, (CTree.leaf o : CTree R _).count ≤ 1 := le_refl 1
  unfold cohSoj
  dsimp only
  split_ifs
  · exact le_max_left _ _
  · refine (count_node_le _ _ fun _ _ => hleaf).trans ?_
    rw [mul_one]
    exact (card_filter_le _ _).trans (le_max_right _ _)
  · exact le_max_left _ _
  · exact le_max_left _ _
  · refine (count_node_le _ _ fun _ _ => hleaf).trans ?_
    rw [mul_one]
    exact le_max_right _ _
  · refine (count_node_le (B := 1) _ _ fun y _ => ?_).trans ?_
    · split_ifs <;> exact le_refl 1
    · rw [mul_one]
      exact le_max_right _ _

/-- The first side of a bipartite output of Coherent Split-or-Johnson lies in `C₁`. -/
theorem cohSoj_bip_sub {R : Type*} [DecidableEq R] (C₁ C₂ : Finset R) (c : R → R → ℕ) :
    (cohSoj C₁ C₂ c).AllLeaves fun o => ∀ W₁ W₂ A', o = some (.bip W₁ W₂ A') → W₁ ⊆ C₁ := by
  unfold cohSoj
  dsimp only
  split_ifs
  · intro W₁ W₂ A' h
    cases h
  · intro y _ W₁ W₂ A' h
    cases h
    exact subset_refl _
  · intro W₁ W₂ A' h
    cases h
    exact subset_refl _
  · intro W₁ W₂ A' h
    cases h
  · intro w _ W₁ W₂ A' h
    cases h
  · intro y _
    show CTree.AllLeaves _ (dite _ _ _)
    split_ifs
    · intro W₁ W₂ A' h
      cases h
      exact filter_subset _ _
    · intro W₁ W₂ A' h
      cases h
    · intro W₁ W₂ A' h
      cases h

/-- Both branches of an `if` with at most `B` paths. -/
theorem count_ite_le {C O : Type*} {p : Prop} [Decidable p] {a b : CTree C O} {B : ℕ}
    (ha : a.count ≤ B) (hb : b.count ≤ B) : (if p then a else b).count ≤ B := by
  split_ifs
  · exact ha
  · exact hb

omit [DecidableEq α] in
theorem count_shrink_le {t : ℕ} {V₂ : Finset (Finset α)}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α} {B : ℕ} (hB : 1 ≤ B)
    (hrec : ∀ V₁' V₂' A', V₁'.card ≤ 2 * t → 3 * V₂'.card ≤ 2 * V₂.card →
      (rec V₁' V₂' A').count ≤ B)
    {V₁' : Finset α} {V₂' : Finset (Finset α)} {A' : α → Finset α → Bool}
    (h : V₁'.card ≤ 2 * t) : (shrink V₂ rec V₁' V₂' A').count ≤ B := by
  unfold shrink
  split_ifs with hs
  · exact hrec _ _ _ h hs
  · exact hB

/-- After Coherent Split-or-Johnson: a leaf or one recursive call (with the bound `B`). -/
theorem count_cohCont_le {t : ℕ} {V₁ V₁' C₁ : Finset α}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α} {B : ℕ} (hB : 1 ≤ B)
    (hrec : ∀ V₁'' V₂'' A'', V₁''.card ≤ 2 * t → (rec V₁'' V₂'' A'').count ≤ B)
    (hC : C₁.card ≤ 2 * t) {o : Option (CohOut (α ⊕ Finset α))}
    (ho : ∀ W₁ W₂ A', o = some (.bip W₁ W₂ A') →
      W₁ ⊆ C₁.map ⟨Sum.inl, Sum.inl_injective⟩) :
    (cohCont t V₁ V₁' C₁ rec o).count ≤ B := by
  rcases o with _ | (p | ⟨W₁, W₂, A'⟩)
  · exact hB
  · exact hB
  · have hW : W₁.toLeft.card ≤ 2 * t :=
      card_toLeft_le.trans ((card_le_card (ho W₁ W₂ A' rfl)).trans (by rw [card_map]; exact hC))
    simp only [cohCont]
    split_ifs
    · exact hB
    · exact (count_withPiece_le _ _).trans ((count_withPiece_le _ _).trans
        ((count_withPiece_le _ _).trans (hrec _ _ _ hW)))


/-- After the Design Lemma's choice: at most `(t + 1) B` paths, if every recursive call
with at most two thirds of the cells has at most `B`. -/
theorem count_dlCont_le {t : ℕ} {V₁ V₁' : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} {d : ℕ} (W : (Fin d → V₂) → ℕ)
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α} {B : ℕ}
    (hB : 1 ≤ B) (hV₁' : V₁'.card ≤ 2 * t) (hv : V₂.card ≤ t)
    (hrec : ∀ V₁'' V₂'' A'', V₁''.card ≤ 2 * t → 3 * V₂''.card ≤ 2 * V₂.card →
      (rec V₁'' V₂'' A'').count ≤ B) (x : List V₂) :
    (dlCont t V₁ V₁' V₂ A W rec x).count ≤ (t + 1) * B := by
  have hB' : B ≤ (t + 1) * B := Nat.le_mul_of_pos_left _ (Nat.succ_pos t)
  have hsh : ∀ V₁'' V₂'' A'', V₁''.card ≤ 2 * t → (shrink V₂ rec V₁'' V₂'' A'').count ≤ B :=
    fun _ _ _ h => count_shrink_le hB hrec h
  unfold dlCont
  dsimp only
  split_ifs
  all_goals first
    | exact (count_withPiece_le _ _).trans ((hsh _ _ _ hV₁').trans hB')
    | exact hB.trans hB'
    | refine count_ite_le ?_ ?_
      · exact (count_withPiece_le _ _).trans ((hsh _ _ _ hV₁').trans hB')
      · refine (CTree.count_bind_le (B := B) ?_).trans ?_
        · refine CTree.allLeaves_trans (fun q => rfl) ?_
          refine (cohSoj_bip_sub _ _ _).mono fun o ho => ?_
          exact count_cohCont_le hB hsh ((card_filter_le _ _).trans hV₁') ho
        · refine Nat.mul_le_mul_right _ ((CTree.count_trans (fun _ => rfl) _).trans_le
            ((count_cohSoj_le _ _ _).trans ?_))
          rw [card_map]
          exact max_le (by omega) (((card_filter_le _ _).trans hv).trans (Nat.le_succ t))


/-! ### The bound -/

/-- The cost of one level that makes choices: `64 (t + 1)^13`. -/
def cntM (t : ℕ) : ℕ := 64 * (t + 1) ^ 13

/-- The largest base size: `⌊√(27 L³)⌋` with `L = ⌈log₂ 2t⌉`. -/
def cntV (t : ℕ) : ℕ := Nat.sqrt (27 * Nat.clog 2 (2 * t) ^ 3)

/-- The bound for `|V₂| = v`: `M^{lvl v} · vb^vb`. -/
def cntF (t v : ℕ) : ℕ := cntM t ^ lvl v * cntV t ^ cntV t

omit [DecidableEq α] in
theorem one_le_pow_self (n : ℕ) : 1 ≤ n ^ n := by
  rcases n with _ | n
  · simp
  · exact Nat.one_le_pow _ _ (Nat.succ_pos n)

omit [DecidableEq α] in
theorem one_le_cntF (t v : ℕ) : 1 ≤ cntF t v :=
  Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by unfold cntM; positivity))
    (Nat.one_le_iff_ne_zero.1 (one_le_pow_self _)))

omit [DecidableEq α] in
theorem cntF_mono (t : ℕ) {v w : ℕ} (h : v ≤ w) : cntF t v ≤ cntF t w :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by unfold cntM; positivity) (lvl_mono h))

/-- **One level**: the count of `bstep` given the counts of the recursive calls. -/
theorem count_bstep_le {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool}
    {rec : Finset α → Finset (Finset α) → (α → Finset α → Bool) → STree α}
    (hv : V₂.card ≤ t) (h₁ : V₁.card ≤ 2 * t)
    (hrec : ∀ V₁' V₂' A', V₁'.card ≤ 2 * t →
      (rec V₁' V₂' A').count ≤ cntF t (min V₂'.card V₂.card)) :
    (bstep t V₁ V₂ A rec).count ≤ cntF t V₂.card := by
  have h1F := one_le_cntF t V₂.card
  unfold bstep
  dsimp only
  split_ifs with hd hJ hb hS
  · exact h1F
  · -- the base case
    refine (count_node_le (B := 1) _ _ fun _ _ => le_refl 1).trans ?_
    rw [mul_one]
    refine (card_enums_le V₂).trans (le_trans ?_ (Nat.le_mul_of_pos_left _
      (pow_pos (by unfold cntM; positivity) _)))
    have hvb : V₂.card ≤ cntV t := Nat.le_sqrt'.2 hb
    rcases Nat.eq_zero_or_pos V₂.card with h0 | h0
    · rw [h0, pow_zero]
      exact one_le_pow_self _
    · exact (Nat.pow_le_pow_left hvb _).trans (Nat.pow_le_pow_right (by omega) hvb)
  · exact (count_withPiece_le _ _).trans ((hrec _ _ _ ((card_filter_le _ _).trans h₁)).trans
      (cntF_mono t (min_le_right _ _)))
  · -- the Design Lemma's choice
    have ht : 1 ≤ t := by
      by_contra h0
      apply hb
      have : V₂.card = 0 := by omega
      rw [IsBase, this]
      simp
    have hv2 : 2 ≤ V₂.card := by
      by_contra h2
      apply hb
      have hL : 1 ≤ Nat.clog 2 (2 * t) := Nat.clog_pos (by norm_num) (by omega)
      have : V₂.card ^ 2 ≤ 1 := by
        rcases (show V₂.card = 0 ∨ V₂.card = 1 by omega) with h | h <;> rw [h] <;> norm_num
      unfold IsBase
      nlinarith [Nat.one_le_pow 3 _ hL]
    set v := V₂.card with hvdef
    have hlvl : lvl v = lvl (2 * v / 3) + 1 := lvl_of_two_le hv2
    have hchild : ∀ ch, (dlCont t V₁ (tfDeg V₁ V₂ A ((bigDegs t V₁ V₂ A).min' hd)) V₂ A
        (wlOn (arity v (sOf v ((bigDegs t V₁ V₂ A).min' hd))
          (tfDeg V₁ V₂ A ((bigDegs t V₁ V₂ A).min' hd)).card)
          (daryCol V₂ ((tfDeg V₁ V₂ A ((bigDegs t V₁ V₂ A).min' hd)).image
            (fOf V₂ A ((bigDegs t V₁ V₂ A).min' hd)))
            (arity v (sOf v ((bigDegs t V₁ V₂ A).min' hd))
              (tfDeg V₁ V₂ A ((bigDegs t V₁ V₂ A).min' hd)).card)))
        rec (decodeV₂ V₂ ch)).count ≤ (t + 1) * cntF t (2 * v / 3) := by
      intro ch
      refine count_dlCont_le _ (one_le_cntF _ _) ((card_filter_le _ _).trans h₁) hv ?_ _
      intro V₁'' V₂'' A'' h1'' h3
      exact (hrec _ _ _ h1'').trans (cntF_mono t (by omega))
    refine (count_node_le _ _ fun ch _ => hchild ch).trans ?_
    refine (Nat.mul_le_mul_right ((t + 1) * cntF t (2 * v / 3))
      (show _ ≤ 64 * t ^ 12 from ?_)).trans ?_
    · refine card_image_le.trans ((card_filter_le _ _).trans ((card_tuplesLt_le _ ?_ _).trans ?_))
      · rw [card_univ, Fintype.card_coe]
        exact hv2
      · rw [card_univ, Fintype.card_coe]
        exact pow_arity_le hv2 hv ((card_filter_le _ _).trans h₁)
    · rw [cntF, cntF, hlvl, pow_succ, cntM]
      have h12 : t ^ 12 ≤ (t + 1) ^ 12 := Nat.pow_le_pow_left (Nat.le_succ t) 12
      have e : (t + 1) ^ 13 = (t + 1) ^ 12 * (t + 1) := pow_succ _ _
      calc 64 * t ^ 12 * ((t + 1) * (cntM t ^ lvl (2 * v / 3) * cntV t ^ cntV t))
          ≤ 64 * (t + 1) ^ 12 * ((t + 1) * (cntM t ^ lvl (2 * v / 3) * cntV t ^ cntV t)) := by
            gcongr
        _ = (64 * (t + 1) ^ 13) ^ lvl (2 * v / 3) * (64 * (t + 1) ^ 13) * cntV t ^ cntV t := by
            rw [cntM, e]
            ring
  · exact h1F

/-- **The count of Bipartite Split-or-Johnson**, by strong induction on `|V₂|`. -/
theorem count_bsoj_le_cntF {t : ℕ} :
    ∀ n (V₁ : Finset α) (V₂ : Finset (Finset α)) (A : α → Finset α → Bool), V₂.card = n →
      V₂.card ≤ t → V₁.card ≤ 2 * t → (bsoj t V₁ V₂ A).count ≤ cntF t V₂.card := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V₁ V₂ A hn hv h₁
    rw [bsoj]
    refine count_bstep_le hv h₁ fun V₁' V₂' A' h₁' => ?_
    split_ifs with hlt
    · rw [min_eq_left hlt.le]
      exact ih _ (hn ▸ hlt) V₁' V₂' A' rfl (by omega) h₁'
    · exact one_le_cntF _ _

/-- The closed form: `cntF t t ≤ 2^{128 (⌈log₂ t⌉ + 2)²}`. -/
theorem cntF_le (t : ℕ) : cntF t t ≤ 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) := by
  have htL : t ≤ 2 ^ Nat.clog 2 t := Nat.le_pow_clog (by norm_num) t
  have hcv : cntV t ^ 2 ≤ 27 * Nat.clog 2 (2 * t) ^ 3 := Nat.sqrt_le' _
  have hL' : Nat.clog 2 (2 * t) ≤ Nat.clog 2 t + 1 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ]; omega)
  generalize Nat.clog 2 t = L at htL hL' ⊢
  have hM : cntM t ≤ 2 ^ (13 * L + 19) := by
    have h1 : t + 1 ≤ 2 ^ (L + 1) := by
      rw [pow_succ]
      have := Nat.one_le_two_pow (n := L)
      omega
    calc cntM t = 64 * (t + 1) ^ 13 := by rw [cntM]
      _ ≤ 64 * (2 ^ (L + 1)) ^ 13 := by gcongr
      _ = 2 ^ (13 * L + 19) := by ring
  have hlvl : lvl t ≤ 2 * L + 1 := lvl_le_of_le_pow L t htL
  have hV : cntV t ^ cntV t ≤ 2 ^ (94 * (L + 1) ^ 2) := by
    exact pow_self_le (by omega) (hcv.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL' 3)))
  calc cntF t t = cntM t ^ lvl t * cntV t ^ cntV t := by rw [cntF]
    _ ≤ (2 ^ (13 * L + 19)) ^ (2 * L + 1) * 2 ^ (94 * (L + 1) ^ 2) := by
        gcongr
        · exact Nat.one_le_two_pow
    _ = 2 ^ ((13 * L + 19) * (2 * L + 1) + 94 * (L + 1) ^ 2) := by
        rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (128 * (L + 2) ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

end BCount

/-- **The multiplicative cost of Bipartite Split-or-Johnson.** -/
theorem bsoj_count_le {t : ℕ} {V₁ : Finset α} {V₂ : Finset (Finset α)}
    {A : α → Finset α → Bool} (hv : V₂.card ≤ t) (h₁ : V₁.card ≤ 2 * t) :
    (bsoj t V₁ V₂ A).count ≤ 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2) :=
  (BCount.count_bsoj_le_cntF _ V₁ V₂ A rfl hv h₁).trans
    ((BCount.cntF_mono t hv).trans (BCount.cntF_le t))

end GraphIso.SplitJohnson
