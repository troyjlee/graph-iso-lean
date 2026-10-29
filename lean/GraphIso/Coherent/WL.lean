module

public import GraphIso.Coherent.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Lex
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.List.GetD

/-!
# The `k`-ary Weisfeiler–Leman refinement: the model

The `k`-ary Weisfeiler–Leman refinement (Helfgott, Algorithm 3, with the configuration functor
`F₂` of §2.3 folded into every round) of a colouring `c` of the `k`-tuples of `Fin m`. These are
the functions that the programs of `GraphIso/Coherent/WLProg.lean` compute.

* **Rounds.** Round 0 colours a tuple by its input colour and its equality pattern (`sig0`).
  Each later round colours `x` by its signature `sig c x`: the colour of `x`, the colours of
  `x ∘ τ` for all maps of positions `τ` (`posMaps`), and the sorted list of the vectors
  `vec c x z = (c (update x j z))_j` over all points `z`.
* **Canonical colour names.** The new colour is the rank of the signature in the sorted list of
  the distinct signatures (`sigList`, `rank`). That list depends only on the set of signatures,
  so the colours of a relabelled structure are the relabelled colours, names included
  (`wl_relabel`).
* **Termination.** A round refines the previous colouring (the signature starts with the old
  colour, `sigColour_sig`), so the number of colours never decreases; when it does not grow,
  equal colours have equal signatures (`sig_eq_of_card_eq`) and the iteration stops. There are
  at most `m ^ k` colours, so `m ^ k + 1` rounds suffice (`wlStep_wlIter`).
* **Coherence at the fixpoint** (`wl_isCoherent`): equal signatures give the colours of `x ∘ τ`
  for every `τ` (configuration axiom (b)) and equal multisets of vectors, hence equal
  intersection numbers; the equality pattern of round 0 gives axiom (a).
* **Decoding** (`wl_decode`): the state carries a list mapping each colour to the input colour
  of its tuples. Hence `wl` refines the input (`wl_refines`), `π` maps `c` to `d` exactly when it
  maps the refinements and the colour lists agree (`wl_iso_iff`), and the refinement has the
  same twins as the input (`isTwin_wl_iff`).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

/-- `k`-tuples of points of `Fin m`. -/
abbrev Tup (k m : ℕ) := Fin k → Fin m

variable {k m : ℕ}

/-- All maps of positions `Fin k → Fin k`, listed by code. -/
def posMaps (k : ℕ) : List (Fin k → Fin k) :=
  (List.finRange (k ^ k)).map finFunctionFinEquiv.symm

/-- The equality pattern of a tuple: `1` at `(i, j)` if `x i = x j`, row by row. -/
def pattern (x : Tup k m) : List ℕ :=
  (List.finRange k).flatMap fun i => (List.finRange k).map fun j => if x i = x j then 1 else 0

/-- The colours of `x` with position `j` replaced by `z`, for `j = 0, …, k − 1`. -/
def vec (c : Tup k m → ℕ) (x : Tup k m) (z : Fin m) : List ℕ :=
  (List.finRange k).map fun j => c (update x j z)

/-- The round-0 signature: the colour and the equality pattern. -/
def sig0 (c : Tup k m → ℕ) (x : Tup k m) : List (List ℕ) := [[c x], pattern x]

/-- **The signature of a round**: the colour, the colours of `x ∘ τ` for all maps of positions
`τ`, and the sorted list of the vectors `vec c x z` over all points `z`. -/
def sig (c : Tup k m → ℕ) (x : Tup k m) : List (List ℕ) :=
  [c x] :: (posMaps k).map (fun τ => c (x ∘ τ)) ::
    ((List.finRange m).map (vec c x)).insertionSort (· ≤ ·)

/-- The sorted list of the distinct signatures. -/
def sigList (s : Tup k m → List (List ℕ)) : List (List (List ℕ)) :=
  (univ.image s).sort (· ≤ ·)

/-- The new colour: the rank of the signature among the distinct signatures. -/
def rank (s : Tup k m → List (List ℕ)) (x : Tup k m) : ℕ := (sigList s).idxOf (s x)

/-- The previous colour recorded at the head of a signature. -/
def sigColour (s : List (List ℕ)) : ℕ := (s.headD []).headD 0

/-- The state of the refinement: the colouring, its number of colours, and the list decoding
each colour into the input colour. -/
abbrev WLState (k m : ℕ) := (Tup k m → ℕ) × ℕ × List ℕ

/-- Round 0: colour by the input colour and the equality pattern. -/
def wlInit (c : Tup k m → ℕ) : WLState k m :=
  (rank (sig0 c), (sigList (sig0 c)).length, (sigList (sig0 c)).map sigColour)

/-- One round, or `none` when it splits no colour class. -/
def wlStep (st : WLState k m) : Option (WLState k m) :=
  if (sigList (sig st.1)).length = st.2.1 then none
  else some (rank (sig st.1), (sigList (sig st.1)).length,
    (sigList (sig st.1)).map fun s => st.2.2.getD (sigColour s) 0)

/-- Iterate rounds at most `j` times, stopping when a round splits no class. -/
def wlIter : ℕ → WLState k m → WLState k m
  | 0, st => st
  | j + 1, st =>
    match wlStep st with
    | none => st
    | some st' => wlIter j st'

/-- **The `k`-ary Weisfeiler–Leman refinement** of a colouring of the `k`-tuples of `Fin m`: the
stable colouring and the list decoding its colours into the input colours. -/
def wl (k m : ℕ) (c : Tup k m → ℕ) : (Tup k m → ℕ) × List ℕ :=
  ((wlIter (m ^ k + 1) (wlInit c)).1, (wlIter (m ^ k + 1) (wlInit c)).2.2)

/-- The number of colours. -/
def numColours (c : Tup k m → ℕ) : ℕ := (univ.image c).card

/-! ### Ranks -/

theorem mem_sigList (s : Tup k m → List (List ℕ)) (x : Tup k m) : s x ∈ sigList s := by
  unfold sigList
  rw [Finset.mem_sort]
  exact mem_image_of_mem s (mem_univ x)

theorem rank_lt_length (s : Tup k m → List (List ℕ)) (x : Tup k m) :
    rank s x < (sigList s).length :=
  List.idxOf_lt_length_iff.2 (mem_sigList s x)

theorem getElem_rank (s : Tup k m → List (List ℕ)) (x : Tup k m) :
    (sigList s)[rank s x]'(rank_lt_length s x) = s x :=
  List.getElem_idxOf _

/-- Equal ranks exactly for equal signatures. -/
theorem rank_eq_rank_iff (s : Tup k m → List (List ℕ)) {x y : Tup k m} :
    rank s x = rank s y ↔ s x = s y :=
  List.idxOf_inj (mem_sigList s x)

theorem length_sigList (s : Tup k m → List (List ℕ)) :
    (sigList s).length = (univ.image s).card := by
  unfold sigList
  exact Finset.length_sort _

/-- The ranks have as many colours as there are distinct signatures. -/
theorem numColours_rank (s : Tup k m → List (List ℕ)) :
    numColours (rank s) = (sigList s).length := by
  rw [length_sigList]
  unfold numColours
  have e : univ.image (rank s) = (univ.image s).image fun a => (sigList s).idxOf a := by
    rw [Finset.image_image]
    rfl
  rw [e, Finset.card_image_of_injOn]
  intro a ha b hb hab
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hb
  exact (rank_eq_rank_iff s).1 hab

/-- The colour recorded at the head of the signature. -/
theorem sigColour_sig (c : Tup k m → ℕ) (x : Tup k m) : sigColour (sig c x) = c x := rfl

theorem sigColour_sig0 (c : Tup k m → ℕ) (x : Tup k m) : sigColour (sig0 c x) = c x := rfl

/-- A finer colouring has at least as many colours. -/
theorem card_image_comp_le {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (S : Finset α)
    (f : α → β) (g : β → γ) : (S.image (g ∘ f)).card ≤ (S.image f).card := by
  rw [← Finset.image_image]
  exact Finset.card_image_le

/-- With equally many colours, the coarser colouring determines the finer one. -/
theorem eq_of_card_image_comp_eq {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {S : Finset α} {f : α → β} {g : β → γ} (h : (S.image (g ∘ f)).card = (S.image f).card)
    {x y : α} (hx : x ∈ S) (hy : y ∈ S) (hxy : g (f x) = g (f y)) : f x = f y := by
  rw [← Finset.image_image] at h
  exact Finset.card_image_iff.1 h (mem_image_of_mem f hx) (mem_image_of_mem f hy) hxy

theorem sigColour_comp_sig (c : Tup k m → ℕ) : sigColour ∘ sig c = c := rfl

theorem numColours_le_card_sig (c : Tup k m → ℕ) : numColours c ≤ (univ.image (sig c)).card := by
  unfold numColours
  conv_lhs => rw [← sigColour_comp_sig c]
  exact card_image_comp_le _ _ _

/-- If a round does not increase the number of colours, equal colours have equal
signatures. -/
theorem sig_eq_of_card_eq {c : Tup k m → ℕ} (h : (univ.image (sig c)).card = numColours c)
    {x y : Tup k m} (hxy : c x = c y) : sig c x = sig c y := by
  refine eq_of_card_image_comp_eq (g := sigColour) ?_ (mem_univ x) (mem_univ y) hxy
  rw [sigColour_comp_sig]
  exact h.symm

/-! ### Invariants of the iteration -/

/-- The invariants: the recorded number of colours, the decoding into the input colouring
`c₀`, and the equality pattern. -/
structure WLInv (c₀ : Tup k m → ℕ) (st : WLState k m) : Prop where
  num : st.2.1 = numColours st.1
  dec : ∀ x, st.2.2.getD (st.1 x) 0 = c₀ x
  pat : ∀ x y, st.1 x = st.1 y → pattern x = pattern y

theorem getD_map_sigList (s : Tup k m → List (List ℕ)) (f : List (List ℕ) → ℕ)
    (x : Tup k m) : ((sigList s).map f).getD (rank s x) 0 = f (s x) := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact rank_lt_length s x),
    List.getElem_map, getElem_rank]

theorem wlInv_init (c : Tup k m → ℕ) : WLInv c (wlInit c) where
  num := (numColours_rank _).symm
  dec x := getD_map_sigList (sig0 c) sigColour x
  pat x y h := by
    have := (rank_eq_rank_iff (sig0 c)).1 h
    simp only [sig0, List.cons.injEq] at this
    exact this.2.1

theorem wlStep_eq_some {st st' : WLState k m} (hs : wlStep st = some st') :
    (sigList (sig st.1)).length ≠ st.2.1 ∧ st' = (rank (sig st.1), (sigList (sig st.1)).length,
      (sigList (sig st.1)).map fun s => st.2.2.getD (sigColour s) 0) := by
  unfold wlStep at hs
  split_ifs at hs with h
  exact ⟨h, (Option.some.inj hs).symm⟩

theorem wlStep_eq_none {st : WLState k m} (hs : wlStep st = none) :
    (sigList (sig st.1)).length = st.2.1 := by
  unfold wlStep at hs
  split_ifs at hs with h
  exact h

theorem WLInv.step {c₀ : Tup k m → ℕ} {st st' : WLState k m} (hI : WLInv c₀ st)
    (hs : wlStep st = some st') : WLInv c₀ st' := by
  obtain ⟨-, rfl⟩ := wlStep_eq_some hs
  refine ⟨(numColours_rank _).symm, fun x => ?_, fun x y h => ?_⟩
  · rw [getD_map_sigList]
    exact hI.dec x
  · exact hI.pat x y (congrArg sigColour ((rank_eq_rank_iff (sig st.1)).1 h))

theorem WLInv.iter {c₀ : Tup k m → ℕ} :
    ∀ (j : ℕ) {st : WLState k m}, WLInv c₀ st → WLInv c₀ (wlIter j st)
  | 0, _, hI => hI
  | j + 1, st, hI => by
    unfold wlIter
    rcases hs : wlStep st with _ | st'
    · exact hI
    · exact WLInv.iter j (hI.step hs)

/-! ### Interface for the programs -/

theorem numColours_le (c : Tup k m → ℕ) : numColours c ≤ m ^ k := by
  unfold numColours
  refine (Finset.card_image_le).trans ?_
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

theorem wlInit_inv (c : Tup k m → ℕ) : (wlInit c).2.1 = numColours (wlInit c).1 :=
  (wlInv_init c).num

theorem wlStep_inv {st st' : WLState k m} (h : st.2.1 = numColours st.1)
    (hs : wlStep st = some st') : st'.2.1 = numColours st'.1 ∧ st.2.1 < st'.2.1 := by
  obtain ⟨hne, rfl⟩ := wlStep_eq_some hs
  refine ⟨(numColours_rank _).symm, ?_⟩
  have hle := numColours_le_card_sig st.1
  rw [← length_sigList] at hle
  dsimp only
  omega

theorem wlStep_wlIter_of {c₀ : Tup k m → ℕ} :
    ∀ (j : ℕ) {st : WLState k m}, WLInv c₀ st → m ^ k < j + st.2.1 →
      wlStep (wlIter j st) = none
  | 0, st, hI, hj => by
    have := numColours_le st.1
    rw [← hI.num] at this
    omega
  | j + 1, st, hI, hj => by
    unfold wlIter
    rcases hs : wlStep st with _ | st'
    · exact hs
    · have hlt := (wlStep_inv hI.num hs).2
      exact wlStep_wlIter_of j (hI.step hs) (by omega)

/-- The refinement is stable after `m ^ k + 1` rounds. -/
theorem wlStep_wlIter (c : Tup k m → ℕ) : wlStep (wlIter (m ^ k + 1) (wlInit c)) = none :=
  wlStep_wlIter_of (m ^ k + 1) (wlInv_init c) (by omega)

/-! ### Coherence at the fixpoint -/

/-- Flattening lists of equal lengths is injective. -/
theorem forall_eq_of_flatMap_eq {α β : Type*} {f g : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, (f a).length = (g a).length) → l.flatMap f = l.flatMap g →
      ∀ a ∈ l, f a = g a
  | [], _, _ => by simp
  | a :: l, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h₁, h₂⟩ := List.append_inj h (hl a List.mem_cons_self)
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h₁
    · exact forall_eq_of_flatMap_eq l (fun c hc => hl c (List.mem_cons_of_mem _ hc)) h₂ b hb

/-- Equal patterns have the same equal entries. -/
theorem eq_iff_of_pattern_eq {x y : Tup k m} (h : pattern x = pattern y) (i j : Fin k) :
    x i = x j ↔ y i = y j := by
  unfold pattern at h
  have h₁ := forall_eq_of_flatMap_eq (List.finRange k) (fun _ _ => by simp) h i
    (List.mem_finRange i)
  have h₂ := (List.map_inj_left.1 h₁) j (List.mem_finRange j)
  by_cases hx : x i = x j <;> by_cases hy : y i = y j <;> simp_all

theorem mem_posMaps (τ : Fin k → Fin k) : τ ∈ posMaps k := by
  unfold posMaps
  exact List.mem_map.2 ⟨finFunctionFinEquiv τ, List.mem_finRange _, by simp⟩

theorem card_filter_eq_count (c : Tup k m → ℕ) (x : Tup k m) (r : Fin k → ℕ) :
    (univ.filter fun z => ∀ j, c (update x j z) = r j).card =
      ((List.finRange m).map (vec c x)).count ((List.finRange k).map r) := by
  have e : ∀ z, (vec c x z = (List.finRange k).map r) ↔ ∀ j, c (update x j z) = r j := by
    intro z
    unfold vec
    rw [List.map_inj_left]
    simp only [List.mem_finRange, forall_const]
  rw [List.count_eq_countP, List.countP_map, Fin.univ_def]
  simp only [Finset.card, Finset.filter_val, Multiset.filter_coe, Multiset.coe_card,
    List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro z _
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, Function.comp_apply, beq_iff_eq, e]

/-- A colouring for which a round splits no class is a coherent configuration. -/
theorem isCoherent_of_stable {c : Tup k m → ℕ} (hpat : ∀ x y, c x = c y → pattern x = pattern y)
    (h : (univ.image (sig c)).card = numColours c) : IsCoherent c := by
  refine ⟨fun x y hxy => ⟨eq_iff_of_pattern_eq (hpat x y hxy), fun τ => ?_⟩, ?_⟩
  · have hs := sig_eq_of_card_eq h hxy
    simp only [sig, List.cons.injEq] at hs
    exact (List.map_inj_left.1 hs.2.1) τ (mem_posMaps τ)
  · intro x y hxy r
    have hs := sig_eq_of_card_eq h hxy
    simp only [sig, List.cons.injEq] at hs
    have h₁ := List.perm_insertionSort (· ≤ ·) ((List.finRange m).map (vec c x))
    have h₂ := List.perm_insertionSort (· ≤ ·) ((List.finRange m).map (vec c y))
    rw [hs.2.2] at h₁
    rw [card_filter_eq_count, card_filter_eq_count, (h₁.symm.trans h₂).count_eq]

/-! ### Main theorems -/

/-- **The refinement is a coherent configuration.** After at most `m ^ k + 1` rounds a round
splits no colour class (`wlStep_wlIter`); then equal colours have equal signatures, whose
second component gives the colours of `x ∘ τ` for every map of positions `τ` and whose sorted
vector lists give the intersection numbers. The equality pattern of round 0 is refined by
every later colouring. -/
theorem wl_isCoherent (c : Tup k m → ℕ) : IsCoherent (wl k m c).1 := by
  have hI := WLInv.iter (m ^ k + 1) (wlInv_init c)
  have hfix := wlStep_eq_none (wlStep_wlIter c)
  rw [length_sigList, hI.num] at hfix
  exact isCoherent_of_stable hI.pat hfix

/-- **The colour list decodes the input colouring.** -/
theorem wl_decode (c : Tup k m → ℕ) (x : Tup k m) :
    (wl k m c).2.getD ((wl k m c).1 x) 0 = c x :=
  (WLInv.iter (m ^ k + 1) (wlInv_init c)).dec x

/-- **The refinement refines the input.** -/
theorem wl_refines (c : Tup k m → ℕ) {x y : Tup k m} (h : (wl k m c).1 x = (wl k m c).1 y) :
    c x = c y := by
  rw [← wl_decode c x, ← wl_decode c y, h]

/-! ### Canonicity -/

/-- Relabel a function of tuples by `π`. -/
def relab {β : Type*} (π : Equiv.Perm (Fin m)) (f : Tup k m → β) : Tup k m → β :=
  fun x => f (⇑π⁻¹ ∘ x)

theorem relab_comp {β : Type*} (π : Equiv.Perm (Fin m)) (f : Tup k m → β) (x : Tup k m) :
    relab π f (⇑π ∘ x) = f x := by
  unfold relab
  congr 1
  funext i
  simp [Equiv.Perm.inv_def]

theorem comp_inv_comp (π : Equiv.Perm (Fin m)) (y : Tup k m) : ⇑π ∘ (⇑π⁻¹ ∘ y) = y := by
  funext i
  simp [Equiv.Perm.inv_def]

theorem image_relab {β : Type*} [DecidableEq β] (π : Equiv.Perm (Fin m))
    {s s' : Tup k m → β} (h : ∀ x, s' (⇑π ∘ x) = s x) : univ.image s' = univ.image s := by
  ext b
  simp only [Finset.mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⇑π⁻¹ ∘ y, by rw [← h, comp_inv_comp]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨⇑π ∘ x, h x⟩

theorem sigList_relab (π : Equiv.Perm (Fin m)) {s s' : Tup k m → List (List ℕ)}
    (h : ∀ x, s' (⇑π ∘ x) = s x) : sigList s' = sigList s := by
  unfold sigList
  rw [image_relab π h]

theorem rank_relab (π : Equiv.Perm (Fin m)) {s s' : Tup k m → List (List ℕ)}
    (h : ∀ x, s' (⇑π ∘ x) = s x) : rank s' = relab π (rank s) := by
  funext y
  unfold rank relab
  rw [sigList_relab π h]
  beta_reduce
  rw [← h, comp_inv_comp]

theorem pattern_comp (π : Equiv.Perm (Fin m)) (x : Tup k m) : pattern (⇑π ∘ x) = pattern x := by
  unfold pattern
  simp only [Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]

theorem sig0_relab (π : Equiv.Perm (Fin m)) (c : Tup k m → ℕ) (x : Tup k m) :
    sig0 (relab π c) (⇑π ∘ x) = sig0 c x := by
  unfold sig0
  rw [relab_comp, pattern_comp]

theorem update_comp (π : Equiv.Perm (Fin m)) (x : Tup k m) (j : Fin k) (z : Fin m) :
    ⇑π⁻¹ ∘ update (⇑π ∘ x) j z = update x j (π⁻¹ z) := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · simp [hi, Equiv.Perm.inv_def]

theorem vec_relab (π : Equiv.Perm (Fin m)) (c : Tup k m → ℕ) (x : Tup k m) (z : Fin m) :
    vec (relab π c) (⇑π ∘ x) z = vec c x (π⁻¹ z) := by
  unfold vec relab
  simp only [update_comp]

theorem perm_map_finRange (π : Equiv.Perm (Fin m)) :
    ((List.finRange m).map ⇑π⁻¹).Perm (List.finRange m) :=
  (List.perm_ext_iff_of_nodup ((List.nodup_finRange m).map (Equiv.injective _))
    (List.nodup_finRange m)).2 fun a =>
    ⟨fun _ => List.mem_finRange a, fun _ => List.mem_map.2 ⟨π a, List.mem_finRange _, by simp⟩⟩

theorem sig_relab (π : Equiv.Perm (Fin m)) (c : Tup k m → ℕ) (x : Tup k m) :
    sig (relab π c) (⇑π ∘ x) = sig c x := by
  have hc : ∀ τ : Fin k → Fin k, relab π c ((⇑π ∘ x) ∘ τ) = c (x ∘ τ) := fun τ =>
    relab_comp π c (x ∘ τ)
  have hv : ((List.finRange m).map (vec (relab π c) (⇑π ∘ x))).insertionSort (· ≤ ·) =
      ((List.finRange m).map (vec c x)).insertionSort (· ≤ ·) := by
    have e : (List.finRange m).map (vec (relab π c) (⇑π ∘ x)) =
        ((List.finRange m).map ⇑π⁻¹).map (vec c x) := by
      rw [List.map_map]
      exact List.map_congr_left fun z _ => vec_relab π c x z
    rw [e]
    refine List.Perm.eq_of_pairwise' (List.pairwise_insertionSort _ _)
      (List.pairwise_insertionSort _ _) ?_
    exact (List.perm_insertionSort _ _).trans (((perm_map_finRange π).map _).trans
      (List.perm_insertionSort _ _).symm)
  unfold sig
  rw [relab_comp, hv]
  simp only [hc]

/-- Relabel a state. -/
def relabSt (π : Equiv.Perm (Fin m)) (st : WLState k m) : WLState k m :=
  (relab π st.1, st.2.1, st.2.2)

theorem wlInit_relab (π : Equiv.Perm (Fin m)) (c : Tup k m → ℕ) :
    wlInit (relab π c) = relabSt π (wlInit c) := by
  have h := sig0_relab π c
  unfold wlInit relabSt
  rw [rank_relab π h, sigList_relab π h]

theorem wlStep_relab (π : Equiv.Perm (Fin m)) (st : WLState k m) :
    wlStep (relabSt π st) = (wlStep st).map (relabSt π) := by
  have h := sig_relab π st.1
  dsimp only [wlStep, relabSt]
  simp only [sigList_relab π h, rank_relab π h]
  split_ifs <;> rfl

theorem wlIter_relab (π : Equiv.Perm (Fin m)) :
    ∀ (j : ℕ) (st : WLState k m), wlIter j (relabSt π st) = relabSt π (wlIter j st)
  | 0, _ => rfl
  | j + 1, st => by
    unfold wlIter
    rw [wlStep_relab]
    rcases wlStep st with _ | st'
    · rfl
    · exact wlIter_relab π j st'

/-- **Canonicity**: relabelling the input by `π` relabels the refinement by `π` exactly, colour
names included, and leaves the colour list unchanged. Colours are ranks in the sorted list of
the distinct signatures, which depends only on the set of signatures, and the signature of
`π ∘ x` for the relabelled colouring is the signature of `x`. -/
theorem wl_relabel (c : Tup k m → ℕ) (π : Equiv.Perm (Fin m)) :
    wl k m (fun x => c (⇑π⁻¹ ∘ x)) = (fun x => (wl k m c).1 (⇑π⁻¹ ∘ x), (wl k m c).2) := by
  have e : (fun x => c (⇑π⁻¹ ∘ x)) = relab π c := rfl
  unfold wl
  rw [e, wlInit_relab, wlIter_relab]
  rfl

/-- **Isomorphism transfer**: `π` maps `c` to `d` exactly when it maps the refinement of `c` to
that of `d` and the colour lists agree. -/
theorem wl_iso_iff (c d : Tup k m → ℕ) (π : Equiv.Perm (Fin m)) :
    (∀ x, d (⇑π ∘ x) = c x) ↔
      (wl k m c).2 = (wl k m d).2 ∧ ∀ x, (wl k m d).1 (⇑π ∘ x) = (wl k m c).1 x := by
  constructor
  · intro h
    have hd : d = fun x => c (⇑π⁻¹ ∘ x) := by
      funext y
      rw [← h, comp_inv_comp]
    rw [hd, wl_relabel]
    exact ⟨rfl, fun x => relab_comp π (wl k m c).1 x⟩
  · rintro ⟨h₁, h₂⟩ x
    rw [← wl_decode d, h₂, ← h₁, wl_decode]

/-- The refinement has the same twins as the input. -/
theorem isTwin_wl_iff (c : Tup k m → ℕ) (u v : Fin m) :
    IsTwin (wl k m c).1 u v ↔ IsTwin c u v := by
  have := wl_iso_iff c c (Equiv.swap u v)
  unfold IsTwin
  exact ⟨fun h => this.2 ⟨rfl, h⟩, fun h => (this.1 h).2⟩

end GraphIso.Coherent
