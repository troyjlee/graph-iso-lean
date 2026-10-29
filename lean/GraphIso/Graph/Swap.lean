module

public import GraphIso.Graph.TwoGroup

/-!
# Isomorphisms of two graphs from automorphisms of their union

For graphs `X`, `Y` on `n` points, `Z = X ⊔ Y` on `2n` points (`GraphData.union`). Root `Z` at an
edge `{a, b}` of `X` and an edge `{a', b'}` of `Y` (shifted by `n`).

* `valid_union`, `adj_union_iff`: `Z` is valid, and its edges are those of `X` and the shifted
  edges of `Y`.
* `roots4_union`: the roots `a, b, n + a', n + b'` satisfy `Roots4` for the levels of `Z`.
* `swap_criterion`: when every point of `Z` is reached, `X` has an isomorphism onto `Y` sending
  `{a, b}` to `{a', b'}` exactly when `A_{2n}` has an element sending `a` into `{n + a', n + b'}`.
  For generators of `A_{2n}`, such an element exists exactly when some generator is one.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

variable {Δ n : ℕ} {X Y : GraphData}

/-! ### The union -/

theorem adj_union_iff (hX : X.ValidD Δ n) {u v : ℕ} :
    Adj (GraphData.union n X Y) u v ↔
      (u < n ∧ v < n ∧ Adj X u v) ∨ (n ≤ u ∧ n ≤ v ∧ Adj Y (u - n) (v - n)) := by
  unfold Adj
  by_cases hu : u < n
  · rw [nbrs_union_lt hX.size hu]
    constructor
    · intro h
      exact Or.inl ⟨hu, hX.lt u v h, h⟩
    · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
      · exact h
      · omega
  · rw [nbrs_union_ge hX.size (by omega), List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Or.inr ⟨by omega, by omega, by simpa using hw⟩
    · rintro (⟨h, -⟩ | ⟨-, hv, h⟩)
      · omega
      · exact ⟨v - n, h, by omega⟩

theorem valid_union (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) :
    (GraphData.union n X Y).ValidD Δ (2 * n) := by
  have hadj := fun u v => adj_union_iff (u := u) (v := v) (Y := Y) hX
  refine ⟨by rw [size_union, hX.size, hY.size]; omega, fun u v h => ?_, fun u => ?_,
    fun u v h => ?_, fun u h => ?_, fun u => ?_⟩
  · rcases (hadj u v).1 h with ⟨-, hv, -⟩ | ⟨-, hv, h'⟩
    · omega
    · have := hY.lt _ _ h'
      omega
  · by_cases hu : u < n
    · rw [nbrs_union_lt hX.size hu]
      exact hX.nodup u
    · rw [nbrs_union_ge hX.size (by omega)]
      exact (hY.nodup _).map (fun x y h => by omega)
  · rcases (hadj u v).1 h with ⟨hu, hv, h'⟩ | ⟨hu, hv, h'⟩
    · exact (hadj v u).2 (Or.inl ⟨hv, hu, hX.symm _ _ h'⟩)
    · exact (hadj v u).2 (Or.inr ⟨hv, hu, hY.symm _ _ h'⟩)
  · rcases (hadj u u).1 h with ⟨-, -, h'⟩ | ⟨-, -, h'⟩
    · exact hX.irrefl _ h'
    · exact hY.irrefl _ h'
  · by_cases hu : u < n
    · rw [nbrs_union_lt hX.size hu]
      exact hX.deg u
    · rw [nbrs_union_ge hX.size (by omega), List.length_map]
      exact hY.deg _

/-! ### The roots of the union -/

section Roots

variable {a b a' b' : ℕ} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) (hab : Adj X a b)
  (hab' : Adj Y a' b')
include hX hY hab hab'

/-- The roots of the union. -/
abbrev unionRoots (n a b a' b' : ℕ) : List ℕ := [a, b, n + a', n + b']

/-- The levels of the union from the two edges. -/
abbrev unionLev (n : ℕ) (X Y : GraphData) (a b a' b' : ℕ) : Array ℕ :=
  levels (2 * n) (GraphData.union n X Y) (unionRoots n a b a' b')

omit hab hab' in
theorem isLevels_union :
    IsLevels (2 * n) (GraphData.union n X Y) (unionRoots n a b a' b') (unionLev n X Y a b a' b') :=
  levels_spec (valid_union hX hY)

/-- **The roots of the union are two edges.** -/
theorem roots4_union :
    Roots4 (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') a b (n + a') (n + b') := by
  have hL := isLevels_union (a := a) (b := b) (a' := a') (b' := b') hX hY
  have ha := hX.lt_left hab
  have hb := hX.lt a b hab
  have ha' := hY.lt_left hab'
  have hb' := hY.lt a' b' hab'
  have hne : a ≠ b := fun e => hX.irrefl a (e ▸ hab)
  have hne' : a' ≠ b' := fun e => hY.irrefl a' (e ▸ hab')
  have hadj := fun u v => adj_union_iff (u := u) (v := v) (Y := Y) hX
  refine ⟨by omega, by omega, by omega, by omega, fun v hv => ?_,
    (hadj a b).2 (Or.inl ⟨ha, hb, hab⟩),
    (hadj _ _).2 (Or.inr ⟨by omega, by omega, by simpa using hab'⟩), fun u v hu hv huv => ?_,
    hne, by omega, by omega, by omega, by omega, fun e => hne' (by omega)⟩
  · rw [hL.zero_iff v hv]
    simp
  · have hvalid := valid_union hX hY
    have huN : u < 2 * n := hvalid.lt_left huv
    have hvN : v < 2 * n := hvalid.lt u v huv
    have hu' := (hL.zero_iff u huN).1 hu
    have hv' := (hL.zero_iff v hvN).1 hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu' hv'
    rcases (hadj u v).1 huv with ⟨hun, hvn, h⟩ | ⟨hun, hvn, h⟩
    · have hu'' : u = a ∨ u = b := by omega
      have hv'' : v = a ∨ v = b := by omega
      rcases hu'' with rfl | rfl <;> rcases hv'' with rfl | rfl
      · exact absurd h (hX.irrefl _)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact absurd h (hX.irrefl _)
    · have hu'' : u = n + a' ∨ u = n + b' := by omega
      have hv'' : v = n + a' ∨ v = n + b' := by omega
      rcases hu'' with rfl | rfl <;> rcases hv'' with rfl | rfl
      · exact absurd h (hY.irrefl _)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
      · exact absurd h (hY.irrefl _)

/-- **The union is layered** once every point is reached. -/
theorem layered_union (hreach : ∀ v < 2 * n, get (unionLev n X Y a b a' b') v < 2 * n)
    (hΔ : 2 ≤ Δ) :
    LayeredD Δ (2 * n) (GraphData.union n X Y) (unionRoots n a b a' b')
      (unionLev n X Y a b a' b') := by
  have hR := roots4_union hX hY hab hab'
  have hvalid := valid_union hX hY
  refine ⟨hvalid, isLevels_union hX hY, hreach, fun v hv h0 => ?_, hΔ⟩
  exact ⟨partner a b (n + a') (n + b') v, (adj_root_iff hR hvalid hv h0
    (lev_partner hR hv h0)).2 rfl, lev_partner hR hv h0⟩

end Roots

/-! ### Isomorphisms -/

/-- `φ` is an isomorphism from `X` onto `Y`. -/
def IsIso (n : ℕ) (X Y : GraphData) (φ : Perm (Fin n)) : Prop :=
  ∀ u v, u < n → v < n → (Adj Y (act φ u) (act φ v) ↔ Adj X u v)

/-- `φ` sends the edge `{a, b}` to `{a', b'}`. -/
def SendsEdge (n a b a' b' : ℕ) (φ : Perm (Fin n)) : Prop :=
  (act φ a = a' ∧ act φ b = b') ∨ (act φ a = b' ∧ act φ b = a')

/-! ### From an isomorphism to an automorphism of the union -/

/-- `φ` on `X`, `φ⁻¹` on `Y`, exchanging the two sides. -/
def swapFun (n : ℕ) (φ : Perm (Fin n)) (v : ℕ) : ℕ :=
  if v < n then act φ v + n else if v < 2 * n then act φ⁻¹ (v - n) else v

theorem swapFun_lt (φ : Perm (Fin n)) {v : ℕ} (hv : v < 2 * n) : swapFun n φ v < 2 * n := by
  unfold swapFun
  split
  · have := act_lt φ (show v < n by omega); omega
  · have := act_lt φ⁻¹ (show v - n < n by omega); omega

theorem swapFun_swapFun (φ : Perm (Fin n)) {v : ℕ} (hv : v < 2 * n) :
    swapFun n φ (swapFun n φ v) = v := by
  unfold swapFun
  by_cases h : v < n
  · have := act_lt φ h
    simp only [h, ↓reduceIte, show ¬ act φ v + n < n by omega,
      show act φ v + n < 2 * n by omega, Nat.add_sub_cancel, act_inv_act]
  · have h' := act_lt φ⁻¹ (show v - n < n by omega)
    simp only [h, ↓reduceIte, hv, h', act_act_inv]
    omega

/-- The automorphism of the union exchanging the sides by `φ`. -/
def swapPerm (n : ℕ) (φ : Perm (Fin n)) : Perm (Fin (2 * n)) where
  toFun v := ⟨swapFun n φ v, swapFun_lt φ v.2⟩
  invFun v := ⟨swapFun n φ v, swapFun_lt φ v.2⟩
  left_inv v := Fin.ext (swapFun_swapFun φ v.2)
  right_inv v := Fin.ext (swapFun_swapFun φ v.2)

theorem act_swapPerm (φ : Perm (Fin n)) {v : ℕ} (hv : v < 2 * n) :
    act (swapPerm n φ) v = swapFun n φ v := by
  rw [act_of_lt _ hv]
  rfl

theorem swapFun_of_lt (φ : Perm (Fin n)) {v : ℕ} (hv : v < n) :
    swapFun n φ v = act φ v + n := by
  simp [swapFun, hv]

theorem swapFun_of_ge (φ : Perm (Fin n)) {v : ℕ} (h₁ : n ≤ v) (h₂ : v < 2 * n) :
    swapFun n φ v = act φ⁻¹ (v - n) := by
  simp [swapFun, show ¬ v < n by omega, h₂]

theorem adj_swapPerm (hX : X.ValidD Δ n) {φ : Perm (Fin n)} (hφ : IsIso n X Y φ) {u v : ℕ}
    (hu : u < 2 * n) (hv : v < 2 * n) :
    Adj (GraphData.union n X Y) (act (swapPerm n φ) u) (act (swapPerm n φ) v) ↔
      Adj (GraphData.union n X Y) u v := by
  rw [act_swapPerm φ hu, act_swapPerm φ hv, adj_union_iff hX, adj_union_iff hX]
  by_cases hun : u < n <;> by_cases hvn : v < n
  · rw [swapFun_of_lt φ hun, swapFun_of_lt φ hvn, Nat.add_sub_cancel, Nat.add_sub_cancel]
    have := act_lt φ hun; have := act_lt φ hvn
    constructor
    · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
      · omega
      · exact Or.inl ⟨hun, hvn, (hφ u v hun hvn).1 h⟩
    · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
      · exact Or.inr ⟨by omega, by omega, (hφ u v hun hvn).2 h⟩
      · omega
  · rw [swapFun_of_lt φ hun, swapFun_of_ge φ (by omega) hv]
    have := act_lt φ hun; have := act_lt φ⁻¹ (show v - n < n by omega)
    constructor <;> rintro (⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩) <;> omega
  · rw [swapFun_of_ge φ (by omega) hu, swapFun_of_lt φ hvn]
    have := act_lt φ hvn; have := act_lt φ⁻¹ (show u - n < n by omega)
    constructor <;> rintro (⟨h₁, h₂, -⟩ | ⟨h₁, h₂, -⟩) <;> omega
  · rw [swapFun_of_ge φ (by omega) hu, swapFun_of_ge φ (by omega) hv]
    have h₁ := act_lt φ⁻¹ (show u - n < n by omega)
    have h₂ := act_lt φ⁻¹ (show v - n < n by omega)
    have key := hφ _ _ h₁ h₂
    rw [act_act_inv, act_act_inv] at key
    constructor
    · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
      · exact Or.inr ⟨by omega, by omega, key.2 h⟩
      · omega
    · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
      · omega
      · exact Or.inl ⟨h₁, h₂, key.1 h⟩

/-! ### The criterion -/

section Criterion

variable {a b a' b' : ℕ} (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) (hab : Adj X a b)
  (hab' : Adj Y a' b')
  (hreach : ∀ v < 2 * n, get (unionLev n X Y a b a' b') v < 2 * n)
include hX hY hab hab' hreach

omit hab hab' in
theorem edgeR_union_iff {u v : ℕ} :
    EdgeR (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n) u v ↔
      Adj (GraphData.union n X Y) u v := by
  have hvalid := valid_union hX hY
  constructor
  · exact fun h => h.1
  · intro h
    have hu := hreach u (hvalid.lt_left h)
    have hv := hreach v (hvalid.lt u v h)
    exact ⟨h, by omega, by omega, Or.inl hu⟩

/-- **An isomorphism sending `{a, b}` to `{a', b'}` gives an element of `A_{2n}` moving `a` to the
other side.** -/
theorem swapPerm_mem {φ : Perm (Fin n)} (hφ : IsIso n X Y φ) (he : SendsEdge n a b a' b' φ) :
    swapPerm n φ ∈ AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n) := by
  have hvalid := valid_union hX hY
  have hL := isLevels_union (a := a) (b := b) (a' := a') (b' := b') hX hY
  have ha := hX.lt_left hab
  have hb := hX.lt a b hab
  have ha' := hY.lt_left hab'
  have hb' := hY.lt a' b' hab'
  -- roots go to roots
  have hfwd : ∀ v < 2 * n, v ∈ unionRoots n a b a' b' →
      act (swapPerm n φ) v ∈ unionRoots n a b a' b' := by
    intro v hv hr
    rw [act_swapPerm φ hv]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl
    · rw [swapFun_of_lt φ ha]
      rcases he with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> omega
    · rw [swapFun_of_lt φ hb]
      rcases he with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e] <;> omega
    · rw [swapFun_of_ge φ (by omega) (by omega), Nat.add_sub_cancel_left]
      rcases he with ⟨e, -⟩ | ⟨-, e⟩
      · left; rw [act_inv_eq_iff, e]
      · right; left; rw [act_inv_eq_iff, e]
    · rw [swapFun_of_ge φ (by omega) (by omega), Nat.add_sub_cancel_left]
      rcases he with ⟨-, e⟩ | ⟨e, -⟩
      · right; left; rw [act_inv_eq_iff, e]
      · left; rw [act_inv_eq_iff, e]
  have hroot : ∀ v < 2 * n, act (swapPerm n φ) v ∈ unionRoots n a b a' b' ↔
      v ∈ unionRoots n a b a' b' := by
    intro v hv
    refine ⟨fun h => ?_, hfwd v hv⟩
    have := hfwd _ (act_lt _ hv) h
    rwa [act_swapPerm φ (act_lt _ hv), act_swapPerm φ hv, swapFun_swapFun φ hv] at this
  have hlev := lev_act hvalid hL hroot (fun u v hu hv => adj_swapPerm hX hφ hu hv)
  refine ⟨fun v hv h => absurd (hL.le v hv) (by omega), hlev, fun u v hu hv => ?_⟩
  rw [edgeR_union_iff hX hY hreach, edgeR_union_iff hX hY hreach]
  exact adj_swapPerm hX hφ hu hv

/-- Elements of `A_{2n}` keeping the edge `{a, b}` form a subgroup. -/
def keepSub : Subgroup (Perm (Fin (2 * n))) where
  carrier := {g | g ∈ AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n) ∧
    EPar a b g}
  one_mem' := ⟨one_mem _, Or.inl (act_one a)⟩
  mul_mem' := by
    rintro g h ⟨hg, hgE⟩ ⟨hh, hhE⟩
    refine ⟨mul_mem hg hh, ?_⟩
    rw [edgeParity_mul (roots4_union hX hY hab hab') (valid_union hX hY) (rootAut_of_autR hg)
      (rootAut_of_autR hh)]
    exact ⟨fun _ => hhE, fun _ => hgE⟩
  inv_mem' := by
    rintro g ⟨hg, hgE⟩
    refine ⟨inv_mem hg, ?_⟩
    have h1 := edgeParity_mul (roots4_union hX hY hab hab') (valid_union hX hY)
      (rootAut_of_autR (inv_mem hg)) (rootAut_of_autR hg)
    rw [inv_mul_cancel] at h1
    exact (h1.1 (Or.inl (act_one a))).2 hgE

omit hreach in
/-- **If some element of `A_{2n}` moves `a` to the other side, some generator does.** -/
theorem exists_gen_swap {gens : Set (Perm (Fin (2 * n)))}
    (hgens : Subgroup.closure gens =
      AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n))
    {g : Perm (Fin (2 * n))}
    (hg : g ∈ AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n))
    (hE : ¬ EPar a b g) : ∃ g' ∈ gens, ¬ EPar a b g' := by
  by_contra h
  push Not at h
  have hle : Subgroup.closure gens ≤ keepSub hX hY hab hab' := by
    rw [Subgroup.closure_le]
    intro x hx
    exact ⟨hgens ▸ Subgroup.subset_closure hx, h x hx⟩
  exact hE (hle (hgens ▸ hg)).2

/-- **An element of `A_{2n}` moving `a` to the other side maps `X` into `Y`.** -/
theorem maps_side {g : Perm (Fin (2 * n))}
    (hg : g ∈ AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n))
    (hE : ¬ EPar a b g) : ∀ v < n, n ≤ act g v := by
  have hvalid := valid_union hX hY
  have hR := roots4_union hX hY hab hab'
  have hL := isLevels_union (a := a) (b := b) (a' := a') (b' := b') hX hY
  have ha := hX.lt_left hab
  have hb := hX.lt a b hab
  have hgR := rootAut_of_autR hg
  -- the roots of `X` move to the other side
  have hga : n ≤ act g a := by
    obtain ⟨hgaN, hga0⟩ := act_root hgR hR.lt_a (lev_a hR)
    unfold EPar at hE
    rcases root_cases hR hgaN hga0 with e | e | e | e
    · exact absurd (Or.inl e) hE
    · exact absurd (Or.inr e) hE
    · omega
    · omega
  have hgb : n ≤ act g b := by
    have := act_partner hR hvalid hgR hR.lt_a (lev_a hR)
    rw [partner_a] at this
    rw [this]
    obtain ⟨hgaN, hga0⟩ := act_root hgR hR.lt_a (lev_a hR)
    rcases root_cases hR hgaN hga0 with e | e | e | e
    · omega
    · omega
    · rw [e, partner_c hR]; omega
    · rw [e, partner_d hR]; omega
  intro v hv
  induction h : get (unionLev n X Y a b a' b') v using Nat.strong_induction_on generalizing v with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rcases root_cases hR (by omega) h with e | e | e | e
      · rw [e]; exact hga
      · rw [e]; exact hgb
      · omega
      · omega
    · obtain ⟨u, huv, hu⟩ := hL.wit v (by omega) (h ▸ hk) (h ▸ hreach v (by omega))
      have hun : u < n := by
        rcases (adj_union_iff (Y := Y) hX).1 huv with ⟨-, h', -⟩ | ⟨h', -⟩
        · exact h'
        · omega
      have hgu := ih _ (by omega) u hun rfl
      have hadj : Adj (GraphData.union n X Y) (act g v) (act g u) := by
        have := (hg.2.2 v u (by omega) (by omega)).2 ((edgeR_union_iff hX hY hreach).2 huv)
        exact (edgeR_union_iff hX hY hreach).1 this
      rcases (adj_union_iff (Y := Y) hX).1 hadj with ⟨-, h', -⟩ | ⟨h', -⟩
      · omega
      · exact h'

/-- **The isomorphism read off an element of `A_{2n}` moving `a` to the other side**:
`v ↦ g v − n`. -/
theorem exists_iso_of_swap {g : Perm (Fin (2 * n))}
    (hg : g ∈ AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n))
    (hE : ¬ EPar a b g) :
    ∃ φ : Perm (Fin n), (∀ v < n, act φ v = act g v - n) ∧ IsIso n X Y φ ∧
      SendsEdge n a b a' b' φ := by
  have hR := roots4_union hX hY hab hab'
  have hvalid := valid_union hX hY
  have hside := maps_side hX hY hab hab' hreach hg hE
  have ha := hX.lt_left hab
  have hb := hX.lt a b hab
  let f : Fin n → Fin n := fun x => ⟨act g x - n, by
    have := act_lt g (show x.val < 2 * n by omega)
    have := hside x x.2
    omega⟩
  have hf : Function.Injective f := fun x y h => by
    have hx := hside x x.2
    have hy := hside y y.2
    have : act g x = act g y := by
      have := congrArg Fin.val h
      simp only [f] at this
      omega
    exact Fin.ext (act_injective g this)
  let φ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
  have hφ : ∀ v < n, act φ v = act g v - n := fun v hv => by
    rw [act_of_lt _ hv]
    rfl
  refine ⟨φ, hφ, fun u v hu hv => ?_, ?_⟩
  · rw [hφ u hu, hφ v hv]
    have hgu := hside u hu
    have hgv := hside v hv
    have hX' : Adj X u v ↔ Adj (GraphData.union n X Y) u v := by
      rw [adj_union_iff hX]
      constructor
      · exact fun h => Or.inl ⟨hu, hv, h⟩
      · rintro (⟨-, -, h⟩ | ⟨h, -⟩)
        · exact h
        · omega
    have hY' : Adj Y (act g u - n) (act g v - n) ↔
        Adj (GraphData.union n X Y) (act g u) (act g v) := by
      rw [adj_union_iff hX]
      constructor
      · exact fun h => Or.inr ⟨hgu, hgv, h⟩
      · rintro (⟨h, -⟩ | ⟨-, -, h⟩)
        · omega
        · exact h
    rw [hX', hY', ← edgeR_union_iff hX hY hreach, ← edgeR_union_iff hX hY hreach]
    exact hg.2.2 u v (by omega) (by omega)
  · have hgR := rootAut_of_autR hg
    have hgb := act_partner hR hvalid hgR hR.lt_a (lev_a hR)
    rw [partner_a] at hgb
    obtain ⟨hgaN, hga0⟩ := act_root hgR hR.lt_a (lev_a hR)
    unfold SendsEdge
    rw [hφ a ha, hφ b hb, hgb]
    unfold EPar at hE
    rcases root_cases hR hgaN hga0 with e | e | e | e
    · exact absurd (Or.inl e) hE
    · exact absurd (Or.inr e) hE
    · rw [e, partner_c hR]; left; omega
    · rw [e, partner_d hR]; right; omega

/-- **The swap criterion.** For generators of `A_{2n}`, an isomorphism `X → Y` sending `{a, b}`
to `{a', b'}` exists exactly when some generator moves `a` to the other side. -/
theorem iso_iff_exists_gen {gens : Set (Perm (Fin (2 * n)))}
    (hgens : Subgroup.closure gens =
      AutR (2 * n) (GraphData.union n X Y) (unionLev n X Y a b a' b') (2 * n)) :
    (∃ φ, IsIso n X Y φ ∧ SendsEdge n a b a' b' φ) ↔ ∃ g ∈ gens, ¬ EPar a b g := by
  constructor
  · rintro ⟨φ, hφ, he⟩
    have hmem := swapPerm_mem hX hY hab hab' hreach hφ he
    have hE : ¬ EPar a b (swapPerm n φ) := by
      have ha := hX.lt_left hab
      have hb := hX.lt a b hab
      unfold EPar
      rw [act_swapPerm φ (by omega), swapFun_of_lt φ ha]
      omega
    exact exists_gen_swap hX hY hab hab' hgens hmem hE
  · rintro ⟨g, hg, hE⟩
    have hgA := hgens ▸ Subgroup.subset_closure hg
    obtain ⟨φ, -, hφ, he⟩ := exists_iso_of_swap hX hY hab hab' hreach hgA hE
    exact ⟨φ, hφ, he⟩

end Criterion

end GraphIso.Graph
