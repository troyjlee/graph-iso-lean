module

public import GraphIso.Main.M5CJLeaf
public import GraphIso.Case3.Case3Prog

/-!
# Coloured Johnson pairs in M5: the colourings and their canonicity

Stage 14j-4b, item 2 (`PLAN-14.md` §14.5). Align compares `x`'s first Johnson leaf with `y`'s
leaves as coloured pairs `(J, Q)` (`cjohnOps`): `Q` is a canonical colouring of the base, so the
aligned group preserves it and `rd_ns_cj` applies.

* **Case 2b.** `q2bD m Φ S`: colour `0` off `Φ`, `1` on `Φ ∖ S`, `2 + i` at the `i`-th point of the
  individualized tuple `S`. `cjLeaves2bD`: the coloured Johnson leaves of `y` over all tuples and
  pairs, each with its tuple's colouring; `x`'s pair is `(X₀.2.2, q2bD m Φ (firstTupleD Φ j))`,
  the colouring of the tuple of `firstLeafD`.
  - `cj2b_reach`: a permutation `σ` of the base conjugating `ψ(F(x))` to `ψ(F(y))` and carrying
    `Φ(x)` to `Φ(y)` carries `x`'s coloured pair to one of `y`'s. Choice by choice: `x`'s tuple
    `S` goes to `σ(S)`, a tuple of `y`; `lk_choice` and `leafTree_relabel` carry the leaf, and
    the colourings correspond (`get_q2bD_smul`).
  - `cj2b_hq`: every colour class of a listed coloured leaf off `V₀` has at most `m/2` points,
    from `choiceLeavesD_along` and Case 2's condition `m < 2|Φ|`.
  - `cj2b_valid`: the listed pairs are valid (`CJValid` is `JValid`).
* **Case 3.** `q3D M V C`: colour `1` on the dominant class `C`, `2` on the rest of the fixed
  points `V`, `0` on the support. `cjStructs3D`: the coloured Johnson structures of `y` over all
  good lists, each with its good list's colouring; `x`'s pair is `cjFirst3D`, the first
  structure with the colouring of the first good list.
  - `cj3_reach`: if `σ` carries `Vx` onto `Vy` with renumbering `π` and the colourings of the
    `k`-tuples correspond under `π`, then `σ` carries `x`'s coloured pair to one of `y`'s
    (`outTree_transport`, `c3l_outcome`, and the dominant classes by `mem_c3ClsD_wl`).
  - `cj3_hq`: every colour class of a listed coloured structure off `V₀` has at most `M/2`
    points, from `outcomeD_along`, `c3ClsD_facts` and Case 3's condition `M ≤ 2|V|`.
  - `cj3_valid`: the listed pairs are valid.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Pointwise MulAction Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.Coherent
  GraphIso.SoJTree GraphIso.Case2b GraphIso.Align

/-! ### Coloured data from leaves -/

/-- The coloured Johnson datum of a leaf, if it is a Johnson leaf. -/
def cjOfD (q : Array ℕ) (o : OutD) : List CJData := if o.1 = 2 then [(o.2.2, q)] else []

theorem mem_cjOfD {q : Array ℕ} {o : OutD} {Y : CJData} :
    Y ∈ cjOfD q o ↔ o.1 = 2 ∧ Y = (o.2.2, q) := by
  unfold cjOfD
  split_ifs with h <;> simp [h]

/-! ### Permutations of the base on indices -/

section PermIdx

variable {m : ℕ}

/-- A permutation of `Fin m` on base indices: `σ` below `m`, the identity above. -/
def permIdx (σ : Perm (Fin m)) (v : ℕ) : ℕ := if h : v < m then (σ ⟨v, h⟩).val else v

theorem permIdx_fin (σ : Perm (Fin m)) (x : Fin m) : permIdx σ x.val = (σ x).val := by
  simp [permIdx, x.2]

theorem permIdx_injective (σ : Perm (Fin m)) : Function.Injective (permIdx σ) := by
  intro u v h
  unfold permIdx at h
  by_cases hu : u < m <;> by_cases hv : v < m <;> simp only [hu, hv, dite_true, dite_false] at h
  · exact congrArg Fin.val (σ.injective (Fin.ext h))
  · exact absurd (h ▸ (σ ⟨u, hu⟩).2) hv
  · exact absurd (h.symm ▸ (σ ⟨v, hv⟩).2) hu
  · exact h

theorem idxOf_map_injective {f : ℕ → ℕ} (hf : Function.Injective f) (l : List ℕ) (v : ℕ) :
    (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, ih]
    by_cases h : a = v
    · simp [h]
    · have : f a ≠ f v := fun h' => h (hf h')
      simp [h, this]

/-- The image of a list of base indices under `σ`, as a set of `Fin m`. -/
theorem setOf_map_permIdx (σ : Perm (Fin m)) {S : List ℕ} (hS : ∀ s ∈ S, s < m) :
    setOf m (S.map (permIdx σ)) = σ • setOf m S := by
  ext v
  rw [mem_setOf, Finset.mem_smul_finset]
  constructor
  · intro hv
    obtain ⟨u, hu, huv⟩ := List.mem_map.1 hv
    refine ⟨⟨u, hS u hu⟩, mem_setOf.2 hu, Fin.ext ?_⟩
    rw [Perm.smul_def, ← permIdx_fin, huv]
  · rintro ⟨u, hu, rfl⟩
    rw [Perm.smul_def, ← permIdx_fin]
    exact List.mem_map_of_mem (mem_setOf.1 hu)

end PermIdx


/-! ### Arrays written with one value per index -/

section Writes

theorem get_setIfInBounds (arr : Array ℕ) (i x j : ℕ) :
    get (arr.setIfInBounds i x) j = if j = i ∧ j < arr.size then x else get arr j := by
  unfold GraphIso.get
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < arr.size
    · simp [h2]
    · simp [h2]
  · simp [h1, Ne.symm h1]

theorem get_replicate_zero (m v : ℕ) : get (Array.replicate m 0) v = 0 := by
  unfold GraphIso.get
  rw [Array.getD_eq_getD_getElem?]
  by_cases hv : v < m
  · simp [hv]
  · simp [hv]

/-- **Writes with one value per index**: if every write to an index `j` writes `val j`, the
written array holds `val j` at the written indices in range, and the old entry elsewhere. -/
theorem get_applyWrites_fun (val : ℕ → ℕ) :
    ∀ (ws : List (ℕ × ℕ)) (arr : Array ℕ), (∀ w ∈ ws, w.2 = val w.1) → ∀ j,
      get (Prim.applyWrites (a := .nat) arr ws) j =
        if j ∈ ws.map Prod.fst ∧ j < arr.size then val j else get arr j
  | [], arr, _, j => by simp [Prim.applyWrites]
  | w :: ws, arr, hw, j => by
    have e : Prim.applyWrites (a := .nat) arr (w :: ws) =
        Prim.applyWrites (a := .nat) (arr.setIfInBounds w.1 w.2) ws := rfl
    rw [e, get_applyWrites_fun val ws _ (fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')) j,
      Array.size_setIfInBounds, get_setIfInBounds, hw w List.mem_cons_self]
    simp only [List.map_cons, List.mem_cons]
    by_cases hj : j < arr.size
    · by_cases h1 : j = w.1
      · subst h1
        simp [hj]
      · simp only [h1, false_or, false_and, ↓reduceIte]
    · simp [hj]

theorem applyWrites_append {a : Ty} (arr : Array a.denote) (ws₁ ws₂ : List (ℕ × a.denote)) :
    Prim.applyWrites arr (ws₁ ++ ws₂) = Prim.applyWrites (Prim.applyWrites arr ws₁) ws₂ := by
  simp [Prim.applyWrites, List.foldl_append]

end Writes

/-! ### Case 2b -/

section Case2b

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}

/-- The writes of Case 2b's colouring: `1` on `Φ`, then `2 + i` at the `i`-th point of `S`. -/
def q2bWrites (Φ S : List ℕ) : List (ℕ × ℕ) :=
  Φ.map (fun v => (v, 1)) ++ (List.range S.length).map fun i => (S.getD i 0, i + 2)

/-- **The colouring of Case 2b**, on the base indices `[0, m)`: `0` off `Φ`, `1` on `Φ ∖ S`, and
`2 + i` at the `i`-th point of the individualized tuple `S` (`get_q2bD`). -/
def q2bD (m : ℕ) (Φ S : List ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate m 0) (q2bWrites Φ S)

theorem get_q2bD {m : ℕ} {Φ S : List ℕ} (hS : S.Nodup) {v : ℕ} (hv : v < m) :
    get (q2bD m Φ S) v = if v ∈ S then S.idxOf v + 2 else if v ∈ Φ then 1 else 0 := by
  have hwS : ∀ w ∈ (List.range S.length).map (fun i => (S.getD i 0, i + 2)),
      w.2 = (fun v => S.idxOf v + 2) w.1 := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    rw [List.mem_range] at hi
    simp only [List.getD_eq_getElem _ _ hi]
    rw [hS.idxOf_getElem i hi]
  have hwΦ : ∀ w ∈ Φ.map (fun v => (v, 1)), w.2 = (fun _ => 1) w.1 := by
    intro w hw
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hw
    rfl
  have hmS : v ∈ ((List.range S.length).map fun i => (S.getD i 0, i + 2)).map Prod.fst ↔
      v ∈ S := by
    simp only [List.map_map, List.mem_map, List.mem_range, Function.comp]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    · intro h
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
      exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩
  have hmΦ : v ∈ (Φ.map fun v => (v, 1)).map Prod.fst ↔ v ∈ Φ := by simp
  unfold q2bD q2bWrites
  rw [applyWrites_append, get_applyWrites_fun (fun v => S.idxOf v + 2) _ _ hwS v,
    get_applyWrites_fun (fun _ => 1) _ _ hwΦ v,
    size_applyWrites, Array.size_replicate, get_replicate_zero]
  simp only [hmS, hmΦ, hv, and_true]

/-- The first tuple of Case 2b's choices: that of `firstLeafD`. -/
def firstTupleD (Φ : List ℕ) (j : ℕ) : List ℕ := (tuplesD Φ j).headD []

/-- The coloured Johnson leaves of one tuple `S`, over all pairs. -/
def cjChoice2bD (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ S : List ℕ) :
    List CJData :=
  (pairsD (phiSD (N - n) Φ S).length).flatMap fun ab =>
    (choiceLeavesD O N n F Φ S ab.1 ab.2).flatMap (cjOfD (q2bD (N - n) Φ S))

/-- **The coloured Johnson leaves of Case 2b**: every tuple, every pair, every Johnson leaf, with
the tuple's colouring. -/
def cjLeaves2bD (O : Oracle (groupSig D)) (N n : ℕ) (F : GroupData D.denote) (Φ : List ℕ)
    (j : ℕ) : List CJData :=
  (tuplesD Φ j).flatMap (cjChoice2bD O N n F Φ)

/-- `x`'s coloured pair in Case 2b: the first leaf with the colouring of the first tuple. -/
def cjFirst2bD (N n : ℕ) (Φ : List ℕ) (j : ℕ) (X₀ : OutD) : CJData :=
  (X₀.2.2, q2bD (N - n) Φ (firstTupleD Φ j))

theorem mem_cjLeaves2bD {N n : ℕ} {F : GroupData D.denote} {Φ : List ℕ} {j : ℕ} {Y : CJData} :
    Y ∈ cjLeaves2bD O N n F Φ j ↔ ∃ S ∈ tuplesD Φ j, ∃ ab ∈ pairsD (phiSD (N - n) Φ S).length,
      ∃ o ∈ choiceLeavesD O N n F Φ S ab.1 ab.2, o.1 = 2 ∧ Y = (o.2.2, q2bD (N - n) Φ S) := by
  simp only [cjLeaves2bD, cjChoice2bD, List.mem_flatMap, mem_cjOfD]

/-- The first leaf comes from the first tuple. -/
theorem firstLeafD_firstTuple {N n : ℕ} {F : GroupData D.denote} {Φ : List ℕ} {j : ℕ}
    {X₀ : OutD} (h : firstLeafD O N n F Φ j = some X₀) :
    firstTupleD Φ j ∈ tuplesD Φ j ∧ X₀ ∈ choiceLeavesD O N n F Φ (firstTupleD Φ j) 0 1 := by
  unfold firstLeafD at h
  unfold firstTupleD
  rcases hT : tuplesD Φ j with _ | ⟨S, rest⟩
  · rw [hT] at h
    simp at h
  · rw [hT] at h
    exact ⟨List.mem_cons_self, List.mem_of_mem_head? h⟩

/-- **The colourings correspond**: if `σ` carries `Φ(x)` to `Φ(y)`, it carries the colouring of
a tuple `S` of `x` to that of `σ(S)`. -/
theorem get_q2bD_smul {m : ℕ} (σ : Perm (Fin m)) {Φx Φy S : List ℕ} (hS : S.Nodup)
    (hΦ : σ • setOf m Φx = setOf m Φy) (x : Fin m) :
    get (q2bD m Φy (S.map (permIdx σ))) (σ x).val = get (q2bD m Φx S) x.val := by
  rw [get_q2bD (hS.map (permIdx_injective σ)) (σ x).2, get_q2bD hS x.2, ← permIdx_fin]
  have hΦx : permIdx σ x.val ∈ Φy ↔ x.val ∈ Φx := by
    rw [permIdx_fin, ← mem_setOf, ← mem_setOf, ← hΦ, show σ x = σ • x from rfl,
      Finset.smul_mem_smul_finset_iff]
  rw [idxOf_map_injective (permIdx_injective σ)]
  simp only [List.mem_map, (permIdx_injective σ).eq_iff, exists_eq_right, hΦx]

end Case2b

section Case2bReach

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}

/-- **Canonicity of Case 2b's coloured pairs.** If `σ` conjugates `ψ(F(x))` to `ψ(F(y))` and
carries `Φ(x)` to `Φ(y)`, it carries `x`'s coloured first leaf to one of `y`'s coloured Johnson
leaves: `x`'s tuple `S` goes to the tuple `σ(S)` of `y` (`setOf_map_permIdx`), the leaf goes to a
leaf of that tuple and the transported pair (`lk_choice`, `leafTree_relabel`), and the colourings
correspond (`get_q2bD_smul`). -/
theorem cj2b_reach (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {fxs fys : GensData}
    {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex) (hFyv : GroupValid DV N fys ey)
    (hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N))
    (hFyi : IsInvariant (GensData.denote N fys) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N fxs) n hFxi).range)]
    [DecidablePred (· ∈ (baseHom (GensData.denote N fys) n hFyi).range)]
    {Φx Φy : List ℕ} (hΦxl : ∀ v ∈ Φx, v < N - n) (hΦyl : ∀ v ∈ Φy, v < N - n) {j : ℕ}
    (Hx : Case2bHyp (baseHom _ n hFxi).range (setOf (N - n) Φx) (j + 1))
    (Hy : Case2bHyp (baseHom _ n hFyi).range (setOf (N - n) Φy) (j + 1))
    (σ : Perm (Fin (N - n)))
    (hP : ∀ h, h ∈ (baseHom _ n hFyi).range ↔ σ⁻¹ * h * σ ∈ (baseHom _ n hFxi).range)
    (hΦ : σ • setOf (N - n) Φx = setOf (N - n) Φy)
    {X₀ : OutD} (hfirst : firstLeafD O N n (N, fxs, ex) Φx j = some X₀) (h2 : X₀.1 = 2) :
    ∃ Y ∈ cjLeaves2bD O N n (N, fys, ey) Φy j,
      σ • cjdec (N - n) (cjFirst2bD N n Φx j X₀) = cjdec (N - n) Y := by
  classical
  obtain ⟨hS₀, hX₀⟩ := firstLeafD_firstTuple hfirst
  -- the x side
  obtain ⟨hSlx, hsubx, hcardx⟩ := lk_tuple hΦxl hS₀
  have hposx : 4 ≤ (phiSD (N - n) Φx (firstTupleD Φx j)).length := lk_four hΦxl Hx hS₀
  have hrx : ∀ v, (∃ i, phiE (N - n) Φx (firstTupleD Φx j) i = v) ↔
      v ∈ setOf (N - n) Φx \ setOf (N - n) (firstTupleD Φx j) := phiE_range
  have htrx := lk_pretrans Hx.pres hrx (Hx.trans _ hsubx hcardx)
  have hmsx := lk_choice hO hFxv hFxi Hx.pres hSlx htrx (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩
  have hreach : (leafTree (baseHom _ n hFxi).range (setOf (N - n) (firstTupleD Φx j))
      (phiE (N - n) Φx (firstTupleD Φx j) ⟨0, by omega⟩)
      (phiE (N - n) Φx (firstTupleD Φx j) ⟨1, by omega⟩)
      (phiE (N - n) Φx (firstTupleD Φx j))).Reach (decodeOut (N - n) X₀) := by
    rw [← CTree.mem_leafMs, ← hmsx, Multiset.mem_coe]
    exact List.mem_map_of_mem hX₀
  -- the tuple of `y`
  have hS₁set : setOf (N - n) ((firstTupleD Φx j).map (permIdx σ)) =
      σ • setOf (N - n) (firstTupleD Φx j) := setOf_map_permIdx σ hSlx
  have hS₁ : (firstTupleD Φx j).map (permIdx σ) ∈ tuplesD Φy j := by
    obtain ⟨hlen, hnd, hmem⟩ := (mem_tuplesD Φx j).1 hS₀
    refine (mem_tuplesD Φy j).2 ⟨by rw [List.length_map, hlen],
      hnd.map (permIdx_injective σ), fun v hv => ?_⟩
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
    have hu' : (⟨u, hSlx u hu⟩ : Fin (N - n)) ∈ setOf (N - n) Φx := mem_setOf.2 (hmem u hu)
    have := Finset.smul_mem_smul_finset (a := σ) hu'
    rw [hΦ, mem_setOf] at this
    rwa [permIdx_fin σ ⟨u, hSlx u hu⟩]
  obtain ⟨hSly, hsuby, hcardy⟩ := lk_tuple hΦyl hS₁
  have hry : ∀ v, (∃ i, phiE (N - n) Φy ((firstTupleD Φx j).map (permIdx σ)) i = v) ↔
      v ∈ setOf (N - n) Φy \ setOf (N - n) ((firstTupleD Φx j).map (permIdx σ)) := phiE_range
  have htry := lk_pretrans Hy.pres hry (Hy.trans _ hsuby hcardy)
  have hsd : setOf (N - n) Φy \ setOf (N - n) ((firstTupleD Φx j).map (permIdx σ)) =
      σ • (setOf (N - n) Φx \ setOf (N - n) (firstTupleD Φx j)) := by
    rw [hS₁set, ← hΦ, Finset.smul_finset_sdiff]
  have hlen : (phiSD (N - n) Φy ((firstTupleD Φx j).map (permIdx σ))).length =
      (phiSD (N - n) Φx (firstTupleD Φx j)).length := by
    rw [← lk_card_phi, ← lk_card_phi, hsd, Finset.card_smul_finset]
  have hrange : ∀ v, (∃ i, phiE (N - n) Φy ((firstTupleD Φx j).map (permIdx σ)) i = v) ↔
      ∃ i, phiE (N - n) Φx (firstTupleD Φx j) i = σ⁻¹ v := by
    intro v
    rw [hry, hrx, hsd, Finset.mem_smul_finset]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rwa [Perm.smul_def, perm_inv_apply_self]
    · intro h
      exact ⟨σ⁻¹ v, h, by rw [Perm.smul_def, perm_apply_inv_self]⟩
  have hrel := leafTree_relabel σ hP (setOf (N - n) (firstTupleD Φx j))
    (phiE (N - n) Φx (firstTupleD Φx j) ⟨0, by omega⟩)
    (phiE (N - n) Φx (firstTupleD Φx j) ⟨1, by omega⟩) (phiE (N - n) Φx (firstTupleD Φx j))
    (phiE (N - n) Φy ((firstTupleD Φx j).map (permIdx σ))) hlen hrange
  have hreach' := (SplitJohnson.CTree.reach_act σ).2 hreach
  rw [← hrel] at hreach'
  -- the transported pair in `y`'s numbering
  obtain ⟨a', ha'⟩ := (hrange (σ (phiE (N - n) Φx (firstTupleD Φx j) ⟨0, by omega⟩))).2
    ⟨_, by rw [perm_inv_apply_self]⟩
  obtain ⟨b', hb'⟩ := (hrange (σ (phiE (N - n) Φx (firstTupleD Φx j) ⟨1, by omega⟩))).2
    ⟨_, by rw [perm_inv_apply_self]⟩
  have hab' : a' ≠ b' := by
    intro h
    rw [h] at ha'
    have e := (phiE (N - n) Φx (firstTupleD Φx j)).injective (σ.injective (ha'.symm.trans hb'))
    exact absurd (congrArg Fin.val e) (by simp)
  have hmsy := lk_choice hO hFyv hFyi Hy.pres hSly htry (by omega) a' b'
  rw [hS₁set, ha', hb'] at hmsy
  have hmem : σ • decodeOut (N - n) X₀ ∈ (((choiceLeavesD O N n (N, fys, ey) Φy
      ((firstTupleD Φx j).map (permIdx σ)) a' b').map (decodeOut (N - n)) :
        List (Option (Out (Fin (N - n))))) : Multiset (Option (Out (Fin (N - n))))) := by
    rw [hmsy]
    exact CTree.mem_leafMs.2 hreach'
  rw [Multiset.mem_coe] at hmem
  obtain ⟨Y, hY, hYe⟩ := List.mem_map.1 hmem
  -- `Y` is a Johnson leaf, the image of `X₀`
  rw [ld_decodeOut_two h2, oo_smul_inr] at hYe
  have hY2 : Y.1 = 2 := by
    unfold decodeOut at hYe
    split_ifs at hYe with h1 h1'
    · simp at hYe
    · exact h1'
  rw [ld_decodeOut_two hY2] at hYe
  have hJ : σ • jdec (N - n) X₀.2.2 = jdec (N - n) Y.2.2 :=
    (Sum.inr_injective (Option.some_injective _ hYe)).symm
  refine ⟨(Y.2.2, q2bD (N - n) Φy ((firstTupleD Φx j).map (permIdx σ))),
    mem_cjLeaves2bD.2 ⟨_, hS₁, (a'.val, b'.val),
      Case2b.mem_pairsD.2 ⟨a'.2, b'.2, fun h => hab' (Fin.ext h)⟩, Y, hY, hY2, rfl⟩, ?_⟩
  exact cj_smul_of hJ fun x _ => get_q2bD_smul σ ((mem_tuplesD Φx j).1 hS₀).2.1 hΦ x

/-- **The colour bound of Case 2b**: every colour class of a listed coloured Johnson leaf off
`V₀` has at most `m/2` points. The leaf lies along `Φ ∖ S` (`choiceLeavesD_along`), coloured `1`;
off it, the colour `0` (off `Φ`) has `m − |Φ| < m/2` points by Case 2's condition, and each
colour `2 + i` is one point of `S`. -/
theorem cj2b_hq (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φ S : List ℕ} {j : ℕ}
    (hΦn : Φ.Nodup) (hΦl : ∀ v ∈ Φ, v < N - n) (hΦ2 : N - n < 2 * Φ.length)
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φ) (j + 1))
    (hS : S ∈ tuplesD Φ j) {a b : ℕ} (hab : (a, b) ∈ pairsD (phiSD (N - n) Φ S).length)
    {o : OutD} (ho : o ∈ choiceLeavesD O N n (N, gs, d) Φ S a b) (h2 : o.1 = 2) (c : ℕ) :
    2 * (univ.filter fun γ => γ ∉ (jdec (N - n) o.2.2).V0 ∧
      cjcol (N - n) (o.2.2, q2bD (N - n) Φ S) γ = c).card ≤ N - n := by
  classical
  have hal := choiceLeavesD_along hO hFv hF hΦl H hS hab ho h2
  obtain ⟨-, hSnd, -⟩ := (mem_tuplesD Φ j).1 hS
  have hm4 : 4 ≤ N - n := (lk_four hΦl H hS).trans (length_phiSD_le _ _ _)
  have hΦm : Φ.length ≤ N - n := by
    rw [← lk_setOf_card hΦn hΦl]
    simpa using card_le_univ (setOf (N - n) Φ)
  refine cj_hq_of_along hal (c₁ := 1) (fun v hv => ?_) (fun v hv => ?_) (fun c' => ?_) c
  · obtain ⟨-, h1, h3⟩ := mem_phiSD.1 hv
    rw [get_q2bD hSnd v.2]
    simp [h1, h3]
  · rw [get_q2bD hSnd v.2]
    rw [mem_phiSD] at hv
    split_ifs with h1 h3
    · omega
    · exact absurd ⟨v.2, h3, h1⟩ hv
    · omega
  · by_cases hc0 : c' = 0
    · subst hc0
      have hsub : (univ.filter fun v : Fin (N - n) =>
          v.val ∉ phiSD (N - n) Φ S ∧ get (q2bD (N - n) Φ S) v.val = 0) ⊆
          univ \ setOf (N - n) Φ := by
        intro v hv
        obtain ⟨-, -, hq⟩ := mem_filter.1 hv
        rw [get_q2bD hSnd v.2] at hq
        refine mem_sdiff.2 ⟨mem_univ _, fun hΦv => ?_⟩
        rw [mem_setOf] at hΦv
        by_cases hvS : v.val ∈ S <;> simp [hvS, hΦv] at hq
      have hc := card_le_card hsub
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
        lk_setOf_card hΦn hΦl] at hc
      omega
    · have hle : (univ.filter fun v : Fin (N - n) =>
          v.val ∉ phiSD (N - n) Φ S ∧ get (q2bD (N - n) Φ S) v.val = c').card ≤ 1 := by
        refine Finset.card_le_one.2 fun u hu w hw => ?_
        obtain ⟨-, hu₁, hu₂⟩ := mem_filter.1 hu
        obtain ⟨-, hw₁, hw₂⟩ := mem_filter.1 hw
        rw [get_q2bD hSnd u.2] at hu₂
        rw [get_q2bD hSnd w.2] at hw₂
        rw [mem_phiSD] at hu₁ hw₁
        by_cases huS : u.val ∈ S
        · by_cases hwS : w.val ∈ S
          · simp only [huS, ↓reduceIte] at hu₂
            simp only [hwS, ↓reduceIte] at hw₂
            exact Fin.ext ((List.idxOf_inj huS).1 (by omega))
          · simp only [huS, ↓reduceIte] at hu₂
            simp only [hwS, ↓reduceIte] at hw₂
            split_ifs at hw₂ with h
            · exact absurd ⟨w.2, h, hwS⟩ hw₁
            · omega
        · simp only [huS, ↓reduceIte] at hu₂
          split_ifs at hu₂ with h
          · exact absurd ⟨u.2, h, huS⟩ hu₁
          · omega
      omega

/-- **The listed coloured leaves of Case 2b are valid** (`CJValid` is `JValid` of the leaf's
embedding). -/
theorem cj2b_valid (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φ : List ℕ} {j : ℕ}
    (hΦn : Φ.Nodup) (hΦl : ∀ v ∈ Φ, v < N - n)
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φ) (j + 1)) :
    ∀ Y ∈ cjLeaves2bD O N n (N, gs, d) Φ j, CJValid (N - n) Y := by
  intro Y hY
  obtain ⟨S, hS, ab, hab, o, ho, h2, rfl⟩ := mem_cjLeaves2bD.1 hY
  have hmem : o ∈ allLeavesD O N n (N, gs, d) Φ j :=
    List.mem_flatMap.2 ⟨S, hS, List.mem_flatMap.2 ⟨ab, hab, ho⟩⟩
  rcases allLeavesD_valid (F := (N, gs, d)) hO rfl hFv hF hΦn hΦl H o hmem with ⟨h1, -⟩ | ⟨-, hv⟩
  · omega
  · exact hv

end Case2bReach

/-! ### Case 3 -/

section Case3

open GraphIso.Case3

/-- The writes of Case 3's colouring: `2` on `V`, then `1` on `C`. -/
def q3Writes (V C : List ℕ) : List (ℕ × ℕ) := V.map (fun v => (v, 2)) ++ C.map fun v => (v, 1)

/-- **The colouring of Case 3**, on the base indices `[0, M)`: `1` on the dominant class `C`, `2`
on the rest of the fixed points `V`, `0` on the support (`get_q3D`). -/
def q3D (M : ℕ) (V C : List ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate M 0) (q3Writes V C)

theorem get_q3D {M : ℕ} {V C : List ℕ} {v : ℕ} (hv : v < M) :
    get (q3D M V C) v = if v ∈ C then 1 else if v ∈ V then 2 else 0 := by
  have hwC : ∀ w ∈ C.map (fun v => (v, 1)), w.2 = (fun _ => 1) w.1 := by
    intro w hw
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hw
    rfl
  have hwV : ∀ w ∈ V.map (fun v => (v, 2)), w.2 = (fun _ => 2) w.1 := by
    intro w hw
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hw
    rfl
  have hmC : v ∈ (C.map fun v => (v, 1)).map Prod.fst ↔ v ∈ C := by simp
  have hmV : v ∈ (V.map fun v => (v, 2)).map Prod.fst ↔ v ∈ V := by simp
  unfold q3D q3Writes
  rw [applyWrites_append, get_applyWrites_fun (fun _ => 1) _ _ hwC v,
    get_applyWrites_fun (fun _ => 2) _ _ hwV v,
    size_applyWrites, Array.size_replicate, get_replicate_zero]
  simp only [hmC, hmV, hv, and_true]

/-- The coloured Johnson structures at a good list `z`, with `z`'s colouring. -/
def cjOutcome3D (M k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) : List CJData :=
  (outcomeD M k V W z).flatMap (cjOfD (q3D M V (c3ClsD k V W z)))

/-- **The coloured Johnson structures of Case 3**: every good list, every Johnson structure, with
the good list's colouring. -/
def cjStructs3D (M k : ℕ) (V : List ℕ) (col : Array ℕ) : List CJData :=
  (goodListsD k V.length (wlCD k V.length col)).flatMap (cjOutcome3D M k V (wlCD k V.length col))

/-- The first good list: that of `firstStructD`. -/
def firstGoodD (k : ℕ) (V : List ℕ) (col : Array ℕ) : List ℕ :=
  (goodListsD k V.length (wlCD k V.length col)).headD []

/-- `x`'s coloured pair in Case 3: the first structure with the colouring of the first good
list. -/
def cjFirst3D (M k : ℕ) (V : List ℕ) (col : Array ℕ) (X₀ : OutD) : CJData :=
  (X₀.2.2, q3D M V (c3ClsD k V (wlCD k V.length col) (firstGoodD k V col)))

theorem mem_cjStructs3D {M k : ℕ} {V : List ℕ} {col : Array ℕ} {Y : CJData} :
    Y ∈ cjStructs3D M k V col ↔ ∃ z ∈ goodListsD k V.length (wlCD k V.length col),
      ∃ o ∈ outcomeD M k V (wlCD k V.length col) z, o.1 = 2 ∧
        Y = (o.2.2, q3D M V (c3ClsD k V (wlCD k V.length col) z)) := by
  simp only [cjStructs3D, cjOutcome3D, List.mem_flatMap, mem_cjOfD]

/-- The first structure comes from the first good list. -/
theorem firstStructD_firstGood {M k : ℕ} {V : List ℕ} {col : Array ℕ} {X₀ : OutD}
    (h : firstStructD M k V col = some X₀) :
    firstGoodD k V col ∈ goodListsD k V.length (wlCD k V.length col) ∧
      X₀ ∈ outcomeD M k V (wlCD k V.length col) (firstGoodD k V col) := by
  unfold firstStructD at h
  unfold firstGoodD
  rcases hg : goodListsD k V.length (wlCD k V.length col) with _ | ⟨z, zs⟩
  · rw [hg] at h
    simp at h
  · rw [hg] at h
    exact ⟨List.mem_cons_self, List.mem_of_mem_head? h⟩

/-- **The outcome moves with a renumbering.** If `σ` and the renumbering `π` relate the
numberings `e₁`, `e₂` and the colourings `c₁`, `c₂`, then at the list `z` and its image: the
outcome moves by `σ`, goodness is preserved, and the dominant classes correspond. -/
theorem outTree_transport {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (σ : Perm Γ) {k m₁ m₂ : ℕ}
    (hm : m₁ = m₂) (c₁ : (Fin k → Fin m₁) → ℕ) (c₂ : (Fin k → Fin m₂) → ℕ)
    (e₁ : Fin m₁ ↪ Γ) (e₂ : Fin m₂ ↪ Γ) (π : Perm (Fin m₁))
    (he : ∀ a, e₂ (Fin.cast hm (π a)) = σ (e₁ a))
    (hc : ∀ T : Fin k → Fin m₁, c₂ (Fin.cast hm ∘ π ∘ T) = c₁ T) (z : List (Fin m₁)) :
    outTree (wl k m₂ c₂).1 e₂ (z.map (Fin.cast hm ∘ π)) = (outTree (wl k m₁ c₁).1 e₁ z).act σ ∧
      (DLGood (wl k m₂ c₂).1 (thr m₂) (z.map (Fin.cast hm ∘ π)) ↔
        DLGood (wl k m₁ c₁).1 (thr m₁) z) ∧
      ((domPts (wl k m₂ c₂).1 (z.map (Fin.cast hm ∘ π))).Nonempty ↔
        (domPts (wl k m₁ c₁).1 z).Nonempty) ∧
      ∀ (h₁ : (domPts (wl k m₁ c₁).1 z).Nonempty)
        (h₂ : (domPts (wl k m₂ c₂).1 (z.map (Fin.cast hm ∘ π))).Nonempty) (v : Γ),
        (∃ i ∈ domCls (wl k m₂ c₂).1 (z.map (Fin.cast hm ∘ π)) h₂, e₂ i = σ v) ↔
          ∃ i ∈ domCls (wl k m₁ c₁).1 z h₁, e₁ i = v := by
  subst hm
  have hc' : c₂ = fun T => c₁ (⇑π⁻¹ ∘ T) := by
    funext T
    rw [← hc]
    congr 1
    funext i
    simp
  have hW : ∀ y, (wl k m₁ c₂).1 (⇑π ∘ y) = (wl k m₁ c₁).1 y := fun y => by
    rw [hc', wl_relabel]
    show (wl k m₁ c₁).1 (⇑π⁻¹ ∘ ⇑π ∘ y) = _
    rw [show ⇑π⁻¹ ∘ ⇑π ∘ y = y from funext fun i => by simp]
  have hmap : z.map (Fin.cast rfl ∘ ⇑π) = z.map π := rfl
  rw [hmap]
  refine ⟨outTree_relabel σ π hW he z,
    SplitJohnson.BipRelabel.dlGood_map (π : Fin m₁ ≃ Fin m₁) hW _ z,
    domPts_nonempty_relabel π hW z, fun h₁ h₂ v => ?_⟩
  rw [domCls_relabel π hW z h₁ h₂]
  constructor
  · rintro ⟨i, hi, hiv⟩
    rw [Finset.mem_map_equiv] at hi
    refine ⟨π.symm i, hi, σ.injective ?_⟩
    rw [← hiv, ← he]
    simp
  · rintro ⟨i, hi, rfl⟩
    exact ⟨π i, Finset.mem_map_of_mem _ hi, he i⟩

/-- The dominant class of the data, for the colouring `col` (`mem_c3ClsD_iff` through
`toFun_wlCD`). -/
theorem mem_c3ClsD_wl {M k : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup)
    (col : Array ℕ) (x : List (Fin V.length))
    (hdom : (domPts (wl k V.length (toFun col)).1 x).Nonempty) (v : Fin M) :
    v.val ∈ c3ClsD k V (wlCD k V.length col) (x.map Fin.val) ↔
      ∃ i ∈ domCls (wl k V.length (toFun col)).1 x hdom, lkE V hV hnd i = v := by
  revert hdom
  rw [← toFun_wlCD (k := k)]
  intro hdom
  exact mem_c3ClsD_iff hV hnd _ x hdom v

/-- **Canonicity of Case 3's coloured pairs.** If `σ` carries the fixed points `Vx` onto `Vy`
with renumbering `π`, and the colourings are related by `π`, then `σ` carries `x`'s coloured
first structure to one of `y`'s coloured Johnson structures: `x`'s first good list `z` goes to
`π(z)`, a good list of `y` (`outTree_transport`), the structure to a structure there
(`c3l_outcome`), and the dominant classes, hence the colourings, correspond
(`mem_c3ClsD_wl`). -/
theorem cj3_reach {M k : ℕ} {Vx Vy : List ℕ} (hVx : ∀ v ∈ Vx, v < M) (hVxn : Vx.Nodup)
    (hVy : ∀ v ∈ Vy, v < M) (hVyn : Vy.Nodup) (hlen : Vx.length = Vy.length)
    (σ : Perm (Fin M)) (hσ : ∀ v : Fin M, (σ v).val ∈ Vy ↔ v.val ∈ Vx)
    (π : Perm (Fin Vx.length))
    (hπ : ∀ a, lkE Vy hVy hVyn (Fin.cast hlen (π a)) = σ (lkE Vx hVx hVxn a))
    {cX cY : Array ℕ} (hcol : ∀ T : Fin k → Fin Vx.length, toFun cY (⇑π ∘ T) = toFun cX T)
    {X₀ : OutD} (hfirst : firstStructD M k Vx cX = some X₀) (h2 : X₀.1 = 2) :
    ∃ Y ∈ cjStructs3D M k Vy cY, σ • cjdec M (cjFirst3D M k Vx cX X₀) = cjdec M Y := by
  classical
  obtain ⟨hz₀, hX₀⟩ := firstStructD_firstGood hfirst
  obtain ⟨x₀, hx₀k, hz₀e, hgood⟩ := mem_goodListsD.1 hz₀
  rw [hz₀e] at hX₀
  have hmsx := c3l_outcome (k := k) hVx hVxn cX x₀
  have hreach : (outTree (wl k Vx.length (toFun cX)).1 (lkE Vx hVx hVxn) x₀).Reach
      (decodeOut M X₀) := by
    rw [← CTree.mem_leafMs, ← hmsx, Multiset.mem_coe]
    exact List.mem_map_of_mem hX₀
  obtain ⟨hT, hG, -, hD⟩ := outTree_transport σ hlen (toFun (k := k) cX) (toFun (k := k) cY)
    (lkE Vx hVx hVxn) (lkE Vy hVy hVyn) π hπ
    (fun T => (c3p_toFun_cast hlen cY (⇑π ∘ T)).symm.trans (hcol T)) x₀
  set x₁ := x₀.map (Fin.cast hlen ∘ ⇑π) with hx₁
  have hreach' : (outTree (wl k Vy.length (toFun cY)).1 (lkE Vy hVy hVyn) x₁).Reach
      (σ • decodeOut M X₀) := by
    rw [hT]
    exact (SplitJohnson.CTree.reach_act σ).2 hreach
  have hgood' : DLGood (wl k Vx.length (toFun cX)).1 (thr Vx.length) x₀ := by
    rw [← toFun_wlCD (k := k)]
    exact hgood
  have hz₁ : x₁.map Fin.val ∈ goodListsD k Vy.length (wlCD k Vy.length cY) := by
    refine mem_goodListsD.2 ⟨x₁, by rw [hx₁, List.length_map]; exact hx₀k, rfl, ?_⟩
    have := hG.2 hgood'
    rw [← toFun_wlCD (k := k)] at this
    exact this
  have hmsy := c3l_outcome (k := k) hVy hVyn cY x₁
  have hmem : σ • decodeOut M X₀ ∈ (((outcomeD M k Vy (wlCD k Vy.length cY)
      (x₁.map Fin.val)).map (decodeOut M) : List (Option (Out (Fin M)))) :
        Multiset (Option (Out (Fin M)))) := by
    rw [hmsy]
    exact CTree.mem_leafMs.2 hreach'
  rw [Multiset.mem_coe] at hmem
  obtain ⟨Y, hY, hYe⟩ := List.mem_map.1 hmem
  rw [ld_decodeOut_two h2, oo_smul_inr] at hYe
  have hY2 : Y.1 = 2 := by
    unfold decodeOut at hYe
    split_ifs at hYe with h1 h1'
    · simp at hYe
    · exact h1'
  rw [ld_decodeOut_two hY2] at hYe
  have hJ : σ • jdec M X₀.2.2 = jdec M Y.2.2 :=
    (Sum.inr_injective (Option.some_injective _ hYe)).symm
  -- the dominant classes correspond
  have hdx : (domPts (wl k Vx.length (toFun cX)).1 x₀).Nonempty := by
    rw [← toFun_wlCD (k := k)]
    exact domPts_of_john _ x₀ hX₀ h2
  have hdy : (domPts (wl k Vy.length (toFun cY)).1 x₁).Nonempty := by
    rw [← toFun_wlCD (k := k)]
    exact domPts_of_john _ x₁ hY hY2
  have hcls : ∀ v : Fin M, (σ v).val ∈ c3ClsD k Vy (wlCD k Vy.length cY) (x₁.map Fin.val) ↔
      v.val ∈ c3ClsD k Vx (wlCD k Vx.length cX) (x₀.map Fin.val) := fun v => by
    rw [mem_c3ClsD_wl hVy hVyn cY x₁ hdy, mem_c3ClsD_wl hVx hVxn cX x₀ hdx]
    exact hD hdx hdy v
  refine ⟨(Y.2.2, q3D M Vy (c3ClsD k Vy (wlCD k Vy.length cY) (x₁.map Fin.val))),
    mem_cjStructs3D.2 ⟨_, hz₁, Y, hY, hY2, rfl⟩, ?_⟩
  unfold cjFirst3D
  rw [hz₀e]
  refine cj_smul_of hJ fun v _ => ?_
  rw [get_q3D (σ v).2, get_q3D v.2]
  simp only [hcls, hσ]

/-- **The colour bound of Case 3**: every colour class of a listed coloured Johnson structure
off `V₀` has at most `M/2` points. The structure lies along the dominant class `C`
(`outcomeD_along`), coloured `1`; off it, the colour `0` (the support) has `M − |V| ≤ M/2` points
by Case 3's condition, and the colour `2` (`V ∖ C`) fewer than `|V|/2`, since `C` has more than
`(|V| + 1)/2` points (`c3ClsD_facts`). -/
theorem cj3_hq {M k : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hm : 6 ≤ V.length) (hV2 : M ≤ 2 * V.length) {z : List ℕ}
    (hz : z ∈ goodListsD k V.length (wlCD k V.length col)) {o : OutD}
    (ho : o ∈ outcomeD M k V (wlCD k V.length col) z) (h2 : o.1 = 2) (c : ℕ) :
    2 * (univ.filter fun γ => γ ∉ (jdec M o.2.2).V0 ∧
      cjcol M (o.2.2, q3D M V (c3ClsD k V (wlCD k V.length col) z)) γ = c).card ≤ M := by
  classical
  have hal := outcomeD_along hV hnd col hm hz ho h2
  obtain ⟨x, -, rfl, -⟩ := mem_goodListsD.1 hz
  obtain ⟨hCnd, hCV, hClen⟩ := c3ClsD_facts hnd _ x (domPts_of_john _ x ho h2)
  set C := c3ClsD k V (wlCD k V.length col) (x.map Fin.val) with hCdef
  have hVM : V.length ≤ M := by
    rw [← lk_setOf_card hnd hV]
    simpa using card_le_univ (setOf M V)
  have hCsub : setOf M C ⊆ setOf M V := fun v hv => mem_setOf.2 (hCV _ (mem_setOf.1 hv))
  have hClt : ∀ v ∈ C, v < M := fun v hv => hV v (hCV v hv)
  refine cj_hq_of_along hal (c₁ := 1) (fun v hv => ?_) (fun v hv => ?_) (fun c' => ?_) c
  · rw [get_q3D v.2]
    simp [hv]
  · rw [get_q3D v.2]
    simp only [hv, ↓reduceIte]
    split_ifs <;> omega
  · by_cases hc0 : c' = 0
    · subst hc0
      have hsub : (univ.filter fun v : Fin M => v.val ∉ C ∧ get (q3D M V C) v.val = 0) ⊆
          univ \ setOf M V := by
        intro v hv
        obtain ⟨-, hvC, hq⟩ := mem_filter.1 hv
        rw [get_q3D v.2] at hq
        refine mem_sdiff.2 ⟨mem_univ _, fun hVv => ?_⟩
        rw [mem_setOf] at hVv
        simp [hvC, hVv] at hq
      have hc := card_le_card hsub
      rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin,
        lk_setOf_card hnd hV] at hc
      omega
    · by_cases hc2 : c' = 2
      · subst hc2
        have hsub : (univ.filter fun v : Fin M => v.val ∉ C ∧ get (q3D M V C) v.val = 2) ⊆
            setOf M V \ setOf M C := by
          intro v hv
          obtain ⟨-, hvC, hq⟩ := mem_filter.1 hv
          rw [get_q3D v.2] at hq
          refine mem_sdiff.2 ⟨mem_setOf.2 ?_, fun h => hvC (mem_setOf.1 h)⟩
          by_contra hVv
          simp [hvC, hVv] at hq
        have hc := card_le_card hsub
        rw [card_sdiff_of_subset hCsub, lk_setOf_card hnd hV, lk_setOf_card hCnd hClt] at hc
        unfold tOf at hClen
        omega
      · have hemp : (univ.filter fun v : Fin M => v.val ∉ C ∧ get (q3D M V C) v.val = c') =
            ∅ := by
          refine Finset.filter_eq_empty_iff.2 fun v _ ⟨hvC, hq⟩ => ?_
          rw [get_q3D v.2] at hq
          simp only [hvC, ↓reduceIte] at hq
          split_ifs at hq <;> omega
        rw [hemp, card_empty]
        omega

/-- **The listed coloured structures of Case 3 are valid** (`CJValid` is `JValid` of the
structure's embedding; no twin hypothesis, `c3p_allStructsD_valid`). -/
theorem cj3_valid {M k : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup) (col : Array ℕ)
    (hm : 6 ≤ V.length) : ∀ Y ∈ cjStructs3D M k V col, CJValid M Y := by
  intro Y hY
  obtain ⟨z, hz, o, ho, h2, rfl⟩ := mem_cjStructs3D.1 hY
  rcases c3p_allStructsD_valid hV hnd col hm o (mem_allStructsD.2 ⟨z, hz, ho⟩) with
    ⟨h1, -⟩ | ⟨-, hv⟩
  · omega
  · exact hv

end Case3

end GraphIso.Main
