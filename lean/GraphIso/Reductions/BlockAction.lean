module

public import GraphIso.Reductions.Blocks
public import GraphIso.Reductions.RestrictionData

/-!
# The induced action on blocks

For a block list `bs` (`k` blocks) of a valid window of degree `n`, and a group `G` permuting
the blocks:

* `blockIdx n bs`: the array giving, for each listed point, the index of its block
  (`get_blockIdx`);
* `blockMap g i`: the index of the block containing `g` of the first point of block `i`. It
  is a permutation of the block indices (`blockPerm`), multiplicative in `g`;
* `extendHom : G →* Perm (Fin (n + k))`: `g` on the first `n` points and its action on block
  indices on the last `k` (`extendHom_apply_lt`, `extendHom_apply_ge`). It is injective;
* `PermData.extendTo`: the represented extension, equal to `ofPerm (extendHom g)`
  (`extendTo_eq`);
* `mem_pointwiseStab_extend`: the elements of the extended group fixing every block point are
  exactly the extensions of the block kernel;
* `restrict_extend`: restricting an extension to the first `n` points recovers `g`.
-/

@[expose] public section

namespace GraphIso

open Equiv Cost

/-! ### Block indices -/

/-- One step of the block-index writes: write `(u, i)` for every point `u` of block `b`. -/
def blockWritesStep (acc : ℕ × List (ℕ × ℕ)) (b : List ℕ) : ℕ × List (ℕ × ℕ) :=
  (acc.1 + 1, b.map (fun u => (u, acc.1)) ++ acc.2)

/-- The writes `(u, i)` for every point `u` of the `i`-th block. -/
def blockWrites (bs : List (List ℕ)) : List (ℕ × ℕ) := (bs.foldl blockWritesStep (0, [])).2

theorem blockWrites_fold (bs : List (List ℕ)) :
    ∀ (i : ℕ) (ws : List (ℕ × ℕ)),
      (bs.foldl blockWritesStep (i, ws)).1 = i + bs.length ∧
      ((bs.foldl blockWritesStep (i, ws)).2.map Prod.fst).Perm (ws.map Prod.fst ++ bs.flatten) ∧
      ∀ u j, (u, j) ∈ (bs.foldl blockWritesStep (i, ws)).2 ↔
        (u, j) ∈ ws ∨ ∃ t, ∃ ht : t < bs.length, j = i + t ∧ u ∈ bs[t] := by
  induction bs with
  | nil => intro i ws; simp
  | cons b bs ih =>
    intro i ws
    obtain ⟨h₁, h₂, h₃⟩ := ih (i + 1) (b.map (fun u => (u, i)) ++ ws)
    simp only [List.foldl_cons, blockWritesStep] at h₁ h₂ h₃ ⊢
    refine ⟨by rw [h₁]; simp; omega, ?_, fun u j => ?_⟩
    · refine h₂.trans ?_
      simp only [List.map_append, List.map_map, Function.comp_def, List.map_id', List.flatten_cons]
      exact (List.perm_append_comm.append_right _).trans (by simp [List.append_assoc])
    · rw [h₃]
      simp only [List.mem_append, List.mem_map, Prod.mk.injEq, List.length_cons]
      constructor
      · rintro ((⟨v, hv, rfl, rfl⟩ | h) | ⟨t, ht, rfl, hu⟩)
        · exact Or.inr ⟨0, by omega, by omega, by simpa using hv⟩
        · exact Or.inl h
        · exact Or.inr ⟨t + 1, by omega, by omega, by simpa using hu⟩
      · rintro (h | ⟨t, ht, rfl, hu⟩)
        · exact Or.inl (Or.inr h)
        · rcases t with _ | t
          · exact Or.inl (Or.inl ⟨u, by simpa using hu, rfl, by omega⟩)
          · exact Or.inr ⟨t, by omega, by omega, by simpa using hu⟩

/-- The block index of each listed point. -/
def blockIdx (n : ℕ) (bs : List (List ℕ)) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate n 0) (blockWrites bs)

section Blocks

variable {n : ℕ} {w : WinData} {bs : List (List ℕ)}

theorem get_blockIdx (hw : w.Valid n) (hbs : IsBlockList w bs) {t : ℕ} (ht : t < bs.length)
    {u : ℕ} (hu : u ∈ bs[t]) : get (blockIdx n bs) u = t := by
  obtain ⟨-, hperm, hmem⟩ := blockWrites_fold bs 0 []
  have hnd : ((blockWrites bs).map Prod.fst).Nodup :=
    (hperm.trans (by simp)).nodup_iff.2 (hbs.1.nodup_iff.2 hw.nodup)
  have hmem' : (u, t) ∈ blockWrites bs := (hmem u t).2 (Or.inr ⟨t, ht, by simp, hu⟩)
  have hlt : u < n := hw.lt u (hbs.1.mem_iff.1 (List.mem_flatten.2 ⟨_, List.getElem_mem ht, hu⟩))
  have h := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate n 0) hnd hmem'
    (by simpa using hlt)
  simp only [blockIdx, get, Array.getD_eq_getD_getElem?]
  rw [h]
  rfl

/-- Every listed point lies in a block. -/
theorem exists_block (hbs : IsBlockList w bs) {u : ℕ} (hu : u ∈ w.1) :
    ∃ t, ∃ ht : t < bs.length, u ∈ bs[t] := by
  obtain ⟨b, hb, hub⟩ := List.mem_flatten.1 (hbs.1.mem_iff.2 hu)
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
  exact ⟨t, ht, hub⟩

/-- Points of a block are listed. -/
theorem mem_of_block (hbs : IsBlockList w bs) {t : ℕ} (ht : t < bs.length) {u : ℕ}
    (hu : u ∈ bs[t]) : u ∈ w.1 :=
  hbs.1.mem_iff.1 (List.mem_flatten.2 ⟨_, List.getElem_mem ht, hu⟩)

/-- The first point of each block. -/
def blockReps (bs : List (List ℕ)) : List ℕ := bs.map fun b => b.headD 0

theorem blockReps_mem (hbs : IsBlockList w bs) {t : ℕ} (ht : t < bs.length) :
    (blockReps bs).getD t 0 ∈ bs[t] := by
  have hne := hbs.2 _ (List.getElem_mem ht)
  rw [blockReps, getD_of_lt (by simpa using ht), List.getElem_map]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
  rw [hx]
  simp

theorem block_unique (hw : w.Valid n) (hbs : IsBlockList w bs) {t t' : ℕ} (ht : t < bs.length)
    (ht' : t' < bs.length) {u : ℕ} (hu : u ∈ bs[t]) (hu' : u ∈ bs[t']) : t = t' := by
  rw [← get_blockIdx hw hbs ht hu, ← get_blockIdx hw hbs ht' hu']

theorem blockReps_lt (hw : w.Valid n) (hbs : IsBlockList w bs) {t : ℕ} (ht : t < bs.length) :
    (blockReps bs).getD t 0 < n :=
  hw.lt _ (mem_of_block hbs ht (blockReps_mem hbs ht))

/-! ### The action on block indices -/

/-- The index of the block containing `g` of the first point of block `t`. -/
def blockMap (n : ℕ) (bs : List (List ℕ)) (g : Perm (Fin n)) (t : ℕ) : ℕ :=
  if h : (blockReps bs).getD t 0 < n then get (blockIdx n bs) (g ⟨_, h⟩).val else 0

variable {G : Subgroup (Perm (Fin n))}

/-- An element permuting the blocks maps block `t` into the block `blockMap g t`. -/
theorem blockMap_spec (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs)
    {g : Perm (Fin n)} (hg : g ∈ G) {t : ℕ} (ht : t < bs.length) :
    ∃ ht' : blockMap n bs g t < bs.length,
      ∀ u : Fin n, u.val ∈ bs[t] → (g u).val ∈ bs[blockMap n bs g t] := by
  obtain ⟨b', hb', himg⟩ := hG g hg _ (List.getElem_mem ht)
  obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hb'
  have hr := blockReps_lt hw hbs ht
  have hbm : blockMap n bs g t = t' := by
    unfold blockMap
    simp only [hr, ↓reduceDIte]
    exact get_blockIdx hw hbs ht' (himg _ (blockReps_mem hbs ht))
  subst hbm
  exact ⟨ht', himg⟩

/-- The block map determines the block of the image of any point of block `t`. -/
theorem blockMap_eq (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs)
    {g : Perm (Fin n)} (hg : g ∈ G) {t : ℕ} (ht : t < bs.length) {u : Fin n}
    (hu : u.val ∈ bs[t]) : get (blockIdx n bs) (g u).val = blockMap n bs g t := by
  obtain ⟨ht', himg⟩ := blockMap_spec hw hbs hG hg ht
  exact get_blockIdx hw hbs ht' (himg u hu)

theorem blockMap_one (hw : w.Valid n) (hbs : IsBlockList w bs) {t : ℕ} (ht : t < bs.length) :
    blockMap n bs 1 t = t := by
  unfold blockMap
  simp only [blockReps_lt hw hbs ht, ↓reduceDIte]
  exact get_blockIdx hw hbs ht (blockReps_mem hbs ht)

theorem blockMap_mul (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs)
    {g h : Perm (Fin n)} (hg : g ∈ G) (hh : h ∈ G) {t : ℕ} (ht : t < bs.length) :
    blockMap n bs (g * h) t = blockMap n bs g (blockMap n bs h t) := by
  obtain ⟨ht₁, himg₁⟩ := blockMap_spec hw hbs hG hh ht
  have hr := blockReps_lt hw hbs ht
  have hu : (h ⟨_, hr⟩).val ∈ bs[blockMap n bs h t] := himg₁ _ (blockReps_mem hbs ht)
  rw [← blockMap_eq hw hbs hG hg ht₁ hu]
  unfold blockMap
  simp only [hr, ↓reduceDIte]
  rfl

/-- The action of `g ∈ G` on block indices. -/
def blockPerm (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs) (g : G) :
    Perm (Fin bs.length) where
  toFun t := ⟨blockMap n bs g t, (blockMap_spec hw hbs hG g.2 t.2).1⟩
  invFun t := ⟨blockMap n bs (g⁻¹ : G) t, (blockMap_spec hw hbs hG (g⁻¹ : G).2 t.2).1⟩
  left_inv t := by
    apply Fin.ext
    simp only
    rw [← blockMap_mul hw hbs hG (g⁻¹ : G).2 g.2 t.2]
    simp [blockMap_one hw hbs t.2]
  right_inv t := by
    apply Fin.ext
    simp only
    rw [← blockMap_mul hw hbs hG g.2 (g⁻¹ : G).2 t.2]
    simp [blockMap_one hw hbs t.2]

/-- The action on block indices is a homomorphism. -/
def blockHom (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs) :
    G →* Perm (Fin bs.length) where
  toFun := blockPerm hw hbs hG
  map_one' := by
    ext t
    exact blockMap_one hw hbs t.2
  map_mul' g h := by
    ext t
    exact blockMap_mul hw hbs hG g.2 h.2 t.2

theorem blockHom_apply (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs)
    (g : G) (t : Fin bs.length) : (blockHom hw hbs hG g t).val = blockMap n bs g t := rfl

end Blocks

/-! ### Extending a permutation by an action on extra points -/

section Extend

variable {n k : ℕ}

/-- `g` on the first `n` points and `τ` on the last `k`. -/
def extendFun (g : Perm (Fin n)) (τ : Perm (Fin k)) (x : Fin (n + k)) : Fin (n + k) :=
  if h : x.val < n then Fin.castAdd k (g ⟨x.val, h⟩)
  else Fin.natAdd n (τ ⟨x.val - n, by omega⟩)

@[simp] theorem extendFun_castAdd (g : Perm (Fin n)) (τ : Perm (Fin k)) (y : Fin n) :
    extendFun g τ (Fin.castAdd k y) = Fin.castAdd k (g y) := by
  simp [extendFun]

@[simp] theorem extendFun_natAdd (g : Perm (Fin n)) (τ : Perm (Fin k)) (t : Fin k) :
    extendFun g τ (Fin.natAdd n t) = Fin.natAdd n (τ t) := by
  simp [extendFun]

theorem extendFun_lt (g : Perm (Fin n)) (τ : Perm (Fin k)) {x : Fin (n + k)} (h : x.val < n) :
    (extendFun g τ x).val = (g ⟨x.val, h⟩).val := by
  simp [extendFun, h]

theorem extendFun_ge (g : Perm (Fin n)) (τ : Perm (Fin k)) {x : Fin (n + k)} (h : n ≤ x.val) :
    (extendFun g τ x).val = n + (τ ⟨x.val - n, by omega⟩).val := by
  simp [extendFun, Nat.not_lt.2 h]

theorem extendFun_comp (g g' : Perm (Fin n)) (τ τ' : Perm (Fin k)) (x : Fin (n + k)) :
    extendFun g τ (extendFun g' τ' x) = extendFun (g * g') (τ * τ') x := by
  induction x using Fin.addCases <;> simp

theorem extendFun_one (x : Fin (n + k)) :
    extendFun (1 : Perm (Fin n)) (1 : Perm (Fin k)) x = x := by
  induction x using Fin.addCases <;> simp

/-- The extension of `g` by `τ`, as a permutation. -/
def extendPerm (g : Perm (Fin n)) (τ : Perm (Fin k)) : Perm (Fin (n + k)) where
  toFun := extendFun g τ
  invFun := extendFun g⁻¹ τ⁻¹
  left_inv x := by rw [extendFun_comp]; simpa using extendFun_one x
  right_inv x := by rw [extendFun_comp]; simpa using extendFun_one x

theorem extendPerm_mul (g g' : Perm (Fin n)) (τ τ' : Perm (Fin k)) :
    extendPerm (g * g') (τ * τ') = extendPerm g τ * extendPerm g' τ' := by
  ext x
  exact congrArg Fin.val (extendFun_comp g g' τ τ' x).symm

theorem extendPerm_one : extendPerm (1 : Perm (Fin n)) (1 : Perm (Fin k)) = 1 := by
  ext x
  exact congrArg Fin.val (extendFun_one x)

theorem extendPerm_inv (g : Perm (Fin n)) (τ : Perm (Fin k)) :
    (extendPerm g τ)⁻¹ = extendPerm g⁻¹ τ⁻¹ := rfl

end Extend

/-! ### Arrays -/

theorem array_ext_get {a b : Array ℕ} (hs : a.size = b.size) (h : ∀ i < a.size, get a i = get b i) :
    a = b := by
  refine Array.ext hs fun i h₁ h₂ => ?_
  rw [← get_eq_getElem h₁, ← get_eq_getElem h₂]
  exact h i h₁

theorem get_append_lt {a b : Array ℕ} {i : ℕ} (hi : i < a.size) : get (a ++ b) i = get a i := by
  rw [get_eq_getElem (by simp; omega), get_eq_getElem hi, Array.getElem_append_left hi]

theorem get_append_ge {a b : Array ℕ} {i : ℕ} (hi : a.size ≤ i) (hi' : i < a.size + b.size) :
    get (a ++ b) i = get b (i - a.size) := by
  rw [get_eq_getElem (by simp; omega), get_eq_getElem (by omega), Array.getElem_append_right hi]

/-! ### The induced action -/

section Hom

variable {n : ℕ} {w : WinData} {bs : List (List ℕ)} {G : Subgroup (Perm (Fin n))}
  (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs)

/-- The induced action: `g` on the points, its action on block indices on the `k` extra
points. -/
def extendHom : G →* Perm (Fin (n + bs.length)) where
  toFun g := extendPerm g (blockHom hw hbs hG g)
  map_one' := by
    rw [map_one]
    exact extendPerm_one
  map_mul' g h := by
    rw [map_mul, Subgroup.coe_mul]
    exact extendPerm_mul _ _ _ _

theorem extendHom_lt (g : G) {x : Fin (n + bs.length)} (h : x.val < n) :
    (extendHom hw hbs hG g x).val = ((g : Perm (Fin n)) ⟨x.val, h⟩).val :=
  extendFun_lt _ _ h

theorem extendHom_ge (g : G) {x : Fin (n + bs.length)} (h : n ≤ x.val) :
    (extendHom hw hbs hG g x).val = n + blockMap n bs g (x.val - n) :=
  extendFun_ge _ _ h

theorem extendHom_injective : Function.Injective (extendHom hw hbs hG) := by
  intro g h hgh
  apply Subtype.ext
  ext y
  have := congrArg (fun π : Perm (Fin (n + bs.length)) => (π (Fin.castAdd _ y)).val) hgh
  simpa [extendHom_lt hw hbs hG _ (show (Fin.castAdd bs.length y).val < n from y.2)] using this

/-- The represented extension: the arrays of `g`, then for each block the index of the image
block, shifted by `n`. -/
def PermData.extendTo (n : ℕ) (bidx : Array ℕ) (reps : List ℕ) (g : PermData) : PermData :=
  (g.1 ++ (reps.map fun r => n + get bidx (get g.1 r)).toArray,
    g.2 ++ (reps.map fun r => n + get bidx (get g.2 r)).toArray)

/-- The represented extension is the extension, as data. -/
theorem extendTo_eq {g : PermData} (hg : g.Valid n) (hgG : PermData.denote n g ∈ G) :
    PermData.extendTo n (blockIdx n bs) (blockReps bs) g =
      PermData.ofPerm (extendHom hw hbs hG ⟨PermData.denote n g, hgG⟩) := by
  have hrep : ∀ t < bs.length, (blockReps bs).getD t 0 < n := fun t ht => blockReps_lt hw hbs ht
  have hlenr : (blockReps bs).length = bs.length := by simp [blockReps]
  refine Prod.ext (array_ext_get (by simp [PermData.extendTo, PermData.ofPerm, hg.size_fwd, hlenr])
    fun i hi => ?_) (array_ext_get (by simp [PermData.extendTo, PermData.ofPerm, hg.size_inv,
      hlenr]) fun i hi => ?_)
  · have hi' : i < n + bs.length := by simpa [PermData.extendTo, hg.size_fwd, hlenr] using hi
    simp only [PermData.extendTo, PermData.ofPerm]
    have hof := get_ofFn (fun x => ((extendHom hw hbs hG ⟨PermData.denote n g, hgG⟩) x).val)
      ⟨i, hi'⟩
    simp only at hof
    rw [hof]
    by_cases hin : i < n
    · rw [get_append_lt (by rw [hg.size_fwd]; exact hin), extendHom_lt hw hbs hG _ hin,
        PermData.val_denote_apply hg]
    · rw [get_append_ge (by rw [hg.size_fwd]; omega) (by simp [hg.size_fwd, hlenr]; omega),
        extendHom_ge hw hbs hG _ (show n ≤ i by omega), hg.size_fwd,
        get_list_toArray _ _ _ (by rw [hlenr]; omega)]
      unfold blockMap
      simp only [hrep _ (show i - n < bs.length by omega), ↓reduceDIte]
      rw [PermData.val_denote_apply hg]
  · have hi' : i < n + bs.length := by simpa [PermData.extendTo, hg.size_inv, hlenr] using hi
    simp only [PermData.extendTo, PermData.ofPerm]
    have hof := get_ofFn (fun x => ((extendHom hw hbs hG ⟨PermData.denote n g, hgG⟩)⁻¹ x).val)
      ⟨i, hi'⟩
    simp only at hof
    rw [hof, ← map_inv]
    by_cases hin : i < n
    · rw [get_append_lt (by rw [hg.size_inv]; exact hin), extendHom_lt hw hbs hG _ hin]
      simp only [Subgroup.coe_inv]
      rw [PermData.val_denote_inv_apply hg]
    · rw [get_append_ge (by rw [hg.size_inv]; omega) (by simp [hg.size_inv, hlenr]; omega),
        extendHom_ge hw hbs hG _ (show n ≤ i by omega), hg.size_inv,
        get_list_toArray _ _ _ (by rw [hlenr]; omega)]
      unfold blockMap
      simp only [hrep _ (show i - n < bs.length by omega), ↓reduceDIte, Subgroup.coe_inv]
      rw [PermData.val_denote_inv_apply hg]

include hw hbs in
/-- An element of the block kernel fixes every block index. -/
theorem blockMap_of_mem_blockKernel {g : Perm (Fin n)} (hg : g ∈ blockKernel G bs) {t : ℕ}
    (ht : t < bs.length) : blockMap n bs g t = t := by
  unfold blockMap
  simp only [blockReps_lt hw hbs ht, ↓reduceDIte]
  exact get_blockIdx hw hbs ht (hg.2 _ (List.getElem_mem ht) _ (blockReps_mem hbs ht))

/-- The block points `n, …, n + k - 1`. -/
def blockPts (n k : ℕ) : List ℕ := (List.range k).map (n + ·)

/-- The block points, as a window of degree `n + k`. -/
def blockWin (n k : ℕ) : WinData := WinData.ofPoints (n + k) (blockPts n k)

theorem mem_blockPts {k i : ℕ} : i ∈ blockPts n k ↔ n ≤ i ∧ i < n + k := by
  simp only [blockPts, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨i - n, by omega, by omega⟩

theorem mem_blockWin {k : ℕ} {x : Fin (n + k)} :
    x ∈ (blockWin n k).denote (n + k) ↔ n ≤ x.val := by
  simp only [blockWin, WinData.denote_ofPoints, Set.mem_ofPred_eq, mem_blockPts]
  omega

theorem valid_blockWin (n k : ℕ) : (blockWin n k).Valid (n + k) :=
  WinData.valid_ofPoints (List.nodup_range.map fun a b h => by simpa using h) fun i hi => by
    rw [mem_blockPts] at hi
    omega

/-- The extended group keeps the block points among themselves. -/
theorem isInvariant_blockWin :
    IsInvariant (extendHom hw hbs hG).range ((blockWin n bs.length).denote (n + bs.length)) := by
  rintro _ ⟨g, rfl⟩ x hx
  rw [mem_blockWin] at hx ⊢
  rw [extendHom_ge hw hbs hG g hx]
  omega

/-- **The kernel of the induced action on the block points** consists of the extensions of
the block kernel. -/
theorem mem_pointwiseStab_extend {π : Perm (Fin (n + bs.length))} :
    π ∈ pointwiseStab (extendHom hw hbs hG).range ((blockWin n bs.length).denote (n + bs.length)) ↔
      ∃ g : G, (g : Perm (Fin n)) ∈ blockKernel G bs ∧ extendHom hw hbs hG g = π := by
  rw [mem_pointwiseStab]
  constructor
  · rintro ⟨⟨g, rfl⟩, hfix⟩
    refine ⟨g, ⟨g.2, fun b hb u hu => ?_⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
    have hx := hfix (Fin.natAdd n ⟨t, ht⟩) (mem_blockWin.2 (by simp))
    have hval := congrArg Fin.val hx
    rw [extendHom_ge hw hbs hG g (by simp)] at hval
    simp only [Fin.val_natAdd, Nat.add_sub_cancel_left] at hval
    have hbm : blockMap n bs g t = t := by omega
    obtain ⟨ht', himg⟩ := blockMap_spec hw hbs hG g.2 ht
    have := himg u hu
    simp only [hbm] at this
    exact this
  · rintro ⟨g, hgK, rfl⟩
    refine ⟨⟨g, rfl⟩, fun x hx => ?_⟩
    have hnx := mem_blockWin.1 hx
    apply Fin.ext
    rw [extendHom_ge hw hbs hG g hnx,
      blockMap_of_mem_blockKernel hw hbs hgK (show x.val - n < bs.length by omega)]
    omega

/-- The first `n` entries of a permutation's arrays. -/
def PermData.truncTo (n : ℕ) (g : PermData) : PermData :=
  (((List.range n).map (get g.1)).toArray, ((List.range n).map (get g.2)).toArray)

/-- Truncating an extension recovers the permutation. -/
theorem truncTo_extendHom (g : G) :
    PermData.truncTo n (PermData.ofPerm (extendHom hw hbs hG g)) =
      PermData.ofPerm (g : Perm (Fin n)) := by
  refine Prod.ext (array_ext_get (by simp [PermData.truncTo, PermData.ofPerm]) fun i hi => ?_)
    (array_ext_get (by simp [PermData.truncTo, PermData.ofPerm]) fun i hi => ?_)
  · have hin : i < n := by simpa [PermData.truncTo] using hi
    simp only [PermData.truncTo, PermData.ofPerm]
    rw [get_list_toArray _ _ _ (by simpa using hin), getD_of_lt (by simpa using hin),
      List.getElem_range]
    have h₁ := get_ofFn (fun x => ((extendHom hw hbs hG g) x).val) ⟨i, by omega⟩
    have h₂ := get_ofFn (fun x => ((g : Perm (Fin n)) x).val) ⟨i, hin⟩
    simp only at h₁ h₂
    rw [h₁, h₂, extendHom_lt hw hbs hG g hin]
  · have hin : i < n := by simpa [PermData.truncTo] using hi
    simp only [PermData.truncTo, PermData.ofPerm]
    rw [get_list_toArray _ _ _ (by simpa using hin), getD_of_lt (by simpa using hin),
      List.getElem_range]
    have h₁ := get_ofFn (fun x => ((extendHom hw hbs hG g)⁻¹ x).val) ⟨i, by omega⟩
    have h₂ := get_ofFn (fun x => ((g : Perm (Fin n))⁻¹ x).val) ⟨i, hin⟩
    simp only at h₁ h₂
    rw [h₁, h₂, ← map_inv, extendHom_lt hw hbs hG _ hin]
    rfl

/-- Truncating valid generators of the kernel on the block points gives generators of the block
kernel. -/
theorem denote_truncTo {ks : GensData} (hks : GensData.AllValid (n + bs.length) ks)
    (hden : GensData.denote (n + bs.length) ks =
      pointwiseStab (extendHom hw hbs hG).range ((blockWin n bs.length).denote (n + bs.length))) :
    GensData.denote n (ks.map (PermData.truncTo n)) = blockKernel G bs := by
  -- each truncated generator is an element of the block kernel, extending to the generator
  have hgen : ∀ l ∈ ks, ∃ g : G, (g : Perm (Fin n)) ∈ blockKernel G bs ∧
      extendHom hw hbs hG g = PermData.denote _ l ∧
      PermData.denote n (PermData.truncTo n l) = g := by
    intro l hl
    have hmem : PermData.denote _ l ∈ pointwiseStab (extendHom hw hbs hG).range
        ((blockWin n bs.length).denote (n + bs.length)) := hden ▸ GensData.mem_denote_of_mem hl
    obtain ⟨g, hgK, hgl⟩ := (mem_pointwiseStab_extend hw hbs hG).1 hmem
    refine ⟨g, hgK, hgl, ?_⟩
    rw [PermData.eq_ofPerm_denote (hks l hl), ← hgl, truncTo_extendHom, PermData.denote_ofPerm]
  apply le_antisymm
  · rw [GensData.denote_le_iff]
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hl
    obtain ⟨g, hgK, -, hgd⟩ := hgen l' hl'
    rw [hgd]
    exact hgK
  · intro g hgK
    have hE : extendHom hw hbs hG ⟨g, hgK.1⟩ ∈ GensData.denote (n + bs.length) ks := by
      rw [hden]
      exact (mem_pointwiseStab_extend hw hbs hG).2 ⟨⟨g, hgK.1⟩, hgK, rfl⟩
    have key : ∀ x (hx : x ∈ GensData.denote (n + bs.length) ks), ∃ y : G,
        (y : Perm (Fin n)) ∈ GensData.denote n (ks.map (PermData.truncTo n)) ∧
        extendHom hw hbs hG y = x := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => ∃ y : G,
        (y : Perm (Fin n)) ∈ GensData.denote n (ks.map (PermData.truncTo n)) ∧
        extendHom hw hbs hG y = x) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨l, hl, rfl⟩
        obtain ⟨y, -, hyl, hyd⟩ := hgen l hl
        refine ⟨y, ?_, hyl⟩
        rw [← hyd]
        exact GensData.mem_denote_of_mem (List.mem_map.2 ⟨l, hl, rfl⟩)
      · exact ⟨1, one_mem _, map_one _⟩
      · rintro x₁ x₂ - - ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, map_mul _ _ _⟩
      · rintro x - ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, inv_mem hy, map_inv _ _⟩
    obtain ⟨y, hy, hyE⟩ := key _ hE
    have := extendHom_injective hw hbs hG hyE
    rw [this] at hy
    exact hy

/-- The truncated generators are valid. -/
theorem allValid_truncTo {ks : GensData} (hks : GensData.AllValid (n + bs.length) ks)
    (hden : GensData.denote (n + bs.length) ks =
      pointwiseStab (extendHom hw hbs hG).range ((blockWin n bs.length).denote (n + bs.length))) :
    GensData.AllValid n (ks.map (PermData.truncTo n)) := by
  intro l' hl'
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
  have hmem : PermData.denote _ l ∈ pointwiseStab (extendHom hw hbs hG).range
      ((blockWin n bs.length).denote (n + bs.length)) := hden ▸ GensData.mem_denote_of_mem hl
  obtain ⟨g, -, hgl⟩ := (mem_pointwiseStab_extend hw hbs hG).1 hmem
  rw [PermData.eq_ofPerm_denote (hks l hl), ← hgl, truncTo_extendHom]
  exact PermData.valid_ofPerm _

end Hom

/-- The extended generators generate the extended group. -/
theorem GensData.denote_extendTo {n : ℕ} {w : WinData} {bs : List (List ℕ)} {gs : GensData}
    (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs)
    (hgs : GensData.AllValid n gs) :
    GensData.denote (n + bs.length)
        (gs.map (PermData.extendTo n (blockIdx n bs) (blockReps bs))) =
      (extendHom hw hbs hG).range := by
  have htop : Subgroup.closure (((↑) : GensData.denote n gs → Perm (Fin n)) ⁻¹'
      GensData.denoteSet n gs) = ⊤ := Subgroup.closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  unfold GensData.denote
  congr 1
  ext π
  simp only [GensData.denoteSet, List.mem_map, Set.mem_ofPred_eq, Set.mem_image,
    Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨PermData.denote n g, GensData.mem_denote_of_mem hg⟩, ⟨g, hg, rfl⟩,
      by rw [extendTo_eq hw hbs hG (hgs g hg) (GensData.mem_denote_of_mem hg),
        PermData.denote_ofPerm]; rfl⟩
  · rintro ⟨⟨_, hmem⟩, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, by rw [extendTo_eq hw hbs hG (hgs g hg) hmem,
      PermData.denote_ofPerm]; rfl⟩

theorem GensData.allValid_extendTo {n : ℕ} {w : WinData} {bs : List (List ℕ)} {gs : GensData}
    (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs)
    (hgs : GensData.AllValid n gs) :
    GensData.AllValid (n + bs.length)
      (gs.map (PermData.extendTo n (blockIdx n bs) (blockReps bs))) := by
  intro l hl
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hl
  rw [extendTo_eq hw hbs hG (hgs g hg) (GensData.mem_denote_of_mem hg)]
  exact PermData.valid_ofPerm _

end GraphIso
