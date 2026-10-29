module

public import GraphIso.Toolkit.BlockStab

/-!
# The stabilizer of a point of a listed orbit, with coset representatives

Stage 14d, item 6 (`PLAN-14.md` §8), the generic half. A group `G = ⟨gs⟩` of degree `N` acts on
a finite set listed without repetition, `r` elements in all, through a homomorphism
`ρ : G →* Perm (Fin r)`. For every generator the program receives its index map, the list of
`ρ gᵢ j` for `j < r`. As in `blockStabProg` (`GraphIso/Toolkit/BlockStab.lean`):

1. every generator is extended by its index map to degree `N + r` (`PermData.extendIdx`): `g`
   on `[0, N)` and `N + j ↦ N + ρ g j` on `[N, N + r)`, with the inverse index map computed by
   writes to an array (`os_invArr`);
2. the backend generates the extended group, the image of the injective `os_extHom ρ`, and
   returns the stabilizer and an orbit transversal of the point `N`;
3. the stabilizer's generators, truncated to degree `N`, generate the preimage of the
   stabilizer of index `0` (`os_denote_truncTo_le`); the transversal's elements, truncated,
   cover `G` by its cosets, and there are at most `r` of them.

* `exists_idxActHom`: a group acting on a type, and a duplicate-free list closed under it,
  give such a `ρ`, with `L[ρ h j] = h • L[j]`; `idxAct_fix_iff`: `ρ h` fixes `j` exactly when
  `h` fixes `L[j]`.
* `RunsWithin.orbitStabProg`: the spec, with the backend charges as explicit hypotheses.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Equiv Cost GraphIso GraphIso.Programs Pointwise

/-! ### The index action of a listed orbit -/

section IdxAct

variable {H O : Type*} [Group H] [MulAction H O]

/-- **The action on a duplicate-free list closed under the group, by indices.** -/
theorem exists_idxActHom (L : List O) (hL : L.Nodup) (hcl : ∀ (h : H), ∀ x ∈ L, h • x ∈ L) :
    ∃ ρ : H →* Perm (Fin L.length), ∀ h j, L.get (ρ h j) = h • L.get j := by
  classical
  let e : Fin L.length ≃ {x // x ∈ L} := List.Nodup.getEquiv L hL
  let σ : H → Perm {x // x ∈ L} := fun h =>
    { toFun := fun x => ⟨h • x.1, hcl h _ x.2⟩
      invFun := fun x => ⟨h⁻¹ • x.1, hcl h⁻¹ _ x.2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  refine ⟨{ toFun := fun h => e.symm.permCongr (σ h)
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext j
    simp [σ, Equiv.permCongr_apply]
  · intro h₁ h₂
    ext j
    simp [σ, Equiv.permCongr_apply, mul_smul]
  · intro h j
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, Equiv.permCongr_apply, Equiv.symm_symm]
    have : ∀ x : {x // x ∈ L}, L.get (e.symm x) = x.1 := fun x => by
      simp [e, List.Nodup.getEquiv]
    rw [this]
    simp [σ, e, List.Nodup.getEquiv]

/-- An index is fixed exactly when its element is. -/
theorem idxAct_fix_iff {L : List O} (hL : L.Nodup) {ρ : H →* Perm (Fin L.length)}
    (hρ : ∀ h j, L.get (ρ h j) = h • L.get j) (h : H) (j : Fin L.length) :
    ρ h j = j ↔ h • L.get j = L.get j := by
  rw [← hρ]
  constructor
  · intro e
    rw [e]
  · intro e
    exact (List.Nodup.get_inj_iff hL).1 e

end IdxAct

/-! ### The extension by an index action -/

section ExtHom

variable {N r : ℕ} {G : Subgroup (Perm (Fin N))} (ρ : G →* Perm (Fin r))

/-- `g` on the first `N` points, `ρ g` on the last `r`. -/
def os_extHom : G →* Perm (Fin (N + r)) where
  toFun g := extendPerm (g : Perm (Fin N)) (ρ g)
  map_one' := by
    rw [map_one]
    exact extendPerm_one
  map_mul' g h := by
    rw [map_mul, Subgroup.coe_mul]
    exact extendPerm_mul _ _ _ _

theorem os_extHom_lt (g : G) {x : Fin (N + r)} (h : x.val < N) :
    (os_extHom ρ g x).val = ((g : Perm (Fin N)) ⟨x.val, h⟩).val :=
  extendFun_lt _ _ h

theorem os_extHom_ge (g : G) {x : Fin (N + r)} (h : N ≤ x.val) :
    (os_extHom ρ g x).val = N + (ρ g ⟨x.val - N, by omega⟩).val :=
  extendFun_ge _ _ h

theorem os_extHom_injective : Function.Injective (os_extHom ρ) := by
  intro g h hgh
  apply Subtype.ext
  ext y
  have := congrArg (fun π : Perm (Fin (N + r)) => (π (Fin.castAdd _ y)).val) hgh
  simpa [os_extHom_lt ρ _ (show (Fin.castAdd r y).val < N from y.2)] using this

/-- The extension fixes the point `N + j` exactly when `ρ g` fixes `j`. -/
theorem os_extHom_fix_iff (g : G) {j : ℕ} (hj : j < r) :
    os_extHom ρ g ⟨N + j, by omega⟩ = ⟨N + j, by omega⟩ ↔ ρ g ⟨j, hj⟩ = ⟨j, hj⟩ := by
  rw [Fin.ext_iff, os_extHom_ge ρ g (show N ≤ N + j by omega), Fin.ext_iff]
  simp

end ExtHom

/-! ### The extension on data -/

section ExtData

/-- The inverse of an index map of `r` entries: the array with `j` at position `img[j]`. -/
def os_invArr (r : ℕ) (img : List ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate r 0)
    ((List.range r).map fun j => (get img.toArray j, j))

/-- **The extension of `g` by the index map `img`** on `r` points: the arrays of `g`, then
`N + img[j]` (forward) and `N + img⁻¹[j]` (inverse) for `j < r`. -/
def PermData.extendIdx (N r : ℕ) (img : List ℕ) (g : PermData) : PermData :=
  (g.1 ++ ((List.range r).map fun j => N + get img.toArray j).toArray,
    g.2 ++ ((List.range r).map fun j => N + get (os_invArr r img) j).toArray)

/-- The extended generators: generator `i` by the index map `imgs[i]`. -/
def os_extGens (N r : ℕ) (gs : GensData) (imgs : List (List ℕ)) : GensData :=
  (List.range gs.length).map fun i =>
    PermData.extendIdx N r (imgs.getD i []) (gs.getD i (#[], #[]))

theorem os_get_invArr {r : ℕ} {img : List ℕ} {π : Perm (Fin r)}
    (himg : ∀ j (hj : j < r), img.getD j 0 = (π ⟨j, hj⟩).val) {j : ℕ} (hj : j < r) :
    get (os_invArr r img) j = (π⁻¹ ⟨j, hj⟩).val := by
  set k := π⁻¹ ⟨j, hj⟩ with hk
  have hnd : (((List.range r).map fun j => (get img.toArray j, j)).map Prod.fst).Nodup := by
    simp only [List.map_map, Function.comp_def, get_toArray]
    refine List.nodup_range.map_on fun a ha b hb e => ?_
    simp only [List.mem_range] at ha hb
    rw [himg a ha, himg b hb] at e
    have := π.injective (Fin.ext e)
    simpa using this
  have hmem : (j, k.val) ∈ (List.range r).map fun j => (get img.toArray j, j) := by
    refine List.mem_map.2 ⟨k.val, List.mem_range.2 k.2, Prod.ext ?_ rfl⟩
    show get img.toArray k.val = j
    rw [get_toArray, himg k.val k.2]
    simp [hk]
  have h := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate r 0) hnd hmem
    (by simpa using hj)
  simp only [get, Array.getD_eq_getD_getElem?]
  rw [os_invArr, h]
  rfl

variable {N r : ℕ} {G : Subgroup (Perm (Fin N))} (ρ : G →* Perm (Fin r))

/-- **The extension by the index map is the extension, as data.** -/
theorem extendIdx_eq {g : PermData} (hg : g.Valid N) (hgG : PermData.denote N g ∈ G)
    {img : List ℕ} (himg : ∀ j (hj : j < r), img.getD j 0 = (ρ ⟨_, hgG⟩ ⟨j, hj⟩).val) :
    PermData.extendIdx N r img g = PermData.ofPerm (os_extHom ρ ⟨PermData.denote N g, hgG⟩) := by
  refine Prod.ext (array_ext_get (by simp [PermData.extendIdx, PermData.ofPerm, hg.size_fwd])
    fun i hi => ?_) (array_ext_get (by simp [PermData.extendIdx, PermData.ofPerm, hg.size_inv])
    fun i hi => ?_)
  · have hi' : i < N + r := by simpa [PermData.extendIdx, hg.size_fwd] using hi
    simp only [PermData.extendIdx, PermData.ofPerm]
    have hof := get_ofFn (fun x => ((os_extHom ρ ⟨PermData.denote N g, hgG⟩) x).val) ⟨i, hi'⟩
    simp only at hof
    rw [hof]
    by_cases hin : i < N
    · rw [get_append_lt (by rw [hg.size_fwd]; exact hin), os_extHom_lt ρ _ hin,
        PermData.val_denote_apply hg]
    · rw [get_append_ge (by rw [hg.size_fwd]; omega) (by simp [hg.size_fwd]; omega),
        os_extHom_ge ρ _ (show N ≤ i by omega), hg.size_fwd,
        get_list_toArray _ _ _ (by simp; omega), getD_of_lt (by simp; omega),
        List.getElem_range, get_toArray, himg]
  · have hi' : i < N + r := by simpa [PermData.extendIdx, hg.size_inv] using hi
    simp only [PermData.extendIdx, PermData.ofPerm]
    have hof := get_ofFn (fun x => ((os_extHom ρ ⟨PermData.denote N g, hgG⟩)⁻¹ x).val)
      ⟨i, hi'⟩
    simp only at hof
    rw [hof, ← map_inv]
    by_cases hin : i < N
    · rw [get_append_lt (by rw [hg.size_inv]; exact hin), os_extHom_lt ρ _ hin]
      simp only [Subgroup.coe_inv]
      rw [PermData.val_denote_inv_apply hg]
    · rw [get_append_ge (by rw [hg.size_inv]; omega) (by simp [hg.size_inv]; omega),
        os_extHom_ge ρ _ (show N ≤ i by omega), hg.size_inv,
        get_list_toArray _ _ _ (by simp; omega), getD_of_lt (by simp; omega),
        List.getElem_range, os_get_invArr himg, map_inv]

end ExtData

/-! ### Truncation -/

section Trunc

variable {N r : ℕ} {G : Subgroup (Perm (Fin N))} (ρ : G →* Perm (Fin r))

/-- Truncating an extension recovers the permutation. -/
theorem os_truncTo_extendPerm (g : Perm (Fin N)) (τ : Perm (Fin r)) :
    PermData.truncTo N (PermData.ofPerm (extendPerm g τ)) = PermData.ofPerm g := by
  refine Prod.ext (array_ext_get (by simp [PermData.truncTo, PermData.ofPerm]) fun i hi => ?_)
    (array_ext_get (by simp [PermData.truncTo, PermData.ofPerm]) fun i hi => ?_)
  · have hin : i < N := by simpa [PermData.truncTo] using hi
    simp only [PermData.truncTo, PermData.ofPerm]
    rw [get_list_toArray _ _ _ (by simpa using hin), getD_of_lt (by simpa using hin),
      List.getElem_range]
    have h₁ := get_ofFn (fun x => ((extendPerm g τ) x).val) ⟨i, by omega⟩
    have h₂ := get_ofFn (fun x => (g x).val) ⟨i, hin⟩
    simp only at h₁ h₂
    rw [h₁, h₂]
    exact extendFun_lt g τ (x := ⟨i, by omega⟩) hin
  · have hin : i < N := by simpa [PermData.truncTo] using hi
    simp only [PermData.truncTo, PermData.ofPerm]
    rw [get_list_toArray _ _ _ (by simpa using hin), getD_of_lt (by simpa using hin),
      List.getElem_range]
    have h₁ := get_ofFn (fun x => ((extendPerm g τ)⁻¹ x).val) ⟨i, by omega⟩
    have h₂ := get_ofFn (fun x => (g⁻¹ x).val) ⟨i, hin⟩
    simp only at h₁ h₂
    rw [h₁, h₂, extendPerm_inv]
    exact extendFun_lt g⁻¹ τ⁻¹ (x := ⟨i, by omega⟩) hin

/-- A valid element of the extended group truncates to the element it extends. -/
theorem os_truncTo_of_mem_range {l : PermData} (hl : PermData.Valid (N + r) l)
    (hmem : PermData.denote (N + r) l ∈ (os_extHom ρ).range) :
    ∃ g : G, os_extHom ρ g = PermData.denote (N + r) l ∧
      PermData.Valid N (PermData.truncTo N l) ∧ PermData.denote N (PermData.truncTo N l) = g := by
  obtain ⟨g, hg⟩ := hmem
  have e : PermData.truncTo N l = PermData.ofPerm (g : Perm (Fin N)) := by
    rw [PermData.eq_ofPerm_denote hl, ← hg]
    exact os_truncTo_extendPerm _ _
  refine ⟨g, hg, ?_, ?_⟩
  · rw [e]
    exact PermData.valid_ofPerm _
  · rw [e, PermData.denote_ofPerm]

/-- **Truncating generators of a subgroup of the extended group** gives generators of its
preimage under the extension. -/
theorem os_denote_truncTo_le {ks : GensData} (hks : GensData.AllValid (N + r) ks)
    (hle : GensData.denote (N + r) ks ≤ (os_extHom ρ).range) :
    GensData.AllValid N (ks.map (PermData.truncTo N)) ∧
      GensData.denote N (ks.map (PermData.truncTo N)) =
        ((GensData.denote (N + r) ks).comap (os_extHom ρ)).map G.subtype := by
  have hgen : ∀ l ∈ ks, ∃ g : G, os_extHom ρ g = PermData.denote _ l ∧
      PermData.Valid N (PermData.truncTo N l) ∧ PermData.denote N (PermData.truncTo N l) = g :=
    fun l hl => os_truncTo_of_mem_range ρ (hks l hl) (hle (GensData.mem_denote_of_mem hl))
  refine ⟨fun l' hl' => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    obtain ⟨_, -, hv, -⟩ := hgen l hl
    exact hv
  · rw [GensData.denote_le_iff]
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    obtain ⟨g, hge, -, hgd⟩ := hgen l hl
    rw [hgd]
    refine ⟨g, Subgroup.mem_comap.2 ?_, rfl⟩
    rw [hge]
    exact GensData.mem_denote_of_mem hl
  · rintro _ ⟨g, hg, rfl⟩
    have key : ∀ x (hx : x ∈ GensData.denote (N + r) ks), ∃ y : G,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        os_extHom ρ y = x := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => ∃ y : G,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        os_extHom ρ y = x) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨l, hl, rfl⟩
        obtain ⟨y, hyl, -, hyd⟩ := hgen l hl
        refine ⟨y, ?_, hyl⟩
        rw [← hyd]
        exact GensData.mem_denote_of_mem (List.mem_map.2 ⟨l, hl, rfl⟩)
      · exact ⟨1, one_mem _, map_one _⟩
      · rintro x₁ x₂ - - ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, map_mul _ _ _⟩
      · rintro x - ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, inv_mem hy, map_inv _ _⟩
    obtain ⟨y, hy, hyE⟩ := key _ hg
    have := os_extHom_injective ρ hyE
    rw [this] at hy
    exact hy

end Trunc

/-! ### The extended generators -/

section Gens

variable {N r : ℕ} {gs : GensData}

theorem os_mem_gens {i : ℕ} (hi : i < gs.length) :
    PermData.denote N gs[i] ∈ GensData.denote N gs :=
  GensData.mem_denote_of_mem (List.getElem_mem hi)

/-- **`imgs` lists the index maps of the generators under `ρ`**: entry `j` of `imgs[i]` is
`ρ gᵢ j`, for every generator `gᵢ` and `j < r`. -/
def IsIdxMaps (ρ : GensData.denote N gs →* Perm (Fin r)) (imgs : List (List ℕ)) : Prop :=
  ∀ i (hi : i < gs.length) j (hj : j < r),
    (imgs.getD i []).getD j 0 = (ρ ⟨_, os_mem_gens hi⟩ ⟨j, hj⟩).val

variable {imgs : List (List ℕ)} {ρ : GensData.denote N gs →* Perm (Fin r)}

theorem os_mem_extGens {x : PermData} : x ∈ os_extGens N r gs imgs ↔
    ∃ i, ∃ hi : i < gs.length, x = PermData.extendIdx N r (imgs.getD i []) gs[i] := by
  simp only [os_extGens, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩

theorem os_extGens_eq (hgs : GensData.AllValid N gs) (himg : IsIdxMaps ρ imgs) {x : PermData}
    (hx : x ∈ os_extGens N r gs imgs) :
    ∃ i, ∃ hi : i < gs.length, x = PermData.ofPerm (os_extHom ρ ⟨_, os_mem_gens hi⟩) := by
  obtain ⟨i, hi, rfl⟩ := os_mem_extGens.1 hx
  exact ⟨i, hi, extendIdx_eq ρ (hgs _ (List.getElem_mem hi)) (os_mem_gens hi)
    fun j hj => himg i hi j hj⟩

theorem os_allValid_extGens (hgs : GensData.AllValid N gs) (himg : IsIdxMaps ρ imgs) :
    GensData.AllValid (N + r) (os_extGens N r gs imgs) := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := os_extGens_eq hgs himg hx
  exact PermData.valid_ofPerm _

/-- **The extended generators generate the extended group.** -/
theorem os_denote_extGens (hgs : GensData.AllValid N gs) (himg : IsIdxMaps ρ imgs) :
    GensData.denote (N + r) (os_extGens N r gs imgs) = (os_extHom ρ).range := by
  apply le_antisymm
  · rw [GensData.denote_le_iff]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := os_extGens_eq hgs himg hx
    rw [PermData.denote_ofPerm]
    exact ⟨_, rfl⟩
  · rintro _ ⟨⟨g, hg⟩, rfl⟩
    refine Subgroup.closure_induction (p := fun x hx => os_extHom ρ ⟨x, hx⟩ ∈
      GensData.denote (N + r) (os_extGens N r gs imgs)) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨l, hl, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
      have hmem : PermData.extendIdx N r (imgs.getD i []) gs[i] ∈ os_extGens N r gs imgs :=
        os_mem_extGens.2 ⟨i, hi, rfl⟩
      have := GensData.mem_denote_of_mem (n := N + r) hmem
      rwa [extendIdx_eq ρ (hgs _ (List.getElem_mem hi)) (os_mem_gens hi)
        (fun j hj => himg i hi j hj), PermData.denote_ofPerm] at this
    · exact (map_one (os_extHom ρ)).symm ▸ one_mem _
    · intro x y hx hy ihx ihy
      have e : (⟨x * y, mul_mem hx hy⟩ : GensData.denote N gs) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e, map_mul]
      exact mul_mem ihx ihy
    · intro x hx ihx
      have e : (⟨x⁻¹, inv_mem hx⟩ : GensData.denote N gs) = (⟨x, hx⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact inv_mem ihx

end Gens

/-! ### Programs -/

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `PermData.extendIdx`: the inverse index map by writes to an array, then the two arrays. -/
def extendIdxProg (N r : var .nat) (img : var (.list .nat)) (g : var Ty.perm) :
    Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun f => .bind (.op1 .snd g) fun fi =>
  .bind (.op1 .arrayOfList img) fun ia =>
  .bind (.op1 .range r) fun js =>
  .bind (mapList js fun j => .bind (.op2 .arrayGet ia j) fun v => .op2 .pair v j) fun ws =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk r z) fun blank =>
  .bind (.prim .arrayUpdate (.cons blank (.cons ws .nil))) fun inv =>
  .bind (mapList js fun j => .bind (.op2 .arrayGet ia j) fun v => .op2 .add N v) fun l₁ =>
  .bind (mapList js fun j => .bind (.op2 .arrayGet inv j) fun v => .op2 .add N v) fun l₂ =>
  .bind (.op1 .arrayToList f) fun fl => .bind (.op2 .append fl l₁) fun fl' =>
  .bind (.op1 .arrayOfList fl') fun a₁ =>
  .bind (.op1 .arrayToList fi) fun il => .bind (.op2 .append il l₂) fun il' =>
  .bind (.op1 .arrayOfList il') fun a₂ => .op2 .pair a₁ a₂

/-- `os_extGens`: generator `i` extended by the index map `imgs[i]`. -/
def extIdxGensProg (N r : var .nat) (gs : var Ty.gens) (imgs : var (.list (.list .nat))) :
    Prog S rec var Ty.gens :=
  .bind (.op1 .arrayOfList gs) fun ga => .bind (.op1 .arrayOfList imgs) fun ia =>
  .bind (.op1 .length gs) fun s => .bind (.op1 .range s) fun is =>
  mapList is fun i => .bind (.op2 .arrayGet ga i) fun g => .bind (.op2 .arrayGet ia i) fun img =>
    extendIdxProg N r img g

/-- **The stabilizer of index `0` of a listed orbit, with coset representatives**: extend the
generators by their index maps, generate at degree `N + r`, the backend's stabilizer and
transversal of the point `N`, truncate. -/
def orbitStabProg (N r : var .nat) (gs : var Ty.gens) (imgs : var (.list (.list .nat))) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.list Ty.perm)) :=
  .bind (.op2 .add N r) fun Nr =>
  .bind (extIdxGensProg N r gs imgs) fun egs =>
  .bind (.op2 .pair Nr egs) fun a₁ =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a₁) fun Ge =>
  .bind (.op2 .pair Ge N) fun a₂ =>
  .bind (Prog.call (S := groupSig D) GroupOp.stabilizer a₂) fun Se =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbitTransversal a₂) fun tr =>
  .bind (.op1 .snd Se) fun sd => .bind (.op1 .fst sd) fun ses =>
  .bind (mapList ses fun l => truncProg N l) fun st =>
  .bind (.op2 .pair N st) fun a₃ =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a₃) fun H =>
  .bind (mapList tr fun vr => .bind (.op1 .snd vr) fun r => truncProg N r) fun rs =>
  .op2 .pair H rs

end Programs

/-! ### Specs of the extension programs -/

section ExtSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem os_getD_toArray {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.toArray.getD i d = l.getD i d := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem RunsWithin.extendIdxProg {N r : ℕ} (img : List ℕ) {g : PermData} (h₁ : g.1.size = N)
    (h₂ : g.2.size = N) :
    RunsWithin X body (SoJTree.extendIdxProg N r img g) (PermData.extendIdx N r img g)
      (6 * N + 21 * r + img.length + 20) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 2) fun j _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 2) fun j _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
    run_step (RunsWithin.mapList_le (c := 2) fun j _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost]))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, PermData.extendIdx, os_invArr, get,
      Ty.default]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, Args.tail, List.length_map,
      List.length_append, Array.length_toList, List.length_range, Array.size_replicate, h₁, h₂]
    omega

/-- The cost of `extIdxGensProg`: degree `N`, `r` points, `s` generators, `q` index maps. -/
def extIdxGensCost (N r s q : ℕ) : ℕ := s * (6 * N + 21 * r + r + 25) + q + 3 * s + 6

theorem RunsWithin.extIdxGensProg {N r : ℕ} {gs : GensData} {imgs : List (List ℕ)}
    (hsz : ∀ g ∈ gs, g.1.size = N ∧ g.2.size = N)
    (hlen : ∀ i < gs.length, (imgs.getD i []).length ≤ r) :
    RunsWithin X body (SoJTree.extIdxGensProg N r gs imgs) (os_extGens N r gs imgs)
      (extIdxGensCost N r gs.length imgs.length) := by
  have hel : ∀ i ∈ List.range gs.length, RunsWithin X body
      (Prog.bind (Prog.op2 (rec := (a, b)) (S := S) (var := Ty.denote) .arrayGet gs.toArray i)
        fun g => Prog.bind (Prog.op2 .arrayGet imgs.toArray i) fun img =>
          SoJTree.extendIdxProg N r img g)
      (PermData.extendIdx N r (imgs.getD i []) (gs.getD i (#[], #[])))
      (6 * N + 21 * r + r + 22) := by
    intro i hi
    have hi' := List.mem_range.1 hi
    have hg := hsz _ (List.getElem_mem hi')
    have eg : gs.toArray.getD i (Ty.default Ty.perm) = gs[i] := by
      rw [os_getD_toArray, List.getD_eq_getElem _ _ hi']
    have ei : imgs.toArray.getD i (Ty.default (.list .nat)) = imgs.getD i [] :=
      os_getD_toArray _ _ _
    have h := RunsWithin.extendIdxProg (X := X) (body := body) (N := N) (r := r)
      (imgs.getD i []) (g := gs[i]) hg.1 hg.2
    have hl := hlen i hi'
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      show RunsWithin X body (SoJTree.extendIdxProg N r
        (imgs.toArray.getD i (Ty.default (.list .nat))) (gs.toArray.getD i (Ty.default Ty.perm)))
        _ _
      rw [eg, ei, List.getD_eq_getElem gs _ hi']
      exact h
    case hc =>
      simp only [Prim.cost]
      omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.mapList_le hel).of_eq (by simp [Prim.eval, os_extGens])
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, extIdxGensCost]
    ring_nf
    omega

end ExtSpecs

/-! ### The spec -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The extended group, as generated by the backend. -/
def osGroup (O : Oracle (groupSig D)) (N r : ℕ) (gs : GensData) (imgs : List (List ℕ)) :
    GroupData D.denote :=
  O.run GroupOp.generate (N + r, os_extGens N r gs imgs)

/-- The stabilizer of the point `N` in the extended group, as computed by the backend. -/
def osStab (O : Oracle (groupSig D)) (N r : ℕ) (gs : GensData) (imgs : List (List ℕ)) :
    GroupData D.denote :=
  O.run GroupOp.stabilizer (osGroup O N r gs imgs, N)

/-- The orbit transversal of the point `N` in the extended group. -/
def osTrans (O : Oracle (groupSig D)) (N r : ℕ) (gs : GensData) (imgs : List (List ℕ)) :
    List (ℕ × PermData) :=
  O.run GroupOp.orbitTransversal (osGroup O N r gs imgs, N)

/-- The stabilizer of index `0` and its coset representatives, as computed. -/
def orbitStabModel (O : Oracle (groupSig D)) (N r : ℕ) (gs : GensData) (imgs : List (List ℕ)) :
    GroupData D.denote × List PermData :=
  (O.run GroupOp.generate (N, (osStab O N r gs imgs).2.1.map (PermData.truncTo N)),
    (osTrans O N r gs imgs).map fun vr => PermData.truncTo N vr.2)

/-- The operations used by `orbitStabProg`. -/
def orbitStabOps (op : GroupOp) : Prop :=
  op = .generate ∨ op = .stabilizer ∨ op = .orbitTransversal

/-- The cost of `orbitStabProg`: degree `N`, `r` points, `s` generators, `q` index maps, `sS`
stabilizer generators, `L` transversal pairs, and the four backend charges. -/
def orbitStabCost (N r s q sS L Bge Bst Btr Bgt : ℕ) : ℕ :=
  extIdxGensCost N r s q + sS * (11 * N + 13) + L * (11 * N + 14) + Bge + Bst + Btr + Bgt + 20

/-- **The stabilizer of index `0` of a listed orbit, with coset representatives.** For valid
generators `gs` of `G` at degree `N`, a homomorphism `ρ : G →* Perm (Fin r)` (`0 < r`) and the
index maps `imgs` of the generators under `ρ`, the result is the preimage under `ρ` of the
stabilizer of `0`, given by valid generators, together with at most `r` valid coset
representatives covering `G`. -/
theorem RunsWithin.orbitStabProg (hO : MeetsContractOn DV orbitStabOps X.O)
    (hPre : ∀ op x, orbitStabOps op → GroupPre DV op x → X.Pre op x)
    {N r : ℕ} {gs : GensData} {imgs : List (List ℕ)} (hgs : GensData.AllValid N gs) (hr : 0 < r)
    (ρ : GensData.denote N gs →* Perm (Fin r)) (himg : IsIdxMaps ρ imgs)
    (hlen : ∀ i < gs.length, (imgs.getD i []).length ≤ r) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
      (osGroup X.O N r gs imgs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (osGroup X.O N r gs imgs, N)
      (osStab X.O N r gs imgs) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (osGroup X.O N r gs imgs, N)
      (osTrans X.O N r gs imgs) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (osStab X.O N r gs imgs).2.1.map (PermData.truncTo N))
      (orbitStabModel X.O N r gs imgs).1 ≤ Bgt) :
    RunsWithin X body (SoJTree.orbitStabProg N r gs imgs) (orbitStabModel X.O N r gs imgs)
        (orbitStabCost N r gs.length imgs.length (osStab X.O N r gs imgs).2.1.length
          (osTrans X.O N r gs imgs).length Bge Bst Btr Bgt) ∧
      (orbitStabModel X.O N r gs imgs).1.1 = N ∧
      GroupValid DV N (orbitStabModel X.O N r gs imgs).1.2.1
        (orbitStabModel X.O N r gs imgs).1.2.2 ∧
      GensData.denote N (orbitStabModel X.O N r gs imgs).1.2.1 =
        ((MulAction.stabilizer (Perm (Fin r)) (⟨0, hr⟩ : Fin r)).comap ρ).map
          (GensData.denote N gs).subtype ∧
      (∀ x ∈ (orbitStabModel X.O N r gs imgs).2, PermData.Valid N x) ∧
      IsLeftCover (GensData.denote N gs) (GensData.denote N (orbitStabModel X.O N r gs imgs).1.2.1)
        (fun i : Fin (orbitStabModel X.O N r gs imgs).2.length =>
          PermData.denote N ((orbitStabModel X.O N r gs imgs).2.get i)) ∧
      (orbitStabModel X.O N r gs imgs).2.length ≤ r := by
  have hk : N < N + r := by omega
  -- the extended group
  have hegv := os_allValid_extGens hgs himg
  have hegden := os_denote_extGens hgs himg
  have hgpost := hO .generate (N + r, os_extGens N r gs imgs) (Or.inl rfl) hegv
  rcases hGe' : X.O.run GroupOp.generate (N + r, os_extGens N r gs imgs) with ⟨N₁, egs, d₁⟩
  have hGe : osGroup X.O N r gs imgs = (N₁, egs, d₁) := hGe'
  rw [hGe'] at hgpost
  obtain ⟨hN₁, hGev, hGeden⟩ := hgpost
  change N₁ = N + r at hN₁
  subst N₁
  have hE : GensData.denote (N + r) egs = (os_extHom ρ).range := by
    change GensData.denote _ egs = GensData.denote _ (os_extGens N r gs imgs) at hGeden
    rw [hGeden]
    exact hegden
  -- the stabilizer of the point `N`
  have hpreS : GroupPre DV .stabilizer ((N + r, egs, d₁), N) := ⟨hGev, hk⟩
  have hSpost := hO .stabilizer _ (Or.inr (Or.inl rfl)) hpreS
  rcases hS : X.O.run GroupOp.stabilizer ((N + r, egs, d₁), N) with ⟨N₂, ses, e₂⟩
  have hSm : osStab X.O N r gs imgs = (N₂, ses, e₂) := by
    rw [osStab, hGe]
    exact hS
  rw [hS] at hSpost
  obtain ⟨hN₂, hSv, hSden⟩ := hSpost
  change N₂ = N + r at hN₂
  subst N₂
  have hSden' : GensData.denote _ ses = pointStab (GensData.denote _ egs) ⟨N, hk⟩ := hSden hk
  -- the transversal of the point `N`
  have hpreT : GroupPre DV .orbitTransversal ((N + r, egs, d₁), N) := ⟨hGev, hk⟩
  have hTpost := hO .orbitTransversal _ (Or.inr (Or.inr rfl)) hpreT
  obtain ⟨tr, htr_def⟩ : ∃ tr : List (ℕ × PermData),
      X.O.run GroupOp.orbitTransversal ((N + r, egs, d₁), N) = tr := ⟨_, rfl⟩
  have hTm : osTrans X.O N r gs imgs = tr := by
    rw [osTrans, hGe]
    exact htr_def
  rw [htr_def] at hTpost
  obtain ⟨hnd, hfst, htr⟩ := hTpost
  -- the truncated stabilizer generators
  have hle : GensData.denote (N + r) ses ≤ (os_extHom ρ).range := by
    rw [hSden', ← hE]
    exact inf_le_left
  obtain ⟨htv, htden⟩ := os_denote_truncTo_le ρ hSv.1 hle
  have hfpost := hO .generate (N, ses.map (PermData.truncTo N)) (Or.inl rfl) htv
  rcases hH : X.O.run GroupOp.generate (N, ses.map (PermData.truncTo N)) with ⟨N₃, hs, e₃⟩
  rw [hH] at hfpost
  obtain ⟨hN₃, hHv, hHden⟩ := hfpost
  change N₃ = N at hN₃
  subst N₃
  have hmodel : orbitStabModel X.O N r gs imgs =
      ((N, hs, e₃), tr.map fun vr => PermData.truncTo N vr.2) := by
    rw [orbitStabModel, hSm, hTm]
    exact congrArg (fun z => (z, tr.map fun vr => PermData.truncTo N vr.2)) hH
  -- the denotation of the stabilizer
  have hHden' : GensData.denote N hs =
      ((pointStab (os_extHom ρ).range ⟨N, hk⟩).comap (os_extHom ρ)).map
        (GensData.denote N gs).subtype := by
    change GensData.denote N hs = GensData.denote N (ses.map (PermData.truncTo N)) at hHden
    rw [hHden, htden, hSden', hE]
  have hcomap : (pointStab (os_extHom ρ).range ⟨N, hk⟩).comap (os_extHom ρ) =
      (MulAction.stabilizer (Perm (Fin r)) (⟨0, hr⟩ : Fin r)).comap ρ := by
    ext g
    rw [Subgroup.mem_comap, mem_pointStab, Subgroup.mem_comap, MulAction.mem_stabilizer_iff,
      Perm.smul_def]
    have hfix : os_extHom ρ g ⟨N, hk⟩ = ⟨N, hk⟩ ↔ ρ g ⟨0, hr⟩ = ⟨0, hr⟩ :=
      os_extHom_fix_iff ρ g hr
    constructor
    · rintro ⟨-, h⟩
      exact hfix.1 h
    · intro h
      exact ⟨⟨g, rfl⟩, hfix.2 h⟩
  -- the representatives
  have hrep : ∀ vr ∈ tr, ∃ g : GensData.denote N gs,
      os_extHom ρ g = PermData.denote (N + r) vr.2 ∧ PermData.Valid N (PermData.truncTo N vr.2) ∧
        PermData.denote N (PermData.truncTo N vr.2) = g := by
    intro vr hvr
    obtain ⟨hvv, hvE, -⟩ := htr vr hvr
    exact os_truncTo_of_mem_range ρ hvv (hE ▸ hvE)
  have hcard : tr.length ≤ r := by
    have hsub : (tr.map Prod.fst).toFinset ⊆ Finset.Ico N (N + r) := by
      intro j hj
      rw [List.mem_toFinset] at hj
      obtain ⟨hi', hj', p, hp, hpu⟩ := (hfst j).1 hj
      have hp' : p ∈ (os_extHom ρ).range := hE ▸ hp
      obtain ⟨g, hgp⟩ := hp'
      have hv := congrArg Fin.val hpu
      rw [← hgp, os_extHom_ge ρ g (show N ≤ N by omega)] at hv
      exact Finset.mem_Ico.2 ⟨by simp at hv; omega, hj'⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico, List.length_map] at this
    omega
  rw [hmodel]
  refine ⟨?_, rfl, hHv, ?_, ?_, ?_, ?_⟩
  · -- the run and its cost
    have hsz : ∀ g ∈ gs, g.1.size = N ∧ g.2.size = N := fun g hg =>
      ⟨(hgs g hg).size_fwd, (hgs g hg).size_inv⟩
    have hmapT := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.perm)
      (xs := ses) (c := 11 * N + 10) (F := PermData.truncTo N)
      (f := fun l => Programs.truncProg N l) fun l _ => RunsWithin.truncProg N l
    have hmapR := RunsWithin.mapList_le (X := X) (body := body) (a' := .prod .nat Ty.perm)
      (b' := Ty.perm) (xs := tr) (c := 11 * N + 11) (F := fun vr => PermData.truncTo N vr.2)
      (f := fun vr => .bind (.op1 .snd vr) fun r => Programs.truncProg N r) fun vr _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.truncProg N vr.2)
          (by simp [Prim.cost]; omega)
    have hBst2 : X.B.call GroupOp.stabilizer ((N + r, egs, d₁), N) (N + r, ses, e₂) ≤ Bst := by
      rw [← hSm, ← hGe]
      exact hBst
    have hBtr2 : X.B.call GroupOp.orbitTransversal ((N + r, egs, d₁), N) tr ≤ Btr := by
      rw [← hTm, ← hGe]
      exact hBtr
    have hBgt2 : X.B.call GroupOp.generate (N, ses.map (PermData.truncTo N)) (N, hs, e₃) ≤ Bgt := by
      have := hBgt
      rw [hSm, hmodel] at this
      exact this
    have hpairS : Prim.eval (Prim.pair (a := (groupSig D).res GroupOp.generate) (b := .nat))
        (Args.cons (N + r, egs, d₁) (Args.cons N Args.nil)) = ((N + r, egs, d₁), N) := rfl
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.extIdxGensProg hsz hlen)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hegv))
      simp only [Prim.eval]
      rw [hGe']
      run_step (RunsWithin.prim _ _)
      rw [hpairS]
      run_step (RunsWithin.call (hPre _ _ (Or.inr (Or.inl rfl)) hpreS))
      rw [hS]
      run_step (RunsWithin.call (hPre _ _ (Or.inr (Or.inr rfl)) hpreT))
      rw [htr_def]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hmapT
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) htv))
      simp only [Prim.eval]
      rw [hH]
      run_step hmapR
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval]
      simp only [orbitStabCost, hSm, hTm]
      have e1 : X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
          (X.O.run GroupOp.generate (N + r, os_extGens N r gs imgs)) ≤ Bge := hBge
      have e2 : X.B.call GroupOp.stabilizer ((N + r, egs, d₁), N)
          (X.O.run GroupOp.stabilizer ((N + r, egs, d₁), N)) ≤ Bst := by
        rw [hS]
        exact hBst2
      have e3 : X.B.call GroupOp.orbitTransversal ((N + r, egs, d₁), N)
          (X.O.run GroupOp.orbitTransversal ((N + r, egs, d₁), N)) ≤ Btr := by
        rw [htr_def]
        exact hBtr2
      have e4 : X.B.call GroupOp.generate (N, List.map (PermData.truncTo N) ses)
          (X.O.run GroupOp.generate (N, List.map (PermData.truncTo N) ses)) ≤ Bgt := by
        rw [hH]
        exact hBgt2
      generalize X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
          (X.O.run GroupOp.generate (N + r, os_extGens N r gs imgs)) = B₁ at e1 ⊢
      generalize X.B.call GroupOp.stabilizer ((N + r, egs, d₁), N)
          (X.O.run GroupOp.stabilizer ((N + r, egs, d₁), N)) = B₂ at e2 ⊢
      generalize X.B.call GroupOp.orbitTransversal ((N + r, egs, d₁), N)
          (X.O.run GroupOp.orbitTransversal ((N + r, egs, d₁), N)) = B₃ at e3 ⊢
      generalize X.B.call GroupOp.generate (N, List.map (PermData.truncTo N) ses)
          (X.O.run GroupOp.generate (N, List.map (PermData.truncTo N) ses)) = B₄ at e4 ⊢
      generalize extIdxGensCost N r gs.length imgs.length = E
      generalize List.length ses = s₁
      generalize tr.length = s₂
      clear * - e1 e2 e3 e4
      nlinarith
  · -- the denotation
    change GensData.denote N hs = _
    rw [hHden', hcomap]
  · -- valid representatives
    intro x hx
    obtain ⟨vr, hvr, rfl⟩ := List.mem_map.1 hx
    obtain ⟨_, -, hv, -⟩ := hrep vr hvr
    exact hv
  · -- the cover
    refine ⟨fun i => ?_, fun g hg => ?_⟩
    · have hx := List.get_mem (tr.map fun vr => PermData.truncTo N vr.2) i
      obtain ⟨vr, hvr, hvre⟩ := List.mem_map.1 hx
      obtain ⟨g, -, -, hgd⟩ := hrep vr hvr
      rw [← hvre, hgd]
      exact g.2
    · set v := (os_extHom ρ ⟨g, hg⟩ ⟨N, hk⟩).val with hv_def
      have hso : SameOrbit (GensData.denote (N + r) egs) N v := by
        refine ⟨hk, (os_extHom ρ ⟨g, hg⟩ ⟨N, hk⟩).2, os_extHom ρ ⟨g, hg⟩, ?_, rfl⟩
        rw [hE]
        exact ⟨_, rfl⟩
      obtain ⟨vr, hvr, hvr1⟩ := List.mem_map.1 ((hfst v).2 hso)
      obtain ⟨hvv, -, hvu⟩ := htr vr hvr
      obtain ⟨gr, hgr, -, hgrd⟩ := hrep vr hvr
      have hx : PermData.truncTo N vr.2 ∈ tr.map fun vr => PermData.truncTo N vr.2 :=
        List.mem_map.2 ⟨vr, hvr, rfl⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 hx
      refine ⟨i, ?_⟩
      rw [hi, hgrd, hHden']
      refine ⟨gr⁻¹ * ⟨g, hg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, mem_pointStab]
      refine ⟨⟨_, rfl⟩, ?_⟩
      rw [map_mul, map_inv, Perm.mul_apply, Perm.inv_eq_iff_eq, hgr,
        PermData.denote_apply hvv]
      apply Fin.ext
      show v = get vr.2.1 N
      rw [hvu, hvr1]
  · simpa using hcard

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_extendIdxProg {S : Signature} {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat}
    {img₁ : var₁ (.list .nat)} {img₂ : var₂ (.list .nat)} {g₁ : var₁ Ty.perm}
    {g₂ : var₂ Ty.perm} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (himg : ⟨.list .nat, img₁, img₂⟩ ∈ Γ) (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extendIdxProg N₁ r₁ img₁ g₁)
      (extendIdxProg N₂ r₂ img₂ g₂) := by
  unfold extendIdxProg mapList
  prog_wf

theorem wf_extIdxGensProg {S : Signature} {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat}
    {gs₁ : var₁ Ty.gens} {gs₂ : var₂ Ty.gens} {imgs₁ : var₁ (.list (.list .nat))}
    {imgs₂ : var₂ (.list (.list .nat))} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hgs : ⟨Ty.gens, gs₁, gs₂⟩ ∈ Γ) (himgs : ⟨.list (.list .nat), imgs₁, imgs₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (extIdxGensProg N₁ r₁ gs₁ imgs₁)
      (extIdxGensProg N₂ r₂ gs₂ imgs₂) := by
  unfold extIdxGensProg extendIdxProg mapList
  prog_wf

theorem wf_orbitStabProg {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat} {gs₁ : var₁ Ty.gens}
    {gs₂ : var₂ Ty.gens} {imgs₁ : var₁ (.list (.list .nat))} {imgs₂ : var₂ (.list (.list .nat))}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) (hgs : ⟨Ty.gens, gs₁, gs₂⟩ ∈ Γ)
    (himgs : ⟨.list (.list .nat), imgs₁, imgs₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (orbitStabProg N₁ r₁ gs₁ imgs₁)
      (orbitStabProg N₂ r₂ gs₂ imgs₂) := by
  unfold orbitStabProg truncProg mapList
  refine .bind (by prog_wf) fun a₁ a₂ => ?_
  refine .bind (wf_extIdxGensProg (.tail _ hN) (.tail _ hr) (.tail _ hgs) (.tail _ himgs))
    fun e₁ e₂ => ?_
  prog_wf

end Wf

end GraphIso.SoJTree
