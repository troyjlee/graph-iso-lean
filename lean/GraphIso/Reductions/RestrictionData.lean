module

public import GraphIso.Reductions.Restriction
public import GraphIso.GroupOps.Interface
public import GraphIso.Programs.Window

/-!
# Represented restriction

For a valid window `w` of degree `n` listing `m` points:

* `WinData.reindex hw : Fin m ≃ w.denote n` is the list order `j ↦ w[j]`;
* `WinData.pos n w` is the array of positions in the list, `pos[w[j]] = j` (`get_pos`);
* `PermData.restrictTo pos w.1 g` is `g` restricted to the window in list order,
  `j ↦ pos[g[w[j]]]`. For `g ∈ G` it is valid of degree `m` and denotes `ρ g`
  (`denote_restrictTo`);
* `StrData.restrictTo w.1 x` is `x ∘ e` (`denote_restrictTo`);
* the restricted generators generate `ρ(G)` (`GensData.denote_restrictTo`);
* `mapsWindowBy_iff`: the postcondition of `lift` says exactly `ρ r = π'`;
* `WinData.ofPoints m (List.range m)` is the whole domain of degree `m`.
-/

@[expose] public section

namespace GraphIso

open Equiv Cost

/-! ### Writes to arrays -/

theorem getD_of_lt {l : List ℕ} {j : ℕ} (hj : j < l.length) : l.getD j 0 = l[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

theorem size_applyWrites {a : Ty} (arr : Array a.denote) (ws : List (ℕ × a.denote)) :
    (Prim.applyWrites arr ws).size = arr.size := by
  induction ws generalizing arr with
  | nil => rfl
  | cons w ws ih =>
    simp only [Prim.applyWrites, List.foldl_cons] at ih ⊢
    rw [ih, Array.size_setIfInBounds]

theorem getElem?_applyWrites_of_not_mem {a : Ty} (arr : Array a.denote)
    {ws : List (ℕ × a.denote)} {i : ℕ} (hi : i ∉ ws.map Prod.fst) :
    (Prim.applyWrites arr ws)[i]? = arr[i]? := by
  induction ws generalizing arr with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hi
    have h := ih (arr.setIfInBounds w.1 w.2) hi.2
    simp only [Prim.applyWrites, List.foldl_cons] at h ⊢
    rw [h, Array.getElem?_setIfInBounds_ne (Ne.symm hi.1)]

theorem getElem?_applyWrites_of_mem {a : Ty} (arr : Array a.denote) {ws : List (ℕ × a.denote)}
    (hnd : (ws.map Prod.fst).Nodup) {i : ℕ} {v : a.denote} (hiv : (i, v) ∈ ws)
    (hi : i < arr.size) : (Prim.applyWrites arr ws)[i]? = some v := by
  induction ws generalizing arr with
  | nil => simp at hiv
  | cons w ws ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Prim.applyWrites, List.foldl_cons]
    rcases List.mem_cons.1 hiv with rfl | hmem
    · have := getElem?_applyWrites_of_not_mem (arr.setIfInBounds i v) hnd.1
      simp only [Prim.applyWrites] at this
      rw [this, Array.getElem?_setIfInBounds_self_of_lt hi]
    · exact ih (arr.setIfInBounds w.1 w.2) hnd.2 hmem (by rwa [Array.size_setIfInBounds])

namespace WinData

variable {n : ℕ} {w : WinData}

/-- The list order of a valid window: `j ↦ w[j]`. -/
def reindex (hw : w.Valid n) : Fin w.1.length ≃ (w.denote n) :=
  (List.Nodup.getEquiv w.1 hw.nodup).trans
    { toFun := fun a => ⟨⟨a.1, hw.lt a.1 a.2⟩, a.2⟩
      invFun := fun u => ⟨u.1.val, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem reindex_val (hw : w.Valid n) (j : Fin w.1.length) :
    ((reindex hw j : Fin n) : ℕ) = w.1.getD j 0 := by
  simp [reindex, List.getD_eq_getElem?_getD]

/-- The positions of the listed points: `pos[w[j]] = j`. -/
def pos (n : ℕ) (w : WinData) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate n 0)
    ((List.range w.1.length).map fun j => (get w.1.toArray j, j))

theorem get_pos (hw : w.Valid n) {j : ℕ} (hj : j < w.1.length) :
    get (pos n w) (w.1.getD j 0) = j := by
  have hnd :
      (((List.range w.1.length).map fun j => (get w.1.toArray j, j)).map Prod.fst).Nodup := by
    simp only [List.map_map, Function.comp_def, get_toArray]
    refine (List.nodup_range).map_on fun i hi k hk e => ?_
    simp only [List.mem_range] at hi hk
    rw [getD_of_lt hi, getD_of_lt hk] at e
    exact (hw.nodup.getElem_inj_iff).1 e
  have hlt : w.1.getD j 0 < n := by
    rw [getD_of_lt hj]
    exact hw.lt _ (List.getElem_mem hj)
  have h := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate n 0) hnd
    (i := w.1.getD j 0) (v := j) (List.mem_map.2 ⟨j, List.mem_range.2 hj, by rw [get_toArray]⟩)
    (by simpa using hlt)
  have e : get (pos n w) (w.1.getD j 0) = ((pos n w)[w.1.getD j 0]?).getD 0 := by
    simp only [get, Array.getD_eq_getD_getElem?]
  rw [e, pos, h]
  rfl

theorem getD_get_pos (hw : w.Valid n) {u : ℕ} (hu : u ∈ w.1) :
    get (pos n w) u < w.1.length ∧ w.1.getD (get (pos n w) u) 0 = u := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hu
  rw [← getD_of_lt hj, get_pos hw hj]
  exact ⟨hj, rfl⟩

/-- The whole domain of degree `m`, as a window. -/
theorem valid_univ (m : ℕ) : (ofPoints m (List.range m)).Valid m :=
  valid_ofPoints List.nodup_range fun _ h => List.mem_range.1 h

theorem denote_univ (m : ℕ) : (ofPoints m (List.range m)).denote m = Set.univ := by
  ext u
  simp [denote_ofPoints]

end WinData

/-! ### Restricted data -/

/-- `g` and its inverse map the listed points into the list. -/
def PermData.MapsWindow (w : WinData) (g : PermData) : Prop :=
  ∀ u ∈ w.1, get g.1 u ∈ w.1 ∧ get g.2 u ∈ w.1

/-- `g` restricted to the window, in list order: `j ↦ pos[g[w[j]]]`. -/
def PermData.restrictTo (pos : Array ℕ) (pts : List ℕ) (g : PermData) : PermData :=
  ((pts.map fun u => get pos (get g.1 u)).toArray, (pts.map fun u => get pos (get g.2 u)).toArray)

/-- `x` restricted to the window, in list order. -/
def StrData.restrictTo (pts : List ℕ) (x : StrData) : StrData := (pts.map (get x)).toArray

/-- Generators restricted to the window. -/
def GensData.restrictTo (pos : Array ℕ) (pts : List ℕ) (gs : GensData) : GensData :=
  gs.map (PermData.restrictTo pos pts)

section Restrict

variable {n : ℕ} {w : WinData} {G : Subgroup (Perm (Fin n))} {gs : GensData}

theorem get_list_toArray (l : List ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < l.length) :
    get (l.map f).toArray j = f (l.getD j 0) := by
  rw [get_eq_getElem (by simpa using hj), getD_of_lt hj]
  simp

theorem PermData.mapsWindow_of_mem (hW : IsInvariant G (w.denote n)) (hw : w.Valid n)
    {g : PermData} (hg : g.Valid n) (hmem : PermData.denote n g ∈ G) :
    PermData.MapsWindow w g := by
  intro u hu
  have hun : u < n := hw.lt u hu
  constructor
  · have := hW.apply_mem hmem (u := ⟨u, hun⟩) hu
    rwa [WinData.mem_denote, PermData.val_denote_apply hg] at this
  · have := hW.inv_apply_mem hmem (u := ⟨u, hun⟩) hu
    rwa [WinData.mem_denote, PermData.val_denote_inv_apply hg] at this

theorem PermData.valid_restrictTo (hw : w.Valid n) {g : PermData} (hg : g.Valid n)
    (hm : PermData.MapsWindow w g) :
    (PermData.restrictTo (WinData.pos n w) w.1 g).Valid w.1.length := by
  have hfw : ∀ j < w.1.length, w.1.getD j 0 ∈ w.1 ∧ w.1.getD j 0 < n := fun j hj => by
    rw [getD_of_lt hj]
    exact ⟨List.getElem_mem hj, hw.lt _ (List.getElem_mem hj)⟩
  refine ⟨by simp [PermData.restrictTo], by simp [PermData.restrictTo], fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · simp only [PermData.restrictTo]
    rw [get_list_toArray _ _ _ hj]
    exact (WinData.getD_get_pos hw (hm _ (hfw j hj).1).1).1
  · simp only [PermData.restrictTo]
    rw [get_list_toArray _ _ _ hj]
    exact (WinData.getD_get_pos hw (hm _ (hfw j hj).1).2).1
  · simp only [PermData.restrictTo]
    have h₁ := WinData.getD_get_pos hw (hm _ (hfw j hj).1).1
    rw [get_list_toArray _ _ _ hj, get_list_toArray _ _ _ h₁.1, h₁.2,
      hg.inv_fwd _ (hfw j hj).2, WinData.get_pos hw hj]
  · simp only [PermData.restrictTo]
    have h₁ := WinData.getD_get_pos hw (hm _ (hfw j hj).1).2
    rw [get_list_toArray _ _ _ hj, get_list_toArray _ _ _ h₁.1, h₁.2,
      hg.fwd_inv _ (hfw j hj).2, WinData.get_pos hw hj]

theorem PermData.denote_restrictTo (hW : IsInvariant G (w.denote n)) (hw : w.Valid n)
    {g : PermData} (hg : g.Valid n) (hmem : PermData.denote n g ∈ G) :
    PermData.denote w.1.length (PermData.restrictTo (WinData.pos n w) w.1 g) =
      restrictHom hW (WinData.reindex hw) ⟨PermData.denote n g, hmem⟩ := by
  have hm := PermData.mapsWindow_of_mem hW hw hg hmem
  have hv := PermData.valid_restrictTo hw hg hm
  symm
  rw [restrictHom_eq_iff]
  intro j
  apply Fin.ext
  have hj := j.2
  have hu : w.1.getD j 0 ∈ w.1 := by
    rw [getD_of_lt hj]
    exact List.getElem_mem hj
  rw [PermData.val_denote_apply hg, WinData.reindex_val, WinData.reindex_val,
    PermData.val_denote_apply hv]
  simp only [PermData.restrictTo]
  rw [get_list_toArray _ _ _ hj, (WinData.getD_get_pos hw (hm _ hu).1).2]

theorem StrData.denote_restrictTo (hw : w.Valid n) (x : StrData) :
    StrData.denote w.1.length (StrData.restrictTo w.1 x) =
      fun j => StrData.denote n x (WinData.reindex hw j) := by
  funext j
  simp only [StrData.denote, StrData.restrictTo]
  rw [get_list_toArray _ _ _ j.2, WinData.reindex_val]

theorem GensData.allValid_restrictTo (hW : IsInvariant (GensData.denote n gs) (w.denote n))
    (hw : w.Valid n) (hgs : GensData.AllValid n gs) :
    GensData.AllValid w.1.length (GensData.restrictTo (WinData.pos n w) w.1 gs) := by
  intro g' hg'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
  exact PermData.valid_restrictTo hw (hgs g hg)
    (PermData.mapsWindow_of_mem hW hw (hgs g hg) (GensData.mem_denote_of_mem hg))

/-- The restricted generators generate the restricted group. -/
theorem GensData.denote_restrictTo (hW : IsInvariant (GensData.denote n gs) (w.denote n))
    (hw : w.Valid n) (hgs : GensData.AllValid n gs) :
    GensData.denote w.1.length (GensData.restrictTo (WinData.pos n w) w.1 gs) =
      (restrictHom hW (WinData.reindex hw)).range := by
  set ρ := restrictHom hW (WinData.reindex hw)
  have htop : Subgroup.closure (((↑) : GensData.denote n gs → Perm (Fin n)) ⁻¹'
      GensData.denoteSet n gs) = ⊤ := Subgroup.closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  unfold GensData.denote
  congr 1
  ext π
  simp only [GensData.denoteSet, GensData.restrictTo, List.mem_map, Set.mem_ofPred_eq,
    Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨PermData.denote n g, GensData.mem_denote_of_mem hg⟩, ⟨g, hg, rfl⟩,
      (PermData.denote_restrictTo hW hw (hgs g hg) _).symm⟩
  · rintro ⟨⟨_, hmem⟩, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, PermData.denote_restrictTo hW hw (hgs g hg) _⟩

/-- The postcondition of `lift` says exactly that `r` restricts to `π'`. -/
theorem mapsWindowBy_iff (hW : IsInvariant G (w.denote n)) (hw : w.Valid n) {r π' : PermData}
    (hr : r.Valid n) (hrG : PermData.denote n r ∈ G) (hπ : π'.Valid w.1.length) :
    MapsWindowBy w r π' ↔
      restrictHom hW (WinData.reindex hw) ⟨PermData.denote n r, hrG⟩ =
        PermData.denote w.1.length π' := by
  rw [restrictHom_eq_iff]
  constructor
  · intro h j
    apply Fin.ext
    rw [PermData.val_denote_apply hr, WinData.reindex_val, WinData.reindex_val,
      PermData.val_denote_apply hπ]
    exact h j j.2
  · intro h j hj
    have := congrArg Fin.val (h ⟨j, hj⟩)
    rwa [PermData.val_denote_apply hr, WinData.reindex_val, WinData.reindex_val,
      PermData.val_denote_apply hπ] at this

end Restrict

end GraphIso
