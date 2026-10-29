module

public import GraphIso.Valence.StepModel

/-!
# The induced generators of a layer step for maximum degree `Δ`

For level `r` with point list `Lr = levList lev N r`, the string-isomorphism instance of the
layer step lives on `D = N + m` points, `m` the number of subsets with at most `Δ` points.

* `indHom Δ hLr hP : P →* Perm (Fin D)`: the induced action of a group `P` of permutations
  mapping `Lr` into itself. It is injective (`indHom_injective`); on the first `N` points it
  is the permutation itself (`act_indHom_lt`).
* `indData Δ N Lr d`: the data of the induced permutation of `d`. The induced generators
  generate the image of `indHom` (`denote_map_indData`).
* `subWin Δ N Lr`: the window of the subsets, invariant under the image
  (`isInvariant_subWin`).
* **Readback** (`readback`): if `ks` generates the elements of the image of `A_r` preserving
  the layer string `xArr` on the window, then their truncations to the first `N` points are
  valid and generate `HR Δ r`.
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Sims

/-! ### The induced action as a homomorphism -/

section Hom

variable (Δ : ℕ) {N : ℕ} {Lr : List ℕ} (hLr : Lr.Pairwise (· < ·))
  {P : Subgroup (Perm (Fin N))} (hP : ∀ g ∈ P, MapsL Lr g)

/-- **The induced action.** -/
def indHom : P →* Perm (Fin (domSize Δ N Lr)) where
  toFun g := indPerm Δ hLr (hP g g.2)
  map_one' := perm_eq_of_act fun v hv => by
    rw [act_indPerm hLr _ hv, act_one]
    exact indFun_one hLr hv
  map_mul' g h := perm_eq_of_act fun v hv => by
    rw [act_mul, act_indPerm hLr (hP _ (g * h).2) hv, act_indPerm hLr (hP h h.2) hv,
      act_indPerm hLr (hP g g.2) (indFun_lt hLr (hP h h.2) hv),
      indFun_mul hLr (hP g g.2) (hP h h.2) hv]
    rfl

variable {Δ}

theorem act_indHom (g : P) {v : ℕ} (hv : v < domSize Δ N Lr) :
    act (indHom Δ hLr hP g) v = indFun Δ N Lr g v :=
  act_indPerm hLr (hP g g.2) hv

theorem act_indHom_lt (g : P) {v : ℕ} (hv : v < N) :
    act (indHom Δ hLr hP g) v = act (g : Perm (Fin N)) v := by
  rw [act_indHom hLr hP g (by simp only [domSize]; omega)]
  simp [indFun, hv]

theorem indHom_injective : Function.Injective (indHom Δ hLr hP) := fun g h e => by
  refine Subtype.ext (perm_eq_of_act fun v hv => ?_)
  rw [← act_indHom_lt hLr hP g hv, ← act_indHom_lt hLr hP h hv, e]

end Hom

/-! ### Induced generators -/

section Data

variable {Δ N : ℕ} {Lr : List ℕ}

variable (Δ N Lr) in
/-- The data of the induced permutation. -/
def indData (d : PermData) : PermData :=
  PermData.ofFun (domSize Δ N Lr) (indFun Δ N Lr (PermData.denote N d))
    (indFun Δ N Lr (PermData.denote N d)⁻¹)

variable (hLr : Lr.Pairwise (· < ·))
include hLr

theorem invPair_indFun {g : Perm (Fin N)} (hg : MapsL Lr g) :
    InvPair (domSize Δ N Lr) (indFun Δ N Lr g) (indFun Δ N Lr g⁻¹) := by
  refine ⟨fun v hv => indFun_lt hLr hg hv, fun v hv => indFun_lt hLr (mapsL_inv hg) hv,
    fun v hv => ?_, fun v hv => ?_⟩
  · rw [indFun_mul hLr (mapsL_inv hg) hg hv, inv_mul_cancel, indFun_one hLr hv]
  · rw [indFun_mul hLr hg (mapsL_inv hg) hv, mul_inv_cancel, indFun_one hLr hv]

theorem valid_indData {d : PermData} (hd : MapsL Lr (PermData.denote N d)) :
    (indData Δ N Lr d).Valid (domSize Δ N Lr) :=
  valid_ofFun (invPair_indFun hLr hd)

theorem denote_indData {d : PermData} (hd : MapsL Lr (PermData.denote N d)) :
    PermData.denote (domSize Δ N Lr) (indData Δ N Lr d) = indPerm Δ hLr hd :=
  denote_ofFun_eq (invPair_indFun hLr hd) fun _ hv => act_indPerm hLr hd hv

theorem allValid_map_indData {gs : GensData} (hP : ∀ g ∈ GensData.denote N gs, MapsL Lr g) :
    GensData.AllValid (domSize Δ N Lr) (gs.map (indData Δ N Lr)) := by
  intro l hl
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hl
  exact valid_indData hLr (hP _ (GensData.mem_denote_of_mem hg))

/-- The induced generators generate the image of the induced action. -/
theorem denote_map_indData {gs : GensData} (hP : ∀ g ∈ GensData.denote N gs, MapsL Lr g) :
    GensData.denote (domSize Δ N Lr) (gs.map (indData Δ N Lr)) = (indHom Δ hLr hP).range := by
  have htop : Subgroup.closure (((↑) : GensData.denote N gs → Perm (Fin N)) ⁻¹'
      GensData.denoteSet N gs) = ⊤ := Subgroup.closure_closure_coe_preimage
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  unfold GensData.denote
  congr 1
  ext π
  simp only [GensData.denoteSet, List.mem_map, Set.mem_ofPred_eq, Set.mem_image,
    Set.mem_preimage]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨PermData.denote N g, GensData.mem_denote_of_mem hg⟩, ⟨g, hg, rfl⟩,
      (denote_indData hLr (hP _ (GensData.mem_denote_of_mem hg))).symm⟩
  · rintro ⟨⟨_, hmem⟩, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, denote_indData hLr (hP _ hmem)⟩

/-- The induced generators generate the image of the induced action of the group they
generate. -/
theorem denote_map_indData' {gs : GensData} {P : Subgroup (Perm (Fin N))}
    (hP : ∀ g ∈ P, MapsL Lr g) (hgs : GensData.denote N gs = P) :
    GensData.denote (domSize Δ N Lr) (gs.map (indData Δ N Lr)) = (indHom Δ hLr hP).range := by
  subst hgs
  exact denote_map_indData hLr hP

omit hLr in
variable (Δ N Lr) in
/-- The window of a layer step: the subsets. -/
abbrev subWin : WinData := blockWin N (nsub Δ Lr)

omit hLr in
theorem valid_subWin : (subWin Δ N Lr).Valid (domSize Δ N Lr) :=
  valid_blockWin _ _

omit hLr in
theorem mem_subWin {x : Fin (domSize Δ N Lr)} :
    x ∈ (subWin Δ N Lr).denote (domSize Δ N Lr) ↔ N ≤ x.val :=
  mem_blockWin

omit hLr in
theorem indFun_ge {g : Perm (Fin N)} {v : ℕ} (h₁ : N ≤ v) (h₂ : v < domSize Δ N Lr) :
    indFun Δ N Lr g v = N + subImg Δ N Lr g (v - N) := by
  simp only [domSize] at h₂
  simp [indFun, show ¬ v < N by omega, h₂]

theorem isInvariant_subWin {P : Subgroup (Perm (Fin N))} (hP : ∀ g ∈ P, MapsL Lr g) :
    IsInvariant (indHom Δ hLr hP).range ((subWin Δ N Lr).denote (domSize Δ N Lr)) := by
  rintro _ ⟨g, rfl⟩ x hx
  rw [mem_subWin] at hx ⊢
  have e : ((indHom Δ hLr hP g) x).val = act (indHom Δ hLr hP g) x.val :=
    (act_of_lt _ x.2).symm
  rw [e, act_indHom hLr hP g x.2, indFun_ge hx x.2]
  omega

end Data

/-! ### Readback -/

section Readback

variable {Δ N : ℕ} {G : GraphData} {lev : Array ℕ} (hG : G.ValidD Δ N) {r : ℕ}

include hG in
/-- The induced element preserves the layer string on the subsets exactly when it lies in
`HR Δ r`. -/
theorem matches_indHom_iff (g : AutR N G lev r) :
    Matches ((subWin Δ N (levList lev N r)).denote (domSize Δ N (levList lev N r)))
        (indHom Δ (pairwise_levList lev N r) (fun _ h => mapsL_of_autR h) g)
        (StrData.denote _ (xArr Δ G lev N r (levList lev N r)))
        (StrData.denote _ (xArr Δ G lev N r (levList lev N r))) ↔
      (g : Perm (Fin N)) ∈ HR N G lev Δ r := by
  have hLr := pairwise_levList lev N r
  have hP : ∀ g ∈ AutR N G lev r, MapsL (levList lev N r) g := fun _ h => mapsL_of_autR h
  have himg : ∀ t, (ht : t < nsub Δ (levList lev N r)) →
      ((indHom Δ hLr hP g) ⟨N + t, by simp only [domSize]; omega⟩).val =
        N + subImg Δ N (levList lev N r) g t := by
    intro t ht
    rw [← act_of_lt _ (by simp only [domSize]; omega),
      act_indHom _ _ g (by simp only [domSize]; omega), indFun_ge (by omega)
        (by simp only [domSize]; omega), Nat.add_sub_cancel_left]
  rw [← xstr_iff g.2]
  constructor
  · intro hm t ht
    have := hm ⟨N + t, by simp only [domSize]; omega⟩ (mem_subWin.2 (by simp))
    simp only [StrData.denote] at this
    rw [himg t ht, get_xArr_sub hG hLr ht,
      get_xArr_sub hG hLr (subImg_lt hLr (hP g g.2) ht)] at this
    exact this
  · intro hx u hu
    have hNu := mem_subWin.1 hu
    have hu' : u.val - N < nsub Δ (levList lev N r) := by
      have := u.2
      simp only [domSize] at this
      omega
    have e : u = ⟨N + (u.val - N), by simp only [domSize]; omega⟩ := Fin.ext (by simp; omega)
    simp only [StrData.denote]
    rw [e, himg _ hu']
    simp only
    rw [get_xArr_sub hG hLr hu', get_xArr_sub hG hLr (subImg_lt hLr (hP g g.2) hu')]
    exact hx _ hu'

include hG in
/-- **Readback.** If `ks` generates the elements of the image of `A_r` preserving the layer
string on the subsets, the truncations of `ks` are valid and generate `HR Δ r`. -/
theorem readback {G' : Subgroup (Perm (Fin (domSize Δ N (levList lev N r))))}
    (hG' : G' = (indHom Δ (pairwise_levList lev N r)
      fun _ h => mapsL_of_autR (G := G) (r := r) h).range)
    (hW : IsInvariant G' ((subWin Δ N (levList lev N r)).denote
      (domSize Δ N (levList lev N r))))
    {ks : GensData} (hks : GensData.AllValid (domSize Δ N (levList lev N r)) ks)
    (hden : GensData.denote _ ks =
      aut hW (StrData.denote _ (xArr Δ G lev N r (levList lev N r)))) :
    GensData.AllValid N (ks.map (PermData.truncTo N)) ∧
      GensData.denote N (ks.map (PermData.truncTo N)) = HR N G lev Δ r := by
  have hLr := pairwise_levList lev N r
  have hP : ∀ g ∈ AutR N G lev r, MapsL (levList lev N r) g := fun _ h => mapsL_of_autR h
  -- each generator is the induced element of an element of `HR Δ r`
  have hgen : ∀ l ∈ ks, ∃ g : AutR N G lev r, (g : Perm (Fin N)) ∈ HR N G lev Δ r ∧
      indHom Δ hLr hP g = PermData.denote _ l ∧
      (PermData.truncTo N l).Valid N ∧ PermData.denote N (PermData.truncTo N l) = g := by
    intro l hl
    have hmem : PermData.denote _ l ∈ aut hW _ := hden ▸ GensData.mem_denote_of_mem hl
    obtain ⟨hmG, hm⟩ := (mem_aut hW).1 hmem
    rw [hG'] at hmG
    obtain ⟨g, hg⟩ := hmG
    rw [← hg] at hm
    refine ⟨g, (matches_indHom_iff hG g).1 hm, hg,
      truncTo_spec (hks l hl) (by simp only [domSize]; omega) fun i hi => ?_⟩
    rw [← hg, act_indHom_lt _ _ g hi]
  refine ⟨fun l' hl' => ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    obtain ⟨g, -, -, hv, -⟩ := hgen l hl
    exact hv
  · rw [GensData.denote_le_iff]
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
    obtain ⟨g, hgH, -, -, hd⟩ := hgen l hl
    rw [hd]
    exact hgH
  · intro g hgH
    have hE : indHom Δ hLr hP ⟨g, (mem_HR.1 hgH).1⟩ ∈ GensData.denote _ ks := by
      rw [hden]
      refine (mem_aut hW).2 ⟨?_, (matches_indHom_iff hG _).2 hgH⟩
      rw [hG']
      exact ⟨_, rfl⟩
    have key : ∀ x (hx : x ∈ GensData.denote _ ks), ∃ y : AutR N G lev r,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        indHom Δ hLr hP y = x := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => ∃ y : AutR N G lev r,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        indHom Δ hLr hP y = x) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨l, hl, rfl⟩
        obtain ⟨y, -, hyl, -, hyd⟩ := hgen l hl
        refine ⟨y, ?_, hyl⟩
        rw [← hyd]
        exact GensData.mem_denote_of_mem (List.mem_map.2 ⟨l, hl, rfl⟩)
      · exact ⟨1, one_mem _, map_one _⟩
      · rintro x₁ x₂ - - ⟨y₁, hy₁, rfl⟩ ⟨y₂, hy₂, rfl⟩
        exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, map_mul _ _ _⟩
      · rintro x - ⟨y, hy, rfl⟩
        exact ⟨y⁻¹, inv_mem hy, map_inv _ _⟩
    obtain ⟨y, hy, hyE⟩ := key _ hE
    have := indHom_injective _ _ hyE
    rw [this] at hy
    exact hy

end Readback

end GraphIso.Graph.Valence
