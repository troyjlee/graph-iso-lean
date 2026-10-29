module

public import GraphIso.Graph.StepModel
public import Mathlib.GroupTheory.Nilpotent

/-!
# The induced generators of a layer step

For level `r` with point list `Lr = levList lev N r`, the string-isomorphism instance of the
layer step lives on `D = N + m` points, `m` the number of subsets.

* `indHom hnd hP : P →* Perm (Fin D)`: the induced action of a group `P` of permutations
  mapping `Lr` into itself. It is injective (`indHom_injective`); on the first `N` points it is
  the permutation itself (`act_indHom_lt`).
* `indData N Lr d`: the data of the induced permutation of `d`. The induced generators generate
  the image of `indHom` (`denote_map_indData`).
* `tripWin N Lr`: the window of the subsets, invariant under the image
  (`isInvariant_tripWin`). The image of a `2`-group is nilpotent (`isNilpotent_indHom`).
* **Readback** (`readback`): if `ks` generates the elements of the image of `A_r` preserving the
  layer string `xArr` on the window, then their truncations to the first `N` points are valid
  and generate `HR r`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

/-! ### The induced action as a homomorphism -/

section Hom

variable {N : ℕ} {Lr : List ℕ} (hnd : Lr.Nodup) {P : Subgroup (Perm (Fin N))}
  (hP : ∀ g ∈ P, MapsL Lr g)

/-- **The induced action.** -/
def indHom : P →* Perm (Fin (domSize N Lr)) where
  toFun g := indPerm hnd (hP g g.2)
  map_one' := perm_eq_of_act fun v hv => by
    rw [act_indPerm hnd _ hv, act_one]
    exact indFun_one hnd hv
  map_mul' g h := perm_eq_of_act fun v hv => by
    rw [act_mul, act_indPerm hnd (hP _ (g * h).2) hv, act_indPerm hnd (hP h h.2) hv,
      act_indPerm hnd (hP g g.2) (indFun_lt (hP h h.2) hv), indFun_mul (hP h h.2) hv]
    rfl

theorem act_indHom (g : P) {v : ℕ} (hv : v < domSize N Lr) :
    act (indHom hnd hP g) v = indFun N Lr g v :=
  act_indPerm hnd (hP g g.2) hv

theorem act_indHom_lt (g : P) {v : ℕ} (hv : v < N) :
    act (indHom hnd hP g) v = act (g : Perm (Fin N)) v := by
  rw [act_indHom hnd hP g (by simp only [domSize]; omega)]
  simp [indFun, hv]

theorem indHom_injective : Function.Injective (indHom hnd hP) := fun g h e => by
  refine Subtype.ext (perm_eq_of_act fun v hv => ?_)
  rw [← act_indHom_lt hnd hP g hv, ← act_indHom_lt hnd hP h hv, e]

/-- The image of a `2`-group is nilpotent. -/
theorem isNilpotent_indHom (h2 : IsPGroup 2 P) : Group.IsNilpotent (indHom hnd hP).range :=
  (h2.of_surjective _ (indHom hnd hP).rangeRestrict_surjective).isNilpotent

end Hom

/-! ### Induced generators -/

section Data

variable {N : ℕ} {Lr : List ℕ}

/-- The data of the induced permutation. -/
def indData (N : ℕ) (Lr : List ℕ) (d : PermData) : PermData :=
  PermData.ofFun (domSize N Lr) (indFun N Lr (PermData.denote N d))
    (indFun N Lr (PermData.denote N d)⁻¹)

theorem invPair_indFun (hnd : Lr.Nodup) {g : Perm (Fin N)} (hg : MapsL Lr g) :
    InvPair (domSize N Lr) (indFun N Lr g) (indFun N Lr g⁻¹) := by
  refine ⟨fun v hv => indFun_lt hg hv, fun v hv => indFun_lt (mapsL_inv hg) hv,
    fun v hv => ?_, fun v hv => ?_⟩
  · rw [indFun_mul hg hv, inv_mul_cancel, indFun_one hnd hv]
  · rw [indFun_mul (mapsL_inv hg) hv, mul_inv_cancel, indFun_one hnd hv]

theorem valid_indData (hnd : Lr.Nodup) {d : PermData} (hd : MapsL Lr (PermData.denote N d)) :
    (indData N Lr d).Valid (domSize N Lr) :=
  valid_ofFun (invPair_indFun hnd hd)

theorem denote_indData (hnd : Lr.Nodup) {d : PermData} (hd : MapsL Lr (PermData.denote N d)) :
    PermData.denote (domSize N Lr) (indData N Lr d) = indPerm hnd hd :=
  denote_ofFun_eq (invPair_indFun hnd hd) fun _ hv => act_indPerm hnd hd hv

theorem allValid_map_indData (hnd : Lr.Nodup) {gs : GensData}
    (hP : ∀ g ∈ GensData.denote N gs, MapsL Lr g) :
    GensData.AllValid (domSize N Lr) (gs.map (indData N Lr)) := by
  intro l hl
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hl
  exact valid_indData hnd (hP _ (GensData.mem_denote_of_mem hg))

/-- The induced generators generate the image of the induced action. -/
theorem denote_map_indData (hnd : Lr.Nodup) {gs : GensData}
    (hP : ∀ g ∈ GensData.denote N gs, MapsL Lr g) :
    GensData.denote (domSize N Lr) (gs.map (indData N Lr)) = (indHom hnd hP).range := by
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
      (denote_indData hnd (hP _ (GensData.mem_denote_of_mem hg))).symm⟩
  · rintro ⟨⟨_, hmem⟩, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, denote_indData hnd (hP _ hmem)⟩

/-- The induced generators generate the image of the induced action of the group they
generate. -/
theorem denote_map_indData' (hnd : Lr.Nodup) {gs : GensData} {P : Subgroup (Perm (Fin N))}
    (hP : ∀ g ∈ P, MapsL Lr g) (hgs : GensData.denote N gs = P) :
    GensData.denote (domSize N Lr) (gs.map (indData N Lr)) = (indHom hnd hP).range := by
  subst hgs
  exact denote_map_indData hnd hP

/-- The window of a layer step: the subsets. -/
abbrev tripWin (N : ℕ) (Lr : List ℕ) : WinData :=
  blockWin N (nsub Lr)

theorem valid_tripWin (N : ℕ) (Lr : List ℕ) : (tripWin N Lr).Valid (domSize N Lr) :=
  valid_blockWin _ _

theorem mem_tripWin {x : Fin (domSize N Lr)} :
    x ∈ (tripWin N Lr).denote (domSize N Lr) ↔ N ≤ x.val :=
  mem_blockWin

theorem indFun_ge {g : Perm (Fin N)} {v : ℕ} (h₁ : N ≤ v) (h₂ : v < domSize N Lr) :
    indFun N Lr g v = N + tripImg N Lr g (v - N) := by
  simp only [domSize] at h₂
  simp [indFun, show ¬ v < N by omega, h₂]

theorem isInvariant_tripWin (hnd : Lr.Nodup) {P : Subgroup (Perm (Fin N))}
    (hP : ∀ g ∈ P, MapsL Lr g) :
    IsInvariant (indHom hnd hP).range ((tripWin N Lr).denote (domSize N Lr)) := by
  rintro _ ⟨g, rfl⟩ x hx
  rw [mem_tripWin] at hx ⊢
  have e : ((indHom hnd hP g) x).val = act (indHom hnd hP g) x.val := (act_of_lt _ x.2).symm
  rw [e, act_indHom hnd hP g x.2, indFun_ge hx x.2]
  omega

end Data

/-! ### Truncation -/

section Trunc

variable {N M : ℕ}

/-- The truncation of data agreeing with `g` on the first `N` points. -/
theorem truncTo_eq_ofFun {l : PermData} (hl : l.Valid M) (hNM : N ≤ M) {g : Perm (Fin N)}
    (h : ∀ i < N, act (PermData.denote M l) i = act g i) :
    PermData.truncTo N l = PermData.ofFun N (act g) (act g⁻¹) := by
  have h' : ∀ i < N, act (PermData.denote M l)⁻¹ i = act g⁻¹ i := fun i hi => by
    have e := h _ (act_lt g⁻¹ hi)
    rw [act_act_inv] at e
    conv_lhs => rw [← e]
    rw [act_inv_act]
  unfold PermData.truncTo PermData.ofFun
  congr 1
  · congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [get_fst_of_valid hl (by omega), h i hi']
  · congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    rw [get_snd_of_valid hl (by omega), h' i hi']

theorem truncTo_spec {l : PermData} (hl : l.Valid M) (hNM : N ≤ M) {g : Perm (Fin N)}
    (h : ∀ i < N, act (PermData.denote M l) i = act g i) :
    (PermData.truncTo N l).Valid N ∧ PermData.denote N (PermData.truncTo N l) = g := by
  rw [truncTo_eq_ofFun hl hNM h]
  exact ⟨valid_ofFun (invPair_act g), denote_ofFun_eq (invPair_act g) fun _ _ => rfl⟩

end Trunc

/-! ### Readback -/

section Readback

variable {N : ℕ} {G : GraphData} {lev : Array ℕ}

theorem mapsL_of_autR {r : ℕ} {g : Perm (Fin N)} (hg : g ∈ AutR N G lev r) :
    MapsL (levList lev N r) g := fun x hx => by
  obtain ⟨hxN, hlx⟩ := mem_levList.1 hx
  exact mem_levList.2 ⟨act_lt g hxN, by rw [hg.2.1 x hxN, hlx]⟩

variable (hG : G.Valid N) {r : ℕ}

include hG in
/-- The induced element preserves the layer string on the subsets exactly when it lies in
`HR r`. -/
theorem matches_indHom_iff (g : AutR N G lev r) :
    Matches ((tripWin N (levList lev N r)).denote (domSize N (levList lev N r)))
        (indHom (nodup_levList r) (fun _ h => mapsL_of_autR h) g)
        (StrData.denote _ (xArr G lev N r (levList lev N r)))
        (StrData.denote _ (xArr G lev N r (levList lev N r))) ↔
      (g : Perm (Fin N)) ∈ HR N G lev 3 r := by
  have hP : ∀ g ∈ AutR N G lev r, MapsL (levList lev N r) g := fun _ h => mapsL_of_autR h
  have himg : ∀ t, (ht : t < nsub (levList lev N r)) →
      ((indHom (nodup_levList r) hP g) ⟨N + t, by simp only [domSize]; omega⟩).val =
        N + tripImg N (levList lev N r) g t := by
    intro t ht
    rw [← act_of_lt _ (by simp only [domSize]; omega),
      act_indHom _ _ g (by simp only [domSize]; omega), indFun_ge (by omega)
        (by simp only [domSize]; omega), Nat.add_sub_cancel_left]
  rw [← xstr_iff g.2]
  constructor
  · intro hm t ht
    have := hm ⟨N + t, by simp only [domSize]; omega⟩ (mem_tripWin.2 (by simp))
    simp only [StrData.denote] at this
    rw [himg t ht, get_xArr_trip hG ht, get_xArr_trip hG (tripImg_lt (hP g g.2) ht)] at this
    exact this
  · intro hx u hu
    have hNu := mem_tripWin.1 hu
    have hu' : u.val - N < nsub (levList lev N r) := by
      have := u.2
      simp only [domSize] at this
      omega
    have e : u = ⟨N + (u.val - N), by simp only [domSize]; omega⟩ := Fin.ext (by simp; omega)
    simp only [StrData.denote]
    rw [e, himg _ hu']
    simp only
    rw [get_xArr_trip hG hu', get_xArr_trip hG (tripImg_lt (hP g g.2) hu')]
    exact hx _ hu'

include hG in
/-- **Readback.** If `ks` generates the elements of the image of `A_r` preserving the layer
string on the subsets, the truncations of `ks` are valid and generate `HR r`. -/
theorem readback {G' : Subgroup (Perm (Fin (domSize N (levList lev N r))))}
    (hG' : G' = (indHom (nodup_levList r) fun _ h => mapsL_of_autR (G := G) (r := r) h).range)
    (hW : IsInvariant G' ((tripWin N (levList lev N r)).denote (domSize N (levList lev N r))))
    {ks : GensData} (hks : GensData.AllValid (domSize N (levList lev N r)) ks)
    (hden : GensData.denote _ ks =
      aut hW (StrData.denote _ (xArr G lev N r (levList lev N r)))) :
    GensData.AllValid N (ks.map (PermData.truncTo N)) ∧
      GensData.denote N (ks.map (PermData.truncTo N)) = HR N G lev 3 r := by
  have hP : ∀ g ∈ AutR N G lev r, MapsL (levList lev N r) g := fun _ h => mapsL_of_autR h
  -- each generator is the induced element of an element of `HR r`
  have hgen : ∀ l ∈ ks, ∃ g : AutR N G lev r, (g : Perm (Fin N)) ∈ HR N G lev 3 r ∧
      indHom (nodup_levList r) hP g = PermData.denote _ l ∧
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
    have hE : indHom (nodup_levList r) hP ⟨g, (mem_HR.1 hgH).1⟩ ∈ GensData.denote _ ks := by
      rw [hden]
      refine (mem_aut hW).2 ⟨?_, (matches_indHom_iff hG _).2 hgH⟩
      rw [hG']
      exact ⟨_, rfl⟩
    have key : ∀ x (hx : x ∈ GensData.denote _ ks), ∃ y : AutR N G lev r,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        indHom (nodup_levList r) hP y = x := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => ∃ y : AutR N G lev r,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        indHom (nodup_levList r) hP y = x) ?_ ?_ ?_ ?_ hx
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

end GraphIso.Graph
