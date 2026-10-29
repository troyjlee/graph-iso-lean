module

public import GraphIso.Main.CJohnOps
public import GraphIso.Case3.Link
public import GraphIso.SoJTree.LeafStab
public import GraphIso.Toolkit.Transitivity
public import GraphIso.Toolkit.Reduce

/-!
# M4: covers, bridges and individualization

Stage 14j-3, items 1–3 (`PLAN-14.md` §14.3). The pieces of macro-step M4 (a primitive base
action that is not a giant) that connect the toolkit of stage 14b, the leaf stabilizers of
stage 14d and the extensions of stage 14h to reduce-and-derive.

* **Covers.** `IsLeftCover.trans`: a cover of `G` by `r` cosets of `K₁` and of `K₁` by `r'`
  cosets of `K₂` give a cover of `G` by the `r · r'` products. On data: `prodRepsD` (length
  `|rs| · |rs'|`, `length_prodRepsD`), `isLeftCover_prodRepsD`, and the program
  `prodRepsLProg` (`RunsWithin.prodRepsLProg`).
* **Numberings.** `shE L k hk`: a duplicate-free list `L` of base indices as an embedding of
  `Fin k` for any `k = |L|`; `decodeOut_extD_shE`: stage 14h's data extension `extD` along `L`
  decodes to `extOut` along it (any index type, by `subst`).
* **The bridge to stage 14d.** For a window `w` of base positions, `winE` numbers its base
  indices on the window's own index type `Fin |w|`, that of `restrictHom … (WinData.reindex hw)`
  (the `ψ` of `leafStabProg`). `baseHom_winE`: the base action carries these indices as `ψ`
  does. `restrictHom_baseWin_val`: on the base window `[n', N)` (`baseWinD`), `ψ` is the base
  action at `n'`, index by index.
* **Extensions are preserved.** `baseHom_extOut`: if `ψ g` fixes a structure on the window, the
  base action of `g` fixes its extension (`extOut_relabel`). `leafStab_baseHom_extOut`: so
  does every element of the leaf stabilizer computed by `leafStabProg`; `leafStab_le`.
* **Coloured extensions.** `restColsD m L`: colours `0` on `L`, `1` off it (the individualized
  points); with `cjcol`, cells get `0`, remaining points of `L` get `1`, individualized points
  `2`. `cj_ext_stab`: the coloured extension of a fixed Johnson embedding is fixed.
  `cj_ext_hq`: if `J` is Johnson with threshold `t` on `k ≤ 2t` points and `2(m − k) ≤ m`,
  every colour class off `V₀` has at most `m/2` points (the hypothesis of `rd_ns_cj`).
* **Individualization.** `fixFirst_base_inv`; `pointwiseStab_range'`: `pointStabsProg` on
  `List.range' n j` computes `fixFirst G n j` (with at most `m^j` coset representatives,
  `RunsWithin.pointStabsProg`); `indiv_trans`, `indiv_not_two`: for a `d`-transitive, not
  `(d + 1)`-transitive base action (`1 ≤ d`, `d + 1 ≤ m`), `fixFirst G n (d − 1)` is transitive
  and not 2-transitive on `[n + d − 1, N)`; `one_le_degree`; `indiv_of_degree`: the same from
  the computed degree (`degreeModel`) below `cap`. Primitivity of the base action is not needed
  for this (`orbital_config` needs only transitive and not 2-transitive).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Pointwise Cost MulAction GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree GraphIso.Case2b GraphIso.Align

/-! ### Composing left covers -/

section Covers

variable {M : Type*} [Group M]

/-- **Covers compose**: a cover of `G` by cosets of `K₁` and of `K₁` by cosets of `K₂` give a
cover of `G` by cosets of `K₂`, by the products. -/
theorem _root_.GraphIso.IsLeftCover.trans {ι ι' : Type*} {G K₁ K₂ : Subgroup M} {r : ι → M}
    {r' : ι' → M} (h₁ : IsLeftCover G K₁ r) (h₂ : IsLeftCover K₁ K₂ r') (hK : K₁ ≤ G) :
    IsLeftCover G K₂ (fun p : ι × ι' => r p.1 * r' p.2) := by
  refine ⟨fun p => G.mul_mem (h₁.mem p.1) (hK (h₂.mem p.2)), fun g hg => ?_⟩
  obtain ⟨i, hi⟩ := h₁.cover g hg
  obtain ⟨j, hj⟩ := h₂.cover _ hi
  refine ⟨(i, j), ?_⟩
  simpa [mul_inv_rev, mul_assoc] using hj

end Covers

/-! ### Products of representatives, as data -/

section ProdData

/-- The products `r * r'` of two lists of representatives, as data. -/
def prodRepsD (rs rs' : List PermData) : List PermData := prodReps rs (rs'.map fun r => (0, r))

theorem mem_prodRepsD {rs rs' : List PermData} {x : PermData} :
    x ∈ prodRepsD rs rs' ↔ ∃ r ∈ rs, ∃ r' ∈ rs', x = r.mul r' := by
  rw [prodRepsD, mem_prodReps]
  constructor
  · rintro ⟨r, hr, vt, hvt, rfl⟩
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hvt
    exact ⟨r, hr, r', hr', rfl⟩
  · rintro ⟨r, hr, r', hr', rfl⟩
    exact ⟨r, hr, (0, r'), List.mem_map.2 ⟨r', hr', rfl⟩, rfl⟩

theorem length_prodRepsD (rs rs' : List PermData) :
    (prodRepsD rs rs').length = rs.length * rs'.length := by
  rw [prodRepsD, length_prodReps, List.length_map]

theorem prodRepsD_valid {N : ℕ} {rs rs' : List PermData} (hr : ∀ r ∈ rs, r.Valid N)
    (hr' : ∀ r ∈ rs', r.Valid N) : ∀ x ∈ prodRepsD rs rs', x.Valid N := by
  intro x hx
  obtain ⟨r, hr₀, r', hr'₀, rfl⟩ := mem_prodRepsD.1 hx
  exact (hr r hr₀).mul (hr' r' hr'₀)

/-- **The products cover**: decoded, the products of a cover of `G` by cosets of `K₁` with a
cover of `K₁` by cosets of `K₂` cover `G` by cosets of `K₂`. -/
theorem isLeftCover_prodRepsD {N : ℕ} {rs rs' : List PermData} (hr : ∀ r ∈ rs, r.Valid N)
    (hr' : ∀ r ∈ rs', r.Valid N) {G K₁ K₂ : Subgroup (Perm (Fin N))}
    (h₁ : IsLeftCover G K₁ fun i : Fin rs.length => PermData.denote N (rs.get i))
    (h₂ : IsLeftCover K₁ K₂ fun j : Fin rs'.length => PermData.denote N (rs'.get j))
    (hK : K₁ ≤ G) :
    IsLeftCover G K₂ fun i : Fin (prodRepsD rs rs').length =>
      PermData.denote N ((prodRepsD rs rs').get i) := by
  have hc := h₁.trans h₂ hK
  refine ⟨fun i => ?_, fun g hg => ?_⟩
  · obtain ⟨r, hr₀, r', hr'₀, he⟩ := mem_prodRepsD.1 (List.get_mem (prodRepsD rs rs') i)
    rw [he, PermData.denote_mul (hr r hr₀) (hr' r' hr'₀)]
    obtain ⟨i₁, rfl⟩ := List.mem_iff_get.1 hr₀
    obtain ⟨j₁, rfl⟩ := List.mem_iff_get.1 hr'₀
    exact hc.mem (i₁, j₁)
  · obtain ⟨⟨i₁, j₁⟩, hij⟩ := hc.cover g hg
    have hx : (rs.get i₁).mul (rs'.get j₁) ∈ prodRepsD rs rs' :=
      mem_prodRepsD.2 ⟨_, List.get_mem rs i₁, _, List.get_mem rs' j₁, rfl⟩
    obtain ⟨k, hk⟩ := List.mem_iff_get.1 hx
    refine ⟨k, ?_⟩
    rw [hk, PermData.denote_mul (hr _ (List.get_mem rs i₁)) (hr' _ (List.get_mem rs' j₁))]
    exact hij

end ProdData

section ProdProg

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The products of two lists of representatives. -/
def prodRepsLProg (rs rs' : var (.list Ty.perm)) : Prog S rec var (.list Ty.perm) :=
  .bind (mapList rs' fun r => .bind (.op0 (.natLit 0)) fun z => .op2 .pair z r) fun tr =>
  Toolkit.prodRepsProg rs tr

end ProdProg

/-- The cost of `prodRepsLProg`. -/
def prodRepsLCost (N a b : ℕ) : ℕ := b * 5 + 4 + a * (b * (12 * N + 18) + 4)

section ProdSpec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.prodRepsLProg {N : ℕ} {rs rs' : List PermData}
    (hr : ∀ r ∈ rs, PermData.Valid N r) (hr' : ∀ r ∈ rs', PermData.Valid N r) :
    RunsWithin X body (Main.prodRepsLProg rs rs') (prodRepsD rs rs')
      (prodRepsLCost N rs.length rs'.length) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm)
    (b' := .prod .nat Ty.perm) (xs := rs') (c := 2) (F := fun r => (0, r))
    (f := fun r => .bind (.op0 (.natLit 0)) fun z => .op2 .pair z r) fun r _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim _ _) (by simp [Prim.cost])
  have hp := RunsWithin.prodRepsProg (X := X) (body := body) (N := N) hr
    (tr := rs'.map fun r => (0, r)) (by
      intro vt hvt
      obtain ⟨r, hr₀, rfl⟩ := List.mem_map.1 hvt
      exact hr' r hr₀)
  refine RunsWithin.bind_le hm hp ?_
  simp only [prodRepsLCost, List.length_map]
  omega

end ProdSpec

section ProdWf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_prodRepsLProg {rs₁ rs'₁ : var₁ (.list Ty.perm)} {rs₂ rs'₂ : var₂ (.list Ty.perm)}
    (hrs : ⟨.list Ty.perm, rs₁, rs₂⟩ ∈ Γ) (hrs' : ⟨.list Ty.perm, rs'₁, rs'₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (prodRepsLProg rs₁ rs'₁) (prodRepsLProg rs₂ rs'₂) := by
  unfold prodRepsLProg Toolkit.prodRepsProg mapList permMul mapArray mapList
  prog_wf

end ProdWf

/-! ### Numberings of base indices -/

section Shift

variable {m : ℕ}

/-- **The numbering of a duplicate-free list of base indices**, indexed by `Fin k` for any
`k = |L|` (so that it fits the index type a caller already has). -/
def shE (L : List ℕ) (k : ℕ) (hk : L.length = k) (hL : ∀ v ∈ L, v < m) (hnd : L.Nodup) :
    Fin k ↪ Fin m :=
  ⟨fun j => ⟨L[j.val]'(hk ▸ j.2), hL _ (List.getElem_mem _)⟩, fun i j h => by
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 this)⟩

theorem shE_val (L : List ℕ) (k : ℕ) (hk : L.length = k) (hL : ∀ v ∈ L, v < m)
    (hnd : L.Nodup) (j : Fin k) : (shE L k hk hL hnd j).val = L[j.val]'(hk ▸ j.2) := rfl

/-- The range of the numbering is `L`. -/
theorem mem_iff_shE (L : List ℕ) (k : ℕ) (hk : L.length = k) (hL : ∀ v ∈ L, v < m)
    (hnd : L.Nodup) (x : Fin m) : x.val ∈ L ↔ ∃ i, shE L k hk hL hnd i = x := by
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    exact ⟨⟨i, hk ▸ hi⟩, Fin.ext hix⟩
  · rintro ⟨i, rfl⟩
    exact List.getElem_mem _

/-- **The extension of leaf data along `L` is `extOut` along the numbering** (stage 14i's
`c3l_decodeOut_extD`, at an index type of the caller's choice). -/
theorem decodeOut_extD_shE (L : List ℕ) (k : ℕ) (hk : L.length = k) (hL : ∀ v ∈ L, v < m)
    (hnd : L.Nodup) (o : OutD) :
    decodeOut m (extD m L o) = extOut (shE L k hk hL hnd) (decodeOut k o) := by
  subst hk
  exact Case3.c3l_decodeOut_extD L hL hnd o

end Shift

/-! ### The base indices of a window, and the restriction to it -/

section Window

variable {N n : ℕ}

/-- The base indices of a list of base positions. -/
def winBase (n : ℕ) (pts : List ℕ) : List ℕ := pts.map (· - n)

theorem length_winBase (n : ℕ) (pts : List ℕ) : (winBase n pts).length = pts.length :=
  List.length_map _

theorem winBase_lt {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) :
    ∀ v ∈ winBase n w.1, v < N - n := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hv
  have h1 := hw.lt u hu
  have h2 := hwb u hu
  omega

theorem winBase_nodup {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) :
    (winBase n w.1).Nodup := by
  refine hw.nodup.map_on fun a ha b hb hab => ?_
  have h1 := hwb a ha
  have h2 := hwb b hb
  have hab' : a - n = b - n := hab
  omega

/-- **The base indices of a window of base positions, as an embedding** of the window's
index type `Fin |w|` (that of `restrictHom … (WinData.reindex hw)`) into `Fin (N − n)`. -/
def winE {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) : Fin w.1.length ↪ Fin (N - n) :=
  shE (winBase n w.1) w.1.length (length_winBase n w.1) (winBase_lt hw hwb)
    (winBase_nodup hw hwb)

theorem winE_val {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) (j : Fin w.1.length) :
    (winE hw hwb j).val = w.1[j.val] - n := by
  simp [winE, shE_val, winBase]

/-- The base position of the `j`-th window index is the `j`-th window point. -/
theorem basePos_winE {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i)
    (j : Fin w.1.length) :
    (basePos (winE hw hwb j) : Fin N) = (WinData.reindex hw j : Fin N) := by
  apply Fin.ext
  rw [WinData.reindex_val]
  simp only [basePos, winE_val]
  have := hwb _ (List.getElem_mem (l := w.1) (n := j.val) j.2)
  rw [List.getD_eq_getElem _ _ j.2]
  omega

/-- **The bridge**: on a window of base positions, the base action of `G` carries the window's
indices as the restriction `restrictHom` (stage 14d's `ψ`) does. -/
theorem baseHom_winE {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) (hW : IsInvariant G (w.denote N))
    (g : ↥G) (j : Fin w.1.length) :
    baseHom G n hinv g (winE hw hwb j) =
      winE hw hwb (restrictHom hW (WinData.reindex hw) g j) := by
  have h1 := baseHom_apply (hG := hinv) g (winE hw hwb j)
  have h2 := restrictHom_apply hW (WinData.reindex hw) g j
  rw [basePos_winE] at h1
  rw [← h2, ← basePos_winE hw hwb] at h1
  have := congrArg Fin.val h1
  simp only [basePos] at this
  exact Fin.ext (by omega)

/-- Two groups' base actions agree on a common element. -/
theorem baseHom_congr {G H : Subgroup (Perm (Fin N))} (hG : IsInvariant G (baseSet n N))
    (hH : IsInvariant H (baseSet n N)) (g : ↥G) (h : ↥H) (he : g.1 = h.1) :
    baseHom G n hG g = baseHom H n hH h := by
  ext j
  simp only [baseHom, MonoidHom.coe_mk, OneHom.coe_mk, Equiv.coe_fn_mk, he]

/-- The base indices of the window are the image of `winE`. -/
theorem mem_winBase_iff {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i)
    (x : Fin (N - n)) : x.val ∈ winBase n w.1 ↔ ∃ i, winE hw hwb i = x :=
  mem_iff_shE _ _ _ _ _ x

/-- The base indices off the window number `m − |w|`. -/
theorem card_compl_winE {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) :
    (univ \ univ.map (winE hw hwb)).card = (N - n) - w.1.length := by
  rw [card_sdiff_of_subset (subset_univ _), card_map, card_univ, card_univ, Fintype.card_fin,
    Fintype.card_fin]

/-- The window of the base positions `[b, N)`. -/
abbrev baseWinD (N b : ℕ) : WinData := WinData.ofPoints N (basePts b N)

theorem baseWinD_valid (N b : ℕ) : (baseWinD N b).Valid N :=
  WinData.valid_ofPoints (basePts_nodup _ _) fun _ hi => (mem_basePts.1 hi).2

theorem baseWinD_ge {b : ℕ} (hnb : n ≤ b) : ∀ i ∈ (baseWinD N b).1, n ≤ i := by
  intro i hi
  have := (mem_basePts.1 hi).1
  omega

theorem baseWinD_length (N b : ℕ) : (baseWinD N b).1.length = N - b := length_basePts b N

theorem getElem_basePts {b : ℕ} (j : ℕ) (hj : j < (basePts b N).length) :
    (basePts b N)[j] = b + j := by
  simp [basePts]

/-- **The restriction to the base window `[n', N)` is the base action at `n'`**, index by
index. -/
theorem restrictHom_baseWin_val {n' : ℕ} {H : Subgroup (Perm (Fin N))}
    (hinv' : IsInvariant H (baseSet n' N)) (hW : IsInvariant H ((baseWinD N n').denote N))
    (g : ↥H) (j : Fin (baseWinD N n').1.length) :
    ((restrictHom hW (WinData.reindex (baseWinD_valid N n')) g j : Fin _) : ℕ) =
      (baseHom H n' hinv' g ⟨j.val, j.2.trans_eq (baseWinD_length N n')⟩
        : ℕ) := by
  have hwb := baseWinD_ge (N := N) (n := n') (b := n') le_rfl
  have h := baseHom_winE hinv' (baseWinD_valid N n') hwb hW g j
  have hv : ∀ i : Fin (baseWinD N n').1.length, (winE (baseWinD_valid N n') hwb i).val = i.val :=
    fun i => by
      rw [winE_val]
      show (basePts n' N)[i.val] - n' = i.val
      rw [getElem_basePts]
      omega
  have hj : winE (baseWinD_valid N n') hwb j =
      ⟨j.val, j.2.trans_eq (baseWinD_length N n')⟩ := Fin.ext (hv j)
  rw [hj] at h
  rw [h, hv]

end Window

/-! ### Structures extended along a window -/

section Extend

variable {N n : ℕ}

/-- **Extension preserves invariance**: if the restriction `ψ g` to a window of base positions
fixes a structure on the window's indices, the base action of `g` fixes its extension. -/
theorem baseHom_extOut {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i) (hW : IsInvariant G (w.denote N))
    (g : ↥G) {X : Option (Out (Fin w.1.length))}
    (hX : restrictHom hW (WinData.reindex hw) g • X = X) :
    baseHom G n hinv g • extOut (winE hw hwb) X = extOut (winE hw hwb) X := by
  have h := extOut_relabel (baseHom G n hinv g) (restrictHom hW (WinData.reindex hw) g)
    (e := winE hw hwb) (e' := winE hw hwb) (fun i => (baseHom_winE hinv hw hwb hW g i).symm) X
  rw [hX] at h
  exact h.symm

/-- **The leaf stabilizer preserves the extended leaf**: for the group computed by stage 14d's
`leafStabProg` (the preimage under `ψ` of the stabilizer of `X`), its base action fixes the
extension of `X`. -/
theorem leafStab_baseHom_extOut {gs gsK : GensData} (hinvG : IsInvariant (GensData.denote N gs)
    (baseSet n N)) {w : WinData} (hw : w.Valid N) (hwb : ∀ i ∈ w.1, n ≤ i)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) {X : Option (Out (Fin w.1.length))}
    (hden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin w.1.length)) X).comap
        (restrictHom hW (WinData.reindex hw))).map (GensData.denote N gs).subtype)
    (hinvK : IsInvariant (GensData.denote N gsK) (baseSet n N)) (g : ↥(GensData.denote N gsK)) :
    baseHom (GensData.denote N gsK) n hinvK g • extOut (winE hw hwb) X =
      extOut (winE hw hwb) X := by
  have hg : g.1 ∈ ((MulAction.stabilizer (Perm (Fin w.1.length)) X).comap
      (restrictHom hW (WinData.reindex hw))).map (GensData.denote N gs).subtype := by
    rw [← hden]
    exact g.2
  obtain ⟨h, hh, he⟩ := Subgroup.mem_map.1 hg
  rw [baseHom_congr hinvK hinvG g h he.symm]
  exact baseHom_extOut hinvG hw hwb hW h hh

/-- The leaf stabilizer lies in the group. -/
theorem leafStab_le {gs gsK : GensData} {w : WinData} (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) {X : Option (Out (Fin w.1.length))}
    (hden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin w.1.length)) X).comap
        (restrictHom hW (WinData.reindex hw))).map (GensData.denote N gs).subtype) :
    GensData.denote N gsK ≤ GensData.denote N gs := by
  rw [hden]
  exact Subgroup.map_subtype_le _

end Extend

/-! ### Coloured Johnson structures extended along a window -/

section CJExt

variable {m k : ℕ}

/-- **The colours of the remaining points**: `0` at the base indices in `L`, `1` at the others
(the individualized points). As `cjcol` adds one, a remaining point of `L` has colour `1` and
an individualized point colour `2`. -/
def restColsD (m : ℕ) (L : List ℕ) : Array ℕ :=
  ((List.range m).map fun x => if x ∈ L then 0 else 1).toArray

theorem get_restColsD {L : List ℕ} {x : ℕ} (hx : x < m) :
    get (restColsD m L) x = if x ∈ L then 0 else 1 := by
  simp [restColsD, get, hx]

theorem cjcol_restColsD {jd : JData} {L : List ℕ} (x : Fin m) :
    cjcol m (jd, restColsD m L) x =
      if x.val ∈ jrest m jd then (if x.val ∈ L then 0 else 1) + 1 else 0 := by
  unfold cjcol
  rw [get_restColsD x.2]

/-- **A coloured extension is preserved**: if `σ` and `π` are related by the numbering `e` of
`L`, and `π` fixes the Johnson embedding `J`, then `σ` fixes the coloured extension. -/
theorem cj_ext_stab {jd : JData} {L : List ℕ} {J : JEmb (Fin k)} (e : Fin k ↪ Fin m)
    (hL : ∀ x : Fin m, x.val ∈ L ↔ ∃ i, e i = x) (hjd : jdec m jd = extJohn e J)
    (σ : Perm (Fin m)) (π : Perm (Fin k)) (he : ∀ i, e (π i) = σ (e i)) (hJ : π • J = J) :
    σ • cjdec m (jd, restColsD m L) = cjdec m (jd, restColsD m L) := by
  have hJ' : σ • jdec m jd = jdec m jd := by
    rw [hjd, ← extJohn_relabel σ π he J, hJ]
  have hinv : ∀ i, σ⁻¹ (e i) = e (π⁻¹ i) := fun i => by
    have := he (π⁻¹ i)
    rw [perm_apply_inv_self] at this
    rw [this, perm_inv_apply_self]
  have hLσ : ∀ x : Fin m, (σ x).val ∈ L ↔ x.val ∈ L := fun x => by
    rw [hL, hL]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨π⁻¹ i, ?_⟩
      rw [← hinv, hi, perm_inv_apply_self]
    · rintro ⟨i, rfl⟩
      exact ⟨π i, he i⟩
  rw [cj_smul_eq_iff]
  refine ⟨hJ', fun x => ?_⟩
  show cjcol m (jd, restColsD m L) (σ x) = cjcol m (jd, restColsD m L) x
  have hR : (σ x).val ∈ jrest m jd ↔ x.val ∈ jrest m jd := by
    rw [cj_mem_jrest_iff, cj_mem_jrest_iff]
    conv_lhs => rw [← hJ']
    exact restPt_smul σ (jdec m jd) x
  rw [cjcol_restColsD, cjcol_restColsD]
  simp only [hR, hLσ]

/-- **The colour classes outside `V₀` are small**: for a Johnson embedding `J` on `k` points
with `k ≤ 2t` (so `|V₀| > t ≥ k/2`), extended along `e` into `m` points of which at most `m/2`
are left out, each colour class of the coloured extension outside `V₀` has at most `m/2`
points. Colour `0` (cells) and colour `1` (remaining points of `L`) lie in the image of `e`
off `V₀`; colour `2` (individualized points) lies off the image. -/
theorem cj_ext_hq {jd : JData} {L : List ℕ} {J : JEmb (Fin k)} {t : ℕ} (e : Fin k ↪ Fin m)
    (hL : ∀ x : Fin m, x.val ∈ L ↔ ∃ i, e i = x) (hjd : jdec m jd = extJohn e J)
    (hJ : IsJohnson univ t J) (hkt : k ≤ 2 * t) (hS : 2 * (m - k) ≤ m) (c : ℕ) :
    2 * (univ.filter fun γ => γ ∉ (jdec m jd).V0 ∧ cjcol m (jd, restColsD m L) γ = c).card ≤
      m := by
  have hkm : k ≤ m := by simpa using Fintype.card_le_of_embedding e
  have hV0 : (jdec m jd).V0 = J.V0.map e := by rw [hjd]; rfl
  have hΛ : (jdec m jd).Λ = J.Λ.image (fun A : Finset (Fin k) => A.map e) := by rw [hjd]; rfl
  set A₁ : Finset (Fin m) := univ.map e \ J.V0.map e with hA₁
  set A₂ : Finset (Fin m) := univ \ univ.map e with hA₂
  have hA₁c : A₁.card = k - J.V0.card := by
    rw [hA₁, card_sdiff_of_subset (map_subset_map.2 (subset_univ _)), card_map, card_map,
      card_univ, Fintype.card_fin]
  have hA₂c : A₂.card = m - k := by
    rw [hA₂, card_sdiff_of_subset (subset_univ _), card_map, card_univ, card_univ,
      Fintype.card_fin, Fintype.card_fin]
  have hgt := hJ.card_gt
  have hsub : (univ.filter fun γ => γ ∉ (jdec m jd).V0 ∧ cjcol m (jd, restColsD m L) γ = c) ⊆
      if c = 2 then A₂ else A₁ := by
    intro γ hγ
    rw [mem_filter] at hγ
    obtain ⟨-, hγV, hγc⟩ := hγ
    rw [cjcol_restColsD] at hγc
    rw [hV0] at hγV
    by_cases hR : γ.val ∈ jrest m jd
    · by_cases hγL : γ.val ∈ L
      · simp only [hR, hγL, ite_true] at hγc
        subst hγc
        simp only [show ((0 : ℕ) + 1 = 2) = False by decide, ite_false, hA₁, mem_sdiff,
          mem_map, mem_univ, true_and]
        obtain ⟨i, rfl⟩ := (hL γ).1 hγL
        exact ⟨⟨i, rfl⟩, fun h => hγV (mem_map.2 h)⟩
      · simp only [hR, hγL, ite_true, ite_false] at hγc
        subst hγc
        simp only [ite_true, hA₂, mem_sdiff, mem_univ, true_and, mem_map, not_exists]
        intro i hi
        exact hγL ((hL γ).2 ⟨i, hi⟩)
    · simp only [hR, ite_false] at hγc
      subst hγc
      simp only [show ((0 : ℕ) = 2) = False by decide, ite_false, hA₁, mem_sdiff, mem_map,
        mem_univ, true_and]
      refine ⟨?_, fun h => hγV (mem_map.2 h)⟩
      rw [cj_mem_jrest_iff] at hR
      unfold RestPt at hR
      rw [hV0] at hR
      have hB' : ∃ B ∈ (jdec m jd).Λ, γ ∈ B := by
        by_contra hno
        exact hR ⟨hγV, fun B hB hγB => hno ⟨B, hB, hγB⟩⟩
      obtain ⟨B, hB, hγB⟩ := hB'
      rw [hΛ, mem_image] at hB
      obtain ⟨A, -, rfl⟩ := hB
      obtain ⟨i, -, rfl⟩ := mem_map.1 hγB
      exact ⟨i, rfl⟩
  have hcard := card_le_card hsub
  split_ifs at hcard with hc
  · omega
  · omega

end CJExt

/-! ### Individualization -/

section Indiv

variable {N n : ℕ}

/-- After individualizing the first `j` base points, the remaining base `[n + j, N)` is
invariant. -/
theorem fixFirst_base_inv {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    (j : ℕ) : IsInvariant (fixFirst G n j) (baseSet (n + j) N) := by
  have := isInvariant_basePts hinv j
  rwa [denote_basePts] at this

/-- The first `j` base positions, as computed by `pointStabsProg`, give `fixFirst`. -/
theorem pointwiseStab_range' (G : Subgroup (Perm (Fin N))) (n j : ℕ) :
    pointwiseStab G {v : Fin N | v.val ∈ List.range' n j} = fixFirst G n j := by
  unfold fixFirst
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_range'_1]

theorem mem_range'_base {j u : ℕ} (hj : n + j ≤ N) (hu : u ∈ List.range' n j) :
    n ≤ u ∧ u < N := by
  rw [List.mem_range'_1] at hu
  omega

/-- **The individualized group is transitive on the rest**: if the base action is
`d`-transitive (`d ≥ 1`), the pointwise stabilizer of the first `d − 1` base points is
transitive on the remaining base `[n + d − 1, N)`. -/
theorem indiv_trans {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N)) {d : ℕ}
    (hd1 : 1 ≤ d) (hmt : IsMultiplyPretransitive (baseHom G n hinv).range (Fin (N - n)) d)
    (γ δ : Fin (N - (n + (d - 1)))) :
    ∃ g : ↥(fixFirst G n (d - 1)),
      baseHom (fixFirst G n (d - 1)) (n + (d - 1)) (fixFirst_base_inv hinv (d - 1)) g γ = δ := by
  have h' : IsMultiplyPretransitive (baseHom G n hinv).range (Fin (N - n)) ((d - 1) + 1) := by
    rwa [Nat.sub_add_cancel hd1]
  have hso := (sameOrbit_iff_stabTrans hinv (d - 1)).2 (stabTrans_of_isMultiplyPretransitive _ h')
  obtain ⟨_, _, g, hg, hgab⟩ := hso (n + (d - 1) + γ.val)
    (mem_basePts.2 ⟨by omega, by omega⟩) (n + (d - 1) + δ.val)
    (mem_basePts.2 ⟨by omega, by omega⟩)
  refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
  have e := baseHom_apply (hG := fixFirst_base_inv hinv (d - 1)) ⟨g, hg⟩ γ
  have hγp : (basePos γ : Fin N) = ⟨n + (d - 1) + γ.val, by omega⟩ := rfl
  rw [hγp] at e
  simp only at e
  rw [hgab] at e
  have := congrArg Fin.val e
  simp only [basePos] at this
  omega

/-- **The individualized group is not 2-transitive on the rest**: if the base action is
`d`-transitive but not `(d + 1)`-transitive (`1 ≤ d`, `d + 1 ≤ m`), the pointwise stabilizer
of the first `d − 1` base points is not 2-transitive on `[n + d − 1, N)`. -/
theorem indiv_not_two {G : Subgroup (Perm (Fin N))} (hinv : IsInvariant G (baseSet n N))
    {d : ℕ} (hd1 : 1 ≤ d) (hdm : d + 1 ≤ N - n)
    (hmt : IsMultiplyPretransitive (baseHom G n hinv).range (Fin (N - n)) d)
    (hnmt : ¬ IsMultiplyPretransitive (baseHom G n hinv).range (Fin (N - n)) (d + 1)) :
    ¬ IsMultiplyPretransitive
      (baseHom (fixFirst G n (d - 1)) (n + (d - 1)) (fixFirst_base_inv hinv (d - 1))).range
      (Fin (N - (n + (d - 1)))) 2 := by
  intro h2
  have hst1 := stabTrans_of_isMultiplyPretransitive _ (r := 1) h2
  -- the stabilizer of one more point is transitive on the rest: `StabTrans` at `d`
  have hd : StabTrans (baseHom G n hinv).range d := by
    refine (sameOrbit_iff_stabTrans hinv d).1 fun a ha b hb => ?_
    rw [mem_basePts] at ha hb
    obtain ⟨p, ⟨h, rfl⟩, hpfix, hpab⟩ :=
      hst1 ⟨a - (n + (d - 1)), by omega⟩ ⟨b - (n + (d - 1)), by omega⟩
        (by simp only; omega) (by simp only; omega)
    have hfix0 := hpfix ⟨0, by omega⟩ (by simp)
    have e0 := baseHom_apply (hG := fixFirst_base_inv hinv (d - 1)) h ⟨0, by omega⟩
    rw [hfix0] at e0
    have hmem : h.1 ∈ fixFirst G n d := by
      have hps := pointStab_fixFirst G n (d - 1) (show n + (d - 1) < N by omega)
      rw [Nat.sub_add_cancel hd1] at hps
      rw [← hps, mem_pointStab]
      refine ⟨h.2, ?_⟩
      have : (basePos (n := n + (d - 1)) (N := N) ⟨0, by omega⟩ : Fin N) =
          ⟨n + (d - 1), by omega⟩ := Fin.ext (by simp [basePos])
      rw [this] at e0
      exact e0.symm
    have eab := baseHom_apply (hG := fixFirst_base_inv hinv (d - 1)) h
      ⟨a - (n + (d - 1)), by omega⟩
    rw [hpab] at eab
    refine ⟨by omega, by omega, h.1, hmem, ?_⟩
    have ha' : (basePos (n := n + (d - 1)) (N := N) ⟨a - (n + (d - 1)), by omega⟩ : Fin N) =
        ⟨a, by omega⟩ := Fin.ext (by simp only [basePos]; omega)
    have hb' : (basePos (n := n + (d - 1)) (N := N) ⟨b - (n + (d - 1)), by omega⟩ : Fin N) =
        ⟨b, by omega⟩ := Fin.ext (by simp only [basePos]; omega)
    rw [ha', hb'] at eab
    exact eab.symm
  apply hnmt
  refine isMultiplyPretransitive_of_stabTrans _ hdm fun i hi => ?_
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · have := hmt
    have : IsMultiplyPretransitive (baseHom G n hinv).range (Fin (N - n)) (i + 1) :=
      MulAction.isMultiplyPretransitive_of_le (n := d) (by omega) (by simp; omega)
    exact stabTrans_of_isMultiplyPretransitive _ this
  · exact hd

/-- **A transitive base action has degree at least one**: with `1 ≤ cap`, the computed degree
of a transitive base action is at least `1`. -/
theorem one_le_degree {d cap : ℕ} {G : Subgroup (Perm (Fin N))}
    (hinv : IsInvariant G (baseSet n N))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥G, baseHom G n hinv g γ = δ) (hcap : 1 ≤ cap)
    (hspec : d < cap → ¬ IsMultiplyPretransitive (baseHom G n hinv).range (Fin (N - n)) (d + 1)) :
    1 ≤ d := by
  by_contra h0
  have hd0 : d = 0 := by omega
  subst hd0
  apply hspec (by omega)
  rw [MulAction.is_one_pretransitive_iff]
  refine ⟨fun γ δ => ?_⟩
  obtain ⟨g, hg⟩ := htr γ δ
  exact ⟨⟨baseHom G n hinv g, ⟨g, rfl⟩⟩, hg⟩

end Indiv

section IndivDegree

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **Individualization from the computed degree.** For a transitive base action whose computed
degree `d = degreeModel …` (with `cap ≤ m`, e.g. `cap = m − 2` as `giantProg` uses) is below
`cap` (not a giant): `1 ≤ d`, `d + 1 ≤ m`, and the pointwise stabilizer of the first `d − 1`
base points is transitive and not 2-transitive on the remaining base `[n + d − 1, N)`. -/
theorem indiv_of_degree (hO : MeetsContractOn DV degreeOps X.O) {N s n cap : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s G₀) {gs : GensData}
    {dd : D.denote} (hG : GroupValid DV N gs dd) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hcap : cap ≤ N - n)
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hinv g γ = δ)
    (hlt : degreeModel X.O n cap (N, gs, dd) < cap) :
    1 ≤ degreeModel X.O n cap (N, gs, dd) ∧ degreeModel X.O n cap (N, gs, dd) + 1 ≤ N - n ∧
      (∀ γ δ : Fin (N - (n + (degreeModel X.O n cap (N, gs, dd) - 1))),
        ∃ g : ↥(fixFirst (GensData.denote N gs) n (degreeModel X.O n cap (N, gs, dd) - 1)),
          baseHom _ _ (fixFirst_base_inv hinv (degreeModel X.O n cap (N, gs, dd) - 1)) g γ =
            δ) ∧
      ¬ IsMultiplyPretransitive
        (baseHom _ _ (fixFirst_base_inv hinv (degreeModel X.O n cap (N, gs, dd) - 1))).range
        (Fin (N - (n + (degreeModel X.O n cap (N, gs, dd) - 1)))) 2 := by
  obtain ⟨-, hmt, hstop⟩ := degreeModel_spec hO B hG hs hG₀ hinv hn hcap
  have hnmt := hstop hlt
  have hd1 := one_le_degree hinv htr (by omega) hstop
  have hdm : degreeModel X.O n cap (N, gs, dd) + 1 ≤ N - n := by omega
  exact ⟨hd1, hdm, indiv_trans hinv hd1 hmt, indiv_not_two hinv hd1 hdm hmt hnmt⟩

end IndivDegree

end GraphIso.Main
