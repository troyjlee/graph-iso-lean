module

public import GraphIso.Luks.MaxBlocks
public import GraphIso.Reductions.BlockAction
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The action on a maximal block system

For a group `G` transitive on a window and a block list `bs` that `G` permutes, the action
on block indices is `blockHom : G →* Perm (Fin k)` (`GraphIso/Reductions/BlockAction.lean`).

* `exists_blockHom_eq`: it is transitive on the blocks.
* `length_block_mul`: all blocks have the same size `|W| / k`.
* `card_range_mul_card_blockKernel`: the order of its image times the order of the block
  kernel is `|G|`, so the number of cosets of the kernel is the order of the image.
* `isPreprimitive_blocksOf`: for the labels of the maximal pass (every window point is in the
  class of `u` or has a closure with `u` that is a single class), the image acts
  primitively on the blocks. A block `B` of the image with two elements, translated to
  contain the block of `u`, gives the `G`-invariant relation "the blocks of `p` and `q` lie in
  a common translate of `B`"; it is refined by the labels and joins `u` with a point `v` of
  another block. The closure of `u` and `v` is a single class, and refines that relation, so
  every block lies in `B`.
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv Cost Sims MulAction Pointwise

variable {n : ℕ} {G : Subgroup (Perm (Fin n))} {w : WinData} {bs : List (List ℕ)}

theorem mem_getElem_congr {bs : List (List ℕ)} {i j : ℕ} {hi : i < bs.length}
    {hj : j < bs.length} (e : i = j) {p : ℕ} (h : p ∈ bs[i]) : p ∈ bs[j] := by
  subst e
  exact h

section Action

variable (hw : w.Valid n) (hbs : IsBlockList w bs) (hG : PermutesBlocks G bs)
include hw hbs hG

/-- The block action of a transitive group is transitive. -/
theorem exists_blockHom_eq (htr : ∀ p ∈ w.1, ∀ q ∈ w.1, SameOrbit G p q)
    (t t' : Fin bs.length) : ∃ g : G, blockHom hw hbs hG g t = t' := by
  have hp := blockReps_mem hbs t.2
  have hq := blockReps_mem hbs t'.2
  obtain ⟨hp', hq', g, hg, e⟩ := htr _ (mem_of_block hbs t.2 hp) _ (mem_of_block hbs t'.2 hq)
  refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
  rw [blockHom_apply, ← blockMap_eq hw hbs hG hg t.2 (u := ⟨_, hp'⟩) hp, e]
  exact get_blockIdx hw hbs t'.2 hq

omit hG in
theorem nodup_of_mem_blocks {b : List ℕ} (hb : b ∈ bs) : b.Nodup :=
  (List.nodup_flatten.1 (hbs.1.nodup_iff.2 hw.nodup)).1 b hb

omit hG in
theorem lt_of_mem_block {t : ℕ} (ht : t < bs.length) {p : ℕ} (hp : p ∈ bs[t]) : p < n :=
  hw.lt p (mem_of_block hbs ht hp)

/-- Blocks of a transitive group have the same size. -/
theorem length_block_le (htr : ∀ p ∈ w.1, ∀ q ∈ w.1, SameOrbit G p q)
    (t t' : Fin bs.length) : bs[t.1].length ≤ bs[t'.1].length := by
  obtain ⟨g, hg⟩ := exists_blockHom_eq hw hbs hG htr t t'
  obtain ⟨_, himg⟩ := blockMap_spec hw hbs hG g.2 t.2
  let f : ℕ → ℕ := fun p => if h : p < n then ((g : Perm (Fin n)) ⟨p, h⟩).val else p
  have hmap : ∀ p ∈ bs[t.1], f p ∈ bs[t'.1] := by
    intro p hp
    have hpn := lt_of_mem_block hw hbs t.2 hp
    have := himg ⟨p, hpn⟩ hp
    have e : blockMap n bs g t = t' := by
      rw [← blockHom_apply hw hbs hG g t, hg]
    simp only [f, hpn, ↓reduceDIte]
    exact mem_getElem_congr e this
  have hinj : ∀ p ∈ bs[t.1], ∀ q ∈ bs[t.1], f p = f q → p = q := by
    intro p hp q hq hpq
    have hpn := lt_of_mem_block hw hbs t.2 hp
    have hqn := lt_of_mem_block hw hbs t.2 hq
    simp only [f, hpn, hqn, ↓reduceDIte] at hpq
    have := (g : Perm (Fin n)).injective (Fin.ext hpq)
    exact congrArg Fin.val this
  have hnd := (nodup_of_mem_blocks hw hbs (List.getElem_mem t.2)).map_on hinj
  have := (List.subperm_of_subset hnd fun x hx => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact hmap p hp).length_le
  simpa using this

/-- **Blocks of a transitive group all have size `|W| / k`.** -/
theorem length_block_mul (htr : ∀ p ∈ w.1, ∀ q ∈ w.1, SameOrbit G p q) {b : List ℕ}
    (hb : b ∈ bs) : b.length * bs.length = w.1.length := by
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
  have hall : ∀ b' ∈ bs, b'.length = bs[t].length := by
    intro b' hb'
    obtain ⟨t', ht', rfl⟩ := List.getElem_of_mem hb'
    exact le_antisymm (length_block_le hw hbs hG htr ⟨t', ht'⟩ ⟨t, ht⟩)
      (length_block_le hw hbs hG htr ⟨t, ht⟩ ⟨t', ht'⟩)
  rw [← hbs.1.length_eq, List.length_flatten, List.map_congr_left hall, sum_map_const,
    Nat.mul_comm]

/-- The kernel of the block action is the block kernel. -/
theorem blockHom_eq_one_iff (g : G) : blockHom hw hbs hG g = 1 ↔ (g : Perm (Fin n)) ∈
    blockKernel G bs := by
  constructor
  · intro h
    refine ⟨g.2, fun b hb u hu => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨_, himg⟩ := blockMap_spec hw hbs hG g.2 ht
    have e : blockMap n bs g t = t := by
      have := congrArg (fun π : Perm (Fin bs.length) => (π ⟨t, ht⟩).val) h
      simpa [blockHom_apply] using this
    exact mem_getElem_congr e (himg u hu)
  · intro h
    ext t
    rw [blockHom_apply]
    exact blockMap_of_mem_blockKernel hw hbs h t.2

/-- **The order of the image of the block action times the order of the block kernel is
`|G|`.** -/
theorem card_range_mul_card_blockKernel :
    Nat.card (blockHom hw hbs hG).range * Nat.card (blockKernel G bs) = Nat.card G := by
  have hker : Nat.card (blockHom hw hbs hG).ker = Nat.card (blockKernel G bs) := by
    refine Nat.card_congr
      { toFun := fun g => ⟨(g : G), (blockHom_eq_one_iff hw hbs hG g).1 g.2⟩
        invFun := fun g => ⟨⟨g, (blockKernel_le G bs) g.2⟩,
          (blockHom_eq_one_iff hw hbs hG ⟨g, _⟩).2 g.2⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  rw [← hker, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange (blockHom hw hbs hG)).toEquiv,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

end Action

/-! ### Primitivity -/

section Primitive

variable {gs : GensData} {pts : List ℕ} {mask : Array Bool} {cl : Array ℕ} {u : ℕ}

/-- The image of the block action, acting on block indices. -/
theorem range_smul_def {k : ℕ} {H : Subgroup (Perm (Fin k))} (h : H) (t : Fin k) :
    h • t = (h : Perm (Fin k)) t := rfl

/-- **The block action of the maximal pass is primitive.** -/
theorem isPreprimitive_blocksOf (hW : Win n gs pts) (hgs : GensData.AllValid n gs)
    (hw : WinData.Valid n (pts, mask)) (hcl : LabelsOK n pts cl) (hst : Stable gs pts cl)
    (hu : u ∈ pts) (htr : ∀ p ∈ pts, ∀ q ∈ pts, SameOrbit (GensData.denote n gs) p q)
    (hmax : ∀ v ∈ pts, get cl v = get cl u ∨ oneClass (closure gs pts cl u v) pts u = true)
    (hbs : IsBlockList (pts, mask) (blocksOf cl pts))
    (hG : PermutesBlocks (GensData.denote n gs) (blocksOf cl pts)) :
    IsPreprimitive (blockHom hw hbs hG).range (Fin (blocksOf cl pts).length) := by
  set bs := blocksOf cl pts with hbs_def
  set φ := blockHom hw hbs hG with hφ
  -- the image is transitive
  have htrans : ∀ t t' : Fin bs.length, ∃ h : φ.range, h • t = t' := by
    intro t t'
    obtain ⟨g, hg⟩ := exists_blockHom_eq hw hbs hG htr t t'
    exact ⟨⟨φ g, g, rfl⟩, hg⟩
  have : IsPretransitive φ.range (Fin bs.length) := ⟨htrans⟩
  refine ⟨fun {B} hB => ?_⟩
  by_cases hsub : B.Subsingleton
  · exact Or.inl hsub
  right
  rw [Set.not_subsingleton_iff] at hsub
  obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := hsub
  -- the block of `u`
  obtain ⟨tu, htu, hutu⟩ := exists_block hbs hu
  set Tu : Fin bs.length := ⟨tu, htu⟩
  obtain ⟨h₁, hh₁⟩ := htrans t₁ Tu
  -- the translate of `B` containing the block of `u`
  set B₁ := h₁ • B with hB₁
  have hB₁blk : IsBlock φ.range B₁ := hB.translate h₁
  have hTu : Tu ∈ B₁ := ⟨t₁, ht₁, hh₁⟩
  have ht₂' : h₁ • t₂ ∈ B₁ := Set.smul_mem_smul_set ht₂
  have hne' : h₁ • t₂ ≠ Tu := by
    rw [← hh₁]
    exact fun e => hne (smul_left_cancel h₁ e).symm
  suffices hall : B₁ = Set.univ by
    have : B = h₁⁻¹ • B₁ := by rw [hB₁, smul_smul, inv_mul_cancel, one_smul]
    rw [this, hall, Set.smul_set_univ]
  -- the relation given by translates of `B₁`
  let F : ℕ → ℕ → Prop := fun a b => a = b ∨ ∃ (h : φ.range) (t t' : Fin bs.length),
    t ∈ h • B₁ ∧ t' ∈ h • B₁ ∧ a ∈ bs[t.1] ∧ b ∈ bs[t'.1]
  -- translates sharing a block index are equal
  have hsame : ∀ (h h' : φ.range) (t : Fin bs.length), t ∈ h • B₁ → t ∈ h' • B₁ →
      h • B₁ = h' • B₁ := by
    intro h h' t ht ht'
    by_contra hne
    exact Set.disjoint_left.1 (hB₁blk hne) ht ht'
  have huniq : ∀ (t t' : Fin bs.length) (p : ℕ), p ∈ bs[t.1] → p ∈ bs[t'.1] → t = t' :=
    fun t t' p hp hp' => Fin.ext (block_unique hw hbs t.2 t'.2 hp hp')
  have hFeq : Equivalence F := by
    refine ⟨fun _ => Or.inl rfl, fun {a b} hab => ?_, fun {a b c} hab hbc => ?_⟩
    · rcases hab with rfl | ⟨h, t, t', ht, ht', ha, hb⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h, t', t, ht', ht, hb, ha⟩
    · rcases hab with rfl | ⟨h, t₁, t₂, ht₁, ht₂, ha, hb⟩
      · exact hbc
      rcases hbc with rfl | ⟨h', t₃, t₄, ht₃, ht₄, hb', hc⟩
      · exact Or.inr ⟨h, t₁, t₂, ht₁, ht₂, ha, hb⟩
      have e₂₃ := huniq t₂ t₃ b hb hb'
      subst e₂₃
      have e := hsame h h' t₂ ht₂ ht₃
      exact Or.inr ⟨h, t₁, t₄, ht₁, e ▸ ht₄, ha, hc⟩
  -- every block index lies in a translate
  have hcover : ∀ t : Fin bs.length, ∃ h : φ.range, t ∈ h • B₁ := by
    intro t
    obtain ⟨h, hh⟩ := htrans Tu t
    exact ⟨h, hh ▸ Set.smul_mem_smul_set hTu⟩
  have hFinv : InvRel gs pts F := by
    refine ⟨hFeq, fun g hg a ha b hb hab => ?_⟩
    rcases hab with rfl | ⟨h, t, t', ht, ht', hat, hbt⟩
    · exact Or.inl rfl
    have hgv := hgs g hg
    have hπ : PermData.denote n g ∈ GensData.denote n gs :=
      Subgroup.subset_closure ⟨g, hg, rfl⟩
    set π : GensData.denote n gs := ⟨PermData.denote n g, hπ⟩
    have himg : ∀ (s : Fin bs.length) (p : ℕ), p ∈ bs[s.1] →
        get g.1 p ∈ bs[(φ π s).1] := by
      intro s p hp
      have hpn := lt_of_mem_block hw hbs s.2 hp
      obtain ⟨_, him⟩ := blockMap_spec hw hbs hG hπ s.2
      have := him ⟨p, hpn⟩ hp
      rw [PermData.val_denote_apply hgv] at this
      exact mem_getElem_congr (blockHom_apply hw hbs hG π s).symm this
    refine Or.inr ⟨⟨φ π, π, rfl⟩ * h, φ π t, φ π t', ?_, ?_, himg t a hat, himg t' b hbt⟩
    · rw [mul_smul]
      exact Set.smul_mem_smul_set (a := (⟨φ π, π, rfl⟩ : φ.range)) ht
    · rw [mul_smul]
      exact Set.smul_mem_smul_set (a := (⟨φ π, π, rfl⟩ : φ.range)) ht'
  -- the labels refine `F`
  have hFref : Refines pts cl F := by
    intro a ha b hb hab
    obtain ⟨b₀, hb₀, hab₀, hbb₀⟩ := (mem_blocksOf_iff hcl ha hb).2 hab
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb₀
    obtain ⟨h, hh⟩ := hcover ⟨t, ht⟩
    exact Or.inr ⟨h, ⟨t, ht⟩, ⟨t, ht⟩, hh, hh, hab₀, hbb₀⟩
  -- a point of the second block
  set T₂ := h₁ • t₂
  have hv := blockReps_mem hbs T₂.2
  set v := (blockReps bs).getD T₂.1 0
  have hvp : v ∈ pts := mem_of_block hbs T₂.2 hv
  have hFuv : F u v := Or.inr ⟨1, Tu, T₂, by rw [one_smul]; exact hTu,
    by rw [one_smul]; exact ht₂', hutu, hv⟩
  have hvu : get cl v ≠ get cl u := by
    intro e
    obtain ⟨b₀, hb₀, hvb, hub⟩ := (mem_blocksOf_iff hcl hvp hu).2 e
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb₀
    have e₁ := huniq ⟨t, ht⟩ T₂ v hvb hv
    have e₂ := huniq ⟨t, ht⟩ Tu u hub hutu
    exact hne' (e₁.symm.trans e₂)
  have hone := (hmax v hvp).resolve_left hvu
  obtain ⟨-, -, -, -, hmin⟩ := closure_spec hW hcl hst hu hvp
  have hR := hmin F hFinv hFref hFuv
  rw [oneClass_iff] at hone
  -- every block lies in `B₁`
  refine Set.eq_univ_of_forall fun t => ?_
  have hp := blockReps_mem hbs t.2
  have hpp : (blockReps bs).getD t.1 0 ∈ pts := mem_of_block hbs t.2 hp
  rcases hR _ hpp u hu (hone _ hpp) with e | ⟨h, t', t'', ht', ht'', hp', hu'⟩
  · rw [huniq t Tu u (e ▸ hp) hutu]
    exact hTu
  · have e₁ := huniq t' t _ hp' hp
    have e₂ := huniq t'' Tu u hu' hutu
    rw [e₂] at ht''
    rw [e₁] at ht'
    have e := hsame h 1 Tu ht'' (by rw [one_smul]; exact hTu)
    rw [one_smul] at e
    exact e ▸ ht'

end Primitive

/-! ### The specification of `maxBlocks` -/

/-- The window hypotheses of a valid invariant window. -/
theorem win_of_valid {gs : GensData} (hw : w.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) : Win n gs w.1 := by
  refine ⟨hw.nodup, hw.lt, fun g hg p hp => ?_⟩
  have h := hinv (PermData.denote n g) (Subgroup.subset_closure ⟨g, hg, rfl⟩) ⟨p, hw.lt p hp⟩ hp
  change (PermData.denote n g ⟨p, hw.lt p hp⟩).val ∈ w.1 at h
  rwa [PermData.val_denote_apply (hgs g hg)] at h

/-- **The maximal block system.** For a group transitive on a window of at least two points,
`maxBlocks` is a block list the group permutes, with at least two blocks of equal size, on
which the group acts primitively. -/
theorem maxBlocks_spec {gs : GensData} (hw : w.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) {u : ℕ} {rest : List ℕ}
    (hpts : w.1 = u :: rest) (hrest : rest ≠ [])
    (htr : ∀ j, j ∈ w.1 ↔ SameOrbit (GensData.denote n gs) u j) :
    ∃ (hbs : IsBlockList w (maxBlocks n gs w.1))
      (hG : PermutesBlocks (GensData.denote n gs) (maxBlocks n gs w.1)),
      2 ≤ (maxBlocks n gs w.1).length ∧
      (∀ b ∈ maxBlocks n gs w.1, b.length * (maxBlocks n gs w.1).length = w.1.length) ∧
      IsPreprimitive (blockHom hw hbs hG).range (Fin (maxBlocks n gs w.1).length) := by
  have hW := win_of_valid hw hgs hinv
  have hu : u ∈ w.1 := hpts ▸ List.mem_cons_self
  have htwo : ∃ p ∈ w.1, p ≠ u := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil rest hrest
    have hnd := hw.nodup
    rw [hpts, List.nodup_cons] at hnd
    exact ⟨p, hpts ▸ List.mem_cons_of_mem _ hp, fun e => hnd.1 (e ▸ hp)⟩
  have hmb : maxBlocks n gs w.1 = blocksOf (maxLabels n gs w.1 u) w.1 := by
    rw [hpts]
    rfl
  rw [hmb]
  have hI := maxLabels_spec hW hu htwo
  have hbs : IsBlockList w (blocksOf (maxLabels n gs w.1 u) w.1) :=
    isBlockList_blocksOf hW.nodup hI.labels w.2
  have hG := permutesBlocks_blocksOf hW hgs hI.labels hI.stable
  have htr' : ∀ p ∈ w.1, ∀ q ∈ w.1, SameOrbit (GensData.denote n gs) p q :=
    fun p hp q hq => ((htr p).1 hp).symm.trans ((htr q).1 hq)
  exact ⟨hbs, hG, two_le_length_blocksOf hI.labels hu hI.two,
    fun b hb => length_block_mul hw hbs hG htr' hb,
    isPreprimitive_blocksOf hW hgs hw hI.labels hI.stable hu htr' hI.maximal hbs hG⟩

end GraphIso.Luks
