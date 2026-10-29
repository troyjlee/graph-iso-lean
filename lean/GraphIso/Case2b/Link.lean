module

public import GraphIso.Case2b.Tree
public import GraphIso.Case2b.ChoiceProg
public import GraphIso.Case2b.OutOps

/-!
# Case 2b: the data pipeline is the choice tree

Stage 14h, item 3 (`PLAN-14.md` §12): the leaves computed on data by `allLeavesD` and
`firstLeafD` (`Pipeline.lean`) are those of the model `case2bTree` (`Tree.lean`), for
`P = ψ(F)` (the base action of the group `F` given as backend data, `F.1 = N`), `Φ` the listed
points, and a backend meeting its contract:

* `lk_res`: the group computed for a tuple `S` (`resModel`) is the group the elements of `P`
  fixing `S` induce on `Φ ∖ S` numbered in increasing order (`phiE`, `fixGroup`);
* `lk_orb`, `lk_choice`: its orbital array is the orbital relation `orbRel`, so the leaves of
  one choice decode to those of `leafTree`;
* `allLeavesD_leafMs`: the decoded list of all leaves is the leaf multiset of
  `case2bTree P Φ (j + 1)`, under `Case2bHyp P Φ (j + 1)`;
* `firstLeafD_reach`, `firstLeafD_ne_none`: the first leaf exists and is a leaf of the tree;
* `sojSz_le`: the `soj` tree built for a listed choice has size at most `sojZ (N − n)`, from
  `size_le_of_live`, `height_soj_le` and the liveness and count of `cb_choice_spec`;
* `allLeavesD_valid`, `firstLeafD_valid`: every listed leaf satisfies `OutValid`. Colored
  partitions come from `case2bTree_valid`; Johnson embeddings meet `jvalid_of_isJohnson` with
  the shape conditions `JShape`. These combine the model (`ValidLeaf`) with data facts
  (`LkJD`), which the Johnson leaves of `soj` on data have by an invariant of stage 14d's
  worklist (`lk_sojD_john`: frames with duplicate-free cells).
* `firstLeafD_partLe` (stage 14j-6b-1): a first leaf that is not a Johnson leaf decodes to a
  colored `t`-partition with `t ≤ max ((|Φ| − j + 3) / 2) (m − (|Φ| − j))`
  (`case2bTree_partLe`).
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv MulAction Pointwise Finset GraphIso GraphIso.Cost GraphIso.SplitJohnson
  GraphIso.SoJProg GraphIso.SoJTree GraphIso.Toolkit GraphIso.Recursion GraphIso.Coherent
  GraphIso.Align

/-! ### The group of one choice -/

section Group

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}

/-- Iterated stabilizers compute the pointwise stabilizer (the contract alone). -/
theorem lk_iterStab (hO : MeetsContractOn DV stabOps O) {M : ℕ} :
    ∀ (ps : List ℕ) (ks : GensData) (e : D.denote), (∀ u ∈ ps, u < M) →
      GroupValid DV M ks e →
      (iterStabModel O (M, ks, e) ps).1 = M ∧
        GroupValid DV M (iterStabModel O (M, ks, e) ps).2.1 (iterStabModel O (M, ks, e) ps).2.2 ∧
        GensData.denote M (iterStabModel O (M, ks, e) ps).2.1 =
          pointwiseStab (GensData.denote M ks) {v : Fin M | v.val ∈ ps} := by
  intro ps
  induction ps with
  | nil =>
    intro ks e _ hv
    refine ⟨rfl, hv, ?_⟩
    ext g
    show g ∈ GensData.denote M ks ↔ _
    simp [pointwiseStab]
  | cons u ps ih =>
    intro ks e hps hv
    have hu : u < M := hps u List.mem_cons_self
    have hpre : GroupPre DV .stabilizer ((M, ks, e), u) := ⟨hv, hu⟩
    have hpost := hO .stabilizer _ (Or.inl rfl) hpre
    rcases hS : O.run GroupOp.stabilizer ((M, ks, e), u) with ⟨M', ks', e'⟩
    rw [hS] at hpost
    obtain ⟨hM', hv', hden⟩ := hpost
    change M' = M at hM'
    subst M'
    have hmodel : iterStabModel O (M, ks, e) (u :: ps) = iterStabModel O (M, ks', e') ps := by
      show List.foldl _ (O.run GroupOp.stabilizer ((M, ks, e), u)) ps = _
      rw [hS]
      rfl
    obtain ⟨h1, h2, h3⟩ := ih ks' e' (fun v hv => hps v (List.mem_cons_of_mem _ hv)) hv'
    rw [hmodel]
    refine ⟨h1, h2, ?_⟩
    rw [h3, hden hu, pointwiseStab_pointStab]

/-- Membership in a group of generators read at an equal degree. -/
theorem lk_denote_cast {a b : ℕ} (hab : a = b) (gs : GensData) (π : Perm (Fin b)) :
    π ∈ GensData.denote b gs ↔ (finCongr hab.symm).permCongr π ∈ GensData.denote a gs := by
  subst hab
  exact Iff.rfl

/-- A context carrying the backend alone (the orbital lemmas are stated for contexts). -/
def lkCtx (O : Oracle (groupSig D)) : Ctx (groupSig D) := ⟨O, ⟨fun _ _ _ => 0⟩, fun _ _ => True⟩

end Group

/-! ### The numbering of `Φ ∖ S` -/

section Numbering

variable {m : ℕ} {Φl Sl : List ℕ}

/-- The numbering of `Φ ∖ S` listed by `phiSD`, as an embedding into the base. -/
def phiE (m : ℕ) (Φl Sl : List ℕ) : Fin (phiSD m Φl Sl).length ↪ Fin m :=
  ⟨eFin (phiSD m Φl Sl) fun _ hv => (mem_phiSD.1 hv).1, fun i j h => by
    have := congrArg Fin.val h
    simp only [eFin] at this
    exact Fin.ext ((List.Nodup.getElem_inj_iff (phiSD_nodup m Φl Sl)).1 this)⟩

theorem phiE_val (i : Fin (phiSD m Φl Sl).length) : (phiE m Φl Sl i).val = (phiSD m Φl Sl)[i] :=
  rfl

/-- The range of the numbering is `Φ ∖ S`. -/
theorem phiE_range (v : Fin m) : (∃ i, phiE m Φl Sl i = v) ↔ v ∈ setOf m Φl \ setOf m Sl := by
  simp only [Finset.mem_sdiff, mem_setOf]
  constructor
  · rintro ⟨i, rfl⟩
    have := mem_phiSD.1 (List.getElem_mem i.2)
    exact ⟨this.2.1, this.2.2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem (mem_phiSD.2 ⟨v.2, h1, h2⟩)
    exact ⟨⟨i, hi⟩, Fin.ext hiv⟩

theorem lk_eInv (v : Fin m) : eInv (phiSD m Φl Sl) v = epre (phiE m Φl Sl) v := by
  by_cases hv : v.val ∈ phiSD m Φl Sl
  · obtain ⟨i, hi, -, hiv⟩ := cp2_eInv_some (fun _ hv => (mem_phiSD.1 hv).1) hv
    rw [hi, eq_comm, epre_eq_some]
    exact hiv
  · rw [cp2_eInv_none hv, eq_comm, epre_eq_none]
    rintro i rfl
    exact hv (List.getElem_mem _)

/-- **The extension along the numbering is `extOut`.** -/
theorem lk_pipeExt (o : Option (Out (Fin (phiSD m Φl Sl).length))) :
    pipeExt (eFin (phiSD m Φl Sl) fun _ hv => (mem_phiSD.1 hv).1) (eInv (phiSD m Φl Sl)) o =
      extOut (phiE m Φl Sl) o := by
  have hei : eInv (phiSD m Φl Sl) = epre (phiE m Φl Sl) := funext lk_eInv
  rw [hei]
  rcases o with _ | p | J
  · rfl
  · simp only [pipeExt, extOut, extPart, Option.some.injEq, Sum.inl.injEq, CPart.mk.injEq]
    refine ⟨rfl, funext fun v => ?_⟩
    rcases epre (phiE m Φl Sl) v with _ | i
    · ext w
      simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_map, not_exists, epre_eq_none]
    · exact (Finset.map_eq_image (phiE m Φl Sl) _).symm
  · simp only [pipeExt, extOut, extJohn, Option.some.injEq, Sum.inr.injEq, JEmb.mk.injEq]
    refine ⟨(Finset.map_eq_image (phiE m Φl Sl) _).symm, ?_, trivial, funext fun v => ?_⟩
    · exact image_congr fun A _ => (Finset.map_eq_image (phiE m Φl Sl) A).symm
    · rcases epre (phiE m Φl Sl) v with _ | i
      · rfl
      · exact image_congr fun A _ => (Finset.map_eq_image (phiE m Φl Sl) A).symm

theorem lk_setOf_card {l : List ℕ} (hnd : l.Nodup) (hlt : ∀ v ∈ l, v < m) :
    (setOf m l).card = l.length := by
  have : (setOf m l).map Fin.valEmbedding = l.toFinset := by
    ext x
    simp only [mem_map, mem_setOf, Fin.valEmbedding_apply, List.mem_toFinset]
    exact ⟨fun ⟨y, hy, hyx⟩ => hyx ▸ hy, fun hx => ⟨⟨x, hlt x hx⟩, hx, rfl⟩⟩
  rw [← card_map Fin.valEmbedding, this, List.toFinset_card_of_nodup hnd]

theorem lk_card_phi : (setOf m Φl \ setOf m Sl).card = (phiSD m Φl Sl).length := by
  have : setOf m Φl \ setOf m Sl = univ.map (phiE m Φl Sl) := by
    ext v
    rw [← phiE_range]
    simp
  rw [this, card_map, card_univ, Fintype.card_fin]

/-- A listed tuple: its points are below `m`, among `Φ`, and `j` of them. -/
theorem lk_tuple {j : ℕ} (hΦlt : ∀ v ∈ Φl, v < m) (hS : Sl ∈ tuplesD Φl j) :
    (∀ s ∈ Sl, s < m) ∧ setOf m Sl ⊆ setOf m Φl ∧ (setOf m Sl).card = j := by
  obtain ⟨hlen, hnd, hmem⟩ := (mem_tuplesD Φl j).1 hS
  have hlt : ∀ s ∈ Sl, s < m := fun s hs => hΦlt s (hmem s hs)
  refine ⟨hlt, fun x hx => mem_setOf.2 (hmem _ (mem_setOf.1 hx)), ?_⟩
  rw [lk_setOf_card hnd hlt, hlen]

theorem lk_setOf_val (l : List (Fin m)) : setOf m (l.map Fin.val) = l.toFinset := by
  ext x
  simp only [mem_setOf, List.mem_map, List.mem_toFinset]
  exact ⟨fun ⟨y, hy, hyx⟩ => Fin.ext hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

/-- After a listed tuple, at least four points of `Φ` remain. -/
theorem lk_four {P : Subgroup (Perm (Fin m))} {j : ℕ} (hΦlt : ∀ v ∈ Φl, v < m)
    (H : Case2bHyp P (setOf m Φl) (j + 1)) (hS : Sl ∈ tuplesD Φl j) :
    4 ≤ (phiSD m Φl Sl).length := by
  obtain ⟨-, hsub, hcard⟩ := lk_tuple hΦlt hS
  rw [← lk_card_phi, card_sdiff_of_subset hsub]
  have := H.size
  omega

/-- A tuple is listed: the first `j` points. -/
theorem lk_take_mem {P : Subgroup (Perm (Fin m))} {j : ℕ} (hΦnd : Φl.Nodup)
    (hΦlt : ∀ v ∈ Φl, v < m) (H : Case2bHyp P (setOf m Φl) (j + 1)) :
    Φl.take j ∈ tuplesD Φl j := by
  have hlen := H.size
  rw [lk_setOf_card hΦnd hΦlt] at hlen
  rw [mem_tuplesD]
  refine ⟨by simp; omega, hΦnd.sublist (List.take_sublist _ _), fun x hx => ?_⟩
  exact List.mem_of_mem_take hx

end Numbering


/-! ### Generalities -/

section General

theorem lk_wlRel_congr {Φ : Type*} [Fintype Φ] [DecidableEq Φ] {R R' : Φ → Φ → Prop}
    [i : DecidableRel R] [i' : DecidableRel R'] (h : ∀ u v, R u v ↔ R' u v) :
    wlRel R = wlRel R' := by
  obtain rfl : R = R' := funext₂ fun u v => propext (h u v)
  obtain rfl : i = i' := Subsingleton.elim _ _
  rfl

variable {Γ : Type*} {m' : ℕ} {P : Subgroup (Perm Γ)} {Φ S : Finset Γ} {e : Fin m' ↪ Γ}

/-- Elements of `P` preserving `Φ` and fixing `S` map the numbered `Φ ∖ S` onto itself. -/
theorem lk_maps [DecidableEq Γ] (hpres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ)
    (hr : ∀ v, (∃ i, e i = v) ↔ v ∈ Φ \ S) :
    ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (e i) = e j := by
  intro g hg hS i
  have hi := Finset.mem_sdiff.1 ((hr (e i)).1 ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := (hr (g (e i))).2 (Finset.mem_sdiff.2 ⟨hpres g hg _ hi.1, fun hgS => hi.2 (by
    have := hS _ hgS
    rw [← g.injective this]
    exact hgS)⟩)
  exact ⟨j, hj.symm⟩

/-- Transitivity on `Φ ∖ S` is transitivity of the induced group. -/
theorem lk_pretrans [DecidableEq Γ] (hpres : ∀ g ∈ P, ∀ x ∈ Φ, g x ∈ Φ)
    (hr : ∀ v, (∃ i, e i = v) ↔ v ∈ Φ \ S)
    (htr : ∀ x ∈ Φ \ S, ∀ y ∈ Φ \ S, ∃ g ∈ P, (∀ s ∈ S, g s = s) ∧ g x = y) :
    IsPretransitive (fixGroup P S e) (Fin m') := by
  refine ⟨fun γ δ => ?_⟩
  obtain ⟨g, hg, hS, hgy⟩ := htr (e γ) ((hr _).1 ⟨γ, rfl⟩) (e δ) ((hr _).1 ⟨δ, rfl⟩)
  obtain ⟨h, hh, he⟩ := cb_realize hg hS (lk_maps hpres hr g hg hS)
  exact ⟨⟨h, hh⟩, e.injective ((he γ).symm.trans hgy)⟩

theorem lk_act_one {C O G : Type*} [Group G] [MulAction G C] [MulAction G O] [DecidableEq C]
    (t : CTree C O) : t.act (1 : G) = t := by
  induction t with
  | leaf o => simp only [CTree.act, one_smul]
  | node S k ih =>
    simp only [CTree.act, one_smul, inv_one]
    congr 1
    funext c
    exact ih c

/-- The leaf tree depends on the numbering only through its range. -/
theorem lk_leafTree_congr {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {P : Subgroup (Perm Γ)}
    [DecidablePred (· ∈ P)] (S : Finset Γ) (a b : Γ) {m m₂ : ℕ} (e : Fin m ↪ Γ)
    (e' : Fin m₂ ↪ Γ) (hm : m₂ = m) (hr : ∀ v, (∃ j, e' j = v) ↔ ∃ i, e i = v) :
    leafTree P S a b e' = leafTree P S a b e := by
  have h := leafTree_relabel (1 : Perm Γ) (P := P) (P' := P) (fun g => by simp) S a b e e' hm
    (fun v => by rw [inv_one, Perm.one_apply]; exact hr v)
  rw [lk_act_one, one_smul, Perm.one_apply, Perm.one_apply] at h
  exact h

theorem lk_flatMap_coe {α β γ : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (f : α → List β) (g : β → γ) :
    (((l.flatMap f).map g : List γ) : Multiset γ) =
      ∑ x ∈ l.toFinset, (((f x).map g : List γ) : Multiset γ) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.map_append, ← Multiset.coe_add, ih hl.2, List.toFinset_cons,
      Finset.sum_insert (by simpa using hl.1)]

theorem lk_live_of_trans {C C' O O' : Type*} [DecidableEq C'] {f : C → C'} {r : C' → C}
    {h : O → O'} (hr : ∀ c, r (f c) = c) {t : CTree C O} (ht : (t.trans f r h).Live) :
    t.Live := by
  induction t with
  | leaf o => trivial
  | node S k ih =>
    obtain ⟨hS, hk⟩ := ht
    refine ⟨?_, fun c hc => ih c ?_⟩
    · obtain ⟨c', hc'⟩ := hS
      obtain ⟨c, hc, -⟩ := mem_image.1 hc'
      exact ⟨c, hc⟩
    · have h' : ((k (r (f c))).trans f r h).Live := hk (f c) (mem_image_of_mem f hc)
      rw [hr] at h'
      exact h'

end General

/-! ### The group of one choice is the group of the tree -/

section Res

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}

theorem lk_baseHom_eq {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hG : IsInvariant G (baseSet n N)}
    (g : G) (x y : Fin (N - n)) : baseHom G n hG g x = y ↔ g.1 (basePos x) = basePos y := by
  rw [← baseHom_apply (hG := hG)]
  exact ⟨fun h => by rw [h], fun h => basePos_injective h⟩

theorem lk_baseHom_zero {M : ℕ} {G : Subgroup (Perm (Fin M))} {hG : IsInvariant G (baseSet 0 M)}
    (g : G) : (baseHom G 0 hG g : Perm (Fin M)) = g.1 := by
  ext x
  have h := congrArg Fin.val (baseHom_apply (hG := hG) g x)
  have hx : (basePos (n := 0) x : Fin M) = x := Fin.ext (Nat.zero_add _)
  rw [hx] at h
  simpa [basePos] using h

theorem lk_mem_range_zero {M : ℕ} {G : Subgroup (Perm (Fin M))}
    {hG : IsInvariant G (baseSet 0 M)} (p : Perm (Fin M)) :
    p ∈ (baseHom G 0 hG).range ↔ p ∈ G := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [lk_baseHom_zero]
    exact g.2
  · intro hp
    exact ⟨⟨p, hp⟩, lk_baseHom_zero _⟩

/-- `Φ` preserved by the base action: its positions are invariant. -/
theorem lk_inv_phi {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hG : IsInvariant G (baseSet n N)}
    {Φl : List ℕ} (hpres : ∀ p ∈ (baseHom G n hG).range, ∀ x ∈ setOf (N - n) Φl,
      p x ∈ setOf (N - n) Φl) :
    IsInvariant G {u | u.val ∈ ptsD n Φl} := by
  intro g hg u hu
  change u.val ∈ ptsD n Φl at hu
  obtain ⟨v, hv, hvu⟩ := List.mem_map.1 hu
  have hvlt : v < N - n := by
    have := u.2
    omega
  have hub : u = basePos (n := n) ⟨v, hvlt⟩ := Fin.ext (by simp [basePos, ← hvu])
  have hp := hpres _ ⟨⟨g, hg⟩, rfl⟩ ⟨v, hvlt⟩ (mem_setOf.2 hv)
  change (g u).val ∈ ptsD n Φl
  rw [hub, ← baseHom_apply (hG := hG) ⟨g, hg⟩]
  exact List.mem_map_of_mem (mem_setOf.1 hp)

/-- The positions of `Φ ∖ S` are invariant under the pointwise stabilizer of `S`. -/
theorem lk_inv_win {N n : ℕ} {G : Subgroup (Perm (Fin N))} {Φl Sl : List ℕ}
    (hΦ : IsInvariant G {u | u.val ∈ ptsD n Φl}) :
    IsInvariant (pointwiseStab G {v : Fin N | v.val ∈ ptsD n Sl})
      {u : Fin N | u.val ∈ ptsD n (phiSD (N - n) Φl Sl)} := by
  intro g hg u hu
  obtain ⟨hgF, hgS⟩ := hg
  change u.val ∈ ptsD n (phiSD (N - n) Φl Sl) at hu
  obtain ⟨v, hv, hvu⟩ := List.mem_map.1 hu
  obtain ⟨-, hvΦ, hvS⟩ := mem_phiSD.1 hv
  have hgu := hΦ g hgF u (show u.val ∈ ptsD n Φl from hvu ▸ List.mem_map_of_mem hvΦ)
  change (g u).val ∈ ptsD n Φl at hgu
  obtain ⟨v', hv'Φ, hv'u⟩ := List.mem_map.1 hgu
  change (g u).val ∈ ptsD n (phiSD (N - n) Φl Sl)
  refine hv'u ▸ List.mem_map_of_mem (mem_phiSD.2 ⟨?_, hv'Φ, fun hv'S => ?_⟩)
  · have := (g u).isLt
    omega
  · have hfix := hgS (g u) (show (g u).val ∈ ptsD n Sl from hv'u ▸ List.mem_map_of_mem hv'S)
    have hu' : u = g u := (g.injective hfix).symm
    rw [← hu', ← hvu] at hv'u
    have : v' = v := by omega
    exact hvS (this ▸ hv'S)

/-- **The group of one choice**: the restricted group computed by `resModel` is the group the
elements of `P` fixing `S` induce on `Φ ∖ S` through the numbering. -/
theorem lk_res (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData} {d : D.denote}
    (hFv : GroupValid DV N gs d) (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    {Φl Sl : List ℕ}
    (hpres : ∀ p ∈ (baseHom (GensData.denote N gs) n hF).range, ∀ x ∈ setOf (N - n) Φl,
      p x ∈ setOf (N - n) Φl) (hSl : ∀ s ∈ Sl, s < N - n) :
    (resModel O N n (N, gs, d) Φl Sl).1 = (phiSD (N - n) Φl Sl).length ∧
      GroupValid DV (phiSD (N - n) Φl Sl).length (resModel O N n (N, gs, d) Φl Sl).2.1
        (resModel O N n (N, gs, d) Φl Sl).2.2 ∧
      ∀ h, h ∈ GensData.denote (phiSD (N - n) Φl Sl).length
          (resModel O N n (N, gs, d) Φl Sl).2.1 ↔
        h ∈ fixGroup (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Sl)
          (phiE (N - n) Φl Sl) := by
  set ΦS := phiSD (N - n) Φl Sl with hΦS
  set G := GensData.denote N gs with hG
  have hOs : MeetsContractOn DV stabOps O := fun op x h hp =>
    hO op x (h.elim (fun h => Or.inl h) fun h => Or.inr (Or.inl h)) hp
  have hpS : ∀ u ∈ ptsD n Sl, u < N := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have := hSl v hv
    omega
  obtain ⟨-, hFSv, hFSden⟩ := lk_iterStab hOs (ptsD n Sl) gs d hpS hFv
  set FS := fsModel O n (N, gs, d) Sl with hFSdef
  set w := WinData.ofPoints N (ptsD n ΦS) with hw
  have hwnd : (ptsD n ΦS).Nodup := (phiSD_nodup _ _ _).map fun x y h => by omega
  have hwlt : ∀ u ∈ ptsD n ΦS, u < N := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
    have := (mem_phiSD.1 hv).1
    omega
  have hwv : w.Valid N := WinData.valid_ofPoints hwnd hwlt
  have hWinv : IsInvariant (GensData.denote N FS.2.1) (w.denote N) := by
    change IsInvariant (GensData.denote N (iterStabModel O (N, gs, d) (ptsD n Sl)).2.1) _
    rw [hFSden]
    exact lk_inv_win (lk_inv_phi hpres)
  have hrv : GensData.AllValid ΦS.length (rgensD N n FS.2.1 ΦS) := by
    have := GensData.allValid_restrictTo hWinv hwv hFSv.1
    simpa [rgensD, hw, ptsD] using this
  have hpre : GroupPre DV GroupOp.generate (ΦS.length, rgensD N n FS.2.1 ΦS) := hrv
  have hpost := hO GroupOp.generate _ (Or.inr (Or.inr (Or.inr rfl))) hpre
  refine ⟨hpost.1, hpost.2.1, fun h => ?_⟩
  change h ∈ GensData.denote ΦS.length (O.run GroupOp.generate
    (ΦS.length, rgensD N n FS.2.1 ΦS)).2.1 ↔ _
  rw [hpost.2.2]
  have hlen : w.1.length = ΦS.length := by simp [hw, ptsD]
  rw [lk_denote_cast hlen]
  change (finCongr hlen.symm).permCongr h ∈
    GensData.denote w.1.length (GensData.restrictTo (WinData.pos N w) w.1 FS.2.1) ↔ _
  rw [GensData.denote_restrictTo hWinv hwv hFSv.1, MonoidHom.mem_range]
  -- the window in list order is `Φ ∖ S` numbered
  have hrx : ∀ j : Fin w.1.length,
      ((WinData.reindex hwv j : _) : Fin N) = basePos (phiE (N - n) Φl Sl (Fin.cast hlen j)) := by
    intro j
    apply Fin.ext
    rw [WinData.reindex_val]
    have hj : j.val < (ptsD n ΦS).length := j.2
    change (ptsD n ΦS).getD j 0 = _
    rw [List.getD_eq_getElem _ _ hj]
    simp [ptsD, basePos, phiE_val, hΦS]
  have hcast : ∀ j, Fin.cast hlen ((finCongr hlen.symm).permCongr h j) = h (Fin.cast hlen j) := by
    intro j
    apply Fin.ext
    simp [Equiv.permCongr_apply]
  have hFSmem : ∀ g, g ∈ GensData.denote N FS.2.1 ↔ g ∈ G ∧ ∀ s ∈ Sl, ∀ hs : n + s < N,
      g ⟨n + s, hs⟩ = ⟨n + s, hs⟩ := by
    intro g
    change g ∈ GensData.denote N (iterStabModel O (N, gs, d) (ptsD n Sl)).2.1 ↔ _
    rw [hFSden, mem_pointwiseStab]
    refine and_congr_right fun _ => ⟨fun hfix s hs hsN => hfix _ (List.mem_map_of_mem hs),
      fun hfix u hu => ?_⟩
    obtain ⟨s, hs, hsu⟩ := List.mem_map.1 (show u.val ∈ ptsD n Sl from hu)
    have := hfix s hs (hsu ▸ u.2)
    rwa [show (⟨n + s, hsu ▸ u.2⟩ : Fin N) = u from Fin.ext hsu] at this
  constructor
  · rintro ⟨⟨g, hg⟩, hgh⟩
    rw [restrictHom_eq_iff] at hgh
    obtain ⟨hgG, hgS⟩ := (hFSmem g).1 hg
    refine ⟨baseHom G n hF ⟨g, hgG⟩, ⟨⟨g, hgG⟩, rfl⟩, fun s hs => ?_, fun i => ?_⟩
    · rw [lk_baseHom_eq]
      exact hgS s.val (mem_setOf.1 hs) _
    · rw [lk_baseHom_eq]
      have := hgh (Fin.cast hlen.symm i)
      rw [hrx, hrx, hcast] at this
      simpa using this
  · rintro ⟨_, ⟨⟨g, hgG⟩, rfl⟩, hS, he⟩
    have hg : g ∈ GensData.denote N FS.2.1 := by
      refine (hFSmem g).2 ⟨hgG, fun s hs hsN => ?_⟩
      have hsm : s < N - n := hSl s hs
      have := (lk_baseHom_eq (hG := hF) ⟨g, hgG⟩ ⟨s, hsm⟩ ⟨s, hsm⟩).1
        (hS ⟨s, hsm⟩ (mem_setOf.2 hs))
      exact this
    refine ⟨⟨g, hg⟩, (restrictHom_eq_iff _ _ _ _).2 fun j => ?_⟩
    rw [hrx, hrx, hcast]
    exact (lk_baseHom_eq (hG := hF) ⟨g, hgG⟩ _ _).1 (he _)

/-- The orbital of the computed restricted group is the orbital relation of the tree. -/
theorem lk_orb (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData} {d : D.denote}
    (hFv : GroupValid DV N gs d) (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    {Φl Sl : List ℕ}
    (hpres : ∀ p ∈ (baseHom (GensData.denote N gs) n hF).range, ∀ x ∈ setOf (N - n) Φl,
      p x ∈ setOf (N - n) Φl) (hSl : ∀ s ∈ Sl, s < N - n)
    (htr : IsPretransitive (fixGroup (baseHom (GensData.denote N gs) n hF).range
      (setOf (N - n) Sl) (phiE (N - n) Φl Sl)) (Fin (phiSD (N - n) Φl Sl).length))
    (hpos : 0 < (phiSD (N - n) Φl Sl).length) (a b u v : Fin (phiSD (N - n) Φl Sl).length) :
    arrRel (orbArrD O N n (N, gs, d) Φl Sl) (phiSD (N - n) Φl Sl).length a b u v ↔
      orbRel (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Sl)
        (phiE (N - n) Φl Sl a) (phiE (N - n) Φl Sl b) (phiE (N - n) Φl Sl) u v := by
  obtain ⟨hdeg, hRv, hmem⟩ := lk_res hO hFv hF hpres hSl
  have hOo : MeetsContractOn DV orbitalOps O := fun op x h hp => hO op x (by
    rcases h with h | h | h
    exacts [Or.inr (Or.inl h), Or.inl h, Or.inr (Or.inr (Or.inl h))]) hp
  rw [orbRel_iff (lk_maps hpres phiE_range)]
  unfold orbArrD
  generalize hR : resModel O N n (N, gs, d) Φl Sl = R at hdeg hRv hmem
  obtain ⟨M, gs', d'⟩ := R
  change M = _ at hdeg
  subst hdeg
  have hinv0 : IsInvariant (GensData.denote (phiSD (N - n) Φl Sl).length gs')
      (baseSet 0 (phiSD (N - n) Φl Sl).length) := fun _ _ _ _ => Nat.zero_le _
  have htr' : ∀ γ δ : Fin ((phiSD (N - n) Φl Sl).length - 0),
      ∃ g : ↥(GensData.denote (phiSD (N - n) Φl Sl).length gs'),
        baseHom (GensData.denote (phiSD (N - n) Φl Sl).length gs') 0 hinv0 g γ = δ := by
    intro γ δ
    obtain ⟨⟨h, hh⟩, hhγ⟩ := htr.exists_smul_eq γ δ
    refine ⟨⟨h, (hmem h).2 hh⟩, ?_⟩
    rw [lk_baseHom_zero]
    exact hhγ
  refine (arrRel_orbital (X := lkCtx O) hOo hRv hinv0 hpos htr' a b u v).trans ?_
  constructor
  · rintro ⟨⟨p, hp⟩, ha, hb⟩
    exact ⟨⟨p, (hmem p).1 ((lk_mem_range_zero p).1 hp)⟩, ha, hb⟩
  · rintro ⟨⟨p, hp⟩, ha, hb⟩
    exact ⟨⟨p, (lk_mem_range_zero p).2 ((hmem p).2 hp)⟩, ha, hb⟩

/-- **The colouring of one choice** is `wlRel` of the orbital relation of the tree. -/
theorem lk_colOf (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φl Sl : List ℕ}
    (hpres : ∀ p ∈ (baseHom (GensData.denote N gs) n hF).range, ∀ x ∈ setOf (N - n) Φl,
      p x ∈ setOf (N - n) Φl) (hSl : ∀ s ∈ Sl, s < N - n)
    (htr : IsPretransitive (fixGroup (baseHom (GensData.denote N gs) n hF).range
      (setOf (N - n) Sl) (phiE (N - n) Φl Sl)) (Fin (phiSD (N - n) Φl Sl).length))
    (hpos : 0 < (phiSD (N - n) Φl Sl).length) (a b : Fin (phiSD (N - n) Φl Sl).length) :
    colOf (phiSD (N - n) Φl Sl).length (wlColOf O N n (N, gs, d) Φl Sl a b) =
      wlRel (orbRel (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Sl)
        (phiE (N - n) Φl Sl a) (phiE (N - n) Φl Sl b) (phiE (N - n) Φl Sl)) := by
  rw [← lk_wlRel_congr (lk_orb hO hFv hF hpres hSl htr hpos a b)]
  funext u v
  exact colOf_wlColD _ a.val b.val u v

/-- **The leaves of one choice** decode to the leaves of the leaf tree. -/
theorem lk_choice (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φl Sl : List ℕ}
    (hpres : ∀ p ∈ (baseHom (GensData.denote N gs) n hF).range, ∀ x ∈ setOf (N - n) Φl,
      p x ∈ setOf (N - n) Φl) (hSl : ∀ s ∈ Sl, s < N - n)
    (htr : IsPretransitive (fixGroup (baseHom (GensData.denote N gs) n hF).range
      (setOf (N - n) Sl) (phiE (N - n) Φl Sl)) (Fin (phiSD (N - n) Φl Sl).length))
    (hpos : 0 < (phiSD (N - n) Φl Sl).length) (a b : Fin (phiSD (N - n) Φl Sl).length) :
    (((choiceLeavesD O N n (N, gs, d) Φl Sl a b).map (decodeOut (N - n)) :
        List (Option (Out (Fin (N - n))))) : Multiset (Option (Out (Fin (N - n))))) =
      (leafTree (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Sl)
        (phiE (N - n) Φl Sl a) (phiE (N - n) Φl Sl b) (phiE (N - n) Φl Sl)).leafMs := by
  have hc := lk_colOf hO hFv hF hpres hSl htr hpos a b
  have hext : ∀ o, decodeOut (N - n) (extD (N - n) (phiSD (N - n) Φl Sl) o) =
      extOut (phiE (N - n) Φl Sl) (decodeOut (phiSD (N - n) Φl Sl).length o) := fun o => by
    rw [decodeOut_extD (fun _ hv => (mem_phiSD.1 hv).1), lk_pipeExt]
  unfold choiceLeavesD
  rw [List.map_map,
    List.map_congr_left (f := decodeOut (N - n) ∘ extD (N - n) (phiSD (N - n) Φl Sl))
      (g := extOut (phiE (N - n) Φl Sl) ∘ decodeOut (phiSD (N - n) Φl Sl).length)
      fun o _ => hext o, ← List.map_map, ← Multiset.map_coe]
  generalize wlColOf O N n (N, gs, d) Φl Sl a b = C at hc
  unfold leafTree
  rw [← hc]
  by_cases hd : (disconn univ (colOf (phiSD (N - n) Φl Sl).length C)).Nonempty
  · rw [dite_eq_left hd, leavesOfD_decode_comp _ _ hd]
    rfl
  · rw [dite_eq_right hd, leavesOfD_decode_soj _ _ (not_nonempty_iff_eq_empty.1 hd),
      CTree.leafMs_trans _ _ _ (chBack_chMap _), Multiset.map_map]
    rfl

/-- **The leaves of all pairs** after the tuple `S` decode to those of the pair node. -/
theorem lk_pairs (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φl Sl : List ℕ} {j : ℕ}
    (hΦlt : ∀ v ∈ Φl, v < N - n)
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl) (j + 1))
    (hS : Sl ∈ tuplesD Φl j) :
    ∑ ab ∈ (pairsD (phiSD (N - n) Φl Sl).length).toFinset,
        (((choiceLeavesD O N n (N, gs, d) Φl Sl ab.1 ab.2).map (decodeOut (N - n)) :
          List (Option (Out (Fin (N - n))))) : Multiset (Option (Out (Fin (N - n))))) =
      (pairNode (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl)
        (setOf (N - n) Sl)).leafMs := by
  obtain ⟨hSl, hsub, hcard⟩ := lk_tuple hΦlt hS
  have hpos : 4 ≤ (phiSD (N - n) Φl Sl).length := by
    rw [← lk_card_phi, card_sdiff_of_subset hsub]
    have := H.size
    omega
  have htr := lk_pretrans H.pres phiE_range (H.trans _ hsub hcard)
  simp only [pairNode, CTree.leafMs]
  refine Finset.sum_bij (fun ab hab => ([Sum.inl (phiE (N - n) Φl Sl
      ⟨ab.1, (mem_pairsD.1 (List.mem_toFinset.1 hab)).1⟩), Sum.inl (phiE (N - n) Φl Sl
      ⟨ab.2, (mem_pairsD.1 (List.mem_toFinset.1 hab)).2.1⟩)] : Choice (Fin (N - n))))
    (fun ab hab => ?_) (fun ab hab ab' hab' h => ?_) (fun xy hxy => ?_) (fun ab hab => ?_)
  · obtain ⟨-, -, hne⟩ := mem_pairsD.1 (List.mem_toFinset.1 hab)
    refine mem_image.2 ⟨(_, _), mem_filter.2 ⟨mem_product.2 ⟨(phiE_range _).1 ⟨_, rfl⟩,
      (phiE_range _).1 ⟨_, rfl⟩⟩, fun h => hne ?_⟩, rfl⟩
    exact congrArg Fin.val ((phiE (N - n) Φl Sl).injective h)
  · have h1 := List.cons.inj h
    have h2 := List.cons.inj h1.2
    exact Prod.ext (congrArg Fin.val ((phiE (N - n) Φl Sl).injective (Sum.inl.inj h1.1)))
      (congrArg Fin.val ((phiE (N - n) Φl Sl).injective (Sum.inl.inj h2.1)))
  · obtain ⟨⟨x, y⟩, hmem, rfl⟩ := mem_image.1 hxy
    obtain ⟨hprod, hne⟩ := mem_filter.1 hmem
    obtain ⟨hx, hy⟩ := mem_product.1 hprod
    obtain ⟨i, rfl⟩ := (phiE_range _).2 hx
    obtain ⟨i', rfl⟩ := (phiE_range _).2 hy
    exact ⟨(i.val, i'.val), List.mem_toFinset.2 (mem_pairsD.2 ⟨i.2, i'.2,
      fun h => hne (by rw [Fin.ext h])⟩), rfl⟩
  · obtain ⟨ha, hb, -⟩ := mem_pairsD.1 (List.mem_toFinset.1 hab)
    refine (lk_choice hO hFv hF H.pres hSl htr (by omega) ⟨ab.1, ha⟩ ⟨ab.2, hb⟩).trans ?_
    show _ = (leafTree _ _ _ _ (eOf (setOf (N - n) Φl \ setOf (N - n) Sl))).leafMs
    rw [lk_leafTree_congr _ _ _ (phiE (N - n) Φl Sl) _ lk_card_phi
      fun v => by rw [mem_eOf_range, phiE_range]]

/-- **The data leaves are the leaves of the Case 2b tree**, for the group given as `(N, gs, d)`. -/
theorem lk_allLeaves (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl) (j + 1)) :
    (((allLeavesD O N n (N, gs, d) Φl j).map (decodeOut (N - n)) :
        List (Option (Out (Fin (N - n))))) : Multiset (Option (Out (Fin (N - n))))) =
      (case2bTree (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl)
        (j + 1)).leafMs := by
  unfold allLeavesD
  rw [lk_flatMap_coe (tuplesD_nodup hΦnd j)]
  simp only [case2bTree, CTree.leafMs]
  show _ = ∑ ch ∈ tuplesOf (setOf (N - n) Φl) j, _
  symm
  refine Finset.sum_bij (fun ch _ => (ptsOf ch).map Fin.val)
    (fun ch hch => ?_) (fun ch hch ch' hch' h => ?_) (fun Sl hSl => ?_) (fun ch hch => ?_)
  · obtain ⟨T, hinj, hTΦ, rfl⟩ := cb_tuple_of_mem hch
    rw [ptsOf_ofFn, List.mem_toFinset, mem_tuplesD]
    refine ⟨by simp, (List.nodup_ofFn.2 hinj).map Fin.val_injective, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact mem_setOf.1 (hTΦ i)
  · obtain ⟨T, -, -, rfl⟩ := cb_tuple_of_mem hch
    obtain ⟨T', -, -, rfl⟩ := cb_tuple_of_mem hch'
    rw [ptsOf_ofFn, ptsOf_ofFn] at h
    rw [List.ofFn_injective ((List.map_injective_iff.2 Fin.val_injective) h)]
  · obtain ⟨hlen, hnd, hmem⟩ := (mem_tuplesD Φl j).1 (List.mem_toFinset.1 hSl)
    let T : Fin j → Fin (N - n) := fun k =>
      ⟨Sl[k.val]'(by rw [hlen]; exact k.2), hΦlt _ (hmem _ (List.getElem_mem _))⟩
    have hinj : Function.Injective T := fun k k' h => Fin.ext
      ((List.Nodup.getElem_inj_iff hnd).1 (congrArg Fin.val h))
    refine ⟨(List.ofFn fun k => (Sum.inl (T k) : Fin (N - n) ⊕ Finset (Fin (N - n))) :
      Choice (Fin (N - n))), mem_image.2 ⟨T, mem_filter.2 ⟨mem_univ _, hinj,
        fun k => mem_setOf.2 (hmem _ (List.getElem_mem _))⟩, rfl⟩, ?_⟩
    rw [ptsOf_ofFn]
    refine List.ext_getElem (by simp [hlen]) fun i h₁ h₂ => ?_
    simp [T]
  · obtain ⟨T, hinj, hTΦ, rfl⟩ := cb_tuple_of_mem hch
    have hS : (ptsOf (List.ofFn fun i => (Sum.inl (T i) : Fin (N - n) ⊕ Finset (Fin (N - n))) :
        Choice (Fin (N - n)))).map Fin.val ∈ tuplesD Φl j := by
      rw [ptsOf_ofFn, mem_tuplesD]
      refine ⟨by simp, (List.nodup_ofFn.2 hinj).map Fin.val_injective, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
      exact mem_setOf.1 (hTΦ i)
    rw [lk_flatMap_coe (pairsD_nodup _), lk_pairs hO hFv hF hΦlt H hS, lk_setOf_val]

/-- The first leaf exists, for the group given as `(N, gs, d)`. -/
theorem lk_first_ne (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl) (j + 1)) :
    firstLeafD O N n (N, gs, d) Φl j ≠ none := by
  have hmem := lk_take_mem hΦnd hΦlt H
  unfold firstLeafD
  rcases hT : tuplesD Φl j with _ | ⟨Sl, rest⟩
  · rw [hT] at hmem
    simp at hmem
  have hS : Sl ∈ tuplesD Φl j := by
    rw [hT]
    exact List.mem_cons_self
  obtain ⟨hSl, hsub, hcard⟩ := lk_tuple hΦlt hS
  have h4 := lk_four hΦlt H hS
  have htr := lk_pretrans H.pres phiE_range (H.trans _ hsub hcard)
  have hc : (((choiceLeavesD O N n (N, gs, d) Φl Sl 0 1).map (decodeOut (N - n)) :
      List (Option (Out (Fin (N - n))))) : Multiset (Option (Out (Fin (N - n))))) = _ :=
    lk_choice hO hFv hF H.pres hSl htr (by omega) ⟨0, by omega⟩ ⟨1, by omega⟩
  rw [← lk_leafTree_congr _ _ _ (phiE (N - n) Φl Sl) (eOf _) lk_card_phi
    fun v => by rw [mem_eOf_range, phiE_range]] at hc
  have hlive := (cb_choice_spec H hsub hcard ((phiE_range _).1 ⟨⟨0, by omega⟩, rfl⟩)
    ((phiE_range _).1 ⟨⟨1, by omega⟩, rfl⟩) fun h => absurd
      (congrArg Fin.val ((phiE (N - n) Φl Sl).injective h)) (by simp)).1
  have hcount := (CTree.meas_size_live hlive).2
  show (choiceLeavesD O N n (N, gs, d) Φl Sl 0 1).head? ≠ none
  rw [Ne, List.head?_eq_none_iff]
  intro hnil
  rw [hnil, List.map_nil] at hc
  have h0 := congrArg Multiset.card hc
  rw [CTree.card_leafMs] at h0
  rw [← h0] at hcount
  simp at hcount

/-- The size bound of the `soj` trees of Case 2b on at most `M` points. -/
def sojZ (M : ℕ) : ℕ := 2 * (2 * M + 3) * 2 ^ (129 * (Nat.clog 2 M + 2) ^ 2)

theorem sojZ_mono {M M' : ℕ} (h : M ≤ M') : sojZ M ≤ sojZ M' := by
  unfold sojZ
  refine Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_right two_pos ?_)
  have := Nat.clog_mono_right 2 h
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- The `soj` tree of a listed choice is small, for the group given as `(N, gs, d)`. -/
theorem lk_sojSz (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N)) {Φl : List ℕ}
    (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl) (j + 1))
    {Sl : List ℕ} (hS : Sl ∈ tuplesD Φl j) {a b : ℕ}
    (hab : (a, b) ∈ pairsD (phiSD (N - n) Φl Sl).length) :
    sojSz (phiSD (N - n) Φl Sl).length (wlColOf O N n (N, gs, d) Φl Sl a b) ≤
      sojZ (N - n) := by
  classical
  obtain ⟨ha, hb, hne⟩ := mem_pairsD.1 hab
  obtain ⟨hSl, hsub, hcard⟩ := lk_tuple hΦlt hS
  have h4 := lk_four hΦlt H hS
  have htr := lk_pretrans H.pres phiE_range (H.trans _ hsub hcard)
  have hc := lk_colOf hO hFv hF H.pres hSl htr (by omega) ⟨a, ha⟩ ⟨b, hb⟩
  have hspec := cb_choice_spec H hsub hcard ((phiE_range _).1 ⟨⟨a, ha⟩, rfl⟩)
    ((phiE_range _).1 ⟨⟨b, hb⟩, rfl⟩) fun h => hne
      (congrArg Fin.val ((phiE (N - n) Φl Sl).injective h))
  rw [lk_leafTree_congr _ _ _ (phiE (N - n) Φl Sl) _ lk_card_phi
    fun v => by rw [mem_eOf_range, phiE_range], lk_card_phi] at hspec
  obtain ⟨hlive, hcount, -⟩ := hspec
  have hm' := length_phiSD_le (N - n) Φl Sl
  unfold sojSz
  split
  · rename_i hnil
    have hd : ¬ (disconn univ (colOf (phiSD (N - n) Φl Sl).length
        (wlColOf O N n (N, gs, d) Φl Sl a b))).Nonempty := by
      rw [disconn_wlCol, hnil]
      simp
    rw [hc] at hd ⊢
    unfold leafTree at hlive hcount
    rw [dite_eq_right hd] at hlive hcount
    have hl := lk_live_of_trans (chBack_chMap _) hlive
    rw [CTree.cb_count_trans (chBack_chMap _)] at hcount
    have hh := height_soj_le (wlRel (orbRel (baseHom (GensData.denote N gs) n hF).range
      (setOf (N - n) Sl) (phiE (N - n) Φl Sl ⟨a, ha⟩) (phiE (N - n) Φl Sl ⟨b, hb⟩)
      (phiE (N - n) Φl Sl))) (((phiSD (N - n) Φl Sl).length + 3) / 2)
    rw [Fintype.card_fin] at hh
    refine (CTree.size_le_of_live hl).trans ((Nat.mul_le_mul (Nat.mul_le_mul_left 2
      (show _ + 1 ≤ 2 * (phiSD (N - n) Φl Sl).length + 3 by omega)) hcount).trans ?_)
    exact sojZ_mono hm'
  · exact Nat.zero_le _

end Res

/-! ### The data shape of the Johnson leaves of `soj` -/

section Shape

variable {m : ℕ}

/-- The data shape of a Johnson leaf: duplicate-free points, cells and cell index lists, and
cells distinct as sets. -/
structure LkJ (m : ℕ) (o : OutD) : Prop where
  v0 : o.2.2.1.Nodup
  cells : ∀ c ∈ o.2.2.2.1, c.Nodup
  dist : (o.2.2.2.1.map (setOf m)).Nodup
  fl : ∀ v, (o.2.2.2.2.2.getD v []).Nodup

/-- The items of a level: Johnson leaves with the data shape, child frames with duplicate-free
cells. -/
def LkItem (m : ℕ) : Item → Prop
  | .inl o => o.1 = 2 → LkJ m o
  | .inr ch => ∀ c ∈ ch.cs, c.Nodup

theorem lk_item_of_ne {o : OutD} (h : o.1 ≠ 2) : LkItem m (.inl o) := fun h' => absurd h' h

theorem lk_tag_addPieceD (D : List ℕ) {o : OutD} (h : o.1 ≠ 2) : (addPieceD m D o).1 ≠ 2 := by
  unfold addPieceD
  split_ifs
  · simp [partD]
  · exact h

theorem lk_getD_nodup {l : List (List ℕ)} (hl : ∀ c ∈ l, c.Nodup) (v : ℕ) :
    (l.toArray.getD v []).Nodup := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rcases h : l[v]? with _ | c
  · exact List.nodup_nil
  · exact hl c (List.mem_of_getElem? h)

theorem lk_subCells {cs : List (List ℕ)} (hcs : ∀ c ∈ cs, c.Nodup) (js : List ℕ) :
    ∀ c ∈ subCells cs js, c.Nodup := by
  intro c hc
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hc
  rw [List.getD_eq_getElem?_getD]
  rcases h : cs[j]? with _ | c
  · exact List.nodup_nil
  · exact hcs c (List.mem_of_getElem? h)

theorem lk_item_rec {k : ℕ} {V : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {ops : List WrapOp} (hcs : ∀ c ∈ cs, c.Nodup) : LkItem m (recI k V cs a ops) := by
  unfold recI
  split_ifs
  · exact hcs
  · exact lk_item_of_ne (by simp [noneD])

theorem lk_item_shrink {k : ℕ} {V : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    {ops : List WrapOp} (hcs : ∀ c ∈ cs, c.Nodup) : LkItem m (shrinkI k V cs a ops) := by
  unfold shrinkI
  split_ifs
  · exact hcs
  · exact lk_item_of_ne (by simp [noneD])

theorem lk_item_cont {t k : ℕ} {cs : List (List ℕ)} {D₁ D₂ C₁ : List ℕ} {f : ℕ → ℕ → ℕ}
    (o : Option SoJProg.LeafD) : LkItem m (contI m t k cs D₁ D₂ C₁ f o) := by
  rcases o with _ | ⟨tag, ⟨col, blk⟩, W₁, W₂, g⟩
  · exact lk_item_of_ne (by simp [noneD])
  simp only [contI]
  split_ifs
  · exact lk_item_of_ne (lk_tag_addPieceD _ (lk_tag_addPieceD _ (by simp [partD])))
  · exact lk_item_of_ne (lk_tag_addPieceD _ (lk_tag_addPieceD _ (lk_tag_addPieceD _
      (by simp [partD]))))
  · apply lk_item_shrink
    intro c hc
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 (sp_mem_dedupCellsD hc)
    exact List.nodup_range.filter _

theorem lk_item_coh {t k : ℕ} {cs : List (List ℕ)} {D₁ D₂ C₁ C₂ : List ℕ} {f : ℕ → ℕ → ℕ} :
    ∀ i ∈ (cohI m t k cs D₁ D₂ C₁ C₂ f).1, LkItem m i := by
  intro i hi
  unfold cohI at hi
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_cont _
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hi
    exact lk_item_cont _

theorem lk_item_dl {t : ℕ} {V₁ V₁' : List ℕ} {cs : List (List ℕ)} {a : Array Bool} {d : ℕ}
    {wl : Array ℕ} {xd : List ℕ} (hcs : ∀ c ∈ cs, c.Nodup) :
    ∀ i ∈ (dlI m t V₁ V₁' cs a d wl xd).1, LkItem m i := by
  intro i hi
  rw [sp_dlI_eq] at hi
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_shrink (lk_subCells hcs _)
  unfold sp_dlSkelI at hi
  dsimp only at hi
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_shrink (lk_subCells hcs _)
  unfold sp_dlBigI at hi
  dsimp only at hi
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_of_ne (lk_tag_addPieceD _ (by simp [partD]))
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_shrink (lk_subCells hcs _)
  exact lk_item_coh i hi

theorem lk_fArrD_nodup (k : ℕ) (a : Array Bool) (d₁ v : ℕ) :
    ((fArrD m k a d₁).getD v []).Nodup := by
  unfold fArrD
  refine lk_getD_nodup (fun c hc => ?_) v
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hc
  unfold fOfD nbrD
  split_ifs
  · exact List.nodup_range.filter _
  · exact List.nodup_range.filter _

/-- **The items of a level** have the data shape. -/
theorem lk_item_bstep {t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a : Array Bool}
    (hV : V₁.Nodup) (hcs : ∀ c ∈ cs, c.Nodup) (hcd : (cs.map (setOf m)).Nodup) :
    ∀ i ∈ (bstepI m t V₁ cs a).1, LkItem m i := by
  intro i hi
  rw [sp_bstepI_eq] at hi
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_of_ne (by simp [partD])
  rename_i d₁ _
  split_ifs at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact fun _ => ⟨hV.filter _, hcs, hcd, lk_fArrD_nodup _ _ _⟩
  · obtain ⟨js, -, rfl⟩ := List.mem_map.1 hi
    exact lk_item_of_ne (by simp [partD])
  unfold sp_daryI at hi
  dsimp only at hi
  split at hi
  · rw [List.mem_singleton] at hi
    subst hi
    exact lk_item_rec (lk_subCells hcs _)
  obtain ⟨p, hp, hip⟩ := List.mem_flatMap.1 hi
  obtain ⟨xd, -, rfl⟩ := List.mem_map.1 hp
  exact lk_item_dl hcs i hip

theorem lk_mem_splitI_fst {l : List Item} {o : OutD} (h : o ∈ (splitI l).1) : Sum.inl o ∈ l := by
  obtain ⟨i, hi, he⟩ := List.mem_filterMap.1 h
  cases i with
  | inl o' =>
    simp only [Sum.getLeft?_inl, Option.some.injEq] at he
    exact he ▸ hi
  | inr fr' => simp at he

theorem lk_opD_one (op : WrapOp) {o : OutD} (h : o.1 = 1) : (opD m op o).1 = 1 := by
  unfold opD extendD addPieceD
  split_ifs <;> rfl

theorem lk_opD_ne (op : WrapOp) {o : OutD} (h : o.1 ≠ 1) : opD m op o = o := by
  unfold opD extendD addPieceD
  split_ifs <;> rfl

theorem lk_wrapD_one : ∀ (ops : List WrapOp) {o : OutD}, o.1 = 1 → (wrapD m ops o).1 = 1
  | [], _, h => h
  | op :: ops, _, h => lk_wrapD_one ops (lk_opD_one op h)

/-- The wrappers leave Johnson leaves unchanged. -/
theorem lk_wrapD_two : ∀ (ops : List WrapOp) {o : OutD}, (wrapD m ops o).1 = 2 →
    wrapD m ops o = o
  | [], _, _ => rfl
  | op :: ops, o, h => by
    change (wrapD m ops (opD m op o)).1 = 2 at h
    change wrapD m ops (opD m op o) = o
    by_cases h1 : o.1 = 1
    · rw [lk_wrapD_one ops (lk_opD_one op h1)] at h
      cases h
    · rw [lk_opD_ne op h1] at h ⊢
      exact lk_wrapD_two ops h

theorem lk_step_out {t : ℕ} {fr : FrameD} (hv : fr.Valid m) (hcs : ∀ c ∈ fr.cs, c.Nodup) :
    ∀ o ∈ (stepD m t fr).1, o.1 = 2 → LkJ m o := by
  intro o ho h2
  rw [stepD_eq] at ho
  obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ho
  have he := lk_wrapD_two _ h2
  rw [he] at h2 ⊢
  exact lk_item_bstep hv.nodup hcs hv.cells _ (lk_mem_splitI_fst ho₀) h2

theorem lk_step_child {t : ℕ} {fr : FrameD} (hv : fr.Valid m) (hcs : ∀ c ∈ fr.cs, c.Nodup) :
    ∀ ch ∈ (stepD m t fr).2, ∀ c ∈ ch.cs, c.Nodup := by
  intro ch hch
  rw [stepD_eq] at hch
  obtain ⟨ch₀, hch₀, rfl⟩ := List.mem_map.1 hch
  exact lk_item_bstep hv.nodup hcs hv.cells _ (sp_mem_splitI_snd hch₀)

theorem lk_root (t : ℕ) (C : Array ℕ) :
    (∀ fr ∈ (splitI (tr_sojItems m t C)).2, fr.Valid m ∧ ∀ c ∈ fr.cs, c.Nodup) ∧
      ∀ o ∈ (splitI (tr_sojItems m t C)).1, o.1 = 2 → LkJ m o := by
  refine ⟨fun fr hfr => ?_, fun o ho h2 => ?_⟩
  · obtain ⟨x, hx, hS⟩ := List.mem_map.1 (sp_mem_splitI_snd hfr)
    have hxm := List.mem_range.1 hx
    refine ⟨(sojAtD_frame C hxm hS).1, ?_⟩
    unfold sojAtD at hS
    split_ifs at hS
    split at hS
    · cases hS
    · cases hS
      intro c hc
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hc
      exact List.nodup_singleton y
  · obtain ⟨x, -, hS⟩ := List.mem_map.1 (lk_mem_splitI_fst ho)
    unfold sojAtD at hS
    split_ifs at hS
    · cases hS
      simp [partD] at h2
    · split at hS
      · cases hS
        simp [noneD] at h2
      · cases hS

/-- **The Johnson leaves of `soj` on data have the data shape.** -/
theorem lk_sojD_john (t : ℕ) (C : Array ℕ) : ∀ o ∈ sojD m t C, o.1 = 2 → LkJ m o := by
  obtain ⟨hfr, hout⟩ := lk_root (m := m) t C
  exact tr_worklist_mem (I := fun fr => fr.Valid m ∧ ∀ c ∈ fr.cs, c.Nodup)
    (w := stepWork m t) (P := fun o => o.1 = 2 → LkJ m o)
    (fun fr h ch hch => ⟨⟨(tr_children (t := t) h.1 ch hch).1, lk_step_child h.1 h.2 ch hch⟩,
      (tr_children (t := t) h.1 ch hch).2⟩)
    (fun fr h => tr_size_step h.1) (fun fr _ => tr_one_le_size fr)
    (fun fr h o ho => lk_step_out h.1 h.2 o ho) hfr hout

/-! #### Trimming and extending keep the shape -/

/-- The data facts of a Johnson leaf on `Fin m` from which `JShape` follows with the model. -/
structure LkJD (m : ℕ) (d : JData) : Prop where
  v0 : d.1.Nodup
  v0_lt : ∀ v ∈ d.1, v < m
  cells : ∀ c ∈ d.2.1, c.Nodup
  cell_lt : ∀ c ∈ d.2.1, ∀ a ∈ c, a < m
  dist : (d.2.1.map (setOf m)).Nodup
  fl : ∀ v, (jfl d v).Nodup
  fl_out : ∀ v, m ≤ v → jfl d v = []

theorem lk_getD_out {α : Type*} {l : List α} {v : ℕ} (hv : l.length ≤ v) (d : α) :
    l.toArray.getD v d = d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_none hv]
  rfl

theorem lk_trim {o : OutD} (h : o.1 = 2) (hL : LkJ m o) :
    (trimD m o).1 = 2 ∧ LkJ m (trimD m o) := by
  simp only [trimD, h, ↓reduceIte]
  refine ⟨rfl, hL.v0, hL.cells, hL.dist, lk_getD_nodup (fun c hc => ?_)⟩
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hc
  split_ifs
  · exact hL.fl v
  · exact List.nodup_nil

theorem lk_mapE_nodup {ΦS l : List ℕ} (hΦ : ΦS.Nodup) (hl : l.Nodup) : (mapE ΦS l).Nodup := by
  unfold mapE
  refine (hl.filter _).map_on fun x hx y hy hxy => ?_
  have hx' := (decide_eq_true_iff.1 (List.mem_filter.1 hx).2)
  have hy' := (decide_eq_true_iff.1 (List.mem_filter.1 hy).2)
  rw [List.getD_eq_getElem _ _ hx', List.getD_eq_getElem _ _ hy'] at hxy
  exact (List.Nodup.getElem_inj_iff hΦ).1 hxy

theorem lk_mapE_lt {ΦS : List ℕ} (hlt : ∀ v ∈ ΦS, v < m) (l : List ℕ) :
    ∀ v ∈ mapE ΦS l, v < m := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
  have hi' := decide_eq_true_iff.1 (List.mem_filter.1 hi).2
  rw [List.getD_eq_getElem _ _ hi']
  exact hlt _ (List.getElem_mem _)

/-- **Extending a Johnson leaf along the numbering** gives the data facts. -/
theorem lk_ext {ΦS : List ℕ} (hΦ : ΦS.Nodup) (hlt : ∀ v ∈ ΦS, v < m) {o : OutD}
    (h : o.1 = 2) (hL : LkJ ΦS.length o) :
    (extD m ΦS o).1 = 2 ∧ LkJD m (extD m ΦS o).2.2 := by
  have h1 : o.1 ≠ 1 := by omega
  have hx : extD m ΦS o = johnD (mapE ΦS o.2.2.1) (o.2.2.2.1.map (mapE ΦS)) o.2.2.2.2.1
      ((List.range m).map fun v =>
        if v ∈ ΦS then o.2.2.2.2.2.getD (ΦS.idxOf v) [] else []).toArray := by
    unfold extD
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h)]
  rw [hx]
  refine ⟨rfl, ⟨lk_mapE_nodup hΦ hL.v0, lk_mapE_lt hlt _, fun c hc => ?_, fun c hc => ?_, ?_,
    fun v => lk_getD_nodup (fun c hc => ?_) v, fun v hv => lk_getD_out (by simpa using hv) _⟩⟩
  · obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact lk_mapE_nodup hΦ (hL.cells c₀ hc₀)
  · obtain ⟨c, -, rfl⟩ := List.mem_map.1 hc
    exact lk_mapE_lt hlt c
  · show ((o.2.2.2.1.map (mapE ΦS)).map (setOf m)).Nodup
    rw [List.map_map]
    have : setOf m ∘ mapE ΦS = Finset.image (eFin ΦS hlt) ∘ setOf ΦS.length := by
      funext l
      exact setOf_mapE hlt l
    rw [this, ← List.map_map]
    refine hL.dist.map (Finset.image_injective fun i j hij => ?_)
    exact Fin.ext ((List.Nodup.getElem_inj_iff hΦ).1 (congrArg Fin.val hij))
  · obtain ⟨v, -, rfl⟩ := List.mem_map.1 hc
    split_ifs
    · exact hL.fl _
    · exact List.nodup_nil

/-! #### `JShape` from the data facts and the model -/

theorem lk_jshape {d : JData} (hD : LkJD m d) {t : ℕ} (hJ : IsJohnson univ t (jdec m d))
    (htrim : ∀ v, v ∉ (jdec m d).V0 → (jdec m d).f v = ∅)
    (hdisj : ∀ A ∈ (jdec m d).Λ, Disjoint A (jdec m d).V0) : JShape m d where
  v0_nodup := hD.v0
  v0_lt := hD.v0_lt
  cell_nodup := hD.cells
  cell_ne c hc := by
    obtain ⟨x, hx⟩ := hJ.cells_ne _ (show setOf m c ∈ (jdec m d).Λ from mem_famOf.2 ⟨c, hc, rfl⟩)
    rintro rfl
    simp [mem_setOf] at hx
  cell_lt := hD.cell_lt
  cell_disj := by
    refine (List.pairwise_map.1 hD.dist).imp_of_mem fun {c c'} hc hc' hne a ha ha' => ?_
    have hdis := hJ.cells_disj _ (show setOf m c ∈ (jdec m d).Λ from mem_famOf.2 ⟨c, hc, rfl⟩)
      _ (show setOf m c' ∈ (jdec m d).Λ from mem_famOf.2 ⟨c', hc', rfl⟩) hne
    have hal := hD.cell_lt c hc a ha
    exact Finset.disjoint_left.1 hdis (mem_setOf.2 (show (⟨a, hal⟩ : Fin m).val ∈ c from ha))
      (mem_setOf.2 (show (⟨a, hal⟩ : Fin m).val ∈ c' from ha'))
  cell_v0 c hc a ha ha0 := by
    have hal := hD.cell_lt c hc a ha
    exact Finset.disjoint_left.1 (hdisj _ (mem_famOf.2 ⟨c, hc, rfl⟩))
      (mem_setOf.2 (show (⟨a, hal⟩ : Fin m).val ∈ c from ha))
      (show (⟨a, hal⟩ : Fin m) ∈ setOf m d.1 from mem_setOf.2 ha0)
  trim v hv := by
    by_cases hvm : v < m
    · have h0 := htrim ⟨v, hvm⟩ (by rw [jdec_V0, mem_setOf]; exact hv)
      rw [jdec_f] at h0
      unfold famIdx at h0
      rw [List.toFinset_eq_empty_iff, List.map_eq_nil_iff] at h0
      exact h0
    · exact hD.fl_out v (by omega)
  f_nodup v _ := hD.fl v
  f_lt v hv j hj := by
    have hm := Finset.mem_powersetCard.1 (hJ.maps_to ⟨v, hD.v0_lt v hv⟩
      (by rw [jdec_V0, mem_setOf]; exact hv))
    rw [jdec_f] at hm
    have hcell := hm.1 (mem_famIdx.2 ⟨j, hj, rfl⟩)
    obtain ⟨x, hx⟩ := hJ.cells_ne _ hcell
    by_contra hjl
    rw [cellAt, List.getD_eq_default _ _ (by omega)] at hx
    simp [mem_setOf] at hx

/-- **A valid leaf with the data facts is `OutValid`.** -/
theorem lk_outValid {o : OutD} (hv : ValidLeaf (decodeOut m o))
    (hshape : o.1 = 2 → LkJD m o.2.2) : OutValid m o := by
  by_cases h1 : o.1 = 1
  · rw [ld_decodeOut_one h1] at hv
    rcases hv with ⟨p, t, he, hp⟩ | ⟨J, t, he, -⟩
    · cases he
      exact Or.inl ⟨h1, t, hp⟩
    · cases he
  by_cases h2 : o.1 = 2
  · rw [ld_decodeOut_two h2] at hv
    rcases hv with ⟨p, t, he, -⟩ | ⟨J, t, he, hJ, htrim, hdisj⟩
    · cases he
    · cases he
      exact Or.inr ⟨h2, jvalid_of_isJohnson (lk_jshape (hshape h2) hJ htrim hdisj) hJ⟩
  · have hn : decodeOut m o = none := by simp [decodeOut, h1, h2]
    rw [hn] at hv
    rcases hv with ⟨p, t, he, -⟩ | ⟨J, t, he, -⟩ <;> cases he

/-! #### The listed Johnson leaves -/

theorem lk_extD_tag {ΦS : List ℕ} {o : OutD} (h : (extD m ΦS o).1 = 2) : o.1 = 2 := by
  unfold extD at h
  split_ifs at h with h1 h2
  · simp [partD] at h
  · exact h2
  · exact h

theorem lk_trimD_tag {o : OutD} (h : (trimD m o).1 = 2) : o.1 = 2 := by
  unfold trimD at h
  split_ifs at h with h1
  · exact h1
  · exact h

theorem lk_leaves_shape (C : Array ℕ) : ∀ o ∈ leavesOfD m C, o.1 = 2 → LkJ m o := by
  intro o ho h2
  unfold leavesOfD at ho
  split at ho
  · rw [List.mem_singleton] at ho
    subst ho
    simp [compLeafD, partD] at h2
  · obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    have h2' := lk_trimD_tag h2
    exact (lk_trim h2' (lk_sojD_john _ C o' ho' h2')).2

/-- **Every listed Johnson leaf has the data facts.** -/
theorem lk_allLeaves_shape {D : Ty} {O : Oracle (groupSig D)} {N n : ℕ} {F : GroupData D.denote}
    {Φl : List ℕ} {j : ℕ} : ∀ o ∈ allLeavesD O N n F Φl j, o.1 = 2 → LkJD (N - n) o.2.2 := by
  intro o ho h2
  unfold allLeavesD at ho
  obtain ⟨S, -, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨ab, -, ho⟩ := List.mem_flatMap.1 ho
  unfold choiceLeavesD at ho
  obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
  have h2' := lk_extD_tag h2
  exact (lk_ext (phiSD_nodup _ _ _) (fun v hv => (mem_phiSD.1 hv).1) h2'
    (lk_leaves_shape _ o' ho' h2')).2

end Shape

/-! ### The data leaves are the leaves of the tree -/

section Main

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}

/-- **The leaves listed on data are the leaves of the Case 2b tree**, as multisets, for
`P = ψ(F)` and `Φ` the listed points. -/
theorem allLeavesD_leafMs (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N F.2.1) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)) :
    (((allLeavesD O N n F Φl j).map (decodeOut (N - n)) :
        List (Option (Out (Fin (N - n))))) : Multiset (Option (Out (Fin (N - n))))) =
      (case2bTree (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
        (j + 1)).leafMs := by
  obtain ⟨N', gs, d⟩ := F
  change N' = N at hF1
  subst hF1
  exact lk_allLeaves hO hFv hF hΦnd hΦlt H

theorem lk_first_mem {N n : ℕ} {F : GroupData D.denote} {Φl : List ℕ} {j : ℕ} {o : OutD}
    (h : firstLeafD O N n F Φl j = some o) :
    ∃ Sl ∈ tuplesD Φl j, o ∈ choiceLeavesD O N n F Φl Sl 0 1 := by
  unfold firstLeafD at h
  rcases hT : tuplesD Φl j with _ | ⟨S, rest⟩
  · rw [hT] at h
    simp at h
  · rw [hT] at h
    exact ⟨S, List.mem_cons_self, List.mem_of_mem_head? h⟩

/-- The first leaf is listed. -/
theorem firstLeafD_mem {N n : ℕ} {F : GroupData D.denote} {Φl : List ℕ} {j : ℕ}
    {P : Subgroup (Perm (Fin (N - n)))} (hΦlt : ∀ v ∈ Φl, v < N - n)
    (H : Case2bHyp P (setOf (N - n) Φl) (j + 1)) {o : OutD}
    (h : firstLeafD O N n F Φl j = some o) : o ∈ allLeavesD O N n F Φl j := by
  obtain ⟨Sl, hS, ho⟩ := lk_first_mem h
  have h4 := lk_four hΦlt H hS
  unfold allLeavesD
  exact List.mem_flatMap.2 ⟨Sl, hS, List.mem_flatMap.2 ⟨(0, 1),
    mem_pairsD.2 ⟨by omega, by omega, by decide⟩, ho⟩⟩

/-- **The first leaf is a leaf of the Case 2b tree.** -/
theorem firstLeafD_reach (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N F.2.1) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)) {o : OutD} (h : firstLeafD O N n F Φl j = some o) :
    (case2bTree (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)).Reach (decodeOut (N - n) o) := by
  rw [← CTree.mem_leafMs, ← allLeavesD_leafMs hO hF1 hFv hF hΦnd hΦlt H, Multiset.mem_coe]
  exact List.mem_map_of_mem (firstLeafD_mem hΦlt H h)

/-- **The first leaf exists.** -/
theorem firstLeafD_ne_none (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N F.2.1) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)) :
    firstLeafD O N n F Φl j ≠ none := by
  obtain ⟨N', gs, d⟩ := F
  change N' = N at hF1
  subst hF1
  exact lk_first_ne hO hFv hF hΦnd hΦlt H

/-- **Every listed leaf is valid**: a colored partition with `PartValid` or a trimmed Johnson
embedding with `JValid`. -/
theorem allLeavesD_valid (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N F.2.1) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)) :
    ∀ o ∈ allLeavesD O N n F Φl j, OutValid (N - n) o := by
  intro o ho
  have hreach : (case2bTree (baseHom (GensData.denote N F.2.1) n hF).range
      (setOf (N - n) Φl) (j + 1)).Reach (decodeOut (N - n) o) := by
    rw [← CTree.mem_leafMs, ← allLeavesD_leafMs hO hF1 hFv hF hΦnd hΦlt H, Multiset.mem_coe]
    exact List.mem_map_of_mem ho
  exact lk_outValid (CTree.allLeaves_iff_reach.1 (case2bTree_valid H) _ hreach)
    (lk_allLeaves_shape o ho)

/-- **The first leaf is valid.** -/
theorem firstLeafD_valid (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N F.2.1) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)) {o : OutD} (h : firstLeafD O N n F Φl j = some o) : OutValid (N - n) o :=
  allLeavesD_valid hO hF1 hFv hF hΦnd hΦlt H o (firstLeafD_mem hΦlt H h)

/-- **The first leaf's partition is small** (stage 14j-6b-1, `PLAN-14.md` §14.11 item 1): a
first leaf that is not a Johnson leaf decodes to a colored `t`-partition of the base with
`t ≤ max ((|Φ| − j + 3) / 2) (m − (|Φ| − j))` (`case2bTree_partLe`). -/
theorem firstLeafD_partLe (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N F.2.1) n hF).range)] {Φl : List ℕ}
    (hΦnd : Φl.Nodup) (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1)) {o : OutD} (h : firstLeafD O N n F Φl j = some o) (h2 : o.1 ≠ 2) :
    ∃ (p : CPart (Fin (N - n))) (t : ℕ), decodeOut (N - n) o = some (Sum.inl p) ∧
      IsColPart univ t p ∧ t ≤ max ((Φl.length - j + 3) / 2) (N - n - (Φl.length - j)) := by
  have hv := firstLeafD_valid hO hF1 hFv hF hΦnd hΦlt H h
  have h1 : o.1 = 1 := by
    rcases hv with ⟨h1, -⟩ | ⟨h2', -⟩
    · exact h1
    · exact absurd h2' h2
  have hr := firstLeafD_reach hO hF1 hFv hF hΦnd hΦlt H h
  have hP := CTree.allLeaves_iff_reach.1 (case2bTree_partLe H) _ hr
  rw [ld_decodeOut_one h1] at hP ⊢
  obtain ⟨t, ht, hp⟩ := hP _ rfl
  refine ⟨_, t, rfl, hp, ?_⟩
  rw [lk_setOf_card hΦnd hΦlt, Nat.add_sub_cancel, Fintype.card_fin] at ht
  exact ht

/-- **The `soj` trees of the listed choices are small**: of size at most `sojZ (N − n)`. -/
theorem sojSz_le (hO : MeetsContractOn DV choiceOps O) {N n : ℕ}
    {F : GroupData D.denote} (hF1 : F.1 = N) (hFv : GroupValid DV N F.2.1 F.2.2)
    (hF : IsInvariant (GensData.denote N F.2.1) (baseSet n N)) {Φl : List ℕ}
    (hΦlt : ∀ v ∈ Φl, v < N - n) {j : ℕ}
    (H : Case2bHyp (baseHom (GensData.denote N F.2.1) n hF).range (setOf (N - n) Φl)
      (j + 1))
    {Sl : List ℕ} (hS : Sl ∈ tuplesD Φl j) {a b : ℕ}
    (hab : (a, b) ∈ pairsD (phiSD (N - n) Φl Sl).length) :
    sojSz (phiSD (N - n) Φl Sl).length (wlColOf O N n F Φl Sl a b) ≤ sojZ (N - n) := by
  obtain ⟨N', gs, d⟩ := F
  change N' = N at hF1
  subst hF1
  exact lk_sojSz hO hFv hF hΦlt H hS hab

end Main

end GraphIso.Case2b
