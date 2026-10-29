module

public import GraphIso.Main.M4Bridge
public import GraphIso.Case2b.Link
public import GraphIso.Case3.Link

/-!
# Coloured Johnson pairs in M5: the Johnson leaves

Stage 14j-4b, item 1 (`PLAN-14.md` §14.5). The Johnson leaves of Cases 2b and 3 are trimmed
Johnson embeddings found by Split-or-Johnson on a numbered set (`Φ ∖ S` in Case 2b, the
dominant class `C` in Case 3) and extended to the base along the numbering. They therefore lie
inside that set, and their point set `V₀` covers more than half of it. With a colouring `Q` of
the rest of the base, every colour class off `V₀` then has at most `m/2` points, the hypothesis
`hq` of `rd_ns_cj`.

* **The predicate** `JLeafOf e t o`: every Johnson leaf `o` is `extJohn e J₀` for a Johnson
  embedding `J₀` of `Fin m'` on more than `t` points (`IsJohnson univ t J₀`).
* **The trees.** `leafTree_jleaf` (Case 2b's leaf tree, under `leafTree_spec`'s hypotheses),
  `splitTree_jleaf` (Split-or-UPCC, under `splitTree_spec`'s), `outTree_jleaf` (Case 3's outcome
  at a good list): every reachable leaf satisfies `JLeafOf` along the numbering with
  `t = (m' + 3)/2`.
* **The colour bound.** `cj_ext_hq'`: for the extension along `e : Fin k ↪ Fin m` of a Johnson
  embedding with `k ≤ 2t`, and colours `q` constant (`c₁`) on the image of `e`, each colour class
  of the coloured extension off `V₀` has at most `m/2` points, provided each colour class of `q`
  off the image has at most `m/2` points and avoids `c₁`. This generalizes stage 14j-3's
  `cj_ext_hq` (two colours, all of the complement in one class).
* **On data** (`JAlong m L jd`: `jd` decodes to the extension, along a numbering of the points
  listed by `L`, of a Johnson embedding on more than half of them). `choiceLeavesD_along`
  (Case 2b: a listed Johnson leaf of a choice `(S, a, b)` lies along `Φ ∖ S`, on more than
  `(|Φ ∖ S| + 3)/2` points) and `outcomeD_along` (Case 3: along the dominant class `c3ClsD` of
  the good list). `cj_hq_of_along` turns `JAlong` into the colour bound, and `c3ClsD_facts`
  gives the dominant class: duplicate-free, inside `V`, of more than `(|V| + 1)/2` points.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Pointwise MulAction Cost GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.Recursion GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.Coherent
  GraphIso.SoJTree GraphIso.Case2b GraphIso.Align

/-! ### Johnson leaves along a numbering -/

section Abstract

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] {m : ℕ}

/-- **A Johnson leaf from `Fin m` along `e`**: if `o` is a Johnson embedding, it is the
extension along `e` of a Johnson embedding of `Fin m` on more than `t` points. -/
def JLeafOf (e : Fin m ↪ Γ) (t : ℕ) (o : Option (Out Γ)) : Prop :=
  ∀ J, o = some (Sum.inr J) → ∃ J₀ : JEmb (Fin m), J = extJohn e J₀ ∧ IsJohnson univ t J₀

/-- A valid leaf of Split-or-Johnson on `Fin m`, trimmed and extended along `e`, is a Johnson
leaf from `Fin m`. -/
theorem jleaf_extOut_trim (e : Fin m ↪ Γ) {t : ℕ} {o : Option (Out (Fin m))}
    (h : ValidOut univ t o) : JLeafOf e t (extOut e (trimOut o)) := by
  intro J hJ
  rcases o with _ | p | J₀
  · exact h.elim
  · simp [trimOut, extOut] at hJ
  · refine ⟨trimJ J₀, ?_, isJohnson_trimJ h⟩
    simp only [trimOut, extOut, Option.some.injEq, Sum.inr.injEq] at hJ
    exact hJ.symm

/-- **The Johnson leaves of Case 2b's leaf tree** (under `leafTree_spec`'s hypotheses) are
extensions along `e` of Johnson embeddings of `Fin m` on more than `(m + 3)/2` points. -/
theorem leafTree_jleaf (P : Subgroup (Perm Γ)) [DecidablePred (· ∈ P)] (S : Finset Γ)
    (e : Fin m ↪ Γ) {a' b' : Fin m} (hab : a' ≠ b') (hm : 4 ≤ m)
    (hmaps : ∀ g ∈ P, (∀ s ∈ S, g s = s) → ∀ i, ∃ j, g (e i) = e j)
    (htr : IsPretransitive (fixGroup P S e) (Fin m))
    (h2 : ¬ IsMultiplyPretransitive (fixGroup P S e) (Fin m) 2) :
    (leafTree P S (e a') (e b') e).AllLeaves (JLeafOf e ((m + 3) / 2)) := by
  have hR := orbRel_iff (a' := a') (b' := b') hmaps
  obtain ⟨hcoh, -, -, -⟩ := Recursion.wlRel_spec h2 hab _ hR
  unfold leafTree
  by_cases hd : (disconn univ (Recursion.wlRel (orbRel P S (e a') (e b') e))).Nonempty
  · rw [dite_eq_left hd]
    intro J hJ
    simp at hJ
  · rw [dite_eq_right hd]
    have hu : IsUniprimitive univ (Recursion.wlRel (orbRel P S (e a') (e b') e)) := by
      rcases Recursion.wlRel_split_or_uniprimitive h2 hab _ hR with ⟨h, -⟩ | hu
      · exact absurd h hd
      · exact hu
    obtain ⟨-, -, hvalid⟩ := split_or_johnson hcoh hu
      (t := (m + 3) / 2) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
    rw [SplitJohnson.CTree.allLeaves_iff_reach]
    intro o ho
    obtain ⟨o₀, ho₀, rfl⟩ := (Case2b.CTree.cb_reach_trans (chBack_chMap e)).1 ho
    exact jleaf_extOut_trim e ((SplitJohnson.CTree.allLeaves_iff_reach.1 hvalid) o₀ ho₀)

end Abstract

section Case3Abstract

open GraphIso.Case3 GraphIso.Recursion

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ]

/-- **The Johnson leaves of Split-or-UPCC** (under `splitTree_spec`'s hypotheses) are extensions
along `e` of Johnson embeddings of `Fin n` on more than `(n + 3)/2` points. -/
theorem splitTree_jleaf {n : ℕ} (c : Fin n → Fin n → ℕ) (e : Fin n ↪ Γ) (hn : 4 ≤ n)
    (hcoh : IsCoherent2 c) (hhom : IsHomog univ c) (hncl : ¬ IsClique c univ) :
    (splitTree c e).AllLeaves (JLeafOf e ((n + 3) / 2)) := by
  unfold splitTree
  by_cases hd : (disconn univ c).Nonempty
  · rw [dite_eq_left hd]
    intro J hJ
    simp at hJ
  · rw [dite_eq_right hd]
    have hu : IsUniprimitive univ c := by
      refine ⟨⟨hhom, fun r hr x _ y _ => ?_⟩, hncl⟩
      have hx : comp univ c r x = univ := by
        by_contra hne
        have hmem : r ∈ disconn univ c := by
          unfold disconn
          convert (Finset.mem_filter (s := offCols univ c)
            (p := fun r => ∃ x ∈ (univ : Finset (Fin n)), comp univ c r x ≠ univ)).2
            ⟨hr, x, Finset.mem_univ _, hne⟩
        exact hd ⟨r, hmem⟩
      have hy : y ∈ comp univ c r x := by
        rw [hx]
        exact Finset.mem_univ _
      exact (mem_comp.1 hy).2
    obtain ⟨-, -, hvalid⟩ := split_or_johnson hcoh hu
      (t := (n + 3) / 2) (by rw [Fintype.card_fin]; omega) (by rw [Fintype.card_fin]; omega)
    rw [SplitJohnson.CTree.allLeaves_iff_reach]
    intro o ho
    obtain ⟨o₀, ho₀, rfl⟩ := (Case2b.CTree.cb_reach_trans (chBack_chMap e)).1 ho
    exact jleaf_extOut_trim e ((SplitJohnson.CTree.allLeaves_iff_reach.1 hvalid) o₀ ho₀)

/-- **The Johnson leaves of Case 3's outcome at a good list** with a dominant class `C` are
extensions along the numbering of `C` (then `e`) of Johnson embeddings of `Fin |C|` on more than
`(|C| + 3)/2` points. -/
theorem outTree_jleaf {k m : ℕ} (W : (Fin k → Fin m) → ℕ) (hW : IsCoherent W) (e : Fin m ↪ Γ)
    (hm : 6 ≤ m) {z : List (Fin m)} (hz : DLGood W (thr m) z) (h : (domPts W z).Nonempty) :
    (outTree W e z).AllLeaves
      (JLeafOf ((eOf (domCls W z h)).trans e) (((domCls W z h).card + 3) / 2)) := by
  unfold outTree
  rw [dite_eq_left h]
  have hmin := mem_domPts.1 ((domPts W z).min'_mem h)
  obtain ⟨hlen, u, hu, hncl⟩ : z.length + 2 ≤ k ∧ ∃ u, thr m < (cls1 W z u).card ∧
      ¬ IsClique (skel2 W z) (cls1 W z u) := by
    rcases hz with hall | h2
    · exact absurd (hall _) (not_le.2 hmin)
    · exact h2
  have hC : domCls W z h = cls1 W z u := domCls_eq h hu
  set C := domCls W z h with hCdef
  have hP : ∀ w, w ∈ C ↔ skel2 W z w w = skel1 W z u := fun w => by
    rw [hC, mem_cls1, skel2_self]
  have hcoh : IsCoherent2 (skelOn W z C) :=
    c3m_isCoherent2_equiv (c3m_eqv C _ hP)
      (isCoherent2_restrict (isCoherent2_skel2 hW hlen) (skel1 W z u))
  have hhom : IsHomog univ (skelOn W z C) := fun x _ y _ => by
    show skel2 W z _ _ = skel2 W z _ _
    rw [(hP _).1 (c3m_eOf_mem C x), (hP _).1 (c3m_eOf_mem C y)]
  have hncl' : ¬ IsClique (skelOn W z C) univ := by
    intro hcl
    apply hncl
    rw [← hC]
    intro a ha b hb a' ha' b' hb' hab hab'
    obtain ⟨i, rfl⟩ := (mem_eOf_range C a).2 ha
    obtain ⟨j, rfl⟩ := (mem_eOf_range C b).2 hb
    obtain ⟨i', rfl⟩ := (mem_eOf_range C a').2 ha'
    obtain ⟨j', rfl⟩ := (mem_eOf_range C b').2 hb'
    exact hcl i (mem_univ _) j (mem_univ _) i' (mem_univ _) j' (mem_univ _)
      (fun h => hab (by rw [h])) (fun h => hab' (by rw [h]))
  have hcard : thr m < C.card := by rw [hC]; exact hu
  have hn : 4 ≤ C.card := by unfold thr at hcard; omega
  exact splitTree_jleaf (skelOn W z C) ((eOf C).trans e) hn hcoh hhom hncl'

end Case3Abstract

/-! ### The colour bound -/

section Bound

variable {k m : ℕ}

/-- **The colour classes off `V₀` are small, for a colouring constant on the image.** For the
extension along `e` of a Johnson embedding `J` of `Fin k` with threshold `t` and `k ≤ 2t` (so
`|V₀| > k/2`), and colours `q` equal to `c₁` on the image of `e`: if every colour class of `q`
off the image has at most `m/2` points and avoids `c₁`, every colour class of the coloured
extension off `V₀` has at most `m/2` points. Colour `0` (cells) and colour `c₁ + 1` (remaining
points of the image) lie in the image off `V₀`; any other colour lies off the image. -/
theorem cj_ext_hq' {jd : JData} {q : Array ℕ} {J : JEmb (Fin k)} {t : ℕ} (e : Fin k ↪ Fin m)
    (hjd : jdec m jd = extJohn e J) (hJ : IsJohnson univ t J) (hkt : k ≤ 2 * t) {c₁ : ℕ}
    (hq₁ : ∀ i, get q (e i).val = c₁)
    (hoff : ∀ γ : Fin m, (∀ i, e i ≠ γ) → get q γ.val ≠ c₁)
    (hcls : ∀ c, 2 * (univ.filter fun γ : Fin m => (∀ i, e i ≠ γ) ∧ get q γ.val = c).card ≤ m)
    (c : ℕ) :
    2 * (univ.filter fun γ => γ ∉ (jdec m jd).V0 ∧ cjcol m (jd, q) γ = c).card ≤ m := by
  have hkm : k ≤ m := by simpa using Fintype.card_le_of_embedding e
  have hV0 : (jdec m jd).V0 = J.V0.map e := by rw [hjd]; rfl
  have hΛ : (jdec m jd).Λ = J.Λ.image (fun A : Finset (Fin k) => A.map e) := by rw [hjd]; rfl
  set A₁ : Finset (Fin m) := univ.map e \ J.V0.map e with hA₁
  have hA₁c : A₁.card = k - J.V0.card := by
    rw [hA₁, card_sdiff_of_subset (map_subset_map.2 (subset_univ _)), card_map, card_map,
      card_univ, Fintype.card_fin]
  have hgt := hJ.card_gt
  have hV0k : J.V0.card ≤ k := by simpa using card_le_univ J.V0
  -- a point off the image is a remaining point
  have hrest : ∀ γ : Fin m, (∀ i, e i ≠ γ) → γ.val ∈ jrest m jd := by
    intro γ hγ
    rw [cj_mem_jrest_iff]
    refine ⟨fun hV => ?_, fun B hB hγB => ?_⟩
    · rw [hV0] at hV
      obtain ⟨i, -, hi⟩ := mem_map.1 hV
      exact hγ i hi
    · rw [hΛ, mem_image] at hB
      obtain ⟨A, -, rfl⟩ := hB
      obtain ⟨i, -, hi⟩ := mem_map.1 hγB
      exact hγ i hi
  by_cases hc : c = 0 ∨ c = c₁ + 1
  · have hsub : (univ.filter fun γ => γ ∉ (jdec m jd).V0 ∧ cjcol m (jd, q) γ = c) ⊆ A₁ := by
      intro γ hγ
      obtain ⟨-, hγV, hγc⟩ := mem_filter.1 hγ
      rw [hV0] at hγV
      by_cases him : ∃ i, e i = γ
      · obtain ⟨i, rfl⟩ := him
        exact mem_sdiff.2 ⟨mem_map_of_mem _ (mem_univ _), hγV⟩
      · have hγ' : ∀ i, e i ≠ γ := fun i hi => him ⟨i, hi⟩
        have hR := hrest γ hγ'
        unfold cjcol at hγc
        simp only [hR, ↓reduceIte] at hγc
        rcases hc with rfl | rfl
        · omega
        · exact absurd (by omega) (hoff γ hγ')
    have := card_le_card hsub
    omega
  · rw [not_or] at hc
    have hsub : (univ.filter fun γ => γ ∉ (jdec m jd).V0 ∧ cjcol m (jd, q) γ = c) ⊆
        univ.filter fun γ : Fin m => (∀ i, e i ≠ γ) ∧ get q γ.val = c - 1 := by
      intro γ hγ
      obtain ⟨-, -, hγc⟩ := mem_filter.1 hγ
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      by_cases him : ∃ i, e i = γ
      · exfalso
        obtain ⟨i, rfl⟩ := him
        unfold cjcol at hγc
        split_ifs at hγc
        · rw [hq₁] at hγc
          exact hc.2 hγc.symm
        · exact hc.1 hγc.symm
      · have hγ' : ∀ i, e i ≠ γ := fun i hi => him ⟨i, hi⟩
        have hR := hrest γ hγ'
        unfold cjcol at hγc
        simp only [hR, ↓reduceIte] at hγc
        exact ⟨hγ', by omega⟩
    exact (Nat.mul_le_mul_left 2 (card_le_card hsub)).trans (hcls _)

end Bound

/-! ### Johnson data along a list -/

section Along

variable {m : ℕ}

/-- **Johnson data along a list `L`**: `jd` decodes to the extension, along a numbering of the
points listed by `L`, of a Johnson embedding on more than half of them. -/
def JAlong (m : ℕ) (L : List ℕ) (jd : JData) : Prop :=
  ∃ (r : ℕ) (e : Fin r ↪ Fin m) (J₀ : JEmb (Fin r)) (t : ℕ),
    (∀ v : Fin m, (∃ i, e i = v) ↔ v.val ∈ L) ∧ jdec m jd = extJohn e J₀ ∧
      IsJohnson univ t J₀ ∧ r ≤ 2 * t

/-- Johnson data along a list decode to a Johnson embedding. -/
theorem isJohnson_of_along {L : List ℕ} {jd : JData} (h : JAlong m L jd) :
    ∃ t, IsJohnson univ t (jdec m jd) := by
  obtain ⟨r, e, J₀, t, -, hjd, hJ, -⟩ := h
  exact ⟨t, hjd ▸ extJohn_valid e hJ⟩

/-- **The colour bound for Johnson data along `L`**: with colours `q` equal to `c₁` on `L`,
different from `c₁` off `L`, and with every colour class off `L` of at most `m/2` points, every
colour class of the coloured data off `V₀` has at most `m/2` points (`cj_ext_hq'`). -/
theorem cj_hq_of_along {L : List ℕ} {jd : JData} (h : JAlong m L jd) {q : Array ℕ} {c₁ : ℕ}
    (hq₁ : ∀ v : Fin m, v.val ∈ L → get q v.val = c₁)
    (hoff : ∀ v : Fin m, v.val ∉ L → get q v.val ≠ c₁)
    (hcls : ∀ c, 2 * (univ.filter fun v : Fin m => v.val ∉ L ∧ get q v.val = c).card ≤ m)
    (c : ℕ) :
    2 * (univ.filter fun γ => γ ∉ (jdec m jd).V0 ∧ cjcol m (jd, q) γ = c).card ≤ m := by
  obtain ⟨r, e, J₀, t, hr, hjd, hJ, hrt⟩ := h
  have hoffL : ∀ v : Fin m, (∀ i, e i ≠ v) ↔ v.val ∉ L := fun v => by
    rw [← hr v]
    exact ⟨fun h ⟨i, hi⟩ => h i hi, fun h i hi => h ⟨i, hi⟩⟩
  refine cj_ext_hq' e hjd hJ hrt (fun i => hq₁ _ ((hr _).1 ⟨i, rfl⟩))
    (fun v hv => hoff v ((hoffL v).1 hv)) (fun c' => ?_) c
  have hset : (univ.filter fun γ : Fin m => (∀ i, e i ≠ γ) ∧ get q γ.val = c') =
      univ.filter fun v : Fin m => v.val ∉ L ∧ get q v.val = c' := by
    ext v
    simp only [mem_filter, mem_univ, true_and, hoffL]
  rw [hset]
  exact hcls c'

end Along

/-! ### Case 2b on data -/

section Case2bData

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}

/-- The elements of `P` fixing `S` are not doubly transitive on `Φ ∖ S`, numbered by `e`. -/
theorem lk_not_two {Γ : Type*} [DecidableEq Γ] {m' : ℕ} {P : Subgroup (Perm Γ)} {Φ S : Finset Γ}
    {e : Fin m' ↪ Γ} (hr : ∀ v, (∃ i, e i = v) ↔ v ∈ Φ \ S)
    (h : ¬ ∀ x₁ ∈ Φ \ S, ∀ x₂ ∈ Φ \ S, ∀ y₁ ∈ Φ \ S, ∀ y₂ ∈ Φ \ S, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g ∈ P, (∀ s ∈ S, g s = s) ∧ g x₁ = y₁ ∧ g x₂ = y₂) :
    ¬ IsMultiplyPretransitive (fixGroup P S e) (Fin m') 2 := by
  intro h2
  rw [is_two_pretransitive_iff] at h2
  refine h fun x₁ hx₁ x₂ hx₂ y₁ hy₁ y₂ hy₂ hx hy => ?_
  obtain ⟨u₁, rfl⟩ := (hr _).2 hx₁
  obtain ⟨u₂, rfl⟩ := (hr _).2 hx₂
  obtain ⟨v₁, rfl⟩ := (hr _).2 hy₁
  obtain ⟨v₂, rfl⟩ := (hr _).2 hy₂
  obtain ⟨⟨h, g, hg, hgS, he⟩, h₁, h₂⟩ :=
    h2 (a := u₁) (b := u₂) (c := v₁) (d := v₂) (fun h => hx (by rw [h]))
      (fun h => hy (by rw [h]))
  refine ⟨g, hg, hgS, ?_, ?_⟩
  · rw [he]
    exact congrArg e h₁
  · rw [he]
    exact congrArg e h₂

/-- **A listed Johnson leaf of Case 2b lies along `Φ ∖ S`.** For a choice `(S, (a, b))` of the
Case 2b tree's data, every Johnson leaf is the extension along the numbering `phiE` of `Φ ∖ S`
of a Johnson embedding of `Fin |Φ ∖ S|` on more than `(|Φ ∖ S| + 3)/2` points. -/
theorem choiceLeavesD_along (hO : MeetsContractOn DV choiceOps O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hFv : GroupValid DV N gs d)
    (hF : IsInvariant (GensData.denote N gs) (baseSet n N))
    [DecidablePred (· ∈ (baseHom (GensData.denote N gs) n hF).range)] {Φl Sl : List ℕ} {j : ℕ}
    (hΦlt : ∀ v ∈ Φl, v < N - n)
    (H : Case2bHyp (baseHom (GensData.denote N gs) n hF).range (setOf (N - n) Φl) (j + 1))
    (hS : Sl ∈ tuplesD Φl j) {a b : ℕ} (hab : (a, b) ∈ pairsD (phiSD (N - n) Φl Sl).length)
    {o : OutD} (ho : o ∈ choiceLeavesD O N n (N, gs, d) Φl Sl a b) (h2 : o.1 = 2) :
    JAlong (N - n) (phiSD (N - n) Φl Sl) o.2.2 := by
  obtain ⟨hSl, hsub, hcard⟩ := lk_tuple hΦlt hS
  obtain ⟨ha, hb, hne⟩ := Case2b.mem_pairsD.1 hab
  have hpos : 4 ≤ (phiSD (N - n) Φl Sl).length := lk_four hΦlt H hS
  have hr : ∀ v, (∃ i, phiE (N - n) Φl Sl i = v) ↔ v ∈ setOf (N - n) Φl \ setOf (N - n) Sl :=
    phiE_range
  have htr := lk_pretrans H.pres hr (H.trans _ hsub hcard)
  have hmaps := lk_maps H.pres hr
  have hnt := lk_not_two hr (H.notTwo _ hsub hcard)
  have hms := lk_choice hO hFv hF H.pres hSl htr (by omega) ⟨a, ha⟩ ⟨b, hb⟩
  have hmem : decodeOut (N - n) o ∈ (leafTree (baseHom (GensData.denote N gs) n hF).range
      (setOf (N - n) Sl) (phiE (N - n) Φl Sl ⟨a, ha⟩) (phiE (N - n) Φl Sl ⟨b, hb⟩)
      (phiE (N - n) Φl Sl)).leafMs := by
    rw [← hms, Multiset.mem_coe]
    exact List.mem_map_of_mem ho
  have hj := (SplitJohnson.CTree.allLeaves_iff_reach.1
    (leafTree_jleaf _ _ (phiE (N - n) Φl Sl) (a' := ⟨a, ha⟩) (b' := ⟨b, hb⟩)
      (fun h => hne (congrArg Fin.val h)) hpos hmaps htr hnt))
    _ (CTree.mem_leafMs.1 hmem)
  obtain ⟨J₀, hJe, hJ⟩ := hj _ (ld_decodeOut_two h2)
  refine ⟨_, phiE (N - n) Φl Sl, J₀, _, fun v => ?_, hJe, hJ, by omega⟩
  rw [hr, mem_sdiff, mem_setOf, mem_setOf, mem_phiSD]
  exact ⟨fun h => ⟨v.2, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

end Case2bData

/-! ### Case 3 on data -/

section Case3Data

open GraphIso.Case3

/-- **The dominant class of a good list `z`**, as base indices: the class of `domA` when a
vertex colour class has more than `t` points (`outcomeD`'s Split-or-UPCC branch), else empty. -/
def c3ClsD (k : ℕ) (V : List ℕ) (W : Array ℕ) (z : List ℕ) : List ℕ :=
  match domA (col1D k V.length W z) (tOf V.length) with
  | none => []
  | some u₀ => classB V (classA (col1D k V.length W z) u₀)

/-- **A listed Johnson structure of Case 3 lies along the dominant class.** At a good list `z`
of the refinement of `col`, every Johnson structure is the extension, along a numbering of the
dominant class `c3ClsD`, of a Johnson embedding on more than half of it. -/
theorem outcomeD_along {M k : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup)
    (col : Array ℕ) (hm : 6 ≤ V.length) {z : List ℕ}
    (hz : z ∈ goodListsD k V.length (wlCD k V.length col)) {o : OutD}
    (ho : o ∈ outcomeD M k V (wlCD k V.length col) z) (h2 : o.1 = 2) :
    JAlong M (c3ClsD k V (wlCD k V.length col) z) o.2.2 := by
  classical
  obtain ⟨x, -, rfl, hgood⟩ := mem_goodListsD.1 hz
  have hms := c3l_outcome (k := k) hV hnd col x
  rw [← toFun_wlCD (k := k)] at hms
  set W := wlCD k V.length col with hW
  have hmem : decodeOut M o ∈ (outTree (toFun (k := k) W) (lkE V hV hnd) x).leafMs := by
    rw [← hms, Multiset.mem_coe]
    exact List.mem_map_of_mem ho
  unfold c3ClsD
  rcases hsome : domA (col1D k V.length W (x.map Fin.val)) (tOf V.length) with _ | u₀
  · exfalso
    unfold outcomeD at ho
    rw [hsome, List.mem_singleton] at ho
    subst ho
    simp [extD, smallLeafD, partD] at h2
  · obtain ⟨hu, hcard⟩ := domA_col1D_some W x hsome
    have hdom : (domPts (toFun (k := k) W) x).Nonempty := ⟨⟨u₀, hu⟩, mem_domPts.2 hcard⟩
    have hC : domCls (toFun (k := k) W) x hdom = cls1 (toFun (k := k) W) x ⟨u₀, hu⟩ :=
      domCls_eq hdom hcard
    have hset := setOf_classA_col1D (k := k) W x ⟨u₀, hu⟩
    have hcoh : IsCoherent (toFun (k := k) (m := V.length) W) := by
      rw [hW, toFun_wlCD]
      exact wl_isCoherent _
    have hj := (SplitJohnson.CTree.allLeaves_iff_reach.1
      (outTree_jleaf (toFun (k := k) W) hcoh (lkE V hV hnd) hm hgood hdom))
      _ (CTree.mem_leafMs.1 hmem)
    obtain ⟨J₀, hJe, hJ⟩ := hj _ (ld_decodeOut_two h2)
    refine ⟨_, (eOf (domCls (toFun (k := k) W) x hdom)).trans (lkE V hV hnd), J₀, _,
      fun v => ?_, hJe, hJ, by omega⟩
    simp only [Function.Embedding.trans_apply]
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨w, hw, hwj⟩ : ∃ w ∈ domCls (toFun (k := k) W) x hdom,
          eOf (domCls (toFun (k := k) W) x hdom) j = w := ⟨_, c3m_eOf_mem _ j, rfl⟩
      rw [hwj]
      rw [hC, ← hset, mem_setOf] at hw
      refine List.mem_map.2 ⟨_, hw, ?_⟩
      rw [lkE_val, List.getD_eq_getElem _ _ w.2]
      rfl
    · intro hv
      obtain ⟨i, hi, hiv⟩ := List.mem_map.1 hv
      have hiV := c3l_classA_lt (k := k) W _ u₀ i hi
      have hmem' : (⟨i, hiV⟩ : Fin V.length) ∈ domCls (toFun (k := k) W) x hdom := by
        rw [hC, ← hset, mem_setOf]
        exact hi
      obtain ⟨j, hj⟩ := (mem_eOf_range _ _).2 hmem'
      refine ⟨j, Fin.ext ?_⟩
      rw [hj, lkE_val, ← hiv, List.getD_eq_getElem _ _ hiV]
      rfl

/-- A Johnson structure at a good list comes from a large vertex colour class. -/
theorem domPts_of_john {M k : ℕ} {V : List ℕ} (W : Array ℕ) (x : List (Fin V.length))
    {o : OutD} (ho : o ∈ outcomeD M k V W (x.map Fin.val)) (h2 : o.1 = 2) :
    (domPts (toFun (k := k) W) x).Nonempty := by
  rcases hsome : domA (col1D k V.length W (x.map Fin.val)) (tOf V.length) with _ | u₀
  · exfalso
    unfold outcomeD at ho
    rw [hsome, List.mem_singleton] at ho
    subst ho
    simp [extD, smallLeafD, partD] at h2
  · obtain ⟨hu, hcard⟩ := domA_col1D_some W x hsome
    exact ⟨⟨u₀, hu⟩, mem_domPts.2 hcard⟩

/-- **The data's dominant class is the model's**: with a large vertex colour class, a base index
is listed by `c3ClsD` exactly when it numbers a point of `domCls`. -/
theorem mem_c3ClsD_iff {M k : ℕ} {V : List ℕ} (hV : ∀ v ∈ V, v < M) (hnd : V.Nodup)
    (W : Array ℕ) (x : List (Fin V.length)) (hdom : (domPts (toFun (k := k) W) x).Nonempty)
    (v : Fin M) :
    v.val ∈ c3ClsD k V W (x.map Fin.val) ↔
      ∃ i ∈ domCls (toFun (k := k) W) x hdom, lkE V hV hnd i = v := by
  rcases hsome : domA (col1D k V.length W (x.map Fin.val)) (tOf V.length) with _ | u₀
  · exfalso
    obtain ⟨u, hu⟩ := hdom
    exact absurd ((domA_col1D_none_iff W x).1 hsome u) (not_le.2 (mem_domPts.1 hu))
  · obtain ⟨hu, hcard⟩ := domA_col1D_some W x hsome
    have hC : domCls (toFun (k := k) W) x hdom = cls1 (toFun (k := k) W) x ⟨u₀, hu⟩ :=
      domCls_eq hdom hcard
    have hset := setOf_classA_col1D (k := k) W x ⟨u₀, hu⟩
    unfold c3ClsD
    rw [hsome]
    constructor
    · intro hv
      obtain ⟨i, hi, hiv⟩ := List.mem_map.1 hv
      have hiV := c3l_classA_lt (k := k) W _ u₀ i hi
      refine ⟨⟨i, hiV⟩, by rw [hC, ← hset, mem_setOf]; exact hi, Fin.ext ?_⟩
      rw [lkE_val, ← hiv, List.getD_eq_getElem _ _ hiV]
      rfl
    · rintro ⟨w, hw, rfl⟩
      rw [hC, ← hset, mem_setOf] at hw
      refine List.mem_map.2 ⟨_, hw, ?_⟩
      rw [lkE_val, List.getD_eq_getElem _ _ w.2]
      rfl

/-- **The dominant class of the data**: duplicate-free, inside `V`, and of more than
`(|V| + 1)/2` points. -/
theorem c3ClsD_facts {k : ℕ} {V : List ℕ} (hnd : V.Nodup) (W : Array ℕ)
    (x : List (Fin V.length)) (hdom : (domPts (toFun (k := k) W) x).Nonempty) :
    (c3ClsD k V W (x.map Fin.val)).Nodup ∧ (∀ v ∈ c3ClsD k V W (x.map Fin.val), v ∈ V) ∧
      tOf V.length < (c3ClsD k V W (x.map Fin.val)).length := by
  rcases hsome : domA (col1D k V.length W (x.map Fin.val)) (tOf V.length) with _ | u₀
  · exfalso
    obtain ⟨u, hu⟩ := hdom
    exact absurd ((domA_col1D_none_iff W x).1 hsome u) (not_le.2 (mem_domPts.1 hu))
  · obtain ⟨hu, hcard⟩ := domA_col1D_some W x hsome
    have hset := setOf_classA_col1D (k := k) W x ⟨u₀, hu⟩
    unfold c3ClsD
    rw [hsome]
    refine ⟨c3l_classB_nodup (k := k) hnd W _ u₀, fun v hv => ?_, ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
      exact c3p_getD_mem (c3l_classA_lt (k := k) W _ u₀ i hi)
    · rw [length_classB, ← lk_setOf_card (classA_nodup _ u₀) (c3l_classA_lt (k := k) W _ u₀),
        hset]
      exact hcard

end Case3Data

end GraphIso.Main
