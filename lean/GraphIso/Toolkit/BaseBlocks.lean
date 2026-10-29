module

public import GraphIso.Toolkit.Transitivity
public import GraphIso.Luks.MaxBlocksProg
public import GraphIso.Recursion.Coarsen

/-!
# Block systems of the base

`PLAN-14.md` §6 item 5. For a group of degree `N` transitive on its base positions `[n, N)`,
`baseBlocksProg` runs the maximal-block program of milestone 3 (`maxBlocksProg`, no backend
calls) on the base positions. The result is a list of at least two blocks of equal size
(`baseBlocks_spec`):

* if the blocks are single points, the base action is primitive;
* otherwise the blocks have at least two points each and, read as sets of base points
  (`blockFam`), form a block system `IsBlockSys` of the base action `baseHom` in the sense of
  stage 14a, with at least two blocks.
-/

@[expose] public section

namespace GraphIso.Toolkit

open Equiv MulAction Cost Programs GraphIso.Recursion GraphIso.Luks

/-! ### Blocks as sets of base points -/

/-- The base index of a position, if it is a base position. -/
def toBase (n N i : ℕ) : Option (Fin (N - n)) :=
  if h : n ≤ i ∧ i < N then some ⟨i - n, by omega⟩ else none

/-- A list of positions as a set of base points. -/
def baseBlockSet (n N : ℕ) (b : List ℕ) : Finset (Fin (N - n)) :=
  (b.filterMap (toBase n N)).toFinset

/-- A block list as a family of sets of base points. -/
def blockFam (n N : ℕ) (bs : List (List ℕ)) : Finset (Finset (Fin (N - n))) :=
  (bs.map (baseBlockSet n N)).toFinset

theorem mem_baseBlockSet {n N : ℕ} {b : List ℕ} {γ : Fin (N - n)} :
    γ ∈ baseBlockSet n N b ↔ n + γ.val ∈ b := by
  simp only [baseBlockSet, List.mem_toFinset, List.mem_filterMap, toBase]
  constructor
  · rintro ⟨i, hi, hγ⟩
    split_ifs at hγ with h
    simp only [Option.some.injEq] at hγ
    have : i = n + γ.val := by rw [← hγ]; simp; omega
    rwa [← this]
  · intro h
    refine ⟨n + γ.val, h, ?_⟩
    have hlt := γ.2
    have h1 : n ≤ n + γ.val := by omega
    have h2 : n + γ.val < N := by omega
    simp [h1, h2]

/-- The base positions form the window of the base. -/
theorem denote_basePts (n N : ℕ) :
    (WinData.ofPoints N (basePts n N)).denote N = baseSet n N := by
  ext u
  simp only [WinData.denote_ofPoints, Set.mem_ofPred_eq, mem_basePts, baseSet]
  exact ⟨fun h => h.1, fun h => ⟨h, u.2⟩⟩

theorem basePts_cons {n N : ℕ} (h : n < N) : basePts n N = n :: basePts (n + 1) N := by
  unfold basePts
  rw [show N - n = (N - (n + 1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp
  omega

/-- The base positions satisfy `Win` for valid generators preserving the base. -/
theorem win_basePts {N n : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) : Win N gs (basePts n N) :=
  win_of_valid (w := WinData.ofPoints N (basePts n N))
    (WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2) hgs
    (by rw [denote_basePts]; exact hinv)

/-! ### The program -/

section Program

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The maximal block system of a group on its base positions. -/
def baseBlocksProg (n : var .nat) (G : var (Ty.group D)) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .fst G) fun N => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
  .bind (.op2 .sub N n) fun m => .bind (rangeFromProg n m) fun pts => maxBlocksProg N gs pts

end Program

/-- The cost of `baseBlocksProg`. -/
def baseBlocksCost (N m s : ℕ) : ℕ := 5 * m + 8 + maxBlocksCost N m s

section Specs

variable {D : Ty} {S : Signature} {a b : Ty} {X : Ctx S}
  {body : a.denote → Prog S (a, b) Ty.denote b}

/-- **The cost of `baseBlocksProg`.** -/
theorem RunsWithin.baseBlocksProg {N n : ℕ} {gs : GensData} {d : D.denote}
    (hgs : GensData.AllValid N gs) (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) :
    RunsWithin X body (Toolkit.baseBlocksProg n (N, gs, d)) (maxBlocks N gs (basePts n N))
      (baseBlocksCost N (N - n) gs.length) := by
  have hrange := RunsWithin.rangeFromProg (X := X) (body := body) n (N - n)
  have hmb := RunsWithin.maxBlocksProg (X := X) (body := body) (win_basePts hgs hinv)
  rw [length_basePts] at hmb
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hrange
    exact hmb
  case hc =>
    simp only [Prim.cost, baseBlocksCost]
    omega

end Specs

/-! ### The meaning -/

section Meaning

variable {N n : ℕ} {bs : List (List ℕ)}

theorem block_sub_base (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs) {b : List ℕ}
    (hb : b ∈ bs) {x : ℕ} (hx : x ∈ b) : n ≤ x ∧ x < N :=
  mem_basePts.1 (hbs.1.mem_iff.1 (List.mem_flatten.2 ⟨b, hb, hx⟩))

theorem flatten_nodup (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs) :
    bs.flatten.Nodup := hbs.1.nodup_iff.2 (basePts_nodup _ _)

theorem block_nodup (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs) {b : List ℕ}
    (hb : b ∈ bs) : b.Nodup :=
  (List.nodup_flatten.1 (flatten_nodup hbs)).1 b hb

theorem blocks_disjoint (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    {b b' : List ℕ} (hb : b ∈ bs) (hb' : b' ∈ bs) (hne : b ≠ b') : List.Disjoint b b' := by
  have : Std.Symm (List.Disjoint (α := ℕ)) := ⟨fun _ _ h => h.symm⟩
  exact (List.nodup_flatten.1 (flatten_nodup hbs)).2.forall hb hb' hne

theorem card_baseBlockSet (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    {b : List ℕ} (hb : b ∈ bs) : (baseBlockSet n N b).card = b.length := by
  have hsub : ∀ x ∈ b, n ≤ x ∧ x < N := fun x hx => block_sub_base hbs hb hx
  let e : Fin (N - n) ↪ ℕ := ⟨fun γ => n + γ.val, fun γ δ h => Fin.ext (by simpa using h)⟩
  have hmap : (baseBlockSet n N b).map e = b.toFinset := by
    ext x
    simp only [Finset.mem_map, List.mem_toFinset, mem_baseBlockSet]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact hγ
    · intro hx
      have := hsub x hx
      refine ⟨⟨x - n, by omega⟩, by simpa [show n + (x - n) = x by omega] using hx, ?_⟩
      change n + (x - n) = x
      omega
  rw [← Finset.card_map e, hmap, List.toFinset_card_of_nodup (block_nodup hbs hb)]

theorem exists_baseBlock (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (γ : Fin (N - n)) : ∃ b ∈ bs, n + γ.val ∈ b := by
  have : n + γ.val ∈ bs.flatten :=
    hbs.1.mem_iff.2 (mem_basePts.2 ⟨by omega, by have := γ.2; omega⟩)
  obtain ⟨b, hb, hx⟩ := List.mem_flatten.1 this
  exact ⟨b, hb, hx⟩

end Meaning

/-- **The meaning of `baseBlocksProg`.** For a base action that is transitive on at least two
points, the maximal blocks are at least two blocks of equal size. If they are single points, the
base action is primitive; otherwise they form a block system of the base action with at least
two blocks of at least two points. -/
theorem baseBlocks_spec {N n : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (h2 : n + 2 ≤ N)
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hinv g γ = δ) :
    2 ≤ (maxBlocks N gs (basePts n N)).length ∧
      (∀ b ∈ maxBlocks N gs (basePts n N),
        b.length = ((maxBlocks N gs (basePts n N)).headD []).length) ∧
      (((maxBlocks N gs (basePts n N)).headD []).length = 1 →
        IsPreprimitive (baseHom (GensData.denote N gs) n hinv).range (Fin (N - n))) ∧
      (2 ≤ ((maxBlocks N gs (basePts n N)).headD []).length →
        IsBlockSys (baseHom (GensData.denote N gs) n hinv)
          (blockFam n N (maxBlocks N gs (basePts n N))) ∧
        2 ≤ (blockFam n N (maxBlocks N gs (basePts n N))).card ∧
        ∀ B ∈ blockFam n N (maxBlocks N gs (basePts n N)), 2 ≤ B.card) := by
  set G := GensData.denote N gs with hGdef
  have hw : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hinvw : IsInvariant G ((WinData.ofPoints N (basePts n N)).denote N) := by
    rw [denote_basePts]
    exact hinv
  have hpts : (WinData.ofPoints N (basePts n N)).1 = n :: basePts (n + 1) N :=
    basePts_cons (by omega)
  have hrest : basePts (n + 1) N ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [length_basePts] at this
    simp at this
    omega
  have htr' : ∀ j, j ∈ (WinData.ofPoints N (basePts n N)).1 ↔ SameOrbit G n j := by
    intro j
    constructor
    · intro hj
      rw [WinData.ofPoints_fst, mem_basePts] at hj
      obtain ⟨g, hg⟩ := htr ⟨0, by omega⟩ ⟨j - n, by omega⟩
      have e := baseHom_apply (hG := hinv) g ⟨0, by omega⟩
      rw [hg] at e
      have hb0 : basePos (n := n) (N := N) ⟨0, by omega⟩ = ⟨n, by omega⟩ := by
        ext
        simp [basePos]
      rw [hb0] at e
      refine ⟨by omega, hj.2, g.1, g.2, ?_⟩
      rw [← e]
      ext
      simp only [basePos]
      omega
    · intro h
      exact h.mem_of_invariant hinvw (by rw [hpts]; exact List.mem_cons_self)
  obtain ⟨hbs, hG, hlen, hsize, hprim⟩ := maxBlocks_spec hw hgs hinvw hpts hrest htr'
  simp only [WinData.ofPoints_fst] at hsize
  have hbsrfl : maxBlocks N gs (basePts n N) =
      maxBlocks N gs (WinData.ofPoints N (basePts n N)).1 := rfl
  rw [hbsrfl]
  set bs := maxBlocks N gs (WinData.ofPoints N (basePts n N)).1 with hbsdef
  have hne : bs ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  have hhead : bs.headD [] ∈ bs := by
    obtain ⟨b, rest, hb⟩ := List.exists_cons_of_ne_nil hne
    rw [hb]
    exact List.mem_cons_self
  have hequal : ∀ b ∈ bs, b.length = (bs.headD []).length := by
    intro b hb
    have h1 := hsize b hb
    have h2 := hsize _ hhead
    have hpos : 0 < bs.length := by omega
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  refine ⟨hlen, hequal, fun h1 => ?_, fun h2b => ?_⟩
  · -- singleton blocks: the base action is primitive
    have hsing : ∀ t (ht : t < bs.length), bs[t] = [(blockReps bs).getD t 0] := by
      intro t ht
      have hl : bs[t].length = 1 := (hequal _ (List.getElem_mem ht)).trans h1
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hl
      have hrep := blockReps_mem hbs ht
      rw [hx, List.mem_singleton] at hrep
      rw [hx, hrep]
    have hrepb : ∀ t (ht : t < bs.length), n ≤ (blockReps bs).getD t 0 ∧
        (blockReps bs).getD t 0 < N := fun t ht =>
      block_sub_base hbs (List.getElem_mem ht) (blockReps_mem hbs ht)
    let f : Fin bs.length → Fin (N - n) := fun t =>
      ⟨(blockReps bs).getD t 0 - n, by have := hrepb t t.2; omega⟩
    have hf : ∀ (g : G) (t : Fin bs.length),
        f (blockHom hw hbs hG g t) = baseHom G n hinv g (f t) := by
      intro g t
      have hb := hrepb t t.2
      obtain ⟨ht', himg⟩ := blockMap_spec hw hbs hG g.2 t.2
      have hu := himg ⟨_, hb.2⟩ (blockReps_mem hbs t.2)
      rw [hsing _ ht', List.mem_singleton] at hu
      have e := baseHom_apply (hG := hinv) g (f t)
      have hpos : basePos (n := n) (N := N) (f t) = ⟨(blockReps bs).getD t 0, hb.2⟩ := by
        ext
        simp only [basePos, f]
        omega
      rw [hpos] at e
      have e2 : n + (baseHom G n hinv g (f t)).val =
          (g.1 ⟨(blockReps bs).getD t 0, hb.2⟩).val := congrArg Fin.val e
      apply Fin.ext
      show (blockReps bs).getD (blockHom hw hbs hG g t).val 0 - n =
        (baseHom G n hinv g (f t)).val
      rw [blockHom_apply, ← hu]
      omega
    have hsurj : Function.Surjective f := by
      intro γ
      obtain ⟨b, hb, hx⟩ := exists_baseBlock hbs γ
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hb
      rw [hsing t ht, List.mem_singleton] at hx
      exact ⟨⟨t, ht⟩, Fin.ext (by simp only [f]; omega)⟩
    let φ : (blockHom hw hbs hG).range → (baseHom G n hinv).range := fun p =>
      ⟨baseHom G n hinv (Classical.choose p.2), ⟨_, rfl⟩⟩
    let F : Fin bs.length →ₑ[φ] Fin (N - n) :=
      { toFun := f
        map_smul' := by
          intro p t
          have hp := Classical.choose_spec p.2
          change f ((p : Perm (Fin bs.length)) t) = baseHom G n hinv (Classical.choose p.2) (f t)
          conv_lhs => rw [← hp]
          exact hf _ t }
    have := hprim
    exact IsPreprimitive.of_surjective (f := F) hsurj
  · -- blocks of at least two points: a block system
    have hcardB : ∀ b ∈ bs, (baseBlockSet n N b).card = (bs.headD []).length := fun b hb =>
      (card_baseBlockSet hbs hb).trans (hequal b hb)
    have hnonempty : ∀ b ∈ bs, (baseBlockSet n N b).Nonempty := by
      intro b hb
      rw [← Finset.card_pos, hcardB b hb]
      omega
    have hdisj : ∀ b ∈ bs, ∀ b' ∈ bs, baseBlockSet n N b ≠ baseBlockSet n N b' →
        Disjoint (baseBlockSet n N b) (baseBlockSet n N b') := by
      intro b hb b' hb' hne'
      have hbb : b ≠ b' := fun h => hne' (h ▸ rfl)
      have hd := blocks_disjoint hbs hb hb' hbb
      rw [Finset.disjoint_left]
      intro γ h1 h2
      rw [mem_baseBlockSet] at h1 h2
      exact hd h1 h2
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro B hB
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hB)
      exact hnonempty b hb
    · intro B hB C hC hBC
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hB)
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hC)
      exact hdisj b hb c hc hBC
    · intro γ
      obtain ⟨b, hb, hx⟩ := exists_baseBlock hbs γ
      exact ⟨baseBlockSet n N b, List.mem_toFinset.2 (List.mem_map_of_mem hb),
        mem_baseBlockSet.2 hx⟩
    · intro g B hB
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hB)
      obtain ⟨b', hb', himg⟩ := hG g.1 g.2 b hb
      have hsub : setAct (baseHom G n hinv) g (baseBlockSet n N b) ⊆ baseBlockSet n N b' := by
        intro δ hδ
        rw [setAct_apply, Finset.mem_smul_finset] at hδ
        obtain ⟨γ, hγ, rfl⟩ := hδ
        rw [mem_baseBlockSet] at hγ ⊢
        have e := baseHom_apply (hG := hinv) g γ
        have hx := himg (basePos γ) (by simpa [basePos] using hγ)
        rw [← e] at hx
        simpa [basePos] using hx
      have hcard : (setAct (baseHom G n hinv) g (baseBlockSet n N b)).card =
          (baseBlockSet n N b').card := by
        rw [setAct_apply, Finset.card_smul_finset, hcardB b hb, hcardB b' hb']
      rw [Finset.eq_of_subset_of_card_le hsub hcard.ge]
      exact List.mem_toFinset.2 (List.mem_map_of_mem hb')
    · obtain ⟨b₀, b₁, rest, hbs01⟩ : ∃ b₀ b₁ rest, bs = b₀ :: b₁ :: rest := by
        rcases hbsx : bs with _ | ⟨b₀, _ | ⟨b₁, rest⟩⟩
        · simp [hbsx] at hlen
        · simp [hbsx] at hlen
        · exact ⟨b₀, b₁, rest, rfl⟩
      have hb₀ : b₀ ∈ bs := by rw [hbs01]; exact List.mem_cons_self
      have hb₁ : b₁ ∈ bs := by rw [hbs01]; simp
      have hne01 : baseBlockSet n N b₀ ≠ baseBlockSet n N b₁ := by
        intro h
        have hnd := flatten_nodup hbs
        rw [hbs01] at hnd
        simp only [List.flatten_cons] at hnd
        obtain ⟨γ, hγ⟩ := hnonempty b₀ hb₀
        have h1 := mem_baseBlockSet.1 hγ
        have h2 := mem_baseBlockSet.1 (h ▸ hγ)
        exact (List.disjoint_of_nodup_append hnd) h1
          (List.mem_append_left _ h2)
      have hsub : ({baseBlockSet n N b₀, baseBlockSet n N b₁} : Finset _) ⊆ blockFam n N bs := by
        intro B hB
        simp only [Finset.mem_insert, Finset.mem_singleton] at hB
        rcases hB with rfl | rfl
        · exact List.mem_toFinset.2 (List.mem_map_of_mem hb₀)
        · exact List.mem_toFinset.2 (List.mem_map_of_mem hb₁)
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hne01] at this
      exact this
    · intro B hB
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hB)
      rw [hcardB b hb]
      exact h2b

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_baseBlocksProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (baseBlocksProg n₁ G₁) (baseBlocksProg n₂ G₂) := by
  unfold baseBlocksProg
  refine .bind (.prim _ (.cons hG .nil)) fun N₁ N₂ =>
    .bind (.prim _ (.cons (by simp [hG]) .nil)) fun gd₁ gd₂ =>
    .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun gs₁ gs₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun m₁ m₂ =>
    .bind (by unfold rangeFromProg mapList; prog_wf) fun p₁ p₂ =>
    wf_maxBlocksProg (by simp) (by simp) (List.Mem.head _)

end Wf

end GraphIso.Toolkit
