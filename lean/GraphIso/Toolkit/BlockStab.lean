module

public import GraphIso.Toolkit.Reduce
public import GraphIso.Toolkit.BaseBlocks
public import GraphIso.Reductions.BlockKernelProg

/-!
# The setwise stabilizer of a block, with coset representatives

The reduction of macro-step M2b (`PLAN-14.md` §6 item 6). For a block list `bs` of base
positions that the group `G = ⟨gs⟩` permutes and a block index `t`:

1. extend the generators by the induced action on the `k = |bs|` block points (`extendProg`,
   as in `blockKernelProg`), and generate the extended group at degree `N + k`;
2. the backend's `stabilizer` and `orbitTransversal` of the block point `N + t` in it;
3. truncate the stabilizer's generators to degree `N` and generate: this is the preimage of the
   setwise stabilizer of block `t` (`denote_truncTo_le`, `comap_pointStab_extend`);
4. truncate the transversal's elements: they cover `G` by cosets of the stabilizer, and there
   are at most `k` of them (one per block in the orbit of `t`).

`RunsWithin.blockStabProg` is the spec. Its denotation is stage 14a's
`blockStab (baseHom G n hG) B` for `B` the block as a set of base points (`baseBlockSet`).
-/

@[expose] public section

namespace GraphIso.Toolkit

open Equiv Cost GraphIso.Programs Pointwise

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The setwise stabilizer of block `t` of `bs`, with coset representatives. -/
def blockStabProg (N : var .nat) (gs : var Ty.gens) (bs : var (.list (.list .nat)))
    (t : var .nat) : Prog (groupSig D) rec var (.prod (Ty.group D) (.list Ty.perm)) :=
  .bind (blockIdxProg N bs) fun bidx => .bind (blockRepsProg bs) fun reps =>
  .bind (.op1 .length bs) fun k => .bind (.op2 .add N k) fun Nk =>
  .bind (mapList gs fun g => extendProg N bidx reps g) fun egs =>
  .bind (.op2 .pair Nk egs) fun a₁ =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a₁) fun Ge =>
  .bind (.op2 .add N t) fun bt =>
  .bind (.op2 .pair Ge bt) fun a₂ =>
  .bind (Prog.call (S := groupSig D) GroupOp.stabilizer a₂) fun Se =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbitTransversal a₂) fun tr =>
  .bind (.op1 .snd Se) fun sd => .bind (.op1 .fst sd) fun ses =>
  .bind (mapList ses fun l => truncProg N l) fun st =>
  .bind (.op2 .pair N st) fun a₃ =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a₃) fun H =>
  .bind (mapList tr fun vr => .bind (.op1 .snd vr) fun r => truncProg N r) fun rs =>
  .op2 .pair H rs

end Programs

section Truncation

variable {N : ℕ} {w : WinData} {bs : List (List ℕ)} {G : Subgroup (Perm (Fin N))}
  (hw : w.Valid N) (hbs : IsBlockList w bs) (hGb : PermutesBlocks G bs)

include hw hbs hGb in
/-- A valid element of the extended group truncates to the element it extends. -/
theorem truncTo_of_mem_extend {l : PermData} (hl : PermData.Valid (N + bs.length) l)
    (hmem : PermData.denote (N + bs.length) l ∈ (extendHom hw hbs hGb).range) :
    ∃ g : G, extendHom hw hbs hGb g = PermData.denote (N + bs.length) l ∧
      PermData.Valid N (PermData.truncTo N l) ∧
      PermData.denote N (PermData.truncTo N l) = g := by
  obtain ⟨g, hg⟩ := hmem
  refine ⟨g, hg, ?_, ?_⟩
  · rw [PermData.eq_ofPerm_denote hl, ← hg, truncTo_extendHom]
    exact PermData.valid_ofPerm _
  · rw [PermData.eq_ofPerm_denote hl, ← hg, truncTo_extendHom, PermData.denote_ofPerm]

include hw hbs hGb in
/-- **Truncating generators of a subgroup of the extended group** gives generators of its
preimage under the extension. -/
theorem denote_truncTo_le {ks : GensData} (hks : GensData.AllValid (N + bs.length) ks)
    (hle : GensData.denote (N + bs.length) ks ≤ (extendHom hw hbs hGb).range) :
    GensData.AllValid N (ks.map (PermData.truncTo N)) ∧
      GensData.denote N (ks.map (PermData.truncTo N)) =
        ((GensData.denote (N + bs.length) ks).comap (extendHom hw hbs hGb)).map G.subtype := by
  have hgen : ∀ l ∈ ks, ∃ g : G, extendHom hw hbs hGb g = PermData.denote _ l ∧
      PermData.Valid N (PermData.truncTo N l) ∧ PermData.denote N (PermData.truncTo N l) = g :=
    fun l hl => truncTo_of_mem_extend hw hbs hGb (hks l hl)
      (hle (GensData.mem_denote_of_mem hl))
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
    have key : ∀ x (hx : x ∈ GensData.denote (N + bs.length) ks), ∃ y : G,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        extendHom hw hbs hGb y = x := by
      intro x hx
      refine Subgroup.closure_induction (p := fun x _ => ∃ y : G,
        (y : Perm (Fin N)) ∈ GensData.denote N (ks.map (PermData.truncTo N)) ∧
        extendHom hw hbs hGb y = x) ?_ ?_ ?_ ?_ hx
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
    have := extendHom_injective hw hbs hGb hyE
    rw [this] at hy
    exact hy

include hw hbs hGb in
/-- An extension fixes the block point `N + t` exactly when it maps block `t` to itself. -/
theorem extend_fix_iff (g : G) {t : ℕ} (ht : t < bs.length) :
    extendHom hw hbs hGb g ⟨N + t, by omega⟩ = ⟨N + t, by omega⟩ ↔
      blockMap N bs g t = t := by
  rw [Fin.ext_iff, extendHom_ge hw hbs hGb g (show N ≤ N + t by omega)]
  simp

end Truncation

/-- Mapping block `t` to itself is the base action fixing the block as a set of base points. -/
theorem blockMap_eq_self_iff {n N : ℕ} {w : WinData} {bs : List (List ℕ)}
    {G : Subgroup (Perm (Fin N))} (hG : IsInvariant G (baseSet n N)) (hw : w.Valid N)
    (hwb : ∀ i ∈ w.1, n ≤ i) (hbs : IsBlockList w bs) (hGb : PermutesBlocks G bs) (g : G)
    {t : ℕ} (ht : t < bs.length) :
    blockMap N bs g t = t ↔
      baseHom G n hG g • baseBlockSet n N bs[t] = baseBlockSet n N bs[t] := by
  obtain ⟨ht', himg⟩ := blockMap_spec hw hbs hGb g.2 ht
  -- the base action on a point of a block
  have hval : ∀ a : Fin (N - n), n + (baseHom G n hG g a).val = ((g : Perm (Fin N))
      ⟨n + a.val, by omega⟩).val := by
    intro a
    have := congrArg Fin.val (baseHom_apply (hG := hG) g a)
    simpa [basePos] using this
  constructor
  · intro h
    refine smul_finset_eq_of_mapsTo fun a ha => ?_
    rw [mem_baseBlockSet] at ha ⊢
    rw [hval]
    have key : ∀ j (hj : j < bs.length), j = t →
        ((g : Perm (Fin N)) ⟨n + a.val, by omega⟩).val ∈ bs[j] →
        ((g : Perm (Fin N)) ⟨n + a.val, by omega⟩).val ∈ bs[t] := by
      rintro j hj rfl hmem
      exact hmem
    exact key _ ht' h (himg ⟨n + a.val, by omega⟩ ha)
  · intro h
    have hu0 := blockReps_mem hbs ht
    have hu0w := mem_of_block hbs ht hu0
    have hn0 := hwb _ hu0w
    have hlt0 := hw.lt _ hu0w
    set u0 := (blockReps bs).getD t 0 with hu0_def
    have ha : (⟨u0 - n, by omega⟩ : Fin (N - n)) ∈ baseBlockSet n N bs[t] := by
      rw [mem_baseBlockSet]
      simpa [show n + (u0 - n) = u0 by omega] using hu0
    have hb : baseHom G n hG g ⟨u0 - n, by omega⟩ ∈ baseBlockSet n N bs[t] := by
      rw [← h]
      exact Finset.smul_mem_smul_finset ha
    rw [mem_baseBlockSet, hval] at hb
    have he : (⟨n + (u0 - n), by omega⟩ : Fin N) = ⟨u0, hlt0⟩ := Fin.ext (by simp; omega)
    rw [he] at hb
    have := himg ⟨u0, hlt0⟩ hu0
    exact (block_unique hw hbs ht' ht this hb)

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The stabilizer of the block point in the extended group, as computed by the backend. -/
def bsStab (O : Oracle (groupSig D)) (N : ℕ) (bs : List (List ℕ)) (gs : GensData) (t : ℕ) :
    GroupData D.denote :=
  O.run GroupOp.stabilizer (extGroup O N bs gs, N + t)

/-- The orbit transversal of the block point in the extended group. -/
def bsTrans (O : Oracle (groupSig D)) (N : ℕ) (bs : List (List ℕ)) (gs : GensData) (t : ℕ) :
    List (ℕ × PermData) :=
  O.run GroupOp.orbitTransversal (extGroup O N bs gs, N + t)

/-- The setwise stabilizer of block `t` and its coset representatives, as computed. -/
def blockStabModel (O : Oracle (groupSig D)) (N : ℕ) (bs : List (List ℕ)) (gs : GensData)
    (t : ℕ) : GroupData D.denote × List PermData :=
  (O.run GroupOp.generate (N, (bsStab O N bs gs t).2.1.map (PermData.truncTo N)),
    (bsTrans O N bs gs t).map fun vr => PermData.truncTo N vr.2)

/-- The operations used by `blockStabProg`. -/
def blockStabOps (op : GroupOp) : Prop :=
  op = .generate ∨ op = .stabilizer ∨ op = .orbitTransversal

/-- The cost of `blockStabProg`: degree `N`, `m` points in `k` blocks, `s` generators, `sS`
stabilizer generators, `L` transversal pairs, and the four backend charges. -/
def blockStabCost (N m k s sS L Bge Bst Btr Bgt : ℕ) : ℕ :=
  2 * N + 6 * m + 15 * k + s * (6 * N + 14 * k + 16) + sS * (11 * N + 13) +
    L * (11 * N + 14) + Bge + Bst + Btr + Bgt + 30

/-- **The setwise stabilizer of a block, with coset representatives.** For a block list `bs`
of base positions (the blocks of the window `w`) permuted by `G = ⟨gs⟩` and `t < |bs|`, the
result is the preimage of the setwise stabilizer of block `t` under the base action, given by
generators, together with at most `|bs|` coset representatives covering `G`. -/
theorem RunsWithin.blockStabProg (hO : MeetsContractOn DV blockStabOps X.O)
    (hPre : ∀ op x, blockStabOps op → GroupPre DV op x → X.Pre op x)
    {n N : ℕ} {w : WinData} {bs : List (List ℕ)} {gs : GensData} {t : ℕ}
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N)) (hw : w.Valid N)
    (hwb : ∀ i ∈ w.1, n ≤ i) (hbs : IsBlockList w bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hgs : GensData.AllValid N gs)
    (ht : t < bs.length) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + bs.length, extendGens N bs gs)
      (extGroup X.O N bs gs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (extGroup X.O N bs gs, N + t)
      (bsStab X.O N bs gs t) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (extGroup X.O N bs gs, N + t)
      (bsTrans X.O N bs gs t) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (bsStab X.O N bs gs t).2.1.map (PermData.truncTo N))
      (blockStabModel X.O N bs gs t).1 ≤ Bgt) :
    RunsWithin X body (Toolkit.blockStabProg N gs bs t) (blockStabModel X.O N bs gs t)
        (blockStabCost N bs.flatten.length bs.length gs.length
          (bsStab X.O N bs gs t).2.1.length (bsTrans X.O N bs gs t).length Bge Bst Btr Bgt) ∧
      (blockStabModel X.O N bs gs t).1.1 = N ∧
      GroupValid DV N (blockStabModel X.O N bs gs t).1.2.1
        (blockStabModel X.O N bs gs t).1.2.2 ∧
      GensData.denote N (blockStabModel X.O N bs gs t).1.2.1 =
        (Recursion.blockStab (baseHom (GensData.denote N gs) n hG)
          (baseBlockSet n N bs[t])).map (GensData.denote N gs).subtype ∧
      (∀ r ∈ (blockStabModel X.O N bs gs t).2, PermData.Valid N r) ∧
      IsLeftCover (GensData.denote N gs) (GensData.denote N (blockStabModel X.O N bs gs t).1.2.1)
        (fun i : Fin (blockStabModel X.O N bs gs t).2.length =>
          PermData.denote N ((blockStabModel X.O N bs gs t).2.get i)) ∧
      (blockStabModel X.O N bs gs t).2.length ≤ bs.length := by
  set G0 := GensData.denote N gs with hG0
  have hk : N + t < N + bs.length := by omega
  -- the extended group
  have hegv := GensData.allValid_extendTo hw hbs hGb hgs
  have hegden := GensData.denote_extendTo hw hbs hGb hgs
  have hgpost := hO .generate (N + bs.length, extendGens N bs gs) (Or.inl rfl) hegv
  rcases hGe' : X.O.run GroupOp.generate (N + bs.length, extendGens N bs gs) with
    ⟨N₁, egs, d₁⟩
  have hGe : extGroup X.O N bs gs = (N₁, egs, d₁) := hGe'
  rw [hGe'] at hgpost
  obtain ⟨hN₁, hGev, hGeden⟩ := hgpost
  change N₁ = N + bs.length at hN₁
  subst N₁
  have hE : GensData.denote (N + bs.length) egs = (extendHom hw hbs hGb).range := by
    change GensData.denote _ egs = GensData.denote _ (extendGens N bs gs) at hGeden
    rw [hGeden]
    exact hegden
  -- the stabilizer of the block point
  have hpreS : GroupPre DV .stabilizer ((N + bs.length, egs, d₁), N + t) := ⟨hGev, hk⟩
  have hSpost := hO .stabilizer _ (Or.inr (Or.inl rfl)) hpreS
  rcases hS : X.O.run GroupOp.stabilizer ((N + bs.length, egs, d₁), N + t) with
    ⟨N₂, ses, e₂⟩
  have hSm : bsStab X.O N bs gs t = (N₂, ses, e₂) := by
    rw [bsStab, hGe]
    exact hS
  rw [hS] at hSpost
  obtain ⟨hN₂, hSv, hSden⟩ := hSpost
  change N₂ = N + bs.length at hN₂
  subst N₂
  have hSden' : GensData.denote _ ses = pointStab (GensData.denote _ egs) ⟨N + t, hk⟩ :=
    hSden hk
  -- the transversal of the block point
  have hpreT : GroupPre DV .orbitTransversal ((N + bs.length, egs, d₁), N + t) := ⟨hGev, hk⟩
  have hTpost := hO .orbitTransversal _ (Or.inr (Or.inr rfl)) hpreT
  obtain ⟨tr, htr_def⟩ : ∃ tr : List (ℕ × PermData),
      X.O.run GroupOp.orbitTransversal ((N + bs.length, egs, d₁), N + t) = tr := ⟨_, rfl⟩
  have hTm : bsTrans X.O N bs gs t = tr := by
    rw [bsTrans, hGe]
    exact htr_def
  rw [htr_def] at hTpost
  obtain ⟨hnd, hfst, htr⟩ := hTpost
  -- the truncated stabilizer generators
  have hle : GensData.denote (N + bs.length) ses ≤ (extendHom hw hbs hGb).range := by
    rw [hSden', ← hE]
    exact inf_le_left
  obtain ⟨htv, htden⟩ := denote_truncTo_le hw hbs hGb hSv.1 hle
  have hfpost := hO .generate (N, ses.map (PermData.truncTo N)) (Or.inl rfl) htv
  rcases hH : X.O.run GroupOp.generate (N, ses.map (PermData.truncTo N)) with ⟨N₃, hs, e₃⟩
  rw [hH] at hfpost
  obtain ⟨hN₃, hHv, hHden⟩ := hfpost
  change N₃ = N at hN₃
  subst N₃
  have hmodel : blockStabModel X.O N bs gs t =
      ((N, hs, e₃), tr.map fun vr => PermData.truncTo N vr.2) := by
    rw [blockStabModel, hSm, hTm]
    exact congrArg (fun z => (z, tr.map fun vr => PermData.truncTo N vr.2)) hH
  -- the denotation of the stabilizer
  have hHden' : GensData.denote N hs =
      ((pointStab (extendHom hw hbs hGb).range ⟨N + t, hk⟩).comap
        (extendHom hw hbs hGb)).map G0.subtype := by
    change GensData.denote N hs = GensData.denote N (ses.map (PermData.truncTo N)) at hHden
    rw [hHden, htden, hSden', hE]
  have hcomap : (pointStab (extendHom hw hbs hGb).range ⟨N + t, hk⟩).comap
      (extendHom hw hbs hGb) =
        Recursion.blockStab (baseHom G0 n hG) (baseBlockSet n N bs[t]) := by
    ext g
    rw [Subgroup.mem_comap, mem_pointStab, Recursion.blockStab, Subgroup.mem_comap,
      MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨-, hfix⟩
      exact (blockMap_eq_self_iff hG hw hwb hbs hGb g ht).1
        ((extend_fix_iff hw hbs hGb g ht).1 hfix)
    · intro h
      exact ⟨⟨g, rfl⟩, (extend_fix_iff hw hbs hGb g ht).2
        ((blockMap_eq_self_iff hG hw hwb hbs hGb g ht).2 h)⟩
  -- the representatives
  have hrep : ∀ vr ∈ tr, ∃ g : G0,
      extendHom hw hbs hGb g = PermData.denote (N + bs.length) vr.2 ∧
        PermData.Valid N (PermData.truncTo N vr.2) ∧
        PermData.denote N (PermData.truncTo N vr.2) = g := by
    intro vr hvr
    obtain ⟨hvv, hvE, -⟩ := htr vr hvr
    exact truncTo_of_mem_extend hw hbs hGb hvv (hE ▸ hvE)
  have hcard : tr.length ≤ bs.length := by
    have hsub : (tr.map Prod.fst).toFinset ⊆ Finset.Ico N (N + bs.length) := by
      intro j hj
      rw [List.mem_toFinset] at hj
      have hso := (hfst j).1 hj
      obtain ⟨hi', hj', p, hp, hpu⟩ := hso
      have hp' : p ∈ (extendHom hw hbs hGb).range := hE ▸ hp
      obtain ⟨g, hgp⟩ := hp'
      have hv := congrArg Fin.val hpu
      rw [← hgp, extendHom_ge hw hbs hGb g (show N ≤ N + t by omega)] at hv
      exact Finset.mem_Ico.2 ⟨by simp at hv; omega, hj'⟩
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, Nat.card_Ico, List.length_map] at this
    omega
  rw [hmodel]
  refine ⟨?_, rfl, hHv, ?_, ?_, ?_, ?_⟩
  · -- the run and its cost
    have hlr : (blockReps bs).length = bs.length := by simp [blockReps]
    have hmapE := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.perm)
      (xs := gs) (c := 6 * N + 14 * (blockReps bs).length + 13)
      (F := PermData.extendTo N (blockIdx N bs) (blockReps bs))
      (f := fun g => Programs.extendProg N (blockIdx N bs) (blockReps bs) g) fun g hg =>
        RunsWithin.extendProg _ _ (hgs g hg).size_fwd (hgs g hg).size_inv
    have hmapT := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.perm)
      (xs := ses) (c := 11 * N + 10) (F := PermData.truncTo N)
      (f := fun l => Programs.truncProg N l) fun l _ => RunsWithin.truncProg N l
    have hmapR := RunsWithin.mapList_le (X := X) (body := body) (a' := .prod .nat Ty.perm)
      (b' := Ty.perm) (xs := tr) (c := 11 * N + 11) (F := fun vr => PermData.truncTo N vr.2)
      (f := fun vr => .bind (.op1 .snd vr) fun r => Programs.truncProg N r) fun vr _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.truncProg N vr.2)
          (by simp [Prim.cost]; omega)
    have hGe2 : X.O.run GroupOp.generate
        (N + bs.length, gs.map (PermData.extendTo N (blockIdx N bs) (blockReps bs))) =
        (N + bs.length, egs, d₁) := hGe'
    have hBge2 : X.B.call GroupOp.generate
        (N + bs.length, gs.map (PermData.extendTo N (blockIdx N bs) (blockReps bs)))
        (N + bs.length, egs, d₁) ≤ Bge := by
      rw [← hGe]
      exact hBge
    have hBst2 : X.B.call GroupOp.stabilizer ((N + bs.length, egs, d₁), N + t)
        (N + bs.length, ses, e₂) ≤ Bst := by
      rw [← hSm, ← hGe]
      exact hBst
    have hBtr2 : X.B.call GroupOp.orbitTransversal ((N + bs.length, egs, d₁), N + t) tr ≤ Btr := by
      rw [← hTm, ← hGe]
      exact hBtr
    have hBgt2 : X.B.call GroupOp.generate (N, ses.map (PermData.truncTo N)) (N, hs, e₃) ≤ Bgt := by
      have := hBgt
      rw [hSm, hmodel] at this
      exact this
    have hpairS : Prim.eval (Prim.pair (a := (groupSig D).res GroupOp.generate) (b := .nat))
        (Args.cons (N + bs.length, egs, d₁) (Args.cons (N + t) Args.nil)) =
        ((N + bs.length, egs, d₁), N + t) := rfl
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.blockIdxProg N bs)
      run_step (RunsWithin.blockRepsProg bs)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hmapE
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hegv))
      simp only [Prim.eval]
      rw [hGe2]
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
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
      simp only [Prim.cost, Prim.eval, Args.head_cons, hlr]
      simp only [blockStabCost, hSm, hTm]
      have e1 : X.B.call GroupOp.generate
          (N + bs.length, List.map (PermData.extendTo N (blockIdx N bs) (blockReps bs)) gs)
          (X.O.run GroupOp.generate
            (N + bs.length, List.map (PermData.extendTo N (blockIdx N bs) (blockReps bs)) gs))
            ≤ Bge := hBge
      have e2 : X.B.call GroupOp.stabilizer ((N + bs.length, egs, d₁), N + t)
          (X.O.run GroupOp.stabilizer ((N + bs.length, egs, d₁), N + t)) ≤ Bst := by
        rw [hS]
        exact hBst2
      have e3 : X.B.call GroupOp.orbitTransversal ((N + bs.length, egs, d₁), N + t)
          (X.O.run GroupOp.orbitTransversal ((N + bs.length, egs, d₁), N + t)) ≤ Btr := by
        rw [htr_def]
        exact hBtr2
      have e4 : X.B.call GroupOp.generate (N, List.map (PermData.truncTo N) ses)
          (X.O.run GroupOp.generate (N, List.map (PermData.truncTo N) ses)) ≤ Bgt := by
        rw [hH]
        exact hBgt2
      generalize X.B.call GroupOp.generate
          (N + bs.length, List.map (PermData.extendTo N (blockIdx N bs) (blockReps bs)) gs)
          (X.O.run GroupOp.generate
            (N + bs.length, List.map (PermData.extendTo N (blockIdx N bs) (blockReps bs)) gs))
          = B₁ at e1 ⊢
      generalize X.B.call GroupOp.stabilizer ((N + bs.length, egs, d₁), N + t)
          (X.O.run GroupOp.stabilizer ((N + bs.length, egs, d₁), N + t)) = B₂ at e2 ⊢
      generalize X.B.call GroupOp.orbitTransversal ((N + bs.length, egs, d₁), N + t)
          (X.O.run GroupOp.orbitTransversal ((N + bs.length, egs, d₁), N + t)) = B₃ at e3 ⊢
      generalize X.B.call GroupOp.generate (N, List.map (PermData.truncTo N) ses)
          (X.O.run GroupOp.generate (N, List.map (PermData.truncTo N) ses)) = B₄ at e4 ⊢
      generalize List.length gs = s₀
      generalize List.length ses = s₁
      generalize tr.length = s₂
      generalize bs.length = k₀
      generalize bs.flatten.length = m₀
      clear * - e1 e2 e3 e4
      nlinarith
  · -- the denotation
    change GensData.denote N hs = _
    rw [hHden', hcomap]
  · -- valid representatives
    intro r hr
    obtain ⟨vr, hvr, rfl⟩ := List.mem_map.1 hr
    obtain ⟨_, -, hv, -⟩ := hrep vr hvr
    exact hv
  · -- the cover
    refine ⟨fun i => ?_, fun g hg => ?_⟩
    · have hx := List.get_mem (tr.map fun vr => PermData.truncTo N vr.2) i
      obtain ⟨vr, hvr, hvre⟩ := List.mem_map.1 hx
      obtain ⟨g, -, -, hgd⟩ := hrep vr hvr
      rw [← hvre, hgd]
      exact g.2
    · set v := (extendHom hw hbs hGb ⟨g, hg⟩ ⟨N + t, hk⟩).val with hv_def
      have hso : SameOrbit (GensData.denote (N + bs.length) egs) (N + t) v := by
        refine ⟨hk, (extendHom hw hbs hGb ⟨g, hg⟩ ⟨N + t, hk⟩).2,
          extendHom hw hbs hGb ⟨g, hg⟩, ?_, rfl⟩
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
      show v = get vr.2.1 (N + t)
      rw [hvu, hvr1]
  · simpa using hcard

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_blockStabProg {N₁ t₁ : var₁ .nat} {N₂ t₂ : var₂ .nat} {gs₁ : var₁ Ty.gens}
    {gs₂ : var₂ Ty.gens} {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hgs : ⟨Ty.gens, gs₁, gs₂⟩ ∈ Γ)
    (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (blockStabProg N₁ gs₁ bs₁ t₁)
      (blockStabProg N₂ gs₂ bs₂ t₂) := by
  unfold blockStabProg blockIdxProg blockRepsProg extendProg truncProg mapList
  prog_wf

end Wf

end GraphIso.Toolkit
