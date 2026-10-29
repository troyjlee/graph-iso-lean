module

public import GraphIso.SoJTree.LeafProg
public import GraphIso.SoJTree.OrbitClosure
public import GraphIso.SoJTree.OrbitStab
public import GraphIso.Reductions.RestrictionProg

/-!
# Leaf stabilizers

Stage 14d, item 6 (`PLAN-14.md` §8): the reduction of macro-step M4 to the stabilizer of a
leaf of Split-or-Johnson, by orbit–stabilizer on leaf structures.

A group `G = ⟨gs⟩` of degree `N` leaves invariant the listed points `w.1` of a configuration
(`k = |w.1|` points, `ψ : G →* Perm (Fin k)` the induced action on their indices,
`restrictHom`). A leaf `o₀ : OutD` decodes to a structure on `Fin k`.

* `leafStabProg`: restrict the generators to the listed points (`restrictPermProg`), compute the
  orbit of `o₀` with the index maps of the generators (`orbitProg` with `actOutProg` and
  `outEqProg`), then the stabilizer of index `0` with coset representatives
  (`orbitStabProg`).
* `RunsWithin.leafStabProg`: the result denotes exactly the preimage under `ψ` of the
  stabilizer of the decoded leaf, `{g ∈ G | ψ g • decodeOut k o₀ = decodeOut k o₀}`, by valid
  generators, with valid coset representatives forming an `IsLeftCover`, at most as many as
  the orbit has elements; the cost is explicit, with the backend charges as hypotheses.
* `leafOrbit_length_eq`: the orbit computed has `Nat.card` of the orbit of the decoded leaf
  under `ψ(G)` elements.
* **The M4 index bound** (`leafStab_index_le_count`, `leafStab_reps_le_count`): if `ψ(G)`
  preserves the colouring `c` and the leaf is reachable in `soj c t`, the orbit, and so the
  number of coset representatives, is at most `(soj c t).count`.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Equiv Cost GraphIso GraphIso.Programs GraphIso.SplitJohnson Pointwise

/-! ### The program -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The stabilizer of a leaf, with coset representatives.** -/
def leafStabProg (N k : var .nat) (pos : var (.array .nat)) (ps : var (.list .nat))
    (gs : var Ty.gens) (o₀ : var outTy) :
    Prog (groupSig D) rec var (.prod (Ty.group D) (.list Ty.perm)) :=
  .bind (mapList gs fun g => restrictPermProg pos ps g) fun gd =>
  .bind (orbitProg (fun σ x => actOutProg k σ x) (fun x y => outEqProg k x y) gd o₀) fun oi =>
  .bind (.op1 .fst oi) fun orb => .bind (.op1 .snd oi) fun imgs =>
  .bind (.op1 .length orb) fun r =>
  orbitStabProg N r gs imgs

end Programs

/-! ### The data model -/

section Model

/-- The orbit of the leaf `o₀` under the generators restricted to `ps`, with their index
maps. -/
def leafOrbit (k : ℕ) (pos : Array ℕ) (ps : List ℕ) (gs : GensData) (o₀ : OutD) :
    List OutD × List (List ℕ) :=
  orbitD (τ := outTy) (actOutD k) (outEqD k) k (GensData.restrictTo pos ps gs) o₀

/-- The size of the orbit. -/
def leafR (k : ℕ) (pos : Array ℕ) (ps : List ℕ) (gs : GensData) (o₀ : OutD) : ℕ :=
  (leafOrbit k pos ps gs o₀).1.length

/-- The index maps of the generators. -/
def leafImgs (k : ℕ) (pos : Array ℕ) (ps : List ℕ) (gs : GensData) (o₀ : OutD) :
    List (List ℕ) :=
  (leafOrbit k pos ps gs o₀).2

/-- The stabilizer of the leaf and its coset representatives, as computed. -/
def leafStabModel {D : Ty} (O : Oracle (groupSig D)) (N k : ℕ) (pos : Array ℕ) (ps : List ℕ)
    (gs : GensData) (o₀ : OutD) : GroupData D.denote × List PermData :=
  orbitStabModel O N (leafR k pos ps gs o₀) gs (leafImgs k pos ps gs o₀)

/-- The cost of `leafStabProg`: degree `N`, `k` points, leaves of size at most `s`, `g`
generators, an orbit of `r` leaves, `sS` stabilizer generators, `L` transversal pairs, and the
four backend charges. -/
def leafStabCost (N k s g r sS L Bge Bst Btr Bgt : ℕ) : ℕ :=
  g * (12 * k + 12) + orbitCost r g (actOutCost k s) (outEqCost k s) +
    orbitStabCost N r g g sS L Bge Bst Btr Bgt + r + 5

end Model

/-! ### The index action through `ψ` -/

section IdxAct

/-- The index action of a duplicate-free list of length `r`, closed under a group acting
through `ψ`. -/
theorem ls_exists_rho {H : Type*} [Group H] {k : ℕ} {O : Type*} [MulAction (Perm (Fin k)) O]
    [Inhabited O] (ψ : H →* Perm (Fin k)) {r : ℕ} (L : List O) (hlen : L.length = r)
    (hL : L.Nodup) (hcl : ∀ h, ∀ x ∈ L, ψ h • x ∈ L) :
    ∃ ρ : H →* Perm (Fin r), ∀ h (j : ℕ) (hj : j < r),
      L.getD (ρ h ⟨j, hj⟩).val default = ψ h • L.getD j default := by
  subst hlen
  let _ : MulAction H O := MulAction.compHom O ψ
  obtain ⟨ρ, hρ⟩ := exists_idxActHom (H := H) L hL hcl
  refine ⟨ρ, fun h j hj => ?_⟩
  have := hρ h ⟨j, hj⟩
  rw [List.getD_eq_getElem _ _ (ρ h ⟨j, hj⟩).2, List.getD_eq_getElem _ _ hj]
  exact this

end IdxAct

/-! ### Specifications -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
  {N : ℕ} {w : WinData} {gs : GensData}

theorem ls_getD_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) {l : List α} {j : ℕ}
    (hj : j < l.length) : (l.map f).getD j default = f (l.getD j default) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj,
    List.getElem_map]

/-- The data hypotheses of the orbit closure on leaves. -/
theorem ls_orbitHyp (hgd : GensData.AllValid w.1.length
      (GensData.restrictTo (WinData.pos N w) w.1 gs)) (s : ℕ) :
    OrbitHyp (τ := outTy) (actOutD w.1.length) (outEqD w.1.length) w.1.length
      (decodeOut w.1.length) (fun x => outSize x ≤ s)
      (GensData.restrictTo (WinData.pos N w) w.1 gs) where
  dec_act σ hσ x _ := decodeOut_actOutD (hgd σ hσ) x
  J_act σ _ x hx := (outSize_actOutD_le _ σ x).trans hx
  eqb_iff x y _ _ := outEqD_iff _ x y

/-- **The orbit computed has the orbit's cardinality.** -/
theorem leafOrbit_length_eq (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) (o₀ : OutD) :
    leafR w.1.length (WinData.pos N w) w.1 gs o₀ =
      Nat.card (MulAction.orbit (restrictHom hW (WinData.reindex hw)).range
        (decodeOut w.1.length o₀)) := by
  have hgd := GensData.allValid_restrictTo hW hw hgs
  have h := orbitD_length_eq (ls_orbitHyp hgd (outSize o₀)) (x₀ := o₀) le_rfl
  rw [GensData.denote_restrictTo hW hw hgs] at h
  exact h

/-- The facts about the computed orbit used below. -/
theorem ls_orbit_facts (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) (o₀ : OutD) :
    0 < leafR w.1.length (WinData.pos N w) w.1 gs o₀ ∧
    (∀ i < gs.length, ((leafImgs w.1.length (WinData.pos N w) w.1 gs o₀).getD i []).length ≤
      leafR w.1.length (WinData.pos N w) w.1 gs o₀) ∧
    ∃ ρ : GensData.denote N gs →* Perm (Fin (leafR w.1.length (WinData.pos N w) w.1 gs o₀)),
      IsIdxMaps ρ (leafImgs w.1.length (WinData.pos N w) w.1 gs o₀) ∧
      ∀ hr : 0 < leafR w.1.length (WinData.pos N w) w.1 gs o₀,
        (MulAction.stabilizer (Perm (Fin (leafR w.1.length (WinData.pos N w) w.1 gs o₀)))
          (⟨0, hr⟩ : Fin _)).comap ρ =
        (MulAction.stabilizer (Perm (Fin w.1.length)) (decodeOut w.1.length o₀)).comap
          (restrictHom hW (WinData.reindex hw)) := by
  classical
  have hgd := GensData.allValid_restrictTo hW hw hgs
  have hden := GensData.denote_restrictTo hW hw hgs
  have hspec := orbitD_spec (ls_orbitHyp hgd (outSize o₀)) (x₀ := o₀) le_rfl
  unfold leafR leafImgs leafOrbit
  generalize orbitD (τ := outTy) (actOutD w.1.length) (outEqD w.1.length) w.1.length
    (GensData.restrictTo (WinData.pos N w) w.1 gs) o₀ = OD at hspec ⊢
  obtain ⟨orb, imgs⟩ := OD
  simp only at hspec ⊢
  rw [hden] at hspec
  obtain ⟨h0, hnd, hiff, -, -, hilen⟩ := hspec
  set ψ := restrictHom hW (WinData.reindex hw) with hψ
  set dec := decodeOut w.1.length with hdec_def
  have hr : 0 < orb.length := by
    rcases orb with _ | ⟨x, l⟩
    · simp at h0
    · simp
  have hglen : (GensData.restrictTo (WinData.pos N w) w.1 gs).length = gs.length := by
    simp [GensData.restrictTo]
  have hcl : ∀ g : GensData.denote N gs, ∀ x ∈ orb.map dec, ψ g • x ∈ orb.map dec := by
    intro g x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    have hzo : dec z ∈ MulAction.orbit ψ.range (dec o₀) := (hiff _).1 ⟨z, hz, rfl⟩
    have hgz : ψ g • dec z ∈ MulAction.orbit ψ.range (dec o₀) :=
      MulAction.mem_orbit_of_mem_orbit (⟨ψ g, g, rfl⟩ : ψ.range) hzo
    obtain ⟨z', hz', he⟩ := (hiff _).2 hgz
    exact List.mem_map.2 ⟨z', hz', he⟩
  obtain ⟨ρ, hρ⟩ := ls_exists_rho ψ (orb.map dec) (List.length_map _) hnd hcl
  have hρ' : ∀ g (j : ℕ) (hj : j < orb.length),
      dec (orb.getD (ρ g ⟨j, hj⟩).val default) = ψ g • dec (orb.getD j default) := by
    intro g j hj
    have := hρ g j hj
    rwa [ls_getD_map _ (ρ g ⟨j, hj⟩).2, ls_getD_map _ hj] at this
  have hinj : ∀ i j, i < orb.length → j < orb.length →
      dec (orb.getD i default) = dec (orb.getD j default) → i = j := by
    intro i j hi hj he
    rw [← ls_getD_map dec hi, ← ls_getD_map dec hj, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getD_eq_getElem _ _ (by simpa using hj)] at he
    exact (hnd.getElem_inj_iff).1 he
  have h00 : orb.getD 0 default = o₀ := by
    rw [List.getD_eq_getElem?_getD, h0]
    rfl
  refine ⟨hr, fun i hi => ((hilen i (by rwa [hglen])).1).le, ρ, ?_, fun hr' => ?_⟩
  · intro i hi j hj
    obtain ⟨hlt, hdecj⟩ := (hilen i (by rwa [hglen])).2 j hj
    have hgi : (GensData.restrictTo (WinData.pos N w) w.1 gs).getD i default =
        PermData.restrictTo (WinData.pos N w) w.1 gs[i] := by
      rw [List.getD_eq_getElem _ _ (by rwa [hglen])]
      simp [GensData.restrictTo]
    rw [hgi, PermData.denote_restrictTo hW hw (hgs _ (List.getElem_mem hi)) (os_mem_gens hi)]
      at hdecj
    exact hinj _ _ hlt (ρ _ ⟨j, hj⟩).2 (hdecj.trans (hρ' _ j hj).symm)
  · ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Perm.smul_def]
    have h := hρ' g 0 hr'
    rw [h00] at h
    constructor
    · intro he
      rw [he] at h
      simp only at h
      rw [h00] at h
      exact h.symm
    · intro he
      rw [he, ← h00] at h
      exact Fin.ext (hinj _ _ (ρ g ⟨0, hr'⟩).2 hr' h)

/-- **The stabilizer of a leaf, with coset representatives.** For valid generators `gs` of `G`
at degree `N`, leaving the listed points `w.1` invariant (`ψ` the induced action on their
indices), and a leaf `o₀`, write `r` and `imgs` for the size of the computed orbit and the
index maps (`leafR`, `leafImgs`; `r` is the orbit's cardinality, `leafOrbit_length_eq`). The
program returns `leafStabModel` at cost `leafStabCost`, given the four backend charges. The
group has degree `N`, is valid, and denotes exactly `{g ∈ G | ψ g • decodeOut k o₀ =
decodeOut k o₀}`; the representatives are valid, form an `IsLeftCover` of `G` by it, and number
at most `r`. -/
theorem RunsWithin.leafStabProg (hO : MeetsContractOn DV orbitStabOps X.O)
    (hPre : ∀ op x, orbitStabOps op → GroupPre DV op x → X.Pre op x)
    (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) (o₀ : OutD) {r : ℕ}
    {imgs : List (List ℕ)} (hr : leafR w.1.length (WinData.pos N w) w.1 gs o₀ = r)
    (himgs : leafImgs w.1.length (WinData.pos N w) w.1 gs o₀ = imgs) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
      (osGroup X.O N r gs imgs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (osGroup X.O N r gs imgs, N)
      (osStab X.O N r gs imgs) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (osGroup X.O N r gs imgs, N)
      (osTrans X.O N r gs imgs) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (osStab X.O N r gs imgs).2.1.map (PermData.truncTo N))
      (orbitStabModel X.O N r gs imgs).1 ≤ Bgt) :
    RunsWithin X body
        (SoJTree.leafStabProg N w.1.length (WinData.pos N w) w.1 gs o₀)
        (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀)
        (leafStabCost N w.1.length (outSize o₀) gs.length r
          (osStab X.O N r gs imgs).2.1.length (osTrans X.O N r gs imgs).length
          Bge Bst Btr Bgt) ∧
      (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).1.1 = N ∧
      GroupValid DV N (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).1.2.1
        (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).1.2.2 ∧
      GensData.denote N (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).1.2.1 =
        ((MulAction.stabilizer (Perm (Fin w.1.length)) (decodeOut w.1.length o₀)).comap
          (restrictHom hW (WinData.reindex hw))).map (GensData.denote N gs).subtype ∧
      (∀ x ∈ (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).2,
        PermData.Valid N x) ∧
      IsLeftCover (GensData.denote N gs)
        (GensData.denote N (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).1.2.1)
        (fun i : Fin (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).2.length =>
          PermData.denote N
            ((leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).2.get i)) ∧
      (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).2.length ≤ r := by
  subst hr himgs
  obtain ⟨hpos, hilen, ρ, himg, hstab⟩ := ls_orbit_facts hgs hw hW o₀
  obtain ⟨hrun, hN, hval, hden, hrv, hcov, hlen⟩ :=
    RunsWithin.orbitStabProg (body := body) hO hPre hgs hpos ρ himg hilen hBge hBst hBtr hBgt
  have hgd := GensData.allValid_restrictTo hW hw hgs
  have horb := RunsWithin.orbitProg (X := X) (body := body)
    (ls_orbitHyp hgd (outSize o₀))
    (actP := fun σ x => SoJTree.actOutProg w.1.length σ x)
    (eqP := fun x y => SoJTree.outEqProg w.1.length x y)
    (fun σ _ x hx => RunsWithin.actOutProg _ σ x hx)
    (fun x y hx hy => RunsWithin.outEqProg _ x y hx hy) (x₀ := o₀) le_rfl
  refine ⟨?_, hN, hval, ?_, hrv, hcov, hlen⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.mapList_le (c := 12 * w.1.length + 9) fun g _ =>
        RunsWithin.restrictPermProg (WinData.pos N w) w.1 g)
      run_step horb
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact hrun
    case hc =>
      have e3 := (orbitD_spec (ls_orbitHyp hgd (outSize o₀)) (x₀ := o₀) le_rfl).2.2.2.2.1
      simp only [GensData.restrictTo, List.length_map] at e3
      have e4 : 12 * w.1.length + 9 + 3 = 12 * w.1.length + 12 := by omega
      simp only [Prim.cost, Prim.eval, Args.head, leafStabCost, leafR, leafImgs, leafOrbit,
        GensData.restrictTo, List.length_map, e3, e4]
      omega
  · refine hden.trans ?_
    rw [hstab hpos]

/-- **The M4 index bound.** If `ψ(G)` preserves the colouring `c` of `Fin k` and the decoded
leaf is reachable in `soj c t`, its orbit, computed by `leafStabProg`, has at most
`(soj c t).count` elements. -/
theorem leafStab_index_le_count (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) (o₀ : OutD)
    {c : Fin w.1.length → Fin w.1.length → ℕ} {t : ℕ}
    (hc : ∀ g, relab2 (restrictHom hW (WinData.reindex hw) g) c = c)
    (hreach : (soj c t).Reach (decodeOut w.1.length o₀)) :
    leafR w.1.length (WinData.pos N w) w.1 gs o₀ ≤ (soj c t).count := by
  rw [leafOrbit_length_eq hgs hw hW o₀]
  exact card_orbit_le_count (fun σ hσ => by obtain ⟨g, rfl⟩ := hσ; exact hc g) hreach

/-- **The number of coset representatives of the leaf stabilizer** is at most the count of
`soj c t`, under the hypotheses of `RunsWithin.leafStabProg` and `leafStab_index_le_count`. -/
theorem leafStab_reps_le_count (hO : MeetsContractOn DV orbitStabOps X.O)
    (hPre : ∀ op x, orbitStabOps op → GroupPre DV op x → X.Pre op x)
    (hgs : GensData.AllValid N gs) (hw : w.Valid N)
    (hW : IsInvariant (GensData.denote N gs) (w.denote N)) (o₀ : OutD) {r : ℕ}
    {imgs : List (List ℕ)} (hr : leafR w.1.length (WinData.pos N w) w.1 gs o₀ = r)
    (himgs : leafImgs w.1.length (WinData.pos N w) w.1 gs o₀ = imgs) {Bge Bst Btr Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (N + r, os_extGens N r gs imgs)
      (osGroup X.O N r gs imgs) ≤ Bge)
    (hBst : X.B.call GroupOp.stabilizer (osGroup X.O N r gs imgs, N)
      (osStab X.O N r gs imgs) ≤ Bst)
    (hBtr : X.B.call GroupOp.orbitTransversal (osGroup X.O N r gs imgs, N)
      (osTrans X.O N r gs imgs) ≤ Btr)
    (hBgt : X.B.call GroupOp.generate (N, (osStab X.O N r gs imgs).2.1.map (PermData.truncTo N))
      (orbitStabModel X.O N r gs imgs).1 ≤ Bgt)
    {c : Fin w.1.length → Fin w.1.length → ℕ} {t : ℕ}
    (hc : ∀ g, relab2 (restrictHom hW (WinData.reindex hw) g) c = c)
    (hreach : (soj c t).Reach (decodeOut w.1.length o₀)) :
    (leafStabModel X.O N w.1.length (WinData.pos N w) w.1 gs o₀).2.length ≤ (soj c t).count := by
  have h := (RunsWithin.leafStabProg (a := .unit) (b := .unit) (body := fun x => Prog.ret x) hO
    hPre hgs hw hW o₀ hr himgs hBge hBst hBtr hBgt).2.2.2.2.2.2
  rw [← hr] at h
  exact h.trans (leafStab_index_le_count hgs hw hW o₀ hc hreach)

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem ls_wf_restrictPermProg {pos₁ : var₁ (.array .nat)} {pos₂ : var₂ (.array .nat)}
    {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)} {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm}
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ)
    (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (restrictPermProg pos₁ ps₁ g₁)
      (restrictPermProg pos₂ ps₂ g₂) := by
  unfold restrictPermProg
  refine .bind (.prim _ (.cons hg .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hg]) .nil))
    fun _ _ => .bind (wf_mapList (by simp [hps]) fun Γ' hΓ u₁ u₂ hu =>
      .bind (.prim _ (.cons (hΓ (by simp)) (.cons hu .nil))) fun _ _ =>
        .prim _ (.cons (List.mem_cons_of_mem _ (hΓ (by simp [hpos]))) (.cons (by simp) .nil)))
    fun _ _ => .bind (wf_mapList (by simp [hps]) fun Γ' hΓ u₁ u₂ hu =>
      .bind (.prim _ (.cons (hΓ (by simp)) (.cons hu .nil))) fun _ _ =>
        .prim _ (.cons (List.mem_cons_of_mem _ (hΓ (by simp [hpos]))) (.cons (by simp) .nil)))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
        .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_leafStabProg {N₁ k₁ : var₁ .nat} {N₂ k₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {ps₁ : var₁ (.list .nat)} {ps₂ : var₂ (.list .nat)}
    {gs₁ : var₁ Ty.gens} {gs₂ : var₂ Ty.gens} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ)
    (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ) (hgs : ⟨Ty.gens, gs₁, gs₂⟩ ∈ Γ)
    (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (leafStabProg N₁ k₁ pos₁ ps₁ gs₁ o₁)
      (leafStabProg N₂ k₂ pos₂ ps₂ gs₂ o₂) := by
  unfold leafStabProg
  refine .bind (wf_mapList hgs fun Γ' hΓ g₁ g₂ hg =>
    ls_wf_restrictPermProg (hΓ hpos) (hΓ hps) hg) fun gd₁ gd₂ => ?_
  refine .bind (wf_orbitProg (fun Γ' hΓ x₁ x₂ y₁ y₂ hx hy =>
      wf_actOutProg (hΓ (by simp [hk])) hx hy) (fun Γ' hΓ x₁ x₂ y₁ y₂ hx hy =>
      wf_outEqProg (hΓ (by simp [hk])) hx hy) (by simp) (by simp [ho])) fun _ _ => ?_
  exact .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    wf_orbitStabProg (by simp [hN]) (by simp) (by simp [hgs]) (by simp)

end Wf

end GraphIso.SoJTree
