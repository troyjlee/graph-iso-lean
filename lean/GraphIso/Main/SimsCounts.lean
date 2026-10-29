module

public import GraphIso.Main.M4Step
public import GraphIso.Main.M5Cases

/-!
# Generator counts with the Schreier–Sims backend

Stage 14j-5b, items 1 and 2 (`PLAN-14.md` §14.7). The repaired specs of stage 14j-5a take
generator-count facts as hypotheses; here they are proved for Schreier–Sims.

* **Uniform bounds** at any generator bound `s ≥ M²` (`ssBoundsS`, `rd_ss_boundsS`): a recursion
  keeps one bound at every degree up to its largest, while `ssBounds` and `rd_ss_bounds` fix
  `s = M²`.
* **The strengthened `DOutGens`** of reduce-and-derive, for every tag `1`–`5`
  (`rd_ss_dOutGens_free`, `rd_ss_dOutGens_cj`), the obligation the scope amendment of stage
  14j-5a (`PLAN-14.md` §14.6, item 2) left to this stage. The derive specs are generic in the
  data invariant `DV`, and Schreier–Sims meets every contract for the invariant
  `ssBnd S M gs _ : |gs| ≤ max S M²` (`ssOracle_meets_bnd`), since its `generate`, `stabilizer`
  and `kernel` return at most `M²` generators at degree `M` on valid inputs. So
  `RunsWithin.deriveProg_free` and `RunsWithin.deriveProg_cj`, instantiated with `ssBnd S`, give
  a `DOutcome` whose groups satisfy `ssBnd S`: each is valid with at most `max S M²`
  generators, and the degrees are at most `N` (`dOutGens_of_dOutcome`).
  - The groups of tags `1`, `2` and `4` are re-based `generate` outputs. The validity of the
    re-based generators is what the derive specs prove to meet `generate`'s precondition: for
    tag `4` from the Johnson preservation `hK` of `rd_orbit_cj`, which `rd_ss_dOutGens_cj`
    takes unchanged.
  - The groups of tags `3` and `5` are `generate` and `stabilizer` outputs (the block
    stabilizer and its re-basing; the pointwise stabilizer of the cells' positions).
  - The charges of the instantiation are the exact charges of the specific calls; they play no
    part in the conclusion.
* `rd_orbit_free_ss`, `rd_orbit_cj_ss`: `rd_orbit_free` and `rd_orbit_cj` for Schreier–Sims, with
  the `DOutGens` part dropped from their hypothesis `hch`.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost Solver

/-- **The Schreier–Sims backend's bounds at any generator bound `s ≥ n²`** (stage 14j-5b,
`PLAN-14.md` §14.7, item 1). -/
def ssBoundsS (n s : ℕ) (G₀ : Subgroup (Perm (Fin n))) (h : n * n ≤ s) :
    BackendBounds ssCtx ssDV n s G₀ where
  Borb := orbitsCost n s n + 5
  Bstab := stabCost n s + 5
  Btr := transCost n s + 5
  Bgen := genCost n (n * (s + 1)) + 2
  orbits gs _ w hs _ hpre := by
    obtain ⟨-, hw, -⟩ := hpre
    exact Nat.add_le_add_right (orbitsCost_mono hs (WinData.length_le hw)) 5
  stabilizer _ _ _ hs _ _ := Nat.add_le_add_right (stabCost_mono hs) 5
  transversal _ _ _ hs _ _ := Nat.add_le_add_right (transCost_mono hs) 5
  generate _ _ hl _ := Nat.add_le_add_right (genCost_mono hl) 2
  stabOut _ _ _ _ hpre := (stabModel_spec hpre.1.1 hpre.2).2.2.trans h
  genOut _ hgs _ := (generateModel_spec hgs).2.2.trans h

/-- **The degree-aware data invariant** `|gs| ≤ max S M²` at degree `M`. -/
def ssBnd (S M : ℕ) (gs : GensData) (_ : Unit) : Prop := gs.length ≤ max S (M * M)

/-- **Schreier–Sims meets every contract for `ssBnd S`**: its output groups have at most `M²`
generators at degree `M`. -/
theorem ssOracle_meets_bnd (S : ℕ) : MeetsContract (ssBnd S) ssOracle := by
  rintro op x hpre
  cases op with
  | generate =>
    obtain ⟨n, gs⟩ := x
    obtain ⟨h₁, h₂, h₃⟩ := generateModel_spec (n := n) hpre
    exact ⟨rfl, ⟨h₁, h₃.trans (le_max_right _ _)⟩, h₂⟩
  | mem =>
    obtain ⟨⟨n, gs, _⟩, π⟩ := x
    obtain ⟨⟨hgs, -⟩, hπ⟩ := hpre
    exact memModel_iff hgs hπ
  | orbits =>
    obtain ⟨⟨n, gs, _⟩, w⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, hinv⟩ := hpre
    exact orbitsModel_spec hgs hw hinv
  | stabilizer =>
    obtain ⟨⟨n, gs, _⟩, u⟩ := x
    obtain ⟨⟨hgs, -⟩, hu⟩ := hpre
    obtain ⟨h₁, h₂, h₃⟩ := stabModel_spec hgs hu
    exact ⟨rfl, ⟨h₁, h₃.trans (le_max_right _ _)⟩, fun _ => h₂⟩
  | orbitTransversal =>
    obtain ⟨⟨n, gs, _⟩, u⟩ := x
    obtain ⟨⟨hgs, -⟩, hu⟩ := hpre
    exact orbitBFS_spec hu hgs
  | cosetReps =>
    obtain ⟨⟨n, gs, _⟩, ⟨n', ks, _⟩⟩ := x
    obtain ⟨⟨hgs, -⟩, ⟨hks, -⟩, hn, hK⟩ := hpre
    change n' = n at hn
    subst hn
    exact cosetRepsModel_spec hgs hks hK
  | kernel =>
    obtain ⟨⟨n, gs, _⟩, w⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -⟩ := hpre
    obtain ⟨h₁, h₂, h₃⟩ := kernelModel_spec hgs hw
    exact ⟨rfl, ⟨h₁, h₃.trans (le_max_right _ _)⟩, h₂⟩
  | lift =>
    obtain ⟨⟨n, gs, _⟩, w, π'⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -, -, r, hr, hrG, hmap⟩ := hpre
    exact liftModel_spec hgs hw hr hrG hmap

/-- The Schreier–Sims context with the preconditions of `ssBnd S`. -/
def ssCtxB (S : ℕ) : Ctx (groupSig Ty.unit) := ⟨ssOracle, ssB, GroupPre (ssBnd S)⟩

/-- The backend bounds of `ssBoundsS` in the context `ssCtxB S`. -/
def ssBoundsB (S n s : ℕ) (G₀ : Subgroup (Perm (Fin n))) (h : n * n ≤ s) :
    BackendBounds (ssCtxB S) (ssBnd S) n s G₀ where
  Borb := orbitsCost n s n + 5
  Bstab := stabCost n s + 5
  Btr := transCost n s + 5
  Bgen := genCost n (n * (s + 1)) + 2
  orbits gs _ w hs _ hpre := by
    obtain ⟨-, hw, -⟩ := hpre
    exact Nat.add_le_add_right (orbitsCost_mono hs (WinData.length_le hw)) 5
  stabilizer _ _ _ hs _ _ := Nat.add_le_add_right (stabCost_mono hs) 5
  transversal _ _ _ hs _ _ := Nat.add_le_add_right (transCost_mono hs) 5
  generate _ _ hl _ := Nat.add_le_add_right (genCost_mono hl) 2
  stabOut _ _ _ _ hpre := (stabModel_spec hpre.1.1 hpre.2).2.2.trans h
  genOut _ hgs _ := (generateModel_spec hgs).2.2.trans h

end GraphIso.Sims

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Toolkit Sims Solver

/-- **The uniform bounds of reduce-and-derive at any generator bound `sIn ≥ N²`** (stage 14j-5b,
`PLAN-14.md` §14.7, item 1), with the charges of `rd_ss_bounds` at `sIn` input generators. -/
theorem rd_ss_boundsS (n N sIn Lg : ℕ) (h : N * N ≤ sIn) :
    RDBounds ssCtx ssDV n N sIn Lg (Sims.liftCost N sIn n + 7) (genCost N Lg + 2)
      (orbitsCost N sIn N + 5) (kerCost N sIn N + 5)
      (repsCost N sIn (N * N) (N - n).factorial + 7) where
  lift M hM gs d _ hgs π' _ := by
    change Sims.liftCost M gs.length (List.range n).length + 7 ≤ _
    rw [List.length_range]
    exact Nat.add_le_add_right (rd_liftCost_mono₂ hM hgs le_rfl) 7
  gen M hM hs _ hl := by
    change genCost M hs.length + 2 ≤ _
    exact Nat.add_le_add_right (genCost_mono₂ hM hl) 2
  genOut M hM hs hv := by
    change (generateModel M hs).length ≤ sIn
    exact (generateModel_spec hv).2.2.trans ((Nat.mul_le_mul hM hM).trans h)
  orbits Hd w hN hs hpre := by
    obtain ⟨M, gs, d⟩ := Hd
    obtain ⟨-, hw, -⟩ := hpre
    change orbitsCost M gs.length w.1.length + 5 ≤ _
    exact Nat.add_le_add_right
      (rd_orbitsCost_mono₂ hN hs ((WinData.length_le hw).trans hN)) 5
  kernel gs d _ hgs := by
    change kerCost N gs.length (baseWin n N).1.length + 5 ≤ _
    exact Nat.add_le_add_right
      (kerCost_mono₂ le_rfl hgs (WinData.length_le (baseWin_valid n N))) 5
  kerGens gs d hv _ := by
    change (kernelModel N gs (baseWin n N)).length ≤ sIn
    exact (kernelModel_spec hv.1 (baseWin_valid n N)).2.2.trans h
  kerOrbits gs d w hv _ hw := by
    change orbitsCost N (kernelModel N gs (baseWin n N)).length w.1.length + 5 ≤ _
    exact Nat.add_le_add_right (rd_orbitsCost_mono₂ le_rfl
      ((kernelModel_spec hv.1 (baseWin_valid n N)).2.2.trans h) (WinData.length_le hw)) 5
  cosetReps gs d hv hgs hbase := by
    obtain ⟨-, -, -, -, -, -, -, hrlen⟩ := RunsWithin.kerProg (X := ssCtx) (DV := ssDV)
      (a := Ty.unit) (b := Ty.unit)
      (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
      (n := n) (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hv hbase le_rfl le_rfl
    have hfact : (kerReps ssCtx.O n (N, gs, d)).length ≤ (N - n).factorial := by
      rw [hrlen]
      calc Nat.card (baseHom (GensData.denote N gs) n hbase).range
          ≤ Nat.card (Perm (Fin (N - n))) := Subgroup.card_le_card_group _
        _ = (N - n).factorial := by
            rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    change repsCost N gs.length (kernelModel N gs (baseWin n N)).length
      (kerReps ssCtx.O n (N, gs, d)).length + 7 ≤ _
    exact Nat.add_le_add_right (repsCost_mono₃ hgs
      (kernelModel_spec hv.1 (baseWin_valid n N)).2.2 hfact) 7

/-! ### The strengthened `DOutGens` -/

section DOutGens

variable {n N S : ℕ} {gsG gsK : GensData} {w : WinData} {L : LabelData}

/-- **The generator counts of an outcome for `ssBnd S`**: every group of the outcome has degree
at most `N`, so at most `max S N² = S` generators. The degree of the reduction's groups (tags `3`
and `5`) is the hypothesis `hdeg` (`rd_deg_free`, `rd_deg_cj`); the child's follows from its
base bound. -/
theorem dOutGens_of_dOutcome {gs : GensData} {d : Unit} {O : List ℕ} {r : DOut Ty.unit}
    (hS : N * N ≤ S) (hn : n ≤ N) (hdeg : r.1 = 3 ∨ r.1 = 5 → r.2.1.1.1 ≤ N)
    (h : DOutcome (ssBnd S) n N w L gs d O r) : DOutGens S r := by
  have key : ∀ {M : ℕ} {gs' : GensData}, M ≤ N → gs'.length ≤ max S (M * M) →
      gs'.length ≤ S := fun hM hl =>
    hl.trans (max_le le_rfl ((Nat.mul_le_mul hM hM).trans hS))
  cases h with
  | noHint _ _ => exact ⟨fun h => by simp at h, fun h => by simp at h⟩
  | inter hc _ hm => exact ⟨fun h => by simp at h, fun _ => key (by omega) hc.valid.2⟩
  | blockLab hc _ hm =>
    exact ⟨fun h => by simp at h, fun _ => key (by omega) hc.valid.2⟩
  | blockStab _ _ hR _ _ _ _ hG' hm _ _ _ _ =>
    exact ⟨fun _ => ⟨key (hdeg (Or.inl rfl)) hR.2, key (by omega) hG'.2⟩,
      fun h => by simp at h⟩
  | johnUnion hc _ hm =>
    exact ⟨fun h => by simp at h, fun _ => key (by omega) hc.valid.2⟩
  | johnFallback _ _ _ _ _ hR _ _ _ _ _ _ _ =>
    exact ⟨fun _ => ⟨key (hdeg (Or.inr rfl)) hR.2, key (hdeg (Or.inr rfl)) hR.2⟩,
      fun h => by simp at h⟩
  | stuck r h6 =>
    exact ⟨fun h => by rcases h with h | h <;> omega, fun h => by omega⟩

/-- A setting of reduce-and-derive for `ssDV` is one for `ssBnd S`, with at most `S`
generators. -/
theorem DSetting.ssBnd {gs : GensData} {d : Unit} {O : List ℕ}
    (h : DSetting (D := Ty.unit) ssDV n N gsG w L gs d O) (hgs : gs.length ≤ S) :
    DSetting (D := Ty.unit) (ssBnd S) n N gsG w L gs d O :=
  ⟨h.hint, h.gvalid, h.win, h.inv, h.trans, h.faithful, ⟨h.kvalid.1, le_max_of_le_left hgs⟩,
    h.le, h.nodup, h.sub, h.orbit, h.ne⟩

/-- **`DOutGens` for Schreier–Sims without a coloured Johnson structure** (tags `1`, `2`, `3`;
`PLAN-14.md` §14.7, item 2). -/
theorem rd_ss_dOutGens_free {st : ℕ × CJData} (hst : st.1 ≠ 2) (hS : N * N ≤ S) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      DOutGens S (deriveModel ssOracle n N (N, gs, d) O L st) := by
  intro gs d O hset
  have hD := hset.1.ssBnd hset.2.1
  have hO : MeetsContractOn (ssBnd S) deriveOps (ssCtxB S).O :=
    fun op x _ hx => ssOracle_meets_bnd S op x hx
  obtain ⟨-, hout⟩ := RunsWithin.deriveProg_free (X := ssCtxB S) (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    hO (fun _ _ _ h => h) hD hst ⟨le_rfl, le_rfl⟩
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  exact dOutGens_of_dOutcome hS hD.hint.le (fun h => rd_deg_free hO hD hst h) hout

/-- **`DOutGens` for Schreier–Sims with a coloured Johnson structure** (tags `1`–`5`;
`PLAN-14.md` §14.7, item 2), under the structure hypotheses of `rd_orbit_cj`. The Johnson
preservation `hK` gives the validity of the generators re-based onto the cells, which
`RunsWithin.deriveProg_cj` proves for `generate`'s precondition; the output bound of
`ssBnd S` then bounds the child. -/
theorem rd_ss_dOutGens_cj {st : ℕ × CJData} (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {V : Finset (Fin (N - n))} {t : ℕ} (hJ : SplitJohnson.IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hS : N * N ≤ S) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      DOutGens S (deriveModel ssOracle n N (N, gs, d) O L st) := by
  intro gs d O hset
  have hD := hset.1.ssBnd hset.2.1
  have hle := hset.2.2
  have hO : MeetsContractOn (ssBnd S) deriveOps (ssCtxB S).O :=
    fun op x _ hx => ssOracle_meets_bnd S op x hx
  have hKH : ∀ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hD.base_inv g • cjdec (N - n) st.2 =
        cjdec (N - n) st.2 := by
    rintro ⟨π, hπ⟩
    rw [dv_baseHom_le hle hKb hD.base_inv hπ]
    exact hK ⟨π, hle hπ⟩
  obtain ⟨-, hout⟩ := RunsWithin.deriveProg_cj (X := ssCtxB S) (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    hO (fun _ _ _ h => h) hD hst hJv hJ hKH ⟨le_rfl, le_rfl⟩
    ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩ le_rfl
    le_rfl
    (ssBoundsB S (n + (cellPosD n st.2.1.2.1).length)
      (max ((n + (cellPosD n st.2.1.2.1).length) * (n + (cellPosD n st.2.1.2.1).length))
        (rebaseModel ssOracle n N (cellPosD n st.2.1.2.1) gs).2.1.length) ⊤ (le_max_left _ _))
    (le_max_right _ _) le_top
  exact dOutGens_of_dOutcome hS hD.hint.le
    (fun h => rd_deg_cj hO hD hst hJv (fun g => ((cj_smul_eq_iff' _ _ _).1 (hKH g)).1) h) hout

/-- **`rd_orbit_free` for Schreier–Sims**: the generator counts `DOutGens` are proved
(`rd_ss_dOutGens_free`), so `hch` asks only for the charges. -/
theorem rd_orbit_free_ss {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
    {st : ℕ × CJData} (hst : st.1 ≠ 2) (hS : N * N ≤ S)
    {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ Bd : ℕ}
    (hch : ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      M1Charges ssCtx n N gs d (WinData.ofPoints N O) L Borb Bgen ∧
      BlkCharges ssCtx n (m1Model ssCtx.O n N (N, gs, d) (WinData.ofPoints N O) L).1.1
        (m1Model ssCtx.O n N (N, gs, d) (WinData.ofPoints N O) L).1.2.1
        s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ ∧
      deriveFreeCost n N O.length gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt Bgen₃ +
        5 ≤ Bd) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      RDOrbit ssCtx body ssDV n N w L st S Bd gs d O :=
  rd_orbit_free (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hst
    fun gs d O hset => ⟨(hch gs d O hset).1, (hch gs d O hset).2.1, (hch gs d O hset).2.2,
      rd_ss_dOutGens_free hst hS gs d O hset⟩

/-- **`rd_orbit_cj` for Schreier–Sims**: the generator counts `DOutGens` are proved
(`rd_ss_dOutGens_cj`, from the same structure hypotheses), so `hch` asks only for the charges. -/
theorem rd_orbit_cj_ss {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
    {st : ℕ × CJData} (hst : st.1 = 2)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hJv : Align.JValid (N - n) st.2.1)
    {V : Finset (Fin (N - n))} {t : ℕ} (hJ : SplitJohnson.IsJohnson V t (Align.jdec (N - n) st.2.1))
    (hK : ∀ g : ↥(GensData.denote N gsK),
      baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) st.2 = cjdec (N - n) st.2)
    (hS : N * N ≤ S) {Borb Bgen s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ Bgen₄ uB Bd : ℕ}
    (hch : ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      M1Charges ssCtx n N gs d (WinData.ofPoints N O) (labDiffD (markArr (N - n) st.2.1.1) L O)
        Borb Bgen ∧
      BlkCharges ssCtx n (m1Model ssCtx.O n N (N, gs, d) (WinData.ofPoints N O)
          (labDiffD (markArr (N - n) st.2.1.1) L O)).1.1
        (m1Model ssCtx.O n N (N, gs, d) (WinData.ofPoints N O)
          (labDiffD (markArr (N - n) st.2.1.1) L O)).1.2.1
        s₁ Bgen₂ Bge Bst Btr Bgt sS Lt sH Bgen₃ ∧
      ssCtx.B.call GroupOp.generate (n + (cellPosD n st.2.1.2.1).length,
          rebaseGens n N (cellPosD n st.2.1.2.1) gs)
        (rebaseModel ssCtx.O n N (cellPosD n st.2.1.2.1) gs) ≤ Bgen₄ ∧
      ((labJUD st.2.1.2.1.length (markArr (N - n) st.2.1.1) st.2.1.2.2.2 L O).getD
        (O.headD 0) []).length ≤ uB ∧
      (∃ (s' : ℕ) (G₀ : Subgroup (Perm (Fin (n + (cellPosD n st.2.1.2.1).length))))
        (B : BackendBounds ssCtx ssDV (n + (cellPosD n st.2.1.2.1).length) s' G₀),
        (rebaseModel ssCtx.O n N (cellPosD n st.2.1.2.1) gs).2.1.length ≤ s' ∧
        GensData.denote (n + (cellPosD n st.2.1.2.1).length)
          (rebaseModel ssCtx.O n N (cellPosD n st.2.1.2.1) gs).2.1 ≤ G₀ ∧
        deriveCJCost n N O.length L.size gs.length Borb Bgen s₁ sS Lt sH Bgen₂ Bge Bst Btr Bgt
          Bgen₃ Bgen₄ uB B.Btr B.Bstab + 5 ≤ Bd)) :
    ∀ gs d O, RDSet ssDV n N gsG w L gsK S gs d O →
      RDOrbit ssCtx body ssDV n N w L st S Bd gs d O :=
  rd_orbit_cj (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h) hst hKb hJv hJ hK
    fun gs d O hset => ⟨(hch gs d O hset).1, (hch gs d O hset).2.1, (hch gs d O hset).2.2.1,
      (hch gs d O hset).2.2.2.1, (hch gs d O hset).2.2.2.2,
      rd_ss_dOutGens_cj hst hKb hJv hJ hK hS gs d O hset⟩

end DOutGens

/-! ### The other generator counts -/

section Counts

/-- `generate` returns at most `M²` generators at degree `M` on valid inputs. -/
theorem ss_generate_gens_le {M : ℕ} {hs : GensData} (hv : GensData.AllValid M hs) :
    (ssCtx.O.run GroupOp.generate (M, hs)).2.1.length ≤ M * M :=
  (ssOracle_gens_le hv).1

/-- **M2b's `hsR`**: groups generated below the block stabilizer, at degree `N`. -/
theorem ss_hsR (N : ℕ) (H : GensData) :
    ∀ hs : GensData, GensData.AllValid N hs → GensData.denote N hs ≤ GensData.denote N H →
      (ssCtx.O.run GroupOp.generate (N, hs)).2.1.length ≤ N * N :=
  fun _ hv _ => ss_generate_gens_le hv

/-- **Case 2a's `hgR`**, at the degrees `M ≤ K` of the restricted sub-calls. -/
theorem ss_hgR (K s : ℕ) :
    ∀ M ≤ K, ∀ hs : GensData, GensData.AllValid M hs → hs.length ≤ s →
      (ssCtx.O.run GroupOp.generate (M, hs)).2.1.length ≤ K * K :=
  fun _ hM _ hv _ => (ss_generate_gens_le hv).trans (Nat.mul_le_mul hM hM)

/-- The kernel of a valid group at degree `M` has at most `M²` generators. -/
theorem ss_kernel_gens_le {M : ℕ} {gs : GensData} {w : WinData} (hgs : GensData.AllValid M gs)
    (hw : w.Valid M) : (ssCtx.O.run GroupOp.kernel ((M, gs, ()), w)).2.1.length ≤ M * M :=
  (kernelModel_spec hgs hw).2.2

/-- **M5's `hsK`**: the kernels of the restriction for the pullback sub-calls of Case 2a. -/
theorem ss_hsK {N : ℕ} {G₀ : Subgroup (Perm (Fin N))} {xy : StrData × StrData} {wl sIn : ℕ} :
    ∀ (w' : WinData) (σ' : PermData) (gs' : GensData) (d' : Ty.unit.denote),
      Giant.PbSubP ssDV G₀ xy wl sIn (xy, w', σ', N, gs', d') →
      (ssCtx.O.run GroupOp.kernel ((N, gs', d'), w')).2.1.length ≤ N * N := by
  rintro w' σ' gs' d' ⟨-, hv, -⟩
  exact ss_kernel_gens_le hv.group.1 hv.win

/-- **M5's `Bm`**: the Schreier–Sims backend at every degree `M`, with `sm M = M²`. -/
def ssBm : ∀ M, BackendBounds ssCtx ssDV M (M * M) ⊤ := fun M => ssBounds M ⊤

/-- **M2b's `hsR'`**: the block stabilizer re-based onto block `0` has at most `N²`
generators, by `RunsWithin.m2bProg` for the invariant `ssBnd 0`. -/
theorem ss_m2bRb_gens_le {n N : ℕ} {gs : GensData} {bs : List (List ℕ)} (hn : n ≤ N)
    (hbase : IsInvariant (GensData.denote N gs) (baseSet n N)) (hgs : GensData.AllValid N gs)
    (hbs : IsBlockList (WinData.ofPoints N (basePts n N)) bs)
    (hGb : PermutesBlocks (GensData.denote N gs) bs) (hbs0 : 0 < bs.length) :
    (m2bRb ssCtx.O n N gs bs).2.1.length ≤ N * N := by
  have hwbv : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hwbn : ∀ i ∈ (WinData.ofPoints N (basePts n N)).1, n ≤ i :=
    fun i hi => (mem_basePts.1 hi).1
  have hO : MeetsContractOn (ssBnd 0) blockStabOps (ssCtxB 0).O :=
    fun op x _ hx => ssOracle_meets_bnd 0 op x hx
  obtain ⟨-, -, -, -, -, -, -, hdeg3, hval3, -⟩ := RunsWithin.m2bProg (X := ssCtxB 0)
    (DV := ssBnd 0) (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    hO (fun _ _ _ h => h) hn hbase hwbv hwbn hbs hGb hgs hbs0 le_rfl le_rfl le_rfl le_rfl le_rfl
    #[] [] (T := 0) (by simp)
  have hflat : bs.flatten.length = N - n := by
    rw [hbs.1.length_eq, WinData.ofPoints_fst, length_basePts]
  have hkle : (bs.toArray.getD 0 []).length ≤ N - n := by
    rw [← hflat, mr_getD_toArray', List.getD_eq_getElem _ _ hbs0, List.length_flatten]
    exact List.le_sum_of_mem (List.mem_map.2 ⟨_, List.getElem_mem hbs0, rfl⟩)
  have h := hval3.2
  change _ ≤ max 0 ((n + (bs.toArray.getD 0 []).length) * (n + (bs.toArray.getD 0 []).length))
    at h
  exact (h.trans (max_le (Nat.zero_le _) le_rfl)).trans
    (Nat.mul_le_mul (by omega) (by omega))

/-- **M4's `hKs`**: the stabilizer `K` of M4's structure has at most `S` generators when the
instance has at most `S ≥ N²`. This follows M4's construction (`indiv_of_degree`,
`RunsWithin.pointStabsProg`, `m4Struct_spec`) for the invariant `ssBnd S`, under M4's case
conditions (`htr`, `hng`, `hk4`, as in `RunsWithin.m4StepProg`). -/
theorem ss_m4K_gens_le {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {n₀ n : ℕ} {L : LabelData} {S : ℕ}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hgs : gs.length ≤ S) (hS : N * N ≤ S) :
    (m4K ssCtx.O n (N, gs, ())).2.1.length ≤ S := by
  have hO : MeetsContractOn (ssBnd S) rdOps (ssCtxB S).O :=
    fun op x _ hx => ssOracle_meets_bnd S op x hx
  have hOdeg : MeetsContractOn (ssBnd S) degreeOps (ssCtxB S).O :=
    fun op x h hx => hO op x (m4_degOps h) hx
  have hOs : MeetsContractOn (ssBnd S) stabOps (ssCtxB S).O :=
    fun op x h hx => hO op x (m4_stabOps h) hx
  have hOm : MeetsContractOn (ssBnd S) m4StructOps (ssCtxB S).O :=
    fun op x h hx => hO op x (m4_structOps h) hx
  have hn : n ≤ N := hI.le
  have hinv : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hG : GroupValid (D := Ty.unit) (ssBnd S) N gs () :=
    ⟨hI.valid.group.1, show gs.length ≤ max S (N * N) from le_max_of_le_left hgs⟩
  have B := ssBoundsB S N S ⊤ hS
  obtain ⟨-, hdm, htrH, h2H⟩ := indiv_of_degree hOdeg B hG hgs le_top hinv hn
    (cap := N - n - 2) (by omega) htr hng
  have hjd : m4J ssCtx.O n (N, gs, ()) + 1 ≤ N - n := by
    have : m4Deg ssCtx.O n (N, gs, ()) + 1 ≤ N - n := hdm
    unfold m4J
    omega
  have hS' : ∀ u ∈ (List.range (m4J ssCtx.O n (N, gs, ()))).map (n + ·), n ≤ u ∧ u < N := by
    intro u hu
    simp only [List.mem_map, List.mem_range] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    omega
  obtain ⟨-, hpsN₀, hpsv₀, hpsden, -⟩ := Toolkit.RunsWithin.pointStabsProg
    (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    hOs (fun _ _ _ h => h) hG hinv hS' B hgs le_top
  have hpsN : (m4PS ssCtx.O n (N, gs, ())).1.1 = N := hpsN₀
  have hpsv : GroupValid (D := Ty.unit) (ssBnd S) N (m4PS ssCtx.O n (N, gs, ())).1.2.1
      (m4PS ssCtx.O n (N, gs, ())).1.2.2 := hpsv₀
  have hHden : GensData.denote N (m4PS ssCtx.O n (N, gs, ())).1.2.1 =
      fixFirst (GensData.denote N gs) n (m4J ssCtx.O n (N, gs, ())) := by
    show GensData.denote N (pointStabsModel (ssCtxB S).O (N, gs, ())
      ((List.range (m4J ssCtx.O n (N, gs, ()))).map (n + ·))).1.2.1 = _
    rw [hpsden, range_map_eq_range', pointwiseStab_range']
  have hinvH : IsInvariant (GensData.denote N (m4PS ssCtx.O n (N, gs, ())).1.2.1)
      (baseSet (n + m4J ssCtx.O n (N, gs, ())) N) := by
    rw [hHden]
    exact fixFirst_base_inv hinv _
  obtain ⟨htrH', h2H'⟩ := m4_trans_congr hHden.symm (fixFirst_base_inv hinv _) hinvH
  have hn' : n + m4J ssCtx.O n (N, gs, ()) < N := by omega
  have hk4' : 4 ≤ N - (n + m4J ssCtx.O n (N, gs, ())) := by omega
  have hP1 : (m4PS ssCtx.O n (N, gs, ())).1 =
      (N, (m4PS ssCtx.O n (N, gs, ())).1.2.1, (m4PS ssCtx.O n (N, gs, ())).1.2.2) :=
    Prod.ext hpsN rfl
  obtain ⟨-, hKv, -⟩ := m4Struct_spec (X := ssCtxB S) hOm (fun _ _ _ h => h) hpsv hinvH hn'
    (htrH' htrH) (h2H' h2H) hk4' ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  rw [← hP1] at hKv
  exact hKv.2.trans (max_le le_rfl hS)

end Counts

end GraphIso.Main
