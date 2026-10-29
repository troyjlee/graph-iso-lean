module

public import GraphIso.CertProg.Cert

/-!
# The certificate and the comparison of certificates

Stage 14e, item 6 (`PLAN-14.md` §9).

* `certProg`: `G_A` (`stabSetProg`), the paired beard of `(x, A)` with itself from `1 • G_A`
  (`pairLoopProg`), then `K(A)`, the pointwise stabilizer in `H(A)` of the string positions
  outside `W(A)` (`iterStabProg`), and the fullness test (`giantAProg` on `K(A)`).
  `RunsWithin.certProg`: `W(A)`, `H(A)` and `K(A)` are milestone 13's `beardW`, `beardH` and
  `certK` (through `toStab`), and the test answers `IsGiantOn φ A (certK φ A x)`.
* `certIsoProg`: a lift `τ` mapping the tuple `T` onto `T'` (`moveProg`), `G_A`, the paired beard
  of `(x, A)` and `(x', A')` from `τ • G_A`, and the tuple transporter (`tupleTransProg`) in the
  final group from the positions of `T` to the `σ⁻¹`-images of the positions of `T'`.
  `RunsWithin.certIsoProg`: the answer is `CertIso φ x x' T T'` (through `certIso_iff`).
* The number of generators of `G_A` is bounded by the backend's `genOut`: the generators that
  `giantSetStabProg` passes to `generate` are valid (`giantGens_allValid`).
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates Cost
  GraphIso.Programs GraphIso.Solver

/-! ### Generators of `G_A` and of iterated stabilizers -/

section Gens

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The generators passed to `generate` by `giantSetStabProg` are valid.** -/
theorem giantGens_allValid (hO : MeetsContractOn DV giantOps X.O)
    (hPre : ∀ op x, giantOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hgiant : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hG).range)
    {A : List ℕ} (hA : A.Nodup) (hAm : ∀ x ∈ A, x < N - n) {b₁ b₂ : ℕ} (hb : b₁ ≠ b₂)
    (hb₁ : b₁ < N - n) (hb₂ : b₂ < N - n) (hbA₁ : b₁ ∉ A) (hbA₂ : b₂ ∉ A) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Bl : ℕ}
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl) :
    GensData.AllValid N (giantGens X.O n (N, gs, d) A b₁ b₂) := by
  have hOl : MeetsContractOn DV liftOps X.O := fun op x hop hx =>
    hO op x (by rw [liftOps] at hop; simp [giantOps, hop]) hx
  have hPl : ∀ op x, liftOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rw [liftOps] at hop; simp [giantOps, hop]) hx
  have hOs : MeetsContractOn DV stabOps X.O := fun op x hop hx =>
    hO op x (by rcases hop with h | h <;> simp [giantOps, h]) hx
  have hPs : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rcases hop with h | h <;> simp [giantOps, h]) hx
  intro g hg
  rw [giantGens, List.mem_append] at hg
  rcases hg with hg | hg
  · cases A with
    | nil => simp [giantLifts] at hg
    | cons a₀ rest =>
      simp only [giantLifts, List.mem_map] at hg
      obtain ⟨x, hx, rfl⟩ := hg
      have ha₀ : a₀ < N - n := hAm a₀ List.mem_cons_self
      have hnd := List.nodup_cons.1 hA
      have hrest : ∀ x ∈ rest, x < N - n ∧ a₀ ≠ x := fun x hx =>
        ⟨hAm x (List.mem_cons_of_mem _ hx), fun h => hnd.1 (h ▸ hx)⟩
      have hbx : ∀ x ∈ a₀ :: rest, x ≠ b₁ ∧ x ≠ b₂ := fun x hx =>
        ⟨fun h => hbA₁ (h ▸ hx), fun h => hbA₂ (h ▸ hx)⟩
      exact ((lifts_spec (X := X) (body := fun (_ : Ty.unit.denote) =>
        (Prog.ret () : Prog (groupSig D) (.unit, .unit) Ty.denote .unit)) hOl hPl hGv hG hgiant ha₀
        hrest hb hb₁ hb₂ hbx
        hBl).2 x hx).1
  · have hps : ∀ u ∈ A.map (n + ·), u < N := by
      intro u hu
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu
      have := hAm x hx
      omega
    exact (RunsWithin.iterStabProg (X := X) (body := fun (_ : Ty.unit.denote) =>
      (Prog.ret () : Prog (groupSig D) (.unit, .unit) Ty.denote .unit)) hOs hPs hGv hps B hs
      hG₀).2.2.1.1 g hg

/-- `G_A` has at most `s` generators. -/
theorem stabSet_gens_le (hO : MeetsContractOn DV giantOps X.O)
    (hPre : ∀ op x, giantOps op → GroupPre DV op x → X.Pre op x) {n N : ℕ} {gs : GensData}
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hgiant : alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hG).range)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (hk : al.length + 2 ≤ N - n)
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {Bl : ℕ}
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl) :
    (stabSetModel X.O n (N, gs, d) al).2.1.length ≤ s := by
  obtain ⟨b₁, b₂, rest, hos, hb, hb₁, hb₂, hbA₁, hbA₂⟩ := exists_outside hal halm hk
  have hmodel :
      stabSetModel X.O n (N, gs, d) al = giantSetStabModel X.O n (N, gs, d) al b₁ b₂ := by
    simp only [stabSetModel]
    rw [hos]
  have hv := giantGens_allValid (X := X) hO hPre hGv hG hgiant hal halm hb hb₁
    hb₂ hbA₁ hbA₂ B hs hG₀ hBl
  have hpost := hO .generate (N, giantGens X.O n (N, gs, d) al b₁ b₂) (by simp [giantOps]) hv
  rw [hmodel]
  refine B.genOut _ hv ?_
  obtain ⟨-, -, hden⟩ := hpost
  rw [← hden]
  intro g hg
  have : GensData.denote N (giantSetStabModel X.O n (N, gs, d) al b₁ b₂).2.1 ≤
      GensData.denote N gs := by
    obtain ⟨-, -, -, hden'⟩ := RunsWithin.giantSetStabProg (X := X) (body := fun
      (_ : Ty.unit.denote) => (Prog.ret () : Prog (groupSig D) (.unit, .unit) Ty.denote .unit))
      hO hPre hGv
      hG hgiant hal halm hb hb₁ hb₂ hbA₁ hbA₂ B hs hG₀ hBl (le_refl _)
    rw [hden']
    rintro _ ⟨g', -, rfl⟩
    exact g'.2
  exact hG₀ (this hg)

/-- The iterated stabilizer has at most `s` generators and lies in `G₀`. -/
theorem iterStab_gens_le (hO : MeetsContractOn DV stabOps X.O) {M s : ℕ}
    {G₀ : Subgroup (Perm (Fin M))} (B : BackendBounds X DV M s G₀) :
    ∀ (ps : List ℕ) (H : GroupData D.denote), (∀ u ∈ ps, u < M) → H.1 = M →
      GroupValid DV M H.2.1 H.2.2 → H.2.1.length ≤ s → GensData.denote M H.2.1 ≤ G₀ →
      (iterStabModel X.O H ps).2.1.length ≤ s := by
  intro ps
  induction ps with
  | nil => intro H _ _ _ h _; exact h
  | cons u ps ih =>
    intro H hps hdeg hv hlen hle
    obtain ⟨M', ks, e⟩ := H
    change M' = M at hdeg
    subst hdeg
    have hu : u < M' := hps u List.mem_cons_self
    have hpre : GroupPre DV .stabilizer ((M', ks, e), u) := ⟨hv, hu⟩
    have hpost := hO .stabilizer _ (Or.inl rfl) hpre
    have hout := B.stabOut ks e u hle hpre
    rcases hS : X.O.run GroupOp.stabilizer ((M', ks, e), u) with ⟨M'', ks', e'⟩
    rw [hS] at hpost hout
    obtain ⟨hM'', hv', hden⟩ := hpost
    change M'' = M' at hM''
    subst hM''
    have hstep :
        iterStabModel X.O (M'', ks, e) (u :: ps) = iterStabModel X.O (M'', ks', e') ps := by
      show List.foldl _ (X.O.run GroupOp.stabilizer ((M'', ks, e), u)) ps = _
      rw [hS]
      rfl
    rw [hstep]
    refine ih _ (fun v hv => hps v (List.mem_cons_of_mem _ hv)) rfl hv' hout ?_
    change GensData.denote M'' ks' ≤ G₀
    rw [hden hu]
    exact inf_le_left.trans hle

end Gens

/-! ### The semantic bridges of the certificate -/

section Bridges

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **The pointwise stabilizer of the string positions outside a window**, in milestone 13's
terms: the `fixingSubgroup` of the complement. -/
theorem toStab_pointwiseStab_compl {A : Finset (Fin (N - n))} {K : Subgroup (Perm (Fin N))}
    {W : Set (Fin n)} {comp : List ℕ}
    (hcomp : ∀ j, j ∈ comp ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∉ W) :
    toStab φ A (pointwiseStab K {v : Fin N | v.val ∈ comp}) =
      toStab φ A K ⊓ fixingSubgroup (stabA φ A) Wᶜ := by
  ext s
  obtain ⟨g, hg⟩ := strR_surjective hC s.1
  have hs : s = ⟨strR hC g, hg ▸ s.2⟩ := Subtype.ext hg.symm
  rw [Subgroup.mem_inf, hs, mem_toStab_strR, mem_toStab_strR, mem_fixingSubgroup_iff]
  simp only [pointwiseStab, Subgroup.mem_mk, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl ⟨fun h u hu => ?_, fun h v hv => ?_⟩
  · apply Fin.ext
    show ((strR hC g • u : Fin n) : ℕ) = u.val
    rw [strR_smul_val, h _ ((hcomp u.val).2 ⟨u.2, hu⟩)]
  · obtain ⟨hvn, hvW⟩ := (hcomp v.val).1 hv
    have := congrArg Fin.val (h ⟨v.val, hvn⟩ hvW)
    change ((strR hC g • (⟨v.val, hvn⟩ : Fin n) : Fin n) : ℕ) = v.val at this
    rw [strR_smul_val] at this
    exact Fin.ext this

/-- **The initial coset of the paired beard**: `τ • G_A`, for `τ ∈ G` moving `A` onto `A'`. -/
theorem denotes_pairCoset_zero (hφ : IsPhi hC φ) {A A' : Finset (Fin (N - n))}
    {x x' : Fin n → ℕ} {τ : Perm (Fin N)} (hτ : τ ∈ G)
    (hτA : baseHom G n hC.base ⟨τ, hτ⟩ • A = A') {GA : Subgroup (Perm (Fin N))}
    (hGA : GA = (Recursion.blockStab (baseHom G n hC.base) A).map G.subtype) :
    Denotes hC (τ • (GA : Set (Perm (Fin N)))) (pairCoset φ A A' x x' 0) := by
  intro g
  have h0 : ∀ g' : strGroup hC, g' ∈ pairCoset φ A A' x x' 0 ↔ φ g' • A = A' := by
    intro g'
    simp only [pairCoset, Set.mem_ofPred_eq]
    refine ⟨fun h => h.1, fun h => ⟨h, fun j hj => ?_, fun u hu => ?_⟩⟩
    · obtain rfl : j = 0 := by omega
      simp [beard]
    · simp [beard] at hu
  rw [Set.mem_smul_set_iff_inv_smul_mem, hGA, smul_eq_mul]
  constructor
  · rintro ⟨h, hh, he⟩
    have he' : (h : Perm (Fin N)) = τ⁻¹ * g := he
    have hgG : g = τ * h.1 := by rw [he', mul_inv_cancel_left]
    refine ⟨hgG ▸ G.mul_mem hτ h.2, ?_⟩
    rw [h0, hφ]
    have e : (⟨g, hgG ▸ G.mul_mem hτ h.2⟩ : G) = ⟨τ, hτ⟩ * h := Subtype.ext hgG
    rw [e, map_mul, mul_smul]
    have hh' : baseHom G n hC.base h • A = A := hh
    rw [hh', hτA]
  · rintro ⟨hg, hgC⟩
    rw [h0, hφ] at hgC
    refine ⟨⟨τ, hτ⟩⁻¹ * ⟨g, hg⟩, ?_, rfl⟩
    show baseHom G n hC.base (⟨τ, hτ⟩⁻¹ * ⟨g, hg⟩) • A = A
    rw [map_mul, mul_smul, hgC, ← hτA, map_inv, inv_smul_smul]

end Bridges

/-! ### The certificate as a program -/

section CertProgram

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The string positions `< n` outside the list `Wl`. -/
def complProg {S : Signature} (n : var .nat) (Wl : var (.list .nat)) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .range n) fun rn =>
  Toolkit.filterList rn fun j => .bind (cpMemProg j Wl) fun b => .op1 .not b

/-- **The local certificate of a test set**: `W(A)`, `H(A)`, `K(A)` and the fullness test, or
`none` (which does not happen). -/
def certProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (pos : var (.array .nat)) (pA : var (.list .nat)) (xy : var Ty.strs)
    (G : var (Ty.group D)) (al : var (.list .nat)) :
    Prog (groupSig D) rec var
      (.option (.prod (.list .nat) (.prod (Ty.group D) (.prod (Ty.group D) .bool)))) :=
  .bind (stabSetProg n G al) fun GA =>
  .bind (.op1 .fst G) fun M => .bind (permOne M) fun one =>
  .bind (pairLoopProg sub n pos pA xy one GA) fun res =>
  .bind (.op1 .fst res) fun Wl => .bind (.op1 .snd res) fun ans =>
  .caseOption ans (.op0 .none) fun c =>
    .bind (.op1 .snd c) fun K =>
    .bind (complProg n Wl) fun comp =>
    .bind (iterStabProg K comp) fun KA =>
    .bind (.op1 .snd KA) fun kd => .bind (.op1 .fst kd) fun kgs =>
    .bind (giantAProg pos pA kgs) fun full =>
    .bind (.op2 .pair KA full) fun t₁ => .bind (.op2 .pair K t₁) fun t₂ =>
    .bind (.op2 .pair Wl t₂) fun t₃ => .op1 .some t₃

end CertProgram

section CertSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem RunsWithin.complProg {S : Signature} {X : Ctx S}
    {body : a.denote → Prog S (a, b) Ty.denote b} (n : ℕ) (Wl : List ℕ) :
    RunsWithin X body (CertProg.complProg n Wl)
      ((List.range n).filter fun j => !Wl.any (· == j)) (n * (3 * Wl.length + 6) + n + 5) := by
  have hf := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := List.range n)
    (P := fun j => !Wl.any (· == j)) (c := 3 * Wl.length + 2)
    (p := fun j => .bind (CertProg.cpMemProg j Wl) fun c => .op1 .not c) fun j _ =>
      RunsWithin.bind_le (RunsWithin.cpMemProg j Wl) (RunsWithin.prim _ _)
        (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hf
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range]
    ring_nf
    omega

/-- The operations used by the certificate programs. -/
def certOps (op : GroupOp) : Prop :=
  op = .stabilizer ∨ op = .orbitTransversal ∨ op = .orbits ∨ op = .generate ∨ op = .lift

/-- The cost of `certProg`. -/
def certCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs : ℕ) : ℕ :=
  outsideCost (N - n) k + giantSetStabCost n N k Bstab Bl Bgs +
    pairLoopCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb + 2 * N +
    (n * (3 * n + 6) + n) + n * (Bstab + 2) + giantACost k s Bgen' Borb' Bstab' + 40

/-- The polynomial factor of `certCost`. -/
def certPoly (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs : ℕ) : ℕ :=
  outsideCost (N - n) k + giantSetStabCost n N k Bstab Bl Bgs + 2 * N +
    (n * (3 * n + 6) + n) + n * (Bstab + 2) + giantACost k s Bgen' Borb' Bstab' + 40 +
    loopPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen

/-- **The certificate costs at most a polynomial times `k!`**, plus at most `n · k! · n`
sub-calls of cost `Cb` each. -/
theorem certCost_le (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs : ℕ) :
    certCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs ≤
      k.factorial * certPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs +
        n * (k.factorial * (n * Cb)) := by
  have h1 := pairLoopCost_le N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb
  have h2 := Nat.le_mul_of_pos_left (outsideCost (N - n) k + giantSetStabCost n N k Bstab Bl Bgs +
    2 * N + (n * (3 * n + 6) + n) + n * (Bstab + 2) + giantACost k s Bgen' Borb' Bstab' + 40)
    (Nat.factorial_pos k)
  unfold certCost certPoly
  rw [Nat.mul_add k.factorial _ (loopPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen)]
  omega

variable {N n : ℕ} {gs : GensData} {hC : CertSetting (GensData.denote N gs) n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- A subgroup of `G` whose elements stabilize `A` is the exact preimage of its `toStab`. -/
theorem denotes_toStab {A : Finset (Fin (N - n))} {H : Subgroup (Perm (Fin N))}
    {L : Subgroup (stabA φ A)} (hHG : H ≤ GensData.denote N gs)
    (hHA : ∀ g : GensData.denote N gs, (g : Perm (Fin N)) ∈ H → strR hC g ∈ stabA φ A)
    (hL : toStab φ A H = L) :
    Denotes hC (H : Set (Perm (Fin N))) (L.map (stabA φ A).subtype : Set (strGroup hC)) := by
  intro g
  constructor
  · intro hg
    refine ⟨hHG hg, ⟨strR hC ⟨g, hHG hg⟩, hHA _ hg⟩, ?_, rfl⟩
    rw [← hL]
    exact (mem_toStab_strR _ _).2 hg
  · rintro ⟨hgG, t, ht, hts⟩
    rw [← hL] at ht
    exact mem_toStab.1 ht ⟨g, hgG⟩ hts.symm

/-- **The local certificate.** For a giant base action, a test set `A` (`k ≥ 5`, `k + 2 ≤ m`)
and `xy = (x, x)`: the program returns `W(A)`, `H(A)`, `K(A)` (milestone 13's `beardW`,
`beardH`, `certK`: their `toStab` images, and the returned groups are exactly the preimages in
`G`) and the answer of the fullness test `IsGiantOn φ A (certK φ A x)`. -/
theorem RunsWithin.certProg (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (h5 : 5 ≤ al.length)
    (hk : al.length + 2 ≤ N - n) {xy : StrData × StrData} (hxy : xy.2 = xy.1) {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) {Bgen Bl Bgs : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ al.length.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ b₁ b₂, X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
      (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) xy n al.length s) (fun _ => Cb) s) :
    ∃ res, RunsWithin X body (CertProg.certProg sub n (WinData.pos N (winA N n al))
          (winA N n al).1 xy (N, gs, d) al) res
        (certCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl Bgs) ∧
      ∃ Wl K KA full, res = some (Wl, K, KA, full) ∧ Wl.Nodup ∧
        (∀ j, j ∈ Wl ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈
          beardW φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N))) ∧
        K.1 = N ∧ GroupValid DV N K.2.1 K.2.2 ∧
        toStab φ (finsetOf (N - n) al) (GensData.denote N K.2.1) =
          beardH φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N)) ∧
        Denotes hC (GensData.denote N K.2.1 : Set (Perm (Fin N)))
          ((beardH φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N))).map
            (stabA φ (finsetOf (N - n) al)).subtype) ∧
        KA.1 = N ∧ GroupValid DV N KA.2.1 KA.2.2 ∧
        toStab φ (finsetOf (N - n) al) (GensData.denote N KA.2.1) =
          certK φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N)) ∧
        Denotes hC (GensData.denote N KA.2.1 : Set (Perm (Fin N)))
          ((certK φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N))).map
            (stabA φ (finsetOf (N - n) al)).subtype) ∧
        (full = true ↔ IsGiantOn φ (finsetOf (N - n) al)
          (certK φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N)))) := by
  set A := finsetOf (N - n) al with hA
  set x := strOn hC.le (xy.1.denote N) with hx
  have hnN := hC.le
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- operations
  have hOgi : MeetsContractOn DV giantOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hPgi : ∀ op y, giantOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hOst : MeetsContractOn DV stepOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hPst : ∀ op y, stepOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hOs : MeetsContractOn DV stabOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h <;> simp [certOps, h]) hy
  have hPs : ∀ op y, stabOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h <;> simp [certOps, h]) hy
  have hOg : MeetsContractOn DV giantAOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h <;> simp [certOps, h]) hy
  have hPg : ∀ op y, giantAOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h <;> simp [certOps, h]) hy
  -- `G_A`
  obtain ⟨hsrun, hsN, hsv, hsden⟩ := RunsWithin.stabSetProg (X := X) (body := body) hOgi hPgi
    hGv hC.base hgiant hal halm hk B hs hGG₀ hBl hBgs
  have hsgen := stabSet_gens_le (X := X) hOgi hPgi hGv hC.base hgiant hal halm hk B hs hGG₀ hBl
  rcases hGA : stabSetModel X.O n (N, gs, d) al with ⟨N₁, gas, ga⟩
  rw [hGA] at hsrun hsN hsv hsden hsgen
  change N₁ = N at hsN
  subst hsN
  -- the initial coset
  have hden₀ : Denotes hC (PermData.denote N₁ (PermData.one N₁) •
      (GensData.denote N₁ gas : Set (Perm (Fin N₁))))
      (pairCoset φ A A x (strOn hC.le (xy.2.denote N₁)) 0) := by
    rw [PermData.denote_one]
    exact denotes_pairCoset_zero hφ (one_mem _) (by rw [show (⟨1, one_mem _⟩ :
      GensData.denote N₁ gs) = 1 from rfl, map_one, one_smul]) hsden
  -- the loop
  obtain ⟨res, hlrun, hat⟩ := RunsWithin.pairLoopProg (X := X) (body := body) hOst hPst hφ hal
    halm h5 (A' := A) (xy := xy) B hGG₀ Bk hsk hBg hsub (PermData.valid_one N₁) hsv hsgen hden₀
  have hnone := atRound_none_iff hat
  rw [hxy] at hnone
  have hne : pairCoset φ A A x x n ≠ ∅ := by
    rw [pairCoset_self]
    exact Set.nonempty_iff_ne_empty.1 ⟨1, (beardG φ A x n).one_mem⟩
  obtain ⟨Wl, ans⟩ := res
  rcases hans : ans with _ | c
  · exact absurd (hnone.1 hans) hne
  obtain ⟨τ, N₂, ks, e⟩ := c
  obtain ⟨hτ, hN₂, hKv, hKs, hKden, hWnd, hWmem⟩ := hat.2 _ hans
  change N₂ = N₁ at hN₂
  subst hN₂
  rw [hxy] at hKden
  obtain ⟨-, hKG, -, hKb⟩ := denotes_group hKden
  have hKtoStab := toStab_eq_beard hKden
  have hbeardH : beardH φ A x = (beard φ A x n).2 := by
    rw [beardH, hcard]
  have hbeardW : beardW φ A x = (beard φ A x n).1 := by
    rw [beardW, hcard]
  -- `K(A)`
  set comp := (List.range n).filter fun j => !Wl.any (· == j) with hcomp_def
  have hcomp : ∀ j, j ∈ comp ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∉ beardW φ A x := by
    intro j
    rw [hcomp_def, List.mem_filter, List.mem_range, hbeardW]
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    constructor
    · rintro ⟨hj, hnot⟩
      exact ⟨hj, fun hW => hnot j ((hWmem j).2 ⟨hj, hW⟩) rfl⟩
    · rintro ⟨hj, hnot⟩
      exact ⟨hj, fun y hy e => hnot (by obtain ⟨_, h⟩ := (hWmem y).1 hy; subst e; exact h)⟩
  have hcompN : ∀ u ∈ comp, u < N₂ := fun u hu => by
    obtain ⟨hu', -⟩ := (hcomp u).1 hu
    omega
  have hWlen : Wl.length ≤ n := length_le_of_lt hWnd fun j hj => ((hWmem j).1 hj).1
  have hcomplen : comp.length ≤ n := by
    rw [hcomp_def]
    exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨hirun, hiN, hiv, hiden⟩ := RunsWithin.iterStabProg (X := X) (body := body) hOs hPs hKv
    hcompN B hKs (hKG.trans hGG₀)
  have higen := iterStab_gens_le (X := X) hOs B comp (N₂, ks, e) hcompN rfl hKv hKs
    (hKG.trans hGG₀)
  rcases hKA : iterStabModel X.O (N₂, ks, e) comp with ⟨N₃, kas, ka⟩
  rw [hKA] at hirun hiN hiv hiden higen
  change N₃ = N₂ at hiN
  subst hiN
  have hKAtoStab : toStab φ A (GensData.denote N₃ kas) = certK φ A x := by
    rw [hiden, toStab_pointwiseStab_compl hcomp, hKtoStab, ← hbeardH, certK]
  have hKAstabs : StabsA hC al (GensData.denote N₃ kas) := by
    refine ⟨fun g hg => hKG (by rw [hiden] at hg; exact hg.1), fun g hg => ?_⟩
    rw [hiden] at hg
    obtain ⟨t, -, ht⟩ := (hKb g).1 hg.1
    rw [← mem_stabA_strR hφ, ← ht]
    exact t.2
  -- exact preimages
  have hKden' : Denotes hC (GensData.denote N₃ ks : Set (Perm (Fin N₃)))
      ((beardH φ A x).map (stabA φ A).subtype) :=
    denotes_toStab hKG (fun g hg => by obtain ⟨t, -, ht⟩ := (hKb g).1 hg; rw [← ht]; exact t.2)
      (by rw [hKtoStab, hbeardH])
  have hKAden : Denotes hC (GensData.denote N₃ kas : Set (Perm (Fin N₃)))
      ((certK φ A x).map (stabA φ A).subtype) :=
    denotes_toStab hKAstabs.1 (fun g hg => (mem_stabA_strR hφ g).2 (hKAstabs.2 g hg)) hKAtoStab
  -- the fullness test
  obtain ⟨hgrun, hgiff⟩ := RunsWithin.giantAProg (X := X) (body := body) hOg hPg
    (winA_valid hal halm) hiv.1 (isInvariant_winA hKAstabs) Bk (higen.trans hsk)
  have hgiff' := giantAModel_iff hφ hal halm hKAstabs hgiff
  rw [hKAtoStab] at hgiff'
  replace hgrun := hgrun.mono ((le_of_eq (congrArg (fun k => giantACost k kas.length Bk.Bgen
    Bk.Borb Bk.Bstab) (length_winA al))).trans (giantACost_mono higen _ _ _))
  refine ⟨some (Wl, (N₃, ks, e), (N₃, kas, ka),
    giantAModel X.O (WinData.pos N₃ (winA N₃ n al)) (winA N₃ n al).1 kas), ?_,
    Wl, (N₃, ks, e), (N₃, kas, ka), _, rfl, hWnd, fun j => by rw [hWmem, hbeardW], rfl, hKv,
    by rw [hKtoStab, hbeardH], hKden', rfl, hiv, hKAtoStab, hKAden, hgiff'⟩
  apply RunsWithin.mono
  case h =>
    unfold CertProg.certProg
    run_step hsrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.permOne _)
    run_step hlrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    rw [hans]
    run_with RunsWithin.caseOption_some _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.complProg n Wl)
    run_step hirun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hgrun
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    have h1 : Wl.length * 3 ≤ n * 3 := by omega
    have h2 : n * (3 * Wl.length + 6) ≤ n * (3 * n + 6) := Nat.mul_le_mul_left _ (by omega)
    have h3 : comp.length * (B.Bstab + 2) ≤ n * (B.Bstab + 2) := Nat.mul_le_mul_right _ hcomplen
    simp only [Prim.cost, Prim.eval, certCost]
    omega

end CertSpec

/-! ### Comparing certificates -/

/-- A tuple of base points from a list. -/
def tupleD (m k : ℕ) (l : List ℕ) (h : ∀ i < k, l.getD i 0 < m) : Fin k → Fin m :=
  fun i => ⟨l.getD i 0, h i i.2⟩

theorem image_tupleD {m : ℕ} {l : List ℕ} (h : ∀ i < l.length, l.getD i 0 < m) :
    Finset.univ.image (tupleD m l.length l h) = finsetOf m l := by
  ext b
  rw [Finset.mem_image, mem_finsetOf]
  constructor
  · rintro ⟨i, -, rfl⟩
    simp only [tupleD]
    rw [List.getD_eq_getElem _ _ i.2]
    exact List.getElem_mem _
  · intro hb
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    refine ⟨⟨i, hi⟩, Finset.mem_univ _, Fin.ext ?_⟩
    show l.getD i 0 = b.val
    rw [List.getD_eq_getElem _ _ hi, hbi]

theorem image_tupleD' {m : ℕ} {l l' : List ℕ} (hlen : l'.length = l.length)
    (h : ∀ i < l.length, l'.getD i 0 < m) :
    Finset.univ.image (tupleD m l.length l' h) = finsetOf m l' := by
  ext b
  rw [Finset.mem_image, mem_finsetOf]
  constructor
  · rintro ⟨i, -, rfl⟩
    show l'.getD i 0 ∈ l'
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · intro hb
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    refine ⟨⟨i, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
    show l'.getD i 0 = b.val
    rw [List.getD_eq_getElem _ _ hi, hbi]

section CertIsoMath

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **Certificates are compared by a tuple transporter** in the final group of the paired
beard: `CertIso φ x x' T T'` holds exactly when some `h ∈ K` maps the positions of `T` to the
`σ⁻¹`-images of the positions of `T'`. -/
theorem certIso_iff_transporter (hφ : IsPhi hC φ) {al al' : List ℕ}
    (hlen : al'.length = al.length) (halm : ∀ i < al.length, al.getD i 0 < N - n)
    (halm' : ∀ i < al.length, al'.getD i 0 < N - n) {x x' : Fin n → ℕ} {σd : PermData}
    (hσd : σd.Valid N) {K : Subgroup (Perm (Fin N))}
    (hden : Denotes hC (PermData.denote N σd • (K : Set (Perm (Fin N))))
      (pairCoset φ (finsetOf (N - n) al) (finsetOf (N - n) al') x x' n)) :
    CertIso φ x x' (tupleD (N - n) al.length al halm) (tupleD (N - n) al.length al' halm') ↔
      ∃ h ∈ K, MapsTuple h (posA n al) (al'.map fun t => get σd.2 (n + t)) := by
  have hnN := hC.le
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [certIso_iff, image_tupleD halm, image_tupleD' hlen halm', hcard]
  -- the base action at the listed points
  have key : ∀ (g₀ : G) (i : ℕ) (hi : i < al.length),
      (φ (strR hC g₀) (tupleD (N - n) al.length al halm ⟨i, hi⟩) =
        tupleD (N - n) al.length al' halm' ⟨i, hi⟩) ↔
      g₀.1 ⟨n + al.getD i 0, by have := halm i hi; omega⟩ =
        ⟨n + al'.getD i 0, by have := halm' i hi; omega⟩ := by
    intro g₀ i hi
    rw [hφ]
    have hb := baseHom_apply (hG := hC.base) g₀ (tupleD (N - n) al.length al halm ⟨i, hi⟩)
    constructor
    · intro h
      rw [h] at hb
      exact hb.symm
    · intro h
      apply Fin.ext
      have := congrArg Fin.val hb
      simp only [basePos, tupleD] at this ⊢
      have h' : (g₀.1 ⟨n + al.getD i 0, by have := halm i hi; omega⟩ : ℕ) = n + al'.getD i 0 :=
        congrArg Fin.val h
      omega
  have hσinv : ∀ i (hi : i < al.length), ((PermData.denote N σd)⁻¹ ⟨n + al'.getD i 0,
      by have := halm' i hi; omega⟩ : Fin N).val = get σd.2 (n + al'.getD i 0) := fun i hi =>
    PermData.val_denote_inv_apply hσd _
  have hps : ∀ j, j < (posA n al).length → (posA n al).getD j 0 = n + al.getD j 0 := by
    intro j hj
    rw [length_posA] at hj
    rw [getD_posA hj, List.getD_eq_getElem _ _ hj]
  have hqs : ∀ j, j < al.length →
      (al'.map fun t => get σd.2 (n + t)).getD j 0 = get σd.2 (n + al'.getD j 0) := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_map,
      List.getD_eq_getElem _ _ (by omega)]
  constructor
  · rintro ⟨g, hgC, hgT⟩
    obtain ⟨g₀, rfl⟩ := strR_surjective hC g
    obtain ⟨h, hh, hgh⟩ := Set.mem_smul_set.1 ((hden g₀.1).2 ⟨g₀.2, hgC⟩)
    refine ⟨h, hh, fun j hj hp => ?_⟩
    rw [length_posA] at hj
    have e := (key g₀ j hj).1 (hgT ⟨j, hj⟩)
    have hh' : h = (PermData.denote N σd)⁻¹ * g₀.1 := by
      rw [← hgh, smul_eq_mul, inv_mul_cancel_left]
    rw [hqs j hj, ← hσinv j hj, hh', Perm.mul_apply]
    congr 2
    rw [← e]
    congr 1
    exact Fin.ext (hps j (by rw [length_posA]; exact hj))
  · rintro ⟨h, hh, hmap⟩
    have hg₀ : PermData.denote N σd * h ∈ PermData.denote N σd • (K : Set (Perm (Fin N))) :=
      Set.smul_mem_smul_set hh
    obtain ⟨hgG, hgC⟩ := (hden _).1 hg₀
    refine ⟨strR hC ⟨_, hgG⟩, hgC, fun i => ?_⟩
    rw [key ⟨_, hgG⟩ i i.2]
    have hil : (i : ℕ) < (posA n al).length := by rw [length_posA]; exact i.2
    have hpi := hps i hil
    have hlt : (posA n al).getD i 0 < N := by rw [hpi]; have := halm i i.2; omega
    have hm := hmap i hil hlt
    rw [hqs i i.2, ← hσinv i i.2] at hm
    have e : (⟨n + al.getD i 0, by have := halm i i.2; omega⟩ : Fin N) =
        ⟨(posA n al).getD i 0, hlt⟩ := Fin.ext hpi.symm
    have e2 : h ⟨(posA n al).getD i 0, hlt⟩ = (PermData.denote N σd)⁻¹ ⟨n + al'.getD i 0,
        by have := halm' i i.2; omega⟩ := Fin.ext hm
    show PermData.denote N σd (h _) = _
    rw [e, e2]
    exact Equiv.apply_symm_apply _ _

end CertIsoMath

section CertIsoProgram

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **The comparison of the certificates** of `(x, T)` and `(x', T')`. -/
def certIsoProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (pos : var (.array .nat)) (pA : var (.list .nat)) (xy : var Ty.strs)
    (G : var (Ty.group D)) (al al' : var (.list .nat)) : Prog (groupSig D) rec var .bool :=
  .bind (moveProg n G al al') fun τ =>
  .bind (stabSetProg n G al) fun GA =>
  .bind (pairLoopProg sub n pos pA xy τ GA) fun res =>
  .bind (.op1 .snd res) fun ans =>
  .caseOption ans (.op0 (.boolLit false)) fun c =>
    .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun K =>
    .bind (.op1 .snd σ) fun σi =>
    .bind (mapList al' fun t => .bind (.op2 .add n t) fun p => .op2 .arrayGet σi p) fun qs =>
    .bind (tupleTransProg K pA qs) fun r =>
    .caseOption r (.op0 (.boolLit false)) fun _ => .op0 (.boolLit true)

end CertIsoProgram

section CertIsoSpec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The cost of `certIsoProg`. -/
def certIsoCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs : ℕ) : ℕ :=
  moveDataCost (N - n) k k + baseWinCost n N + Bl + outsideCost (N - n) k +
    giantSetStabCost n N k Bstab Bl Bgs +
    pairLoopCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb + 5 * k +
    tupleTransCost N k Btr Bstab + 40

/-- The polynomial factor of `certIsoCost`. -/
def certIsoPoly (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs : ℕ) : ℕ :=
  moveDataCost (N - n) k k + baseWinCost n N + Bl + outsideCost (N - n) k +
    giantSetStabCost n N k Bstab Bl Bgs + 5 * k + tupleTransCost N k Btr Bstab + 40 +
    loopPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen

/-- **The comparison costs at most a polynomial times `k!`**, plus at most `n · k! · n`
sub-calls of cost `Cb` each. -/
theorem certIsoCost_le (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs : ℕ) :
    certIsoCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb Bl Bgs ≤
      k.factorial * certIsoPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Bl Bgs +
        n * (k.factorial * (n * Cb)) := by
  have h1 := pairLoopCost_le N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb
  have h2 := Nat.le_mul_of_pos_left (moveDataCost (N - n) k k + baseWinCost n N + Bl +
    outsideCost (N - n) k + giantSetStabCost n N k Bstab Bl Bgs + 5 * k +
    tupleTransCost N k Btr Bstab + 40) (Nat.factorial_pos k)
  unfold certIsoCost certIsoPoly
  rw [Nat.mul_add k.factorial _ (loopPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen)]
  omega

variable {N n : ℕ} {gs : GensData} {hC : CertSetting (GensData.denote N gs) n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **The comparison of local certificates.** For a giant base action and duplicate-free tuples
`T`, `T'` of `k` base points (`k ≥ 5`, `k + 2 ≤ m`), the program answers whether
`CertIso φ x x' T T'` holds. -/
theorem RunsWithin.certIsoProg (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {al al' : List ℕ} (hal : al.Nodup) (hal' : al'.Nodup) (hlen : al'.length = al.length)
    (halm : ∀ x ∈ al, x < N - n) (halm' : ∀ x ∈ al', x < N - n) (h5 : 5 ≤ al.length)
    (hk : al.length + 2 ≤ N - n) {xy : StrData × StrData} {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) {Bgen Bl Bgs : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ al.length.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ b₁ b₂, X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
      (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) xy n al.length s) (fun _ => Cb) s) :
    ∃ res : Bool, RunsWithin X body (CertProg.certIsoProg sub n (WinData.pos N (winA N n al))
          (winA N n al).1 xy (N, gs, d) al al') res
        (certIsoCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl
          Bgs) ∧
      (res = true ↔ CertIso φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.2.denote N))
        (tupleD (N - n) al.length al fun i hi => getD_lt halm hi)
        (tupleD (N - n) al.length al' fun i hi => getD_lt halm' (by omega))) := by
  set A := finsetOf (N - n) al with hA
  set A' := finsetOf (N - n) al' with hA'
  set x := strOn hC.le (xy.1.denote N) with hx
  set x' := strOn hC.le (xy.2.denote N) with hx'
  have hnN := hC.le
  have hOgi : MeetsContractOn DV giantOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hPgi : ∀ op y, giantOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hOst : MeetsContractOn DV stepOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hPst : ∀ op y, stepOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h | h | h <;> simp [certOps, h]) hy
  have hOs : MeetsContractOn DV stabOps X.O := fun op y hop hy =>
    hO op y (by rcases hop with h | h <;> simp [certOps, h]) hy
  have hPs : ∀ op y, stabOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rcases hop with h | h <;> simp [certOps, h]) hy
  have hOl : MeetsContractOn DV liftOps X.O := fun op y hop hy =>
    hO op y (by rw [liftOps] at hop; simp [certOps, hop]) hy
  have hPl : ∀ op y, liftOps op → GroupPre DV op y → X.Pre op y := fun op y hop hy =>
    hPre op y (by rw [liftOps] at hop; simp [certOps, hop]) hy
  -- the move
  obtain ⟨hmrun, hmv, hmmem, hmmap⟩ := RunsWithin.moveProg (X := X) (body := body) hOl hPl hGv
    hC.base hgiant hal hal' hlen halm halm' hk hBl
  have hτA : baseHom (GensData.denote N gs) n hC.base ⟨_, hmmem⟩ • A = A' :=
    baseHom_smul_finsetOf hlen halm hmmap
  rw [hlen] at hmrun
  -- `G_A`
  obtain ⟨hsrun, hsN, hsv, hsden⟩ := RunsWithin.stabSetProg (X := X) (body := body) hOgi hPgi
    hGv hC.base hgiant hal halm hk B hs hGG₀ hBl hBgs
  have hsgen := stabSet_gens_le (X := X) hOgi hPgi hGv hC.base hgiant hal halm hk B hs hGG₀ hBl
  rcases hGA : stabSetModel X.O n (N, gs, d) al with ⟨N₁, gas, ga⟩
  rw [hGA] at hsrun hsN hsv hsden hsgen
  change N₁ = N at hsN
  subst hsN
  have hden₀ := denotes_pairCoset_zero (x := x) (x' := x') hφ hmmem hτA hsden
  -- the loop
  obtain ⟨res, hlrun, hat⟩ := RunsWithin.pairLoopProg (X := X) (body := body) hOst hPst hφ hal
    halm h5 (A' := A') (xy := xy) B hGG₀ Bk hsk hBg hsub hmv hsv hsgen hden₀
  obtain ⟨Wl, ans⟩ := res
  have halmi : ∀ i < al.length, al.getD i 0 < N₁ - n := fun i hi => getD_lt halm hi
  have halmi' : ∀ i < al.length, al'.getD i 0 < N₁ - n := fun i hi => getD_lt halm' (by omega)
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  rcases hans : ans with _ | c
  · -- the final coset is empty: no equivalence
    have hE := hat.1 hans
    refine ⟨false, ?_, ⟨fun h => Bool.noConfusion h, fun hiso => ?_⟩⟩
    · apply RunsWithin.mono
      case h =>
        unfold CertProg.certIsoProg
        run_step hmrun
        run_step hsrun
        run_step hlrun
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        rw [hans]
        run_with RunsWithin.caseOption_none _
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, certIsoCost]
        omega
    · rw [certIso_iff, image_tupleD halmi, image_tupleD' hlen halmi', hcard] at hiso
      obtain ⟨g, hg, -⟩ := hiso
      rw [hE] at hg
      exact absurd hg (Set.notMem_empty _)
  · obtain ⟨σd, N₂, ks, e⟩ := c
    obtain ⟨hσd, hN₂, hKv, hKs, hKden, -, -⟩ := hat.2 _ hans
    change N₂ = N₁ at hN₂
    subst hN₂
    obtain ⟨-, hKG, -, -⟩ := denotes_group hKden
    have hqslt : ∀ u ∈ al'.map fun t => get σd.2 (n + t), u < N₂ := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hu
      have := halm' t ht
      exact hσd.inv_lt _ (by omega)
    have hpslt : ∀ u ∈ posA n al, u < N₂ := by
      intro u hu
      obtain ⟨t, ht, rfl⟩ := mem_posA.1 hu
      have := halm t ht
      omega
    obtain ⟨htrun, htiff, -⟩ := RunsWithin.tupleTransProg (X := X) (body := body) hOs hPs hKv B
      hKs (hKG.trans hGG₀) hpslt hqslt (by simp [length_posA, hlen])
    have hiso := certIso_iff_transporter hφ hlen halmi halmi' hσd hKden
    have hqrun : RunsWithin X body (mapList (a' := .nat) (b' := .nat) al' fun t =>
        .bind (.op2 .add n t) fun p => .op2 .arrayGet σd.2 p)
        (al'.map fun t => get σd.2 (n + t)) (al'.length * (2 + 3) + 2) :=
      RunsWithin.mapList_le fun t _ => RunsWithin.bind_le (RunsWithin.prim _ _)
        (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])
    refine ⟨(tupleTransModel X.O (N₂, ks, e) (posA n al)
      (al'.map fun t => get σd.2 (n + t))).isSome, ?_, ?_⟩
    · apply RunsWithin.mono
      case h =>
        unfold CertProg.certIsoProg
        run_step hmrun
        run_step hsrun
        run_step hlrun
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        rw [hans]
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        run_step hqrun
        rw [show (winA N₂ n al).1 = posA n al from rfl]
        run_step htrun
        rcases htr : tupleTransModel X.O (N₂, ks, e) (posA n al)
          (al'.map fun t => get σd.2 (n + t)) with _ | g
        · exact (RunsWithin.caseOption_none (RunsWithin.prim _ _)).mono le_rfl
        · exact (RunsWithin.caseOption_some (RunsWithin.prim _ _)).mono le_rfl
      case hc =>
        simp only [Prim.cost, certIsoCost, length_posA]
        omega
    · rw [htiff, hiso]

end CertIsoSpec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_complProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {Wl₁ : var₁ (.list .nat)}
    {Wl₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hW : ⟨.list .nat, Wl₁, Wl₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (complProg n₁ Wl₁) (complProg n₂ Wl₂) := by
  unfold complProg
  exact .bind (.prim _ (.cons hn .nil)) fun _ _ => Toolkit.wf_filterList (by simp)
    fun _ hΓ _ _ hj => .bind (wf_cpMemProg hj (hΓ (by simp [hW]))) fun _ _ =>
      .prim _ (.cons (by simp) .nil)

theorem wf_certProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {al₁ : var₁ (.list .nat)} {al₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) :
    Prog.Wf r Γ (certProg sub₁ n₁ pos₁ pA₁ xy₁ G₁ al₁) (certProg sub₂ n₂ pos₂ pA₂ xy₂ G₂ al₂) := by
  unfold certProg
  refine .bind (wf_stabSetProg hn hG hal) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hG]) .nil)) fun _ _ => ?_
  refine .bind (wf_permOne (by simp)) fun _ _ => ?_
  refine .bind (wf_pairLoopProg (hsub.mono fun _ h => by simp [h]) (by simp [hn])
    (by simp [hpos]) (by simp [hpA]) (by simp [hxy]) (by simp) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .caseOption (by simp) (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_complProg (by simp [hn]) (by simp)) fun _ _ => ?_
  refine .bind (wf_iterStabProg (by simp) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_giantAProg (by simp [hpos]) (by simp [hpA]) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) .nil)

theorem wf_certIsoProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {al₁ al'₁ : var₁ (.list .nat)} {al₂ al'₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hal : ⟨.list .nat, al₁, al₂⟩ ∈ Γ) (hal' : ⟨.list .nat, al'₁, al'₂⟩ ∈ Γ) :
    Prog.Wf r Γ (certIsoProg sub₁ n₁ pos₁ pA₁ xy₁ G₁ al₁ al'₁)
      (certIsoProg sub₂ n₂ pos₂ pA₂ xy₂ G₂ al₂ al'₂) := by
  unfold certIsoProg
  refine .bind (wf_moveProg hn hG hal hal') fun _ _ => ?_
  refine .bind (wf_stabSetProg (by simp [hn]) (by simp [hG]) (by simp [hal])) fun _ _ => ?_
  refine .bind (wf_pairLoopProg (hsub.mono fun _ h => by simp [h]) (by simp [hn])
    (by simp [hpos]) (by simp [hpA]) (by simp [hxy]) (by simp) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .caseOption (by simp) (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_mapList (by simp [hal']) fun _ hΓ _ _ ht => .bind (.prim _ (.cons
    (hΓ (by simp [hn])) (.cons ht .nil))) fun _ _ =>
      .prim _ (.cons (List.mem_cons_of_mem _ (hΓ (by simp))) (.cons (by simp) .nil)))
    fun _ _ => ?_
  refine .bind (wf_tupleTransProg (by simp) (by simp [hpA]) (by simp)) fun _ _ => ?_
  exact .caseOption (by simp) (.prim _ .nil) fun _ _ => .prim _ .nil

end Wf

end GraphIso.CertProg
