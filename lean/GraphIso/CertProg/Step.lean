module

public import GraphIso.CertProg.Kernel
public import GraphIso.CertProg.PairBeard
public import GraphIso.Reductions.SubgroupProg
public import GraphIso.Reductions.SequentialProg

/-!
# One step of the paired beard

Stage 14e, item 4 (`PLAN-14.md` §9). A coset `σ • H` of degree `N` represents the paired beard's
coset `C_i = pairCoset φ A A' x x' i` (`Denotes`): its elements are the elements of `G` whose
restriction lies in `C_i`. Then `H` represents the beard's group `H_i` (`denotes_group`,
`toStab_eq_beard`), and one step of the paired beard is a string-isomorphism coset on the
affected points (`denotes_iso_succ`, from `pairCoset_succ`).

`beardStepProg sub …` computes that step:

1. the giant test of `ψ_A(H)` (`giantAProg`); if it fails, the step reports `none` (the beard has
   stopped);
2. the affected points (`affProg`), the kernel `N = H ∩ ker ψ_A` with at most `k!`
   representatives (`kerAProg`), and `N`'s orbits on the affected points (`kerOrbitsProg`);
3. `branchProg` over the representatives, solving inside each branch the orbits one after the
   other (`seqProg`) with the sub-solver `sub`.

`RunsWithin.beardStepProg`: under `SubSolves` for the instances with windows of at most `n / k`
string positions (milestone 13's `kernel_orbit`, `kerOrbit_length_le`), the result is a correct
answer for the affected points in `σ • H`, and it represents `C_{i+1}`.
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates Cost
  GraphIso.Programs GraphIso.Solver

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **A set of permutations of degree `N` represents a set of the restricted group**: its
elements are the elements of `G` whose restriction lies in `C`. -/
def Denotes (hC : CertSetting G n) (S : Set (Perm (Fin N))) (C : Set (strGroup hC)) : Prop :=
  ∀ g : Perm (Fin N), g ∈ S ↔ ∃ hg : g ∈ G, strR hC ⟨g, hg⟩ ∈ C

/-- A string of degree `N` restricted to the string positions. -/
def strOn (hn : n ≤ N) (x : Fin N → ℕ) : Fin n → ℕ := fun j => x ⟨j.val, by omega⟩

theorem strR_smul_val (g : G) (u : Fin n) :
    ((strR hC g • u : Fin n) : ℕ) = (g.1 ⟨u.val, by have := hC.le; omega⟩).val :=
  strR_apply_val hC g u

/-- **The group of a represented coset is the beard's group.** -/
theorem denotes_group {A A' : Finset (Fin (N - n))} {x x' : Fin n → ℕ} {i : ℕ}
    {σ : Perm (Fin N)} {H : Subgroup (Perm (Fin N))}
    (hden : Denotes hC (σ • (H : Set (Perm (Fin N)))) (pairCoset φ A A' x x' i)) :
    ∃ hσ : σ ∈ G, H ≤ G ∧ strR hC ⟨σ, hσ⟩ ∈ pairCoset φ A A' x x' i ∧
      ∀ g : G, (g : Perm (Fin N)) ∈ H ↔ strR hC g ∈ beardG φ A x i := by
  obtain ⟨hσG, hσC⟩ := (hden σ).1 ⟨1, H.one_mem, mul_one σ⟩
  have hHG : H ≤ G := by
    intro h hh
    obtain ⟨hσh, -⟩ := (hden (σ * h)).1 ⟨h, hh, rfl⟩
    have := G.mul_mem (G.inv_mem hσG) hσh
    rwa [inv_mul_cancel_left] at this
  have hC' := pairCoset_eq_smul φ hσC
  refine ⟨hσG, hHG, hσC, fun g => ?_⟩
  have key : (σ * g.1 ∈ σ • (H : Set (Perm (Fin N)))) ↔ g.1 ∈ H := by
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, inv_mul_cancel_left]
    rfl
  rw [← key, hden]
  constructor
  · rintro ⟨hg', hgC⟩
    rw [hC', Set.mem_smul_set_iff_inv_smul_mem] at hgC
    have e : (strR hC ⟨σ, hσG⟩)⁻¹ • strR hC ⟨σ * g.1, hg'⟩ = strR hC g := by
      rw [smul_eq_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rwa [e] at hgC
  · intro hg
    refine ⟨G.mul_mem hσG g.2, ?_⟩
    rw [hC', Set.mem_smul_set_iff_inv_smul_mem]
    have e : (strR hC ⟨σ, hσG⟩)⁻¹ • strR hC ⟨σ * g.1, G.mul_mem hσG g.2⟩ = strR hC g := by
      rw [smul_eq_mul, ← map_inv, ← map_mul]
      congr 1
      exact Subtype.ext (by simp)
    rw [e]
    exact hg

/-- **The group of a represented coset, inside `G_A`, is the beard's group.** -/
theorem toStab_eq_beard {A A' : Finset (Fin (N - n))} {x x' : Fin n → ℕ} {i : ℕ}
    {σ : Perm (Fin N)} {H : Subgroup (Perm (Fin N))}
    (hden : Denotes hC (σ • (H : Set (Perm (Fin N)))) (pairCoset φ A A' x x' i)) :
    toStab φ A H = (beard φ A x i).2 := by
  obtain ⟨-, -, -, hH⟩ := denotes_group hden
  ext s
  obtain ⟨g, hg⟩ := strR_surjective hC s.1
  rw [mem_toStab]
  constructor
  · intro h
    have := (hH g).1 (h g hg)
    rw [hg] at this
    obtain ⟨t, ht, hts⟩ := this
    rwa [show t = s from Subtype.ext hts] at ht
  · intro hs g' hg'
    rw [hH, hg']
    exact ⟨s, hs, rfl⟩

/-- A represented coset's group stabilizes the test set. -/
theorem stabsA_of_denotes (hφ : IsPhi hC φ) {al : List ℕ} {A' : Finset (Fin (N - n))}
    {x x' : Fin n → ℕ} {i : ℕ} {σ : Perm (Fin N)} {H : Subgroup (Perm (Fin N))}
    (hden : Denotes hC (σ • (H : Set (Perm (Fin N))))
      (pairCoset φ (finsetOf (N - n) al) A' x x' i)) : StabsA hC al H := by
  obtain ⟨-, hHG, -, hH⟩ := denotes_group hden
  refine ⟨hHG, fun g hg => ?_⟩
  obtain ⟨t, -, ht⟩ := (hH g).1 hg
  rw [← mem_stabA_strR hφ, ← ht]
  exact t.2

/-- The affected string positions, as positions of degree `N`. -/
def affSet (n : ℕ) (P : Set (Fin n)) : Set (Fin N) := {v | ∃ hv : v.val < n, ⟨v.val, hv⟩ ∈ P}

/-- **One step of the paired beard is a string-isomorphism coset on the affected points.** -/
theorem denotes_iso_succ {A A' : Finset (Fin (N - n))} {xs ys : Fin N → ℕ} {i : ℕ}
    {σ : Perm (Fin N)} {H : Subgroup (Perm (Fin N))}
    (hden : Denotes hC (σ • (H : Set (Perm (Fin N))))
      (pairCoset φ A A' (strOn hC.le xs) (strOn hC.le ys) i))
    (hgiant : IsGiantOn φ A (beard φ A (strOn hC.le xs) i).2) :
    Denotes hC (iso (affSet n (aff φ A (beard φ A (strOn hC.le xs) i).2)) σ H xs ys)
      (pairCoset φ A A' (strOn hC.le xs) (strOn hC.le ys) (i + 1)) := by
  intro g
  rw [pairCoset_succ]
  simp only [iso, Set.mem_ofPred_eq, Matches]
  rw [hden]
  constructor
  · rintro ⟨⟨hg, hgC⟩, hm⟩
    refine ⟨hg, hgC, fun u hu => ?_⟩
    rw [beardW_succ] at hu
    rcases hu with hu | ⟨-, hu⟩
    · exact hgC.2.2 u hu
    · have h := hm ⟨u.val, by have := hC.le; omega⟩ ⟨u.2, hu⟩
      simp only [strOn]
      rw [h]
      congr 1
  · rintro ⟨hg, hgC, hx⟩
    refine ⟨⟨hg, hgC⟩, fun v ⟨hv, hva⟩ => ?_⟩
    have h := hx ⟨v.val, hv⟩ (by rw [beardW_succ]; exact Or.inr ⟨hgiant, hva⟩)
    simp only [strOn] at h
    rw [← h]
    congr 1

/-- The affected points of a group in `G_A` are invariant under it. -/
theorem isInvariant_affSet {A : Finset (Fin (N - n))} {H : Subgroup (Perm (Fin N))}
    (hHG : H ≤ G) (hHA : ∀ g : G, (g : Perm (Fin N)) ∈ H → strR hC g ∈ stabA φ A) :
    IsInvariant H (affSet n (aff φ A (toStab φ A H))) := by
  intro h hh v ⟨hv, hva⟩
  have hhG := hHG hh
  set s : stabA φ A := ⟨strR hC ⟨h, hhG⟩, hHA ⟨h, hhG⟩ hh⟩
  have hs : s ∈ toStab φ A H := (mem_toStab_strR _ _).2 hh
  have hmem := smul_mem_aff φ hs hva
  have hlt : (h v).val < n := hC.str h hhG v hv
  refine ⟨hlt, ?_⟩
  have e : s • (⟨v.val, hv⟩ : Fin n) = ⟨(h v).val, hlt⟩ := by
    apply Fin.ext
    show ((strR hC ⟨h, hhG⟩ • (⟨v.val, hv⟩ : Fin n) : Fin n) : ℕ) = _
    rw [strR_smul_val]
  rwa [e] at hmem

/-! ### Generators of the kernel -/

section PSGens

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The pointwise stabilizer computed by `pointStabsProg` has at most `s` generators. -/
theorem pointStabs_gens_le (hO : MeetsContractOn DV stabOps X.O) {M s : ℕ}
    {G₀ : Subgroup (Perm (Fin M))} (B : BackendBounds X DV M s G₀) :
    ∀ (ps : List ℕ) (acc : GroupData D.denote × List PermData), (∀ u ∈ ps, u < M) →
      acc.1.1 = M → GroupValid DV M acc.1.2.1 acc.1.2.2 → acc.1.2.1.length ≤ s →
      GensData.denote M acc.1.2.1 ≤ G₀ →
      (ps.foldl (psStep X.O) acc).1.2.1.length ≤ s ∧
        GensData.denote M (ps.foldl (psStep X.O) acc).1.2.1 ≤ G₀ := by
  intro ps
  induction ps with
  | nil => intro acc _ _ _ h₁ h₂; exact ⟨h₁, h₂⟩
  | cons u ps ih =>
    intro acc hps hdeg hv hlen hle
    obtain ⟨⟨M', ks, e⟩, reps⟩ := acc
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
    rw [List.foldl_cons]
    have hstep : psStep X.O ((M'', ks, e), reps) u =
        ((M'', ks', e'), prodReps reps (X.O.run GroupOp.orbitTransversal ((M'', ks, e), u))) := by
      simp only [psStep]
      rw [hS]
    rw [hstep]
    refine ih _ (fun v hv => hps v (List.mem_cons_of_mem _ hv)) rfl hv' hout ?_
    change GensData.denote M'' ks' ≤ G₀
    rw [hden hu]
    exact inf_le_left.trans hle

end PSGens

/-! ### The step as a program -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The sub-solver inside a branch: the orbits of the kernel one after the other. -/
def branchSub (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (os : var (.list (.list .nat))) (J : var (Ty.inst D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .snd J) fun wc => .bind (.op1 .snd wc) fun c => seqProg sub xy c os

/-- **One step of the paired beard**: `none` if `ψ_A(H)` is not a giant; otherwise the affected
points and the answer on them in `σ • H`. -/
def beardStepProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (pos : var (.array .nat)) (pA : var (.list .nat)) (xy : var Ty.strs)
    (σ : var Ty.perm) (H : var (Ty.group D)) :
    Prog (groupSig D) rec var (.option (.prod (.list .nat) (Ty.answer D))) :=
  .bind (.op1 .snd H) fun hd => .bind (.op1 .fst hd) fun hgs =>
  .bind (giantAProg pos pA hgs) fun g =>
  .ite g
    (.bind (affProg n pos pA H) fun af =>
      .bind (kerAProg H pA) fun kr => .bind (.op1 .fst kr) fun K => .bind (.op1 .snd kr) fun rs =>
      .bind (.op1 .fst H) fun M => .bind (mkWindow M af) fun w =>
      .bind (kerOrbitsProg K w) fun os =>
      .bind (branchProg (fun J => branchSub sub xy os J) xy w σ K rs) fun ans =>
      .bind (.op2 .pair af ans) fun r => .op1 .some r)
    (.op0 .none)

end Programs

/-! ### The specification of the step -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The instances the step passes to the sub-solver: the strings `xy`, valid, of degree `N`, a
window of string positions with at most `n / k` points, inside `G`, with at most `sIn`
generators. -/
def StepSubP (G : Subgroup (Perm (Fin N))) (xy : StrData × StrData) (n k sIn : ℕ)
    (I : InstData D) : Prop :=
  I.1 = xy ∧ I.Valid DV ∧ I.degree = N ∧ (∀ u ∈ I.2.1.1, u < n) ∧ k * I.2.1.1.length ≤ n ∧
    GensData.denote N I.2.2.2.gens ≤ G ∧ I.2.2.2.gens.length ≤ sIn

/-- The operations used by the step. -/
def stepOps (op : GroupOp) : Prop :=
  op = .stabilizer ∨ op = .orbitTransversal ∨ op = .orbits ∨ op = .generate

/-- The cost of the sequential solution inside one branch. -/
def seqBound (N n Cb : ℕ) : ℕ := n * (Cb + 2 * N + 18) + 3

theorem giantACost_mono {k s₁ s₂ : ℕ} (h : s₁ ≤ s₂) (Bg Bo Bs : ℕ) :
    giantACost k s₁ Bg Bo Bs ≤ giantACost k s₂ Bg Bo Bs := by
  simp only [giantACost]
  have := Nat.mul_le_mul_right (12 * k + 12) h
  omega

/-- **The cost of one step**: the giant test, the affected points, the kernel, the window and
its orbits, and `k!` branches of at most `n` sub-calls of cost `Cb` each. -/
def beardStepCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb : ℕ) : ℕ :=
  giantACost k s Bgen' Borb' Bstab' + affCost n k s Bstab Bgen' Borb' Bstab' +
    kerACost N k Btr Bstab + 2 * N + 5 * n + Borb +
    k.factorial * (24 * N + seqBound N n Cb + s + 45) + Bgen + 50

/-- The part of a step's cost without the factor `k!`. -/
def stepPoly₀ (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen : ℕ) : ℕ :=
  giantACost k s Bgen' Borb' Bstab' + affCost n k s Bstab Bgen' Borb' Bstab' + 2 * N + 7 +
    k * (Btr + Bstab + 8) + 2 * N + 5 * n + Borb + Bgen + 50

/-- The part of a step's cost multiplied by `k!` (besides the sub-solver's). -/
def stepPoly₁ (N n k s : ℕ) : ℕ :=
  k * (k * (12 * N + 18) + 4) + 24 * N + n * (2 * N + 18) + 3 + s + 45

/-- **The polynomial of one step**: a step costs at most `k!` times it, plus `k! · n` sub-calls. -/
def stepPoly (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen : ℕ) : ℕ :=
  stepPoly₀ N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen + stepPoly₁ N n k s

theorem beardStepCost_eq (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb : ℕ) :
    beardStepCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb =
      stepPoly₀ N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen +
        k.factorial * stepPoly₁ N n k s + k.factorial * (n * Cb) := by
  simp only [beardStepCost, kerACost, seqBound, stepPoly₀, stepPoly₁]
  ring

/-- **A step costs at most a polynomial times `k!`**, plus at most `k! · n` sub-calls of cost
`Cb` each. -/
theorem beardStepCost_le (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb : ℕ) :
    beardStepCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb ≤
      k.factorial * stepPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen +
        k.factorial * (n * Cb) := by
  rw [beardStepCost_eq, stepPoly, Nat.mul_add]
  have := Nat.le_mul_of_pos_left (stepPoly₀ N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen)
    (Nat.factorial_pos k)
  omega

theorem cp_length_le_sum {os : List (List ℕ)} (hne : ∀ o ∈ os, o ≠ []) :
    os.length ≤ (os.map List.length).sum := by
  induction os with
  | nil => simp
  | cons o os ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 : 1 ≤ o.length := List.length_pos_iff.2 (hne o List.mem_cons_self)
    have h2 := ih fun o' ho' => hne o' (List.mem_cons_of_mem _ ho')
    omega

theorem cp_sum_seqCost (N Cb : ℕ) (os : List (List ℕ)) :
    (os.map (seqCost N fun _ => Cb)).sum =
      os.length * (Cb + 2 * N + 13) + 5 * (os.map List.length).sum := by
  induction os with
  | nil => simp
  | cons o os ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, seqCost]
    ring

theorem cp_isLeftCover_map {M : ℕ} {G K : Subgroup (Perm (Fin M))} {rs : List PermData}
    (h : IsLeftCover G K fun i : Fin rs.length => PermData.denote M (rs.get i)) :
    IsLeftCover G K fun i : Fin (rs.map (PermData.denote M)).length =>
      (rs.map (PermData.denote M)).get i := by
  refine ⟨fun i => ?_, fun g hg => ?_⟩
  · rw [List.get_eq_getElem, List.getElem_map]
    exact h.mem ⟨i, by simpa using i.2⟩
  · obtain ⟨i, hi⟩ := h.cover g hg
    refine ⟨⟨i, by simp⟩, ?_⟩
    rw [List.get_eq_getElem, List.getElem_map]
    exact hi

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **One step of the paired beard.** If `σ • ⟨hs⟩` represents the paired beard's coset `C_i`,
the step reports `none` exactly when `ψ_A(H_i)` is not a giant (the beard has stopped);
otherwise it returns the affected points of `H_i` and a correct answer on them in `σ • ⟨hs⟩`,
which represents `C_{i+1}` (and is `none` exactly when `C_{i+1}` is empty). -/
theorem RunsWithin.beardStepProg (hO : MeetsContractOn DV stepOps X.O)
    (hPre : ∀ op x, stepOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (h5 : 5 ≤ al.length)
    {A' : Finset (Fin (N - n))} {xy : StrData × StrData} {i : ℕ} {σd : PermData}
    (hσd : σd.Valid N) {hs : GensData} {e : D.denote} (hHv : GroupValid DV N hs e)
    (hden : Denotes hC (PermData.denote N σd • (GensData.denote N hs : Set (Perm (Fin N))))
      (pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.2.denote N)) i))
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    (hlen : hs.length ≤ s) (hGG₀ : G ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) {Bgen : ℕ}
    (hBg : ∀ gs : GensData, GensData.AllValid N gs → gs.length ≤ al.length.factorial * (s + 1) →
      GensData.denote N gs ≤ G →
        X.B.call GroupOp.generate (N, gs) (X.O.run GroupOp.generate (N, gs)) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub (StepSubP (DV := DV) G xy n al.length s) (fun _ => Cb) s) :
    ∃ res : Option (List ℕ × AnswerData D),
      RunsWithin X body (CertProg.beardStepProg sub n (WinData.pos N (winA N n al))
          (winA N n al).1 xy σd (N, hs, e)) res
        (beardStepCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb) ∧
      (res = none ↔ ¬ IsGiantOn φ (finsetOf (N - n) al)
        (beard φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N)) i).2) ∧
      ∀ af ans, res = some (af, ans) → af.Nodup ∧
        (∀ j, j ∈ af ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈ aff φ (finsetOf (N - n) al)
          (beard φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N)) i).2) ∧
        AnsOK DV N (ptsSet N af) (PermData.denote N σd) (GensData.denote N hs)
          (xy.1.denote N) (xy.2.denote N) ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s ∧
          Denotes hC (PermData.denote N c.1 • (GensData.denote N c.2.gens : Set (Perm (Fin N))))
            (pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
              (strOn hC.le (xy.2.denote N)) (i + 1))) ∧
        (ans = none → pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
          (strOn hC.le (xy.2.denote N)) (i + 1) = ∅) := by
  have hnN := hC.le
  set A := finsetOf (N - n) al with hA
  set x := strOn hC.le (xy.1.denote N) with hx
  set x' := strOn hC.le (xy.2.denote N) with hx'
  obtain ⟨hσG, hHG, -, -⟩ := denotes_group hden
  have htoStab := toStab_eq_beard hden
  have hstabs := stabsA_of_denotes hφ hden
  have hk : (winA N n al).1.length = al.length := length_winA al
  -- the operations
  have hOg : MeetsContractOn DV giantAOps X.O := fun op x hop hx =>
    hO op x (by rcases hop with h | h | h <;> simp [stepOps, h]) hx
  have hPg : ∀ op x, giantAOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rcases hop with h | h | h <;> simp [stepOps, h]) hx
  have hOa : MeetsContractOn DV affOps X.O := fun op x hop hx =>
    hO op x (by rcases hop with h | h | h <;> simp [stepOps, h]) hx
  have hPa : ∀ op x, affOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rcases hop with h | h | h <;> simp [stepOps, h]) hx
  have hOs : MeetsContractOn DV stabOps X.O := fun op x hop hx =>
    hO op x (by rcases hop with h | h <;> simp [stepOps, h]) hx
  have hPs : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rcases hop with h | h <;> simp [stepOps, h]) hx
  have hOo : MeetsContractOn DV kerOrbitsOps X.O := fun op x hop hx =>
    hO op x (by rw [kerOrbitsOps] at hop; simp [stepOps, hop]) hx
  have hPo : ∀ op x, kerOrbitsOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rw [kerOrbitsOps] at hop; simp [stepOps, hop]) hx
  have hOgen : MeetsContractOn DV (· = .generate) X.O := fun op x hop hx =>
    hO op x (by simp [stepOps, hop]) hx
  have hPgen : ∀ x, GroupPre DV .generate x → X.Pre .generate x := fun x hx =>
    hPre .generate x (by simp [stepOps]) hx
  -- the giant test
  obtain ⟨hgrun, hgiff⟩ := RunsWithin.giantAProg (X := X) (body := body) hOg hPg
    (winA_valid hal halm) hHv.1 (isInvariant_winA hstabs) Bk (hlen.trans hsk)
  have hgiff' := giantAModel_iff hφ hal halm hstabs hgiff
  rw [htoStab] at hgiff'
  replace hgrun := hgrun.mono ((le_of_eq (congrArg (fun k => giantACost k hs.length Bk.Bgen
    Bk.Borb Bk.Bstab) hk)).trans (giantACost_mono hlen _ _ _))
  by_cases hgiant : IsGiantOn φ A (beard φ A x i).2
  swap
  · -- not a giant: the step stops
    have hg : giantAModel X.O (WinData.pos N (winA N n al)) (winA N n al).1 hs = false := by
      rw [← Bool.not_eq_true, hgiff']
      exact hgiant
    refine ⟨none, ?_, ⟨fun _ => hgiant, fun _ => rfl⟩, fun _ _ h => by cases h⟩
    apply RunsWithin.mono
    case h =>
      unfold CertProg.beardStepProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hgrun
      exact Sims.RunsWithin.ite_neg hg (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost, beardStepCost]
      omega
  -- a giant: the affected points
  have hg : giantAModel X.O (WinData.pos N (winA N n al)) (winA N n al).1 hs = true :=
    hgiff'.2 hgiant
  obtain ⟨hafrun, hafiff⟩ := RunsWithin.affProg (X := X) (body := body) hOa hPa hφ hal halm hHv
    hstabs B hlen (hHG.trans hGG₀) Bk hsk
  replace hafrun := hafrun.mono (le_of_eq (congrArg (fun k => affCost n k s B.Bstab Bk.Bgen Bk.Borb
    Bk.Bstab) hk))
  set af := affModel X.O n (WinData.pos N (winA N n al)) (winA N n al).1 (N, hs, e) with haf
  have hafnd : af.Nodup := affModel_nodup _ _ _ _ _
  have hafiff' : ∀ j, j ∈ af ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈ aff φ A (beard φ A x i).2 := by
    intro j
    rw [hafiff, htoStab]
  have hafn : ∀ j ∈ af, j < n := fun j hj => ((hafiff j).1 hj).1
  have haflen : af.length ≤ n := by
    have := (List.subperm_of_subset hafnd (fun j hj => List.mem_range.2 (hafn j hj))).length_le
    simpa using this
  -- the kernel
  obtain ⟨hkrun, hkN, hkv, hkden, hkrv, hkcov, hkcard⟩ := RunsWithin.kerAProg (X := X)
    (body := body) hOs hPs hal halm hHv hstabs B hlen (hHG.trans hGG₀)
  obtain ⟨hkgens, hkG₀⟩ := pointStabs_gens_le hOs B (posA n al) ((N, hs, e), [PermData.one N])
    (fun u hu => by obtain ⟨x, hx, rfl⟩ := mem_posA.1 hu; have := halm x hx; omega) rfl hHv
    hlen (hHG.trans hGG₀)
  rcases hkr : pointStabsModel X.O (N, hs, e) (posA n al) with ⟨⟨N', ks, e'⟩, rs⟩
  rw [hkr] at hkrun hkN hkv hkden hkrv hkcov hkcard
  have hkgens' : ks.length ≤ s := by
    have := hkgens
    simp only [pointStabsModel] at hkr
    rw [hkr] at this
    exact this
  change N' = N at hkN
  subst hkN
  have hKH : GensData.denote N' ks ≤ GensData.denote N' hs := by
    rw [hkden]
    exact fun g hg => hg.1
  -- the window of the affected points
  set w := WinData.ofPoints N' af with hw_def
  have hw : w.Valid N' := WinData.valid_ofPoints hafnd fun j hj => by
    have := hafn j hj; omega
  have hwden : w.denote N' = affSet n (aff φ A (toStab φ A (GensData.denote N' hs))) := by
    ext v
    rw [WinData.denote_ofPoints]
    exact hafiff v.val
  have hwinv : IsInvariant (GensData.denote N' hs) (w.denote N') := by
    rw [hwden]
    exact isInvariant_affSet hHG fun g hg => (mem_stabA_strR hφ g).2 (hstabs.2 g hg)
  -- the orbits
  obtain ⟨horun, hopart⟩ := RunsWithin.kerOrbitsProg (X := X) (body := body) hOo hPo hkv hw
    (hwinv.mono hKH) B hkgens' (hKH.trans (hHG.trans hGG₀))
  set os : List (List ℕ) := X.O.run GroupOp.orbits ((N', ks, e'), w) with hos
  obtain ⟨hosin, hosu⟩ := seqInputs_of_isOrbitPartition hw hopart
  have hgiant' : IsGiantOn φ A (toStab φ A (GensData.denote N' hs)) := by
    rw [htoStab]; exact hgiant
  have hbound : ∀ o ∈ os, al.length * o.length ≤ n := fun o ho =>
    kerOrbit_length_le hφ hstabs h5 hal halm hgiant' hw (fun j hj => (hafiff j).1 hj)
      (by rw [← hkden]; exact hopart) ho
  have hflat : (os.map List.length).sum = af.length := by
    have := hopart.1.length_eq
    rw [List.length_flatten] at this
    rw [this]
    rfl
  have hoslen : os.length ≤ n := by
    have := cp_length_le_sum fun o ho => (hopart.2 o ho).1
    omega
  -- the branches
  have hinner : SubSolves X body DV (fun J => CertProg.branchSub sub xy os J)
      (fun I => I.1 = xy ∧ I.2.1 = w ∧ I.2.2.2 = (N', ks, e') ∧
        (∃ r ∈ rs, I.2.2.1 = σd.mul r) ∧ I.Valid DV) (fun _ => seqBound N' n Cb) s := by
    rintro ⟨xy', w', τ, Gd⟩ ⟨hI1, hI2, hI3, -, hIv⟩
    simp only at hI1 hI2 hI3
    subst xy' w' Gd
    have hseqsub : SeqSub X body DV sub xy N' os (fun _ => Cb) s (max s ks.length)
        (GensData.denote N' ks) := by
      rintro I ⟨hJ1, hJv, hJdeg, ⟨o, ho, hJw⟩, hJlen, hJle⟩
      refine hsub I ⟨hJ1, hJv, hJdeg, ?_, ?_, ?_, hJlen.trans (max_le le_rfl hkgens')⟩
      · rw [hJw, WinData.ofPoints_fst]
        intro u hu
        exact hafn u (hopart.1.subset (List.mem_flatten.2 ⟨o, ho, hu⟩))
      · rw [hJw, WinData.ofPoints_fst]
        exact hbound o ho
      · exact hJle.trans (hKH.trans hHG)
    obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.seqProg (σd := τ) (Gd := (N', ks, e'))
      (hn := rfl) hIv.rep hkv hosin hseqsub
    refine ⟨ans, ?_, ?_, fun c hc => (hgen c hc).trans (max_le le_rfl hkgens')⟩
    · apply RunsWithin.mono
      case h =>
        unfold CertProg.branchSub
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact hrun
      case hc =>
        simp only [Prim.cost, seqBound, GroupData.degree]
        rw [cp_sum_seqCost]
        have h1 := Nat.mul_le_mul_right (Cb + 2 * N' + 13) hoslen
        have h2 : n * (Cb + 2 * N' + 18) = n * (Cb + 2 * N' + 13) + 5 * n := by ring
        omega
    · show AnsOK DV N' (w.denote N') (PermData.denote N' τ) (GensData.denote N' ks) _ _ ans
      rw [← hosu]
      exact hok
  obtain ⟨ans, hbrun, hbok, hbgen⟩ := RunsWithin.branchProg (X := X) (body := body)
    (sub := fun J => CertProg.branchSub sub xy os J) (G := GensData.denote N' hs) hOgen hPgen
    hw hσd hkv hKH hwinv hkrv (cp_isLeftCover_map hkcov) hinner (fun gs hgs hgl hgle =>
      hBg gs hgs (hgl.trans (Nat.mul_le_mul_right _ hkcard)) (hgle.trans hHG))
  have hansgen : ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s :=
    hbgen s fun gs hgs hle => B.genOut gs hgs (hle.trans (hHG.trans hGG₀))
  refine ⟨some (af, ans), ?_, ⟨fun h => absurd h (Option.some_ne_none _),
    fun h => absurd hgiant h⟩, ?_⟩
  · apply RunsWithin.mono
    case h =>
      unfold CertProg.beardStepProg
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hgrun
      run_with Sims.RunsWithin.ite_pos hg _
      run_step hafrun
      run_step hkrun
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      simp only [Prim.eval]
      run_step (RunsWithin.mkWindow N' af)
      run_step horun
      run_step hbrun
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, beardStepCost]
      have h1 : rs.length * (24 * N' + seqBound N' n Cb + s + 45) ≤
          al.length.factorial * (24 * N' + seqBound N' n Cb + s + 45) :=
        Nat.mul_le_mul_right _ hkcard
      omega
  · rintro af' ans' hres
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hres)
    have hiso : Denotes hC (iso (w.denote N') (PermData.denote N' σd) (GensData.denote N' hs)
        (xy.1.denote N') (xy.2.denote N')) (pairCoset φ A A' x x' (i + 1)) := by
      rw [hwden, htoStab]
      exact denotes_iso_succ hden hgiant
    refine ⟨hafnd, hafiff', hbok, fun c hc => ⟨hansgen c hc, ?_⟩, fun hc => ?_⟩
    · obtain ⟨τ, Kd⟩ := c
      subst hc
      have heq : PermData.denote N' τ • (GensData.denote N' Kd.gens : Set (Perm (Fin N'))) =
          iso (w.denote N') (PermData.denote N' σd) (GensData.denote N' hs) (xy.1.denote N')
            (xy.2.denote N') := hbok.2.2.2
      intro g
      show g ∈ PermData.denote N' τ • (GensData.denote N' Kd.gens : Set (Perm (Fin N'))) ↔ _
      rw [heq]
      exact hiso g
    · subst hc
      have hempty : iso (w.denote N') (PermData.denote N' σd) (GensData.denote N' hs)
          (xy.1.denote N') (xy.2.denote N') = ∅ := hbok
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hcC
      obtain ⟨g, rfl⟩ := strR_surjective hC c
      have := (hiso g.1).2 ⟨g.2, hcC⟩
      rw [hempty] at this
      exact this

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_branchSub {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {os₁ : var₁ (.list (.list .nat))} {os₂ : var₂ (.list (.list .nat))}
    {J₁ : var₁ (Ty.inst D)} {J₂ : var₂ (Ty.inst D)} (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hos : ⟨.list (.list .nat), os₁, os₂⟩ ∈ Γ) (hJ : ⟨Ty.inst D, J₁, J₂⟩ ∈ Γ) :
    Prog.Wf r Γ (branchSub sub₁ xy₁ os₁ J₁) (branchSub sub₂ xy₂ os₂ J₂) := by
  unfold branchSub
  exact .bind (.prim _ (.cons hJ .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => wf_seqProg (hsub.mono fun _ h => by simp [h]) (by simp [hxy]) (by simp)
      (by simp [hos])

theorem wf_beardStepProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm}
    {H₁ : var₁ (Ty.group D)} {H₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) :
    Prog.Wf r Γ (beardStepProg sub₁ n₁ pos₁ pA₁ xy₁ σ₁ H₁)
      (beardStepProg sub₂ n₂ pos₂ pA₂ xy₂ σ₂ H₂) := by
  unfold beardStepProg
  refine .bind (.prim _ (.cons hH .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_giantAProg (by simp [hpos]) (by simp [hpA]) (by simp)) fun _ _ => ?_
  refine .ite (by simp) ?_ (.prim _ .nil)
  refine .bind (wf_affProg (by simp [hn]) (by simp [hpos]) (by simp [hpA]) (by simp [hH]))
    fun _ _ => ?_
  refine .bind (wf_kerAProg (by simp [hH]) (by simp [hpA])) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hH]) .nil)) fun _ _ => ?_
  refine .bind (wf_mkWindow (by simp) (by simp)) fun _ _ => ?_
  refine .bind (wf_kerOrbitsProg (by simp) (by simp)) fun _ _ => ?_
  refine .bind (wf_branchProg (fun Γ' hΓ J₁ J₂ hJ => wf_branchSub (hsub.mono
      (List.Subset.trans (fun _ h => by simp [h]) hΓ)) (hΓ (by simp [hxy])) (hΓ (by simp)) hJ)
    (by simp [hxy]) (by simp) (by simp [hσ]) (by simp) (by simp)) fun _ _ => ?_
  exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) .nil)

end Wf

end GraphIso.CertProg
