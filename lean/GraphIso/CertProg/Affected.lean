module

public import GraphIso.CertProg.TestSets

/-!
# Affected points

Stage 14e, item 3 (`PLAN-14.md` §9). For a group `H ≤ G_A` (generators of degree `N`) and a
test set `A`, `affProg` tests every string position `j < n`: the backend's stabilizer `H_j`,
restricted to the positions of `A`, and the giant test (`giantAProg`). It returns the positions
whose test fails, in increasing order.

`RunsWithin.affProg`: the result is exactly milestone 13's `aff φ A H` (Babai, Def. 10.1.4), with
`H` seen inside `G_A` through `toStab`.
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates Cost
  GraphIso.Programs GraphIso.Solver

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The test of one position: is `ψ_A(H_j)` not a giant? -/
def affTestProg (pos : var (.array .nat)) (pA : var (.list .nat)) (H : var (Ty.group D))
    (j : var .nat) : Prog (groupSig D) rec var .bool :=
  .bind (.op2 .pair H j) fun hj => .bind (Prog.call (S := groupSig D) GroupOp.stabilizer hj)
    fun Hj => .bind (.op1 .snd Hj) fun d => .bind (.op1 .fst d) fun gs =>
  .bind (giantAProg pos pA gs) fun g => .op1 .not g

/-- **The affected string positions** `j < n`. -/
def affProg (n : var .nat) (pos : var (.array .nat)) (pA : var (.list .nat))
    (H : var (Ty.group D)) : Prog (groupSig D) rec var (.list .nat) :=
  .bind (.op1 .range n) fun js => Toolkit.filterList js fun j => affTestProg pos pA H j

end Programs

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The model of `affProg`. -/
def affModel (O : Oracle (groupSig D)) (n : ℕ) (pos : Array ℕ) (pA : List ℕ)
    (H : GroupData D.denote) : List ℕ :=
  (List.range n).filter fun j => !giantAModel O pos pA (O.run GroupOp.stabilizer (H, j)).2.1

/-- The operations used by `affProg`. -/
def affOps (op : GroupOp) : Prop :=
  op = .stabilizer ∨ op = .generate ∨ op = .orbits

/-- The cost of `affProg`: `n` positions, `k` points in `A`, `s` generators of the stabilizers,
the stabilizer charge at degree `N` and the charges at degree `k`. -/
def affCost (n k s Bstab Bgen' Borb' Bstab' : ℕ) : ℕ :=
  n * (Bstab + giantACost k s Bgen' Borb' Bstab' + 12) + n + 5

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- **The affected points.** For a group `H = ⟨hs⟩ ≤ G` whose base action stabilizes the test set
`A`, the program returns the string positions affected by `H` in milestone 13's sense. -/
theorem RunsWithin.affProg (hO : MeetsContractOn DV affOps X.O)
    (hPre : ∀ op x, affOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) {hs : GensData}
    {e : D.denote} (hHv : GroupValid DV N hs e) (hH : StabsA hC al (GensData.denote N hs))
    {s : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    (hlen : hs.length ≤ s) (hG₀ : GensData.denote N hs ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) :
    RunsWithin X body
        (CertProg.affProg n (WinData.pos N (winA N n al)) (winA N n al).1 (N, hs, e))
        (affModel X.O n (WinData.pos N (winA N n al)) (winA N n al).1 (N, hs, e))
        (affCost n (winA N n al).1.length s B.Bstab Bk.Bgen Bk.Borb Bk.Bstab) ∧
      ∀ j, j ∈ affModel X.O n (WinData.pos N (winA N n al)) (winA N n al).1 (N, hs, e) ↔
        ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈
          aff φ (finsetOf (N - n) al) (toStab φ (finsetOf (N - n) al) (GensData.denote N hs)) := by
  have hnN := hC.le
  have hOs : MeetsContractOn DV (· = .stabilizer) X.O := fun op x hop hx =>
    hO op x (Or.inl hop) hx
  have hOg : MeetsContractOn DV giantAOps X.O := fun op x hop hx =>
    hO op x (by rcases hop with h | h | h <;> simp [affOps, h]) hx
  have hPg : ∀ op x, giantAOps op → GroupPre DV op x → X.Pre op x := fun op x hop hx =>
    hPre op x (by rcases hop with h | h | h <;> simp [affOps, h]) hx
  have hwv := winA_valid (N := N) (n := n) hal halm
  -- one position
  have key : ∀ j < n, ∃ cj,
      RunsWithin X body
        (CertProg.affTestProg (WinData.pos N (winA N n al)) (winA N n al).1 (N, hs, e) j)
        (!giantAModel X.O (WinData.pos N (winA N n al)) (winA N n al).1
          (X.O.run GroupOp.stabilizer ((N, hs, e), j)).2.1) cj ∧
        cj ≤ B.Bstab + giantACost (winA N n al).1.length s Bk.Bgen Bk.Borb Bk.Bstab + 8 ∧
        ((!giantAModel X.O (WinData.pos N (winA N n al)) (winA N n al).1
          (X.O.run GroupOp.stabilizer ((N, hs, e), j)).2.1) = true ↔
          ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈ aff φ (finsetOf (N - n) al)
            (toStab φ (finsetOf (N - n) al) (GensData.denote N hs))) := by
    intro j hj
    have hjN : j < N := by omega
    have hpre : GroupPre DV .stabilizer ((N, hs, e), j) := ⟨hHv, hjN⟩
    have hpost := hOs .stabilizer _ rfl hpre
    have hBs := B.stabilizer hs e j hlen hG₀ hpre
    have hout := B.stabOut hs e j hG₀ hpre
    rcases hS : X.O.run GroupOp.stabilizer ((N, hs, e), j) with ⟨N', ks, e'⟩
    rw [hS] at hpost hBs hout
    obtain ⟨hN', hv', hden⟩ := hpost
    change N' = N at hN'
    subst hN'
    change ks.length ≤ s at hout
    have hden' : GensData.denote N' ks = pointStab (GensData.denote N' hs) ⟨j, hjN⟩ := hden hjN
    have hHj : StabsA hC al (GensData.denote N' ks) := by
      refine ⟨fun g hg => hH.1 ?_, fun g hg => hH.2 g ?_⟩
      · rw [hden'] at hg
        exact (mem_pointStab.1 hg).1
      · rw [hden'] at hg
        exact (mem_pointStab.1 hg).1
    have hWj := isInvariant_winA hHj
    obtain ⟨hrun, hiff⟩ := RunsWithin.giantAProg (X := X) (body := body) hOg hPg hwv
      hv'.1 hWj Bk (hout.trans hsk)
    refine ⟨_, ?_, le_refl _, ?_⟩
    · apply RunsWithin.mono
      case h =>
        unfold CertProg.affTestProg
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hpre))
        simp only [Prim.eval]
        rw [hS]
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hrun
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        have hBs' : X.B.call GroupOp.stabilizer ((N', hs, e), j)
            (X.O.run GroupOp.stabilizer ((N', hs, e), j)) ≤ B.Bstab := by rw [hS]; exact hBs
        have hgc : giantACost (winA N' n al).1.length ks.length Bk.Bgen Bk.Borb Bk.Bstab ≤
            giantACost (winA N' n al).1.length s Bk.Bgen Bk.Borb Bk.Bstab := by
          simp only [giantACost]
          have := Nat.mul_le_mul_right (12 * (winA N' n al).1.length + 12) hout
          omega
        simp only [Prim.cost, Prim.eval]
        omega
    · rw [Bool.not_eq_true', ← Bool.not_eq_true]
      show ¬ (giantAModel X.O (WinData.pos N' (winA N' n al)) (winA N' n al).1 ks = true) ↔ _
      rw [giantAModel_iff hφ hal halm hHj hiff, hden',
        show toStab φ (finsetOf (N' - n) al) (pointStab (GensData.denote N' hs) ⟨j, hjN⟩) =
          toStab φ (finsetOf (N' - n) al) (GensData.denote N' hs) ⊓
            stabilizer (stabA φ (finsetOf (N' - n) al)) (⟨j, hj⟩ : Fin n) from
          toStab_pointStab ⟨j, hjN⟩ hj]
      exact ⟨fun h => ⟨hj, h⟩, fun ⟨_, h⟩ => h⟩
  choose cj hrun hcj hiff using key
  refine ⟨?_, fun j => ?_⟩
  · have hf := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := List.range n)
      (P := fun j => !giantAModel X.O (WinData.pos N (winA N n al)) (winA N n al).1
        (X.O.run GroupOp.stabilizer ((N, hs, e), j)).2.1)
      (c := B.Bstab + giantACost (winA N n al).1.length s Bk.Bgen Bk.Borb Bk.Bstab + 8)
      (p := fun j => CertProg.affTestProg (WinData.pos N (winA N n al)) (winA N n al).1
        (N, hs, e) j) fun j hj => (hrun j (List.mem_range.1 hj)).mono (hcj j _)
    apply RunsWithin.mono
    case h =>
      unfold CertProg.affProg
      run_step (RunsWithin.prim _ _)
      exact hf
    case hc =>
      simp only [Prim.cost, Args.head, List.length_range, affCost]
      ring_nf
      omega
  · simp only [affModel, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hj, h⟩
      exact (hiff j hj).1 h
    · rintro ⟨hj, h⟩
      exact ⟨hj, (hiff j hj).2 ⟨hj, h⟩⟩

theorem affModel_nodup (O : Oracle (groupSig D)) (n : ℕ) (pos : Array ℕ) (pA : List ℕ)
    (H : GroupData D.denote) : (affModel O n pos pA H).Nodup :=
  List.nodup_range.filter _

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_affTestProg {pos₁ : var₁ (.array .nat)} {pos₂ : var₂ (.array .nat)}
    {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)} {H₁ : var₁ (Ty.group D)}
    {H₂ : var₂ (Ty.group D)} {j₁ : var₁ .nat} {j₂ : var₂ .nat}
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (affTestProg pos₁ pA₁ H₁ j₁) (affTestProg pos₂ pA₂ H₂ j₂) := by
  unfold affTestProg
  refine .bind (.prim _ (.cons hH (.cons hj .nil))) fun _ _ => ?_
  refine .bind (by prog_wf) fun _ _ => ?_
  refine .bind (.prim _ (.cons (.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  exact .bind (wf_giantAProg (by simp [hpos]) (by simp [hpA]) (by simp)) fun _ _ =>
    .prim _ (.cons (by simp) .nil)

theorem wf_affProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)}
    {H₁ : var₁ (Ty.group D)} {H₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ) (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ)
    (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (affProg n₁ pos₁ pA₁ H₁) (affProg n₂ pos₂ pA₂ H₂) := by
  unfold affProg
  exact .bind (.prim _ (.cons hn .nil)) fun _ _ => Toolkit.wf_filterList (by simp)
    fun _ hΓ _ _ hj => wf_affTestProg (hΓ (by simp [hpos])) (hΓ (by simp [hpA]))
      (hΓ (by simp [hH])) hj

end Wf

end GraphIso.CertProg
