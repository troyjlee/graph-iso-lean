module

public import GraphIso.CertProg.Step
public import GraphIso.CertProg.Transporter

/-!
# The paired beard as a loop, the certificate and the comparison

Stage 14e, items 5–6 (`PLAN-14.md` §9).

* `pairLoopProg`: at most `n` rounds of `beardStepProg` (a fold over `range n`), stopping when
  `ψ_A(H_i)` is not a giant (then the beard is constant from step `i` on: `beard_add_of_fst`,
  `pairCoset_stable`) or when the coset becomes empty (then it stays empty:
  `pairCoset_antitone`). It returns the window list and the final coset.
  `RunsWithin.pairLoopProg`: if the input coset represents `pairCoset … 0`, the result represents
  `pairCoset … n` (`none` exactly when it is empty), and the window list is `beardW` when the
  coset is not empty.
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates Cost
  GraphIso.Programs GraphIso.Solver

/-! ### The paired beard after it stops -/

section Stable

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*}

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
theorem pairCoset_antitone (A A' : Finset Γ) (x x' : Ω → L) {i j : ℕ} (h : i ≤ j) :
    pairCoset φ A A' x x' j ⊆ pairCoset φ A A' x x' i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    intro g hg
    rw [← add_assoc, pairCoset_succ] at hg
    exact ih (by omega) hg.1

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- **If the window does not grow, the paired beard is constant.** -/
theorem pairCoset_stable (A A' : Finset Γ) (x x' : Ω → L) {i : ℕ}
    (hW : (beard φ A x (i + 1)).1 = (beard φ A x i).1) (m : ℕ) :
    pairCoset φ A A' x x' (i + m) = pairCoset φ A A' x x' i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← add_assoc, pairCoset_succ, ih]
    ext g
    refine ⟨fun h => h.1, fun h => ⟨h, fun u hu => ?_⟩⟩
    have hb := beard_add_of_fst φ A x hW (m + 1)
    rw [← add_assoc] at hb
    rw [hb] at hu
    exact h.2.2 u hu

omit [Fintype Ω] [DecidableEq Ω] [Fintype Γ] in
/-- Without a giant, the window does not grow. -/
theorem beardW_succ_of_not_giant (A : Finset Γ) (x : Ω → L) {i : ℕ}
    (h : ¬ IsGiantOn φ A (beard φ A x i).2) : (beard φ A x (i + 1)).1 = (beard φ A x i).1 := by
  rw [beardW_succ]
  ext u
  simp [h]

end Stable

/-! ### The loop as a program -/

/-- The state of the loop: stopped, the window list, the coset. -/
abbrev loopTy (D : Ty) : Ty := .prod .bool (.prod (.list .nat) (Ty.answer D))

section LoopPrograms

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `Wl ∪ af` as a list: `Wl` followed by the new points of `af`. -/
def unionProg (Wl af : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (Toolkit.filterList af fun j => .bind (cpMemProg j Wl) fun c => .op1 .not c) fun new =>
  .op2 .append Wl new

/-- Stop the loop with the current window and coset. -/
def loopStopProg (wa : var (.prod (.list .nat) (Ty.answer D))) : Prog S rec var (loopTy D) :=
  .bind (.op0 (.boolLit true)) fun t => .op2 .pair t wa

/-- **One round of the loop.** -/
def loopRound (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (pos : var (.array .nat)) (pA : var (.list .nat)) (xy : var Ty.strs)
    (st : var (loopTy D)) : Prog (groupSig D) rec var (loopTy D) :=
  .bind (.op1 .fst st) fun done => .ite done (.ret st)
    (.bind (.op1 .snd st) fun wa => .bind (.op1 .fst wa) fun Wl => .bind (.op1 .snd wa) fun ans =>
      .caseOption ans (loopStopProg wa) fun c =>
        .bind (.op1 .fst c) fun σ => .bind (.op1 .snd c) fun H =>
        .bind (beardStepProg sub n pos pA xy σ H) fun r =>
        .caseOption r (loopStopProg wa) fun fa =>
          .bind (.op1 .fst fa) fun af => .bind (.op1 .snd fa) fun ans' =>
          .bind (unionProg Wl af) fun Wl' => .bind (.op0 (.boolLit false)) fun f =>
          .bind (.op2 .pair Wl' ans') fun wa' => .op2 .pair f wa')

/-- **The paired beard**: at most `n` rounds from the coset `σ₀ • H₀`. -/
def pairLoopProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (pos : var (.array .nat)) (pA : var (.list .nat)) (xy : var Ty.strs)
    (σ₀ : var Ty.perm) (H₀ : var (Ty.group D)) :
    Prog (groupSig D) rec var (.prod (.list .nat) (Ty.answer D)) :=
  .bind (.op1 .range n) fun js =>
  .bind (.op2 .pair σ₀ H₀) fun c₀ => .bind (.op1 .some c₀) fun a₀ =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .pair nil a₀) fun wa₀ =>
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .pair f wa₀) fun st₀ =>
  .bind (.foldList js st₀ fun st _ => loopRound sub n pos pA xy st) fun st =>
  .op1 .snd st

end LoopPrograms

section UnionSpec

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of `unionProg`. -/
def unionCost (k l : ℕ) : ℕ := l * (3 * k + 6) + k + 4

theorem RunsWithin.unionProg (Wl af : List ℕ) :
    RunsWithin X body (CertProg.unionProg Wl af) (Wl ++ af.filter fun j => !Wl.any (· == j))
      (unionCost Wl.length af.length) := by
  have hf := RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := af)
    (P := fun j => !Wl.any (· == j)) (c := 3 * Wl.length + 2)
    (p := fun j => .bind (CertProg.cpMemProg j Wl) fun c => .op1 .not c) fun j _ =>
      RunsWithin.bind_le (RunsWithin.cpMemProg j Wl) (RunsWithin.prim _ _)
        (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step hf
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head, unionCost]
    ring_nf
    omega

theorem mem_union_filter {Wl af : List ℕ} {j : ℕ} :
    j ∈ Wl ++ af.filter (fun j => !Wl.any (· == j)) ↔ j ∈ Wl ∨ j ∈ af := by
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hW : j ∈ Wl
      · exact Or.inl hW
      · exact Or.inr ⟨h, fun x hx e => hW (e ▸ hx)⟩

theorem nodup_union_filter {Wl af : List ℕ} (hW : Wl.Nodup) (ha : af.Nodup) :
    (Wl ++ af.filter (fun j => !Wl.any (· == j))).Nodup := by
  refine List.nodup_append.2 ⟨hW, ha.filter _, fun x hx y hy e => ?_⟩
  subst e
  simp only [List.mem_filter, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hy
  exact hy.2 x hx rfl

end UnionSpec

/-! ### The invariant of the loop -/

section Inv

variable {D : Ty} {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- A coset after `i` rounds: valid data of degree `N` with at most `s` generators representing
`pairCoset … i`, with the window list of `beard … i`. -/
def CosetAt (DV : ℕ → GensData → D.denote → Prop) (hC : CertSetting G n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (al : List ℕ) (A' : Finset (Fin (N - n)))
    (xy : StrData × StrData) (s i : ℕ) (Wl : List ℕ) (c : CosetData D) : Prop :=
  c.1.Valid N ∧ c.2.1 = N ∧ GroupValid DV N c.2.2.1 c.2.2.2 ∧ c.2.2.1.length ≤ s ∧
    Denotes hC (PermData.denote N c.1 • (GensData.denote N c.2.2.1 : Set (Perm (Fin N))))
      (pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.2.denote N)) i) ∧
    Wl.Nodup ∧ ∀ j, j ∈ Wl ↔ ∃ hj : j < n, (⟨j, hj⟩ : Fin n) ∈
      (beard φ (finsetOf (N - n) al) (strOn hC.le (xy.1.denote N)) i).1

/-- The state after `i` rounds, or the final result. -/
def AtRound (DV : ℕ → GensData → D.denote → Prop) (hC : CertSetting G n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (al : List ℕ) (A' : Finset (Fin (N - n)))
    (xy : StrData × StrData) (s i : ℕ) (wa : List ℕ × AnswerData D) : Prop :=
  (wa.2 = none → pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
      (strOn hC.le (xy.2.denote N)) i = ∅) ∧
    ∀ c, wa.2 = some c → CosetAt DV hC φ al A' xy s i wa.1 c

/-- **The invariant of the loop** after `i` rounds: a running state is at round `i`; a stopped
state is already at round `n`. -/
def LoopInv (DV : ℕ → GensData → D.denote → Prop) (hC : CertSetting G n)
    (φ : strGroup hC →* Perm (Fin (N - n))) (al : List ℕ) (A' : Finset (Fin (N - n)))
    (xy : StrData × StrData) (s i : ℕ) (st : Bool × List ℕ × AnswerData D) : Prop :=
  (st.1 = false → AtRound DV hC φ al A' xy s i st.2) ∧
    (st.1 = true → AtRound DV hC φ al A' xy s n st.2)

end Inv

/-! ### One round -/

section Round

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- The cost of one round: a step, the union of the windows, bookkeeping. -/
def loopRoundCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb : ℕ) : ℕ :=
  beardStepCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb + unionCost n n + 30

theorem length_le_of_lt {l : List ℕ} {n : ℕ} (hnd : l.Nodup) (hlt : ∀ j ∈ l, j < n) :
    l.length ≤ n := by
  have := (List.subperm_of_subset hnd (fun j hj => List.mem_range.2 (hlt j hj))).length_le
  simpa using this

theorem unionCost_le {k l n : ℕ} (hk : k ≤ n) (hl : l ≤ n) : unionCost k l ≤ unionCost n n := by
  simp only [unionCost]
  have := Nat.mul_le_mul hl (show 3 * k + 6 ≤ 3 * n + 6 by omega)
  omega

/-- **One round of the loop** keeps the invariant. -/
theorem loopRound_spec (hO : MeetsContractOn DV stepOps X.O)
    (hPre : ∀ op x, stepOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (h5 : 5 ≤ al.length)
    {A' : Finset (Fin (N - n))} {xy : StrData × StrData} {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hGG₀ : G ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) {Bgen : ℕ}
    (hBg : ∀ gs : GensData, GensData.AllValid N gs → gs.length ≤ al.length.factorial * (s + 1) →
      GensData.denote N gs ≤ G →
        X.B.call GroupOp.generate (N, gs) (X.O.run GroupOp.generate (N, gs)) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub (StepSubP (DV := DV) G xy n al.length s) (fun _ => Cb) s)
    {i : ℕ} (hi : i < n) {st : Bool × List ℕ × AnswerData D}
    (hinv : LoopInv DV hC φ al A' xy s i st) :
    ∃ st₁, RunsWithin X body (CertProg.loopRound sub n (WinData.pos N (winA N n al))
        (winA N n al).1 xy st) st₁
        (loopRoundCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb) ∧
      LoopInv DV hC φ al A' xy s (i + 1) st₁ := by
  obtain ⟨done, Wl, ans⟩ := st
  set A := finsetOf (N - n) al with hA
  set x := strOn hC.le (xy.1.denote N) with hx
  set x' := strOn hC.le (xy.2.denote N) with hx'
  cases done with
  | true =>
    refine ⟨(true, Wl, ans), ?_, fun h => Bool.noConfusion h, fun _ => hinv.2 rfl⟩
    apply RunsWithin.mono
    case h =>
      unfold CertProg.loopRound
      run_step (RunsWithin.prim _ _)
      exact Sims.RunsWithin.ite_pos rfl (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost, loopRoundCost]
      omega
  | false =>
  obtain ⟨hnone, hsome⟩ := hinv.1 rfl
  cases ans with
  | none =>
    have hCi := hnone rfl
    refine ⟨(true, Wl, none), ?_, fun h => Bool.noConfusion h, fun _ => ⟨fun _ => ?_,
      fun c h => (by simp at h)⟩⟩
    · apply RunsWithin.mono
      case h =>
        unfold CertProg.loopRound
        run_step (RunsWithin.prim _ _)
        run_with Sims.RunsWithin.ite_neg rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOption_none _
        unfold loopStopProg
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, loopRoundCost]
        omega
    · exact Set.subset_eq_empty (pairCoset_antitone φ A A' x x' hi.le) hCi
  | some c =>
    obtain ⟨σd, N', hs, e⟩ := c
    obtain ⟨hσd, hN', hHv, hlen, hden, hWnd, hWmem⟩ := hsome _ rfl
    change N' = N at hN'
    subst hN'
    obtain ⟨res, hrun, hresnone, hressome⟩ := RunsWithin.beardStepProg (X := X) (body := body)
      hO hPre hφ hal halm h5 (A' := A') (xy := xy) (i := i) hσd hHv hden B hlen hGG₀ Bk hsk hBg
      hsub
    have hWlen : Wl.length ≤ n :=
      length_le_of_lt hWnd fun j hj => ((hWmem j).1 hj).1
    rcases res with _ | ⟨af, ans'⟩
    · -- not a giant: stop with the current coset
      have hng := hresnone.1 rfl
      have hW := beardW_succ_of_not_giant φ A x hng
      have hstab := pairCoset_stable φ A A' x x' hW (n - i)
      have hbeard := beard_add_of_fst φ A x hW (n - i)
      rw [show i + (n - i) = n by omega] at hstab hbeard
      refine ⟨(true, Wl, some (σd, N', hs, e)), ?_, fun h => Bool.noConfusion h,
        fun _ => ⟨fun h => (by simp at h), fun c hc => ?_⟩⟩
      · apply RunsWithin.mono
        case h =>
          unfold CertProg.loopRound
          run_step (RunsWithin.prim _ _)
          run_with Sims.RunsWithin.ite_neg rfl _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.caseOption_some _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step hrun
          run_with RunsWithin.caseOption_none _
          unfold loopStopProg
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.prim _ _
        case hc =>
          simp only [Prim.cost, loopRoundCost]
          omega
      · cases hc
        refine ⟨hσd, rfl, hHv, hlen, ?_, hWnd, fun j => ?_⟩
        · rw [hstab]
          exact hden
        · rw [hWmem j, hbeard]
    · -- a giant: continue with the next coset
      obtain ⟨hafnd, hafmem, hok, hcos, hempty⟩ := hressome af ans' rfl
      have hgiant : IsGiantOn φ A (beard φ A x i).2 := by
        by_contra h
        exact absurd (hresnone.2 h) (Option.some_ne_none _)
      have haflen : af.length ≤ n := length_le_of_lt hafnd fun j hj => ((hafmem j).1 hj).1
      refine ⟨(false, Wl ++ af.filter fun j => !Wl.any (· == j), ans'), ?_,
        fun _ => ⟨hempty, fun c hc => ?_⟩, fun h => Bool.noConfusion h⟩
      · apply RunsWithin.mono
        case h =>
          unfold CertProg.loopRound
          run_step (RunsWithin.prim _ _)
          run_with Sims.RunsWithin.ite_neg rfl _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.caseOption_some _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step hrun
          run_with RunsWithin.caseOption_some _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.unionProg Wl af)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.prim _ _
        case hc =>
          have := unionCost_le hWlen haflen
          simp only [Prim.cost, loopRoundCost]
          omega
      · obtain ⟨τ, Kd⟩ := c
        subst hc
        obtain ⟨hgen, hdenK⟩ := hcos _ rfl
        obtain ⟨hτ, hKd, hKv, -⟩ := hok
        refine ⟨hτ, hKd, hKv, hgen, hdenK, nodup_union_filter hWnd hafnd, fun j => ?_⟩
        rw [mem_union_filter, hWmem, hafmem, beardW_succ]
        constructor
        · rintro (⟨hj, h⟩ | ⟨hj, h⟩)
          · exact ⟨hj, Or.inl h⟩
          · exact ⟨hj, Or.inr ⟨hgiant, h⟩⟩
        · rintro ⟨hj, h | ⟨-, h⟩⟩
          · exact Or.inl ⟨hj, h⟩
          · exact Or.inr ⟨hj, h⟩

end Round

/-! ### The loop -/

section Loop

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- The cost of the loop: `n` rounds. -/
def pairLoopCost (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb : ℕ) : ℕ :=
  n * (loopRoundCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb + 1) + n + 10

/-- **The polynomial of the loop**. -/
def loopPoly (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen : ℕ) : ℕ :=
  n * (stepPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen + unionCost n n + 31) + n + 10

/-- **The loop costs at most a polynomial times `k!`**, plus at most `n · k! · n` sub-calls of
cost `Cb` each. -/
theorem pairLoopCost_le (N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb : ℕ) :
    pairLoopCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb ≤
      k.factorial * loopPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen +
        n * (k.factorial * (n * Cb)) := by
  have h1 := beardStepCost_le N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb
  have hF := Nat.factorial_pos k
  have h2 : unionCost n n + 31 ≤ k.factorial * (unionCost n n + 31) :=
    Nat.le_mul_of_pos_left _ hF
  have h3 : n + 10 ≤ k.factorial * (n + 10) := Nat.le_mul_of_pos_left _ hF
  have h4 : loopRoundCost N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen Cb + 1 ≤
      k.factorial * (stepPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen + unionCost n n + 31) +
        k.factorial * (n * Cb) := by
    simp only [loopRoundCost]
    rw [Nat.mul_add, Nat.mul_add] at *
    omega
  simp only [pairLoopCost, loopPoly]
  have h5 := (Nat.mul_le_mul_left n h4).trans (le_of_eq (Nat.mul_add _ _ _))
  have e : k.factorial * (n * (stepPoly N n k s Bstab Btr Borb Bgen' Borb' Bstab' Bgen +
      unionCost n n + 31) + n + 10) = n * (k.factorial * (stepPoly N n k s Bstab Btr Borb Bgen'
        Borb' Bstab' Bgen + unionCost n n + 31)) + k.factorial * (n + 10) := by ring
  rw [e]
  omega

theorem atRound_none_iff {DV : ℕ → GensData → D.denote → Prop} {al : List ℕ}
    {A' : Finset (Fin (N - n))} {xy : StrData × StrData} {s i : ℕ}
    {wa : List ℕ × AnswerData D} (h : AtRound DV hC φ al A' xy s i wa) :
    wa.2 = none ↔ pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
      (strOn hC.le (xy.2.denote N)) i = ∅ := by
  refine ⟨h.1, fun hE => ?_⟩
  rcases hwa : wa.2 with _ | c
  · rfl
  · obtain ⟨-, -, -, -, hden, -⟩ := h.2 c hwa
    obtain ⟨_, -, hσC, -⟩ := denotes_group hden
    rw [hE] at hσC
    exact absurd hσC (Set.notMem_empty _)

/-- **The loop.** -/
theorem RunsWithin.pairLoopProg (hO : MeetsContractOn DV stepOps X.O)
    (hPre : ∀ op x, stepOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {al : List ℕ} (hal : al.Nodup) (halm : ∀ x ∈ al, x < N - n) (h5 : 5 ≤ al.length)
    {A' : Finset (Fin (N - n))} {xy : StrData × StrData} {s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hGG₀ : G ≤ G₀) {sk : ℕ}
    (Bk : BackendBounds X DV (winA N n al).1.length sk ⊤)
    (hsk : s ≤ (winA N n al).1.length * (sk + 1)) {Bgen : ℕ}
    (hBg : ∀ gs : GensData, GensData.AllValid N gs → gs.length ≤ al.length.factorial * (s + 1) →
      GensData.denote N gs ≤ G →
        X.B.call GroupOp.generate (N, gs) (X.O.run GroupOp.generate (N, gs)) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub (StepSubP (DV := DV) G xy n al.length s) (fun _ => Cb) s)
    {σ₀ : PermData} (hσ₀ : σ₀.Valid N) {hs₀ : GensData} {e₀ : D.denote}
    (hH₀ : GroupValid DV N hs₀ e₀) (hlen₀ : hs₀.length ≤ s)
    (hden₀ : Denotes hC (PermData.denote N σ₀ • (GensData.denote N hs₀ : Set (Perm (Fin N))))
      (pairCoset φ (finsetOf (N - n) al) A' (strOn hC.le (xy.1.denote N))
        (strOn hC.le (xy.2.denote N)) 0)) :
    ∃ res : List ℕ × AnswerData D,
      RunsWithin X body (CertProg.pairLoopProg sub n (WinData.pos N (winA N n al))
          (winA N n al).1 xy σ₀ (N, hs₀, e₀)) res
        (pairLoopCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb) ∧
      AtRound DV hC φ al A' xy s n res := by
  have hfold : ∀ len i (st : Bool × List ℕ × AnswerData D), i + len ≤ n →
      LoopInv DV hC φ al A' xy s i st → ∃ st',
        RunsWithin X body (Prog.foldList (a := .nat) (b := loopTy D) (List.range' i len) st
          fun st _ =>
          CertProg.loopRound sub n (WinData.pos N (winA N n al)) (winA N n al).1 xy st) st'
          (len * (loopRoundCost N n al.length s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab
            Bgen Cb + 1)) ∧
        LoopInv DV hC φ al A' xy s (i + len) st' := by
    intro len
    induction len with
    | zero =>
      intro i st _ hinv
      exact ⟨st, (RunsWithin.foldList_nil (X := X) (body := body)).mono (Nat.zero_le _), hinv⟩
    | succ len ih =>
      intro i st hle hinv
      obtain ⟨st₁, hrun₁, hinv₁⟩ := loopRound_spec hO hPre hφ hal halm h5 B hGG₀ Bk hsk hBg hsub
        (show i < n by omega) hinv
      obtain ⟨st', hrun', hinv'⟩ := ih (i + 1) st₁ (by omega) hinv₁
      refine ⟨st', ?_, by rwa [show i + (len + 1) = i + 1 + len by omega]⟩
      rw [List.range'_succ]
      refine (RunsWithin.foldList_cons hrun₁ hrun').mono ?_
      rw [Nat.succ_mul]
      omega
  have hinv₀ : LoopInv DV hC φ al A' xy s 0 (false, [], some (σ₀, N, hs₀, e₀)) := by
    refine ⟨fun _ => ⟨fun h => (by simp at h), fun c hc => ?_⟩, fun h => Bool.noConfusion h⟩
    obtain rfl : c = (σ₀, N, hs₀, e₀) := (Option.some.inj hc).symm
    refine ⟨hσ₀, rfl, hH₀, hlen₀, hden₀, List.nodup_nil, fun j => ?_⟩
    simp [beard]
  obtain ⟨st', hrun, hinv'⟩ := hfold n 0 _ (by omega) hinv₀
  rw [Nat.zero_add] at hinv'
  have hfin : AtRound DV hC φ al A' xy s n st'.2 := by
    rcases hd : st'.1 with _ | _
    · exact hinv'.1 hd
    · exact hinv'.2 hd
  refine ⟨st'.2, ?_, hfin⟩
  apply RunsWithin.mono
  case h =>
    unfold CertProg.pairLoopProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    simp only [Prim.eval]
    rw [List.range_eq_range']
    run_step hrun
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head, pairLoopCost]
    omega

end Loop

/-! ### Well-formedness of the loop -/

section LoopWf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_unionProg {Wl₁ af₁ : var₁ (.list .nat)} {Wl₂ af₂ : var₂ (.list .nat)}
    (hW : ⟨.list .nat, Wl₁, Wl₂⟩ ∈ Γ) (ha : ⟨.list .nat, af₁, af₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (unionProg Wl₁ af₁) (unionProg Wl₂ af₂) := by
  unfold unionProg
  exact .bind (Toolkit.wf_filterList ha fun _ hΓ _ _ hj => .bind (wf_cpMemProg hj (hΓ hW))
    fun _ _ => .prim _ (.cons (by simp) .nil)) fun _ _ =>
      .prim _ (.cons (by simp [hW]) (.cons (by simp) .nil))

theorem wf_loopStopProg {wa₁ : var₁ (.prod (.list .nat) (Ty.answer D))}
    {wa₂ : var₂ (.prod (.list .nat) (Ty.answer D))}
    (hwa : ⟨.prod (.list .nat) (Ty.answer D), wa₁, wa₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (loopStopProg wa₁) (loopStopProg wa₂) := by
  unfold loopStopProg
  exact .bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp [hwa]) .nil))

theorem wf_loopRound {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {st₁ : var₁ (loopTy D)} {st₂ : var₂ (loopTy D)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ)
    (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hst : ⟨loopTy D, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (loopRound sub₁ n₁ pos₁ pA₁ xy₁ st₁) (loopRound sub₂ n₂ pos₂ pA₂ xy₂ st₂) := by
  unfold loopRound
  refine .bind (.prim _ (.cons hst .nil)) fun _ _ => .ite (by simp) (.ret (by simp [hst])) ?_
  refine .bind (.prim _ (.cons (by simp [hst]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .caseOption (by simp) (wf_loopStopProg (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_beardStepProg (hsub.mono fun _ h => by simp [h]) (by simp [hn])
    (by simp [hpos]) (by simp [hpA]) (by simp [hxy]) (by simp) (by simp)) fun _ _ => ?_
  refine .caseOption (by simp) (wf_loopStopProg (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (wf_unionProg (by simp) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_pairLoopProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat} {pos₁ : var₁ (.array .nat)}
    {pos₂ : var₂ (.array .nat)} {pA₁ : var₁ (.list .nat)} {pA₂ : var₂ (.list .nat)}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm}
    {H₁ : var₁ (Ty.group D)} {H₂ : var₂ (Ty.group D)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hpos : ⟨.array .nat, pos₁, pos₂⟩ ∈ Γ)
    (hpA : ⟨.list .nat, pA₁, pA₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ)
    (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ) (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) :
    Prog.Wf r Γ (pairLoopProg sub₁ n₁ pos₁ pA₁ xy₁ σ₁ H₁)
      (pairLoopProg sub₂ n₂ pos₂ pA₂ xy₂ σ₂ H₂) := by
  unfold pairLoopProg
  refine .bind (.prim _ (.cons hn .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hσ]) (.cons (by simp [hH]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.foldList (by simp) (by simp) fun _ _ _ _ =>
    wf_loopRound (hsub.mono fun _ h => by simp [h]) (by simp [hn]) (by simp [hpos])
      (by simp [hpA]) (by simp [hxy]) (by simp)) fun _ _ => ?_
  exact .prim _ (.cons (by simp) .nil)

end LoopWf

end GraphIso.CertProg
