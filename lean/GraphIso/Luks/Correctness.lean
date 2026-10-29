module

public import GraphIso.Luks.Strategy

/-!
# Correctness and cost of Luks's strategy

`luks_spec`: against any backend meeting its contract on the operations the strategy calls
(`luksOps`), with bounds `LuksBounds X DV n s R G₀`, for an ambient group `G₀` whose primitive
sections have order at most `k ^ c` (`PrimBounded G₀ c`) and `n ^ c ≤ R`, the strategy returns
a correct answer on every valid instance of degree `n` with group inside `G₀` and at most `s`
generators, with output groups of at most `s` generators, at cost at most
`luksBound Q c m` for window size `m`: `2 Q m ^ (c + 1) − Q` for `m ≥ 1`, and `Q` for the
empty window.

The proof is by strong induction on the window size alone. In the transitive case the block
system of `maxBlocks` has `k ≥ 2` blocks of size `b = m / k` on which `G` acts primitively,
so the number `R'` of cosets of the block kernel is the order of a primitive group of degree
`k` (`card_range_mul_card_blockKernel`): `R' ≤ k ^ c ≤ n ^ c ≤ R`. Then `luks_block_arith`
applies.
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv Pointwise Cost Programs Solver

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- The specification of Luks's strategy at window size `m`. -/
def LuksSpec (X : Ctx (groupSig D)) (DV : ℕ → GensData → D.denote → Prop) (n s : ℕ)
    (G₀ : Subgroup (Perm (Fin n))) (Q c m : ℕ) : Prop :=
  ∀ (xy : StrData × StrData) (w : WinData) (σd : PermData) (gs : GensData) (d : D.denote),
    InstData.Valid (D := D) (xy, w, σd, n, gs, d) DV → gs.length ≤ s →
    GensData.denote n gs ≤ G₀ → w.1.length = m →
    ∃ ans : AnswerData D,
      RunsWithin X (luksBody D Ty.denote) (luksBody D Ty.denote (xy, w, σd, n, gs, d)) ans
        (luksBound Q c m) ∧
      InstData.OK (D := D) (xy, w, σd, n, gs, d) DV ans ∧
      ∀ c' : CosetData D, ans = some c' → c'.2.gens.length ≤ s

theorem maxBlocksCost_mono {n m m' s s' : ℕ} (hm : m ≤ m') (hs : s ≤ s') :
    maxBlocksCost n m s ≤ maxBlocksCost n m' s' := by
  unfold maxBlocksCost mbCost closureCost
  gcongr

theorem blockKernelCost_mono {n m m' k k' s s' sK sK' Bge Bke Bgt : ℕ} (hm : m ≤ m') (hk : k ≤ k')
    (hs : s ≤ s') (hsK : sK ≤ sK') :
    blockKernelCost n m k s sK Bge Bke Bgt ≤ blockKernelCost n m' k' s' sK' Bge Bke Bgt := by
  unfold blockKernelCost
  gcongr

section Cases

variable (hO : MeetsContractOn DV luksOps X.O)
  (hPre : ∀ op x, luksOps op → GroupPre DV op x → X.Pre op x)
  {n s R : ℕ} {G₀ : Subgroup (Perm (Fin n))} (B : LuksBounds X DV n s R G₀)
include hO hPre

/-- **The transitive case.** -/
theorem luks_transitive_case {c : ℕ} (hprim : PrimBounded G₀ c) (hR : n ^ c ≤ R) {m : ℕ}
    (ih : ∀ m' < m, LuksSpec X DV n s G₀
      (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c m')
    {xy : StrData × StrData} {u : ℕ} {rest : List ℕ} {mask : Array Bool} {σd : PermData}
    {gs : GensData} {d : D.denote}
    (hv : InstData.Valid (D := D) (xy, (u :: rest, mask), σd, n, gs, d) DV) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote n gs ≤ G₀) (hm : (u :: rest).length = m)
    (hfix : GensData.fixesB gs (u :: rest, mask) = false) {o : List ℕ}
    (hos : X.O.run GroupOp.orbits ((n, gs, d), (u :: rest, mask)) = [o]) :
    ∃ ans : AnswerData D,
      RunsWithin X (luksBody D Ty.denote)
        (luksBody D Ty.denote (xy, (u :: rest, mask), σd, n, gs, d)) ans
        (luksBound (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c m) ∧
      InstData.OK (D := D) (xy, (u :: rest, mask), σd, n, gs, d) DV ans ∧
      ∀ c' : CosetData D, ans = some c' → c'.2.gens.length ≤ s := by
  set Q := luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen with hQ
  obtain ⟨hwv, hσ, hGv, hinv⟩ := hv
  change WinData.Valid n (u :: rest, mask) at hwv
  change PermData.Valid n σd at hσ
  change GroupValid DV n gs d at hGv
  change IsInvariant (GensData.denote n gs) (WinData.denote n (u :: rest, mask)) at hinv
  have hmn : m ≤ n := hm ▸ WinData.length_le hwv
  -- the window is transitive
  have hpreO : GroupPre DV .orbits ((n, gs, d), (u :: rest, mask)) := ⟨hGv, hwv, hinv⟩
  have hpostO := hO .orbits _ (Or.inl rfl) hpreO
  change IsOrbitPartition (GensData.denote n gs) (u :: rest, mask)
    (X.O.run .orbits ((n, gs, d), (u :: rest, mask))) at hpostO
  rw [hos] at hpostO
  have htr := hpostO.transitive_of_singleton (i := u) List.mem_cons_self
  have hnfix : ¬ FixesPointwise (GensData.denote n gs) (WinData.denote n (u :: rest, mask)) :=
    fun h => by rw [(GensData.fixesB_iff hGv.1 hwv).2 h] at hfix; cases hfix
  have hrest : rest ≠ [] := by
    rintro rfl
    exact hnfix (fixesPointwise_of_singleton rfl hinv)
  have hW := win_of_valid hwv hGv.1 hinv
  -- the maximal block system
  obtain ⟨hbs, hG, hk2, hsize, hprimitive⟩ :=
    maxBlocks_spec (w := (u :: rest, mask)) hwv hGv.1 hinv rfl hrest htr
  dsimp only at hbs hG hk2 hsize hprimitive
  set bs := maxBlocks n gs (u :: rest) with hbs_def
  set k := bs.length with hk_def
  -- the common block size
  obtain ⟨b₁, hb₁⟩ : ∃ b, b ∈ bs := List.exists_mem_of_length_pos (by omega)
  set b₀ := b₁.length with hb₀_def
  have hall : ∀ b ∈ bs, b.length = b₀ := fun b hb =>
    Nat.eq_of_mul_eq_mul_right (by omega) ((hsize b hb).trans (hsize b₁ hb₁).symm)
  have hkb : k * b₀ = m := by rw [Nat.mul_comm, hsize b₁ hb₁, hm]
  have hb₀pos : 1 ≤ b₀ := by
    have := hbs.2 b₁ hb₁
    exact List.length_pos_of_ne_nil this
  have hb₀lt : b₀ < m := by rw [← hkb]; nlinarith
  have hkn : k ≤ n := by nlinarith
  -- the block kernel
  have hops : ∀ op, blockReduceOps op → luksOps op := by
    intro op hop
    rcases hop with h | h | h <;> simp [luksOps, h]
  have hkops : ∀ op, blockKernelOps op → luksOps op := by
    intro op hop
    rcases hop with h | h <;> simp [luksOps, h]
  obtain ⟨hBge, hBke, hBgt, hsKe, hKs⟩ :=
    B.blocks gs d (u :: rest, mask) bs hs hG₀ hGv hwv hbs hG
  obtain ⟨-, hKn, hKv, hKden⟩ := RunsWithin.blockKernelProg (X := X)
    (body := luksBody D Ty.denote) (fun op x hop hx => hO op x (hkops op hop) hx)
    (fun op x hop hx => hPre op x (hkops op hop) hx) hwv hbs hG hGv.1 hBge hBke hBgt
  have hBcr₀ := B.cosetReps gs d (u :: rest, mask) bs hs hG₀ hGv hwv hbs hG
  have hreduce := RunsWithin.blockReduceProg (X := X) (body := luksBody D Ty.denote)
    (sub := fun J => .recur J) (xy := xy) (σd := σd) (Cw := fun o => 1 + luksBound Q c o.length)
    (s := s) (Bge := B.Bge) (Bke := B.Bke) (Bgt := B.Bgt) (Bcr := B.Bcr) (Bgen := B.Bgen)
    (fun op x hop hx => hO op x (hops op hop) hx) (fun op x hop hx => hPre op x (hops op hop) hx)
    hwv hσ hGv hinv hbs hG hBge hBke hBgt
  rcases hKm : blockKernelModel X.O n bs gs with ⟨n', ks, e⟩
  rw [hKm] at hKn hKv hKden hKs hBcr₀ hreduce
  change n' = n at hKn
  subst n'
  have hKG : GensData.denote n ks ≤ GensData.denote n gs := hKden ▸ blockKernel_le _ _
  -- the number of cosets is the order of a primitive group
  have hcrpre : GroupPre DV .cosetReps ((n, gs, d), (n, ks, e)) := ⟨hGv, hKv, rfl, hKG⟩
  obtain ⟨-, htrans⟩ := hO .cosetReps _ (Or.inr (Or.inr (Or.inr rfl))) hcrpre
  have hcard := htrans.card_eq hKG
  set R' := (X.O.run GroupOp.cosetReps ((n, gs, d), (n, ks, e))).length with hR'_def
  have hrange := card_range_mul_card_blockKernel hwv hbs hG
  rw [← hKden] at hrange
  have hKpos : 0 < Nat.card (GensData.denote n ks) := Nat.card_pos
  have hR'eq : R' = Nat.card (blockHom hwv hbs hG).range :=
    Nat.eq_of_mul_eq_mul_right hKpos (hcard.symm.trans hrange.symm)
  have hRk : R' ≤ k ^ c := hR'eq ▸ hprim _ hG₀ k (blockHom hwv hbs hG) hk2 hprimitive
  have hRR : R' ≤ R := hRk.trans ((Nat.pow_le_pow_left hkn c).trans hR)
  have hR'1 : 1 ≤ R' := by
    have : 0 < Nat.card (GensData.denote n gs) := Nat.card_pos
    rw [hcard] at this
    exact Nat.pos_of_mul_pos_right this
  have hmax : max s ks.length = s := max_eq_left hKs
  -- every block is solved by a recursive call
  have hsub : SeqSub X (luksBody D Ty.denote) DV (fun J => .recur J) xy n bs
      (fun o => 1 + luksBound Q c o.length) s (max s ks.length) (GensData.denote n ks) := by
    rintro ⟨xy', w', τ, n'', ks', e'⟩ ⟨hxy, hval, hdeg, ⟨b, hb, hw'⟩, hlen, hle⟩
    simp only at hxy hw' hlen hle
    change n'' = n at hdeg
    subst xy' w' n''
    obtain ⟨ans, hr, hok, hg⟩ := ih b.length (by rw [hall b hb]; exact hb₀lt) xy
      (WinData.ofPoints n b) τ ks' e' hval (by simpa [GroupData.gens, hmax] using hlen)
      ((hle.trans hKG).trans hG₀) (by simp)
    exact ⟨ans, (RunsWithin.recur hr).mono (by simp), hok, hg⟩
  obtain ⟨ans, hr, hok, -, hg⟩ := hreduce hsub (hBcr₀ hRR) (fun hs' hv' hl hle =>
    B.generate hs' hv' (hl.trans (by rw [hmax]; exact Nat.mul_le_mul_right _ hRR))
      (hle.trans hG₀))
  refine ⟨ans, ?_, hok, hg s fun hs' hv' hle => B.genOut hs' hv' (hle.trans hG₀)⟩
  -- assemble the run
  have hrun := run_luksBody (X := X) (xy := xy) (σd := σd) (G := (n, gs, d))
    (w := (u :: rest, mask)) (RunsWithin.caseList_cons (run_luksNonempty_moved (G := (n, gs, d))
      (w := (u :: rest, mask)) hfix (run_luksMoved (by
        rw [hos]
        exact RunsWithin.caseList_cons (RunsWithin.caseList_nil (run_luksTransitive hW hr)))
        (hPre _ _ (Or.inl rfl) hpreO))))
  refine hrun.mono ?_
  -- the cost
  have hBorb := B.orbits gs d (u :: rest, mask) hs hG₀ hpreO
  have hbranch : blockBranchCost n (fun o => 1 + luksBound Q c o.length) bs =
      3 + k * (luksBound Q c b₀ + 2 * n + 5 * b₀ + 14) := by
    unfold blockBranchCost seqCost
    rw [List.map_congr_left (g := fun _ => luksBound Q c b₀ + 2 * n + 5 * b₀ + 14)
      fun b hb => by simp only [hall b hb]; omega, sum_map_const]
  have hflat : bs.flatten.length = m := by rw [hbs.1.length_eq, hm]
  have hmb := maxBlocksCost_mono (n := n) (hm.le.trans hmn) hs
  have hbk := blockKernelCost_mono (n := n) (Bge := B.Bge) (Bke := B.Bke) (Bgt := B.Bgt)
    (hflat.le.trans hmn) hkn hs hsKe
  have hfx : gs.length * (5 * (u :: rest).length + 3) ≤ s * (5 * n + 3) :=
    Nat.mul_le_mul hs (by omega)
  have harith := luks_block_arith (Q := Q)
    (P := luksNode n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) (E := luksEdge n)
    (E' := luksBranch n s) (self := 7 + 1 + gs.length * (5 * (u :: rest).length + 3) + 4 + 1 +
      X.B.call GroupOp.orbits ((n, gs, d), (u :: rest, mask))
        (X.O.run GroupOp.orbits ((n, gs, d), (u :: rest, mask))) + 1 + 1 + 3 +
      maxBlocksCost n (u :: rest).length gs.length + 3 +
      blockKernelCost n bs.flatten.length k gs.length (extKernel X.O n bs gs).2.1.length B.Bge
        B.Bke B.Bgt + 2 + B.Bcr + B.Bgen + 19) (R := R') (k := k) (b := b₀) (c := c) le_rfl
    (by simp only [luksNode]; omega) hRk hR'1 hk2 hb₀pos
  rw [hkb] at harith
  have hinner : 24 * n + (3 + k * (luksBound Q c b₀ + 2 * n + 5 * b₀ + 14)) + s + 45 ≤
      luksBranch n s + k * (luksEdge n + luksBound Q c b₀) := by
    have : k * (luksBound Q c b₀ + 2 * n + 5 * b₀ + 14) ≤ k * (luksEdge n + luksBound Q c b₀) :=
      Nat.mul_le_mul_left _ (by simp only [luksEdge]; omega)
    simp only [luksBranch]
    omega
  have hmul := Nat.mul_le_mul_left R' hinner
  simp only [GroupData.gens, hbranch, hmax, ← hk_def]
  omega

/-- **The orbit case.** -/
theorem luks_orbits_case {c : ℕ} {m : ℕ}
    (ih : ∀ m' < m, LuksSpec X DV n s G₀
      (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c m')
    {xy : StrData × StrData} {u : ℕ} {rest : List ℕ} {mask : Array Bool} {σd : PermData}
    {gs : GensData} {d : D.denote}
    (hv : InstData.Valid (D := D) (xy, (u :: rest, mask), σd, n, gs, d) DV) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote n gs ≤ G₀) (hm : (u :: rest).length = m)
    (hfix : GensData.fixesB gs (u :: rest, mask) = false) {o₀ o₁ : List ℕ}
    {rest' : List (List ℕ)}
    (hos : X.O.run GroupOp.orbits ((n, gs, d), (u :: rest, mask)) = o₀ :: o₁ :: rest') :
    ∃ ans : AnswerData D,
      RunsWithin X (luksBody D Ty.denote)
        (luksBody D Ty.denote (xy, (u :: rest, mask), σd, n, gs, d)) ans
        (luksBound (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c m) ∧
      InstData.OK (D := D) (xy, (u :: rest, mask), σd, n, gs, d) DV ans ∧
      ∀ c' : CosetData D, ans = some c' → c'.2.gens.length ≤ s := by
  set Q := luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen with hQ
  obtain ⟨hwv, hσ, hGv, hinv⟩ := hv
  change WinData.Valid n (u :: rest, mask) at hwv
  change PermData.Valid n σd at hσ
  change GroupValid DV n gs d at hGv
  change IsInvariant (GensData.denote n gs) (WinData.denote n (u :: rest, mask)) at hinv
  have hmn : m ≤ n := hm ▸ WinData.length_le hwv
  have hpreO : GroupPre DV .orbits ((n, gs, d), (u :: rest, mask)) := ⟨hGv, hwv, hinv⟩
  have hpostO := hO .orbits _ (Or.inl rfl) hpreO
  change IsOrbitPartition (GensData.denote n gs) (u :: rest, mask)
    (X.O.run .orbits ((n, gs, d), (u :: rest, mask))) at hpostO
  rw [hos] at hpostO
  set os := o₀ :: o₁ :: rest' with hos'
  obtain ⟨hseq, hunion⟩ := seqInputs_of_isOrbitPartition hwv hpostO
  have hsub : SeqSub X (luksBody D Ty.denote) DV (fun J => .recur J) xy n os
      (fun o => 1 + luksBound Q c o.length) s (max s gs.length) (GensData.denote n gs) := by
    rintro ⟨xy', w', τ, n'', ks', e'⟩ ⟨hxy, hval, hdeg, ⟨o, ho, hw'⟩, hlen, hle⟩
    simp only at hxy hw' hlen hle
    change n'' = n at hdeg
    subst xy' w' n''
    have hlt : o.length < m := by
      rw [← hm]
      exact hpostO.length_lt ho
    obtain ⟨ans, hr, hok, hg⟩ := ih o.length hlt xy (WinData.ofPoints n o) τ ks' e' hval
      (by simpa [GroupData.gens, max_eq_left hs] using hlen) (hle.trans hG₀) (by simp)
    exact ⟨ans, (RunsWithin.recur hr).mono (by simp), hok, hg⟩
  obtain ⟨ans, hr, hok, hg⟩ := RunsWithin.seqProg (σd := σd) (Gd := (n, gs, d)) rfl hσ hGv
    hseq hsub
  refine ⟨ans, ?_, ?_, fun c' hc => (hg c' hc).trans (max_le le_rfl hs)⟩
  · have hrun := run_luksBody (X := X) (xy := xy) (σd := σd) (G := (n, gs, d))
      (w := (u :: rest, mask)) (RunsWithin.caseList_cons (run_luksNonempty_moved
        (G := (n, gs, d)) (w := (u :: rest, mask)) hfix (run_luksMoved (by
          rw [hos]
          exact RunsWithin.caseList_cons (RunsWithin.caseList_cons hr))
          (hPre _ _ (Or.inl rfl) hpreO))))
    refine hrun.mono ?_
    have hBorb := B.orbits gs d (u :: rest, mask) hs hG₀ hpreO
    have hlen2 : 2 ≤ os.length := by simp [hos']
    have hpos : ∀ o ∈ os, 0 < o.length := fun o ho => hpostO.length_pos ho
    have hsumm : (os.map List.length).sum = m := by rw [← hm]; exact hpostO.length_sum
    have hfx : gs.length * (5 * (u :: rest).length + 3) ≤ s * (5 * n + 3) :=
      Nat.mul_le_mul hs (by omega)
    have harith := luks_seq_arith (Q := Q)
      (P := luksNode n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) (E := luksEdge n)
      (c := c) (self := 7 + 1 + gs.length * (5 * (u :: rest).length + 3) + 4 + 1 +
        X.B.call GroupOp.orbits ((n, gs, d), (u :: rest, mask))
          (X.O.run GroupOp.orbits ((n, gs, d), (u :: rest, mask))) + 1 + 1 + 1)
      (by simp only [hQ, luksQ]; omega) (by simp only [luksNode]; omega) hlen2 hpos
      (f := seqCost n fun o => 1 + luksBound Q c o.length)
      (fun o ho => by
        have hon : o.length ≤ n := (hpostO.length_lt ho).le.trans (hm ▸ hmn)
        simp only [seqCost, luksEdge]
        omega)
    rw [hsumm] at harith
    simp only [GroupData.gens, GroupData.degree]
    omega
  · change AnsOK DV n (WinData.denote n (u :: rest, mask)) _ _ _ _ _
    rw [← hunion]
    exact hok

/-- **Correctness and cost of Luks's strategy.** For an ambient group with bounded primitive
sections, the cost on a window of size `m` is at most `luksBound Q c m`: `2 Q m ^ (c + 1) − Q`
for `m ≥ 1`, and `Q` for the empty window. -/
theorem luks_spec {c : ℕ} (hprim : PrimBounded G₀ c) (hR : n ^ c ≤ R) :
    ∀ m, LuksSpec X DV n s G₀ (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro xy w σd gs d hv hs hG₀ hm
  rcases w with ⟨pts, mask⟩
  rcases pts with _ | ⟨u, rest⟩
  · -- the empty window
    have hm0 : m = 0 := by simpa using hm.symm
    obtain ⟨hwv, hσ, hGv, hinv⟩ := hv
    change PermData.Valid n σd at hσ
    change GroupValid DV n gs d at hGv
    refine ⟨some (σd, n, gs, d), ?_, ?_, fun c' hc => by cases hc; exact hs⟩
    · refine (run_luksBody (RunsWithin.caseList_nil (RunsWithin.prim _ _))).mono ?_
      simp only [Prim.cost, hm0, luksBound, ↓reduceIte, luksQ, luksNode]
      omega
    · have hW : WinData.denote n ([], mask) = ∅ := by
        ext v; simp [WinData.denote]
      change AnsOK DV n (WinData.denote n ([], mask)) _ _ _ _ _
      rw [hW]
      exact AnsOK.empty_window hσ rfl hGv
  · have hm0 : m ≠ 0 := by simp at hm; omega
    cases hfix : GensData.fixesB gs (u :: rest, mask)
    · -- the window is moved: ask for the orbits
      have hv' := hv
      obtain ⟨hwv, -, hGv, hinv⟩ := hv'
      change WinData.Valid n (u :: rest, mask) at hwv
      change GroupValid DV n gs d at hGv
      have hpreO : GroupPre DV .orbits ((n, gs, d), (u :: rest, mask)) := ⟨hGv, hwv, hinv⟩
      have hpostO := hO .orbits _ (Or.inl rfl) hpreO
      change IsOrbitPartition (GensData.denote n gs) (u :: rest, mask)
        (X.O.run .orbits ((n, gs, d), (u :: rest, mask))) at hpostO
      rcases hos : X.O.run GroupOp.orbits ((n, gs, d), (u :: rest, mask)) with
        _ | ⟨o₀, _ | ⟨o₁, rest'⟩⟩
      · rw [hos] at hpostO
        exact absurd rfl (hpostO.ne_nil (by simp))
      · exact luks_transitive_case hO hPre B hprim hR ih hv hs hG₀ hm hfix hos
      · exact luks_orbits_case hO hPre B ih hv hs hG₀ hm hfix hos
    · -- the group fixes the window pointwise
      obtain ⟨hwv, hσ, hGv, hinv⟩ := hv
      change WinData.Valid n (u :: rest, mask) at hwv
      change PermData.Valid n σd at hσ
      change GroupValid DV n gs d at hGv
      have hmn : m ≤ n := hm ▸ WinData.length_le hwv
      have hfixS : FixesPointwise (GensData.denote n gs) (WinData.denote n (u :: rest, mask)) :=
        (GensData.fixesB_iff hGv.1 hwv).1 hfix
      refine ⟨if matchesB (u :: rest, mask) σd xy.1 xy.2 then some (σd, n, gs, d) else none,
        ?_, ?_, ?_⟩
      · refine (run_luksBody (RunsWithin.caseList_cons
          (run_luksNonempty_fixed (G := (n, gs, d)) hfix run_luksFixed))).mono
          (le_luksBound_of_le hm0 ?_)
        have hlen : (u :: rest).length = m := hm
        have : gs.length * (5 * (u :: rest).length + 3) ≤ s * (5 * n + 3) :=
          Nat.mul_le_mul hs (by omega)
        simp only [luksQ, luksNode, GroupData.gens, List.length_cons] at hlen this ⊢
        omega
      · change AnsOK DV n _ _ _ _ _ _
        cases hmat : matchesB (u :: rest, mask) σd xy.1 xy.2
        · have := (matchesB_iff hwv hσ xy.1 xy.2).not.1 (by simp [hmat])
          exact iso_of_fixesPointwise_of_not_matches hfixS this
        · have := (matchesB_iff hwv hσ xy.1 xy.2).1 hmat
          exact ⟨hσ, rfl, hGv, (iso_of_fixesPointwise_of_matches hfixS this).symm⟩
      · intro c' hc
        split at hc
        · cases hc; exact hs
        · cases hc

end Cases

end GraphIso.Luks
