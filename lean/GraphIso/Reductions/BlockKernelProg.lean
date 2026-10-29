module

public import GraphIso.Reductions.BlockAction
public import GraphIso.Reductions.BlocksProg

/-!
# The block kernel by the induced action

`blockKernelProg n gs bs` computes generators of the block kernel of `G = ⟨gs⟩` for a block
list `bs` (`k` blocks) that `G` permutes, using only `generate` and `kernel`:

1. the block index of every listed point (`blockIdxProg`) and the first point of every block;
2. the extension of every generator to degree `n + k`, acting on the `k` block points by the
   induced action (`extendProg`), and the group they generate at degree `n + k`;
3. the kernel of that group on the block points (`kernel`), which consists of the
   extensions of the block kernel (`mem_pointwiseStab_extend`);
4. the truncation of its generators to the first `n` points (`truncProg`), and the group they
   generate at degree `n`, which is the block kernel (`denote_truncTo`).

The degree change is in the costs: the extension and the kernel are computed at degree
`n + k`.
-/

@[expose] public section

namespace GraphIso.Programs

open Equiv Cost

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The block index of every listed point. -/
def blockIdxProg (n : var .nat) (bs : var (.list (.list .nat))) : Prog S rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nil =>
  .bind (.op2 .pair z nil) fun acc₀ =>
  .bind (.foldList bs acc₀ fun acc b =>
      .bind (.op1 .fst acc) fun i => .bind (.op1 .snd acc) fun ws =>
      .bind (mapList b fun u => .op2 .pair u i) fun bw =>
      .bind (.op2 .append bw ws) fun ws' =>
      .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' => .op2 .pair i' ws')
    fun fin =>
  .bind (.op1 .snd fin) fun ws =>
  .bind (.op2 .arrayMk n z) fun blank => .prim .arrayUpdate (.cons blank (.cons ws .nil))

/-- The first point of every block. -/
def blockRepsProg (bs : var (.list (.list .nat))) : Prog S rec var (.list .nat) :=
  mapList bs fun b => .caseList b (.op0 (.natLit 0)) fun x _ => .ret x

/-- The extension of `g` by the induced action on the block points. -/
def extendProg (n : var .nat) (bidx : var (.array .nat)) (reps : var (.list .nat))
    (g : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun f => .bind (.op1 .snd g) fun fi =>
  .bind (mapList reps fun r => .bind (.op2 .arrayGet f r) fun v =>
      .bind (.op2 .arrayGet bidx v) fun t => .op2 .add n t) fun l₁ =>
  .bind (mapList reps fun r => .bind (.op2 .arrayGet fi r) fun v =>
      .bind (.op2 .arrayGet bidx v) fun t => .op2 .add n t) fun l₂ =>
  .bind (.op1 .arrayToList f) fun fl => .bind (.op2 .append fl l₁) fun fl' =>
  .bind (.op1 .arrayOfList fl') fun a₁ =>
  .bind (.op1 .arrayToList fi) fun il => .bind (.op2 .append il l₂) fun il' =>
  .bind (.op1 .arrayOfList il') fun a₂ => .op2 .pair a₁ a₂

/-- The first `n` entries of a permutation's arrays. -/
def truncProg (n : var .nat) (g : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun f => .bind (.op1 .snd g) fun fi =>
  .bind (.op1 .range n) fun is =>
  .bind (mapList is fun i => .op2 .arrayGet f i) fun l₁ =>
  .bind (mapList is fun i => .op2 .arrayGet fi i) fun l₂ =>
  .bind (.op1 .arrayOfList l₁) fun a₁ => .bind (.op1 .arrayOfList l₂) fun a₂ => .op2 .pair a₁ a₂

/-- Generators of the block kernel, by the induced action on `n + k` points. -/
def blockKernelProg (n : var .nat) (gs : var Ty.gens) (bs : var (.list (.list .nat))) :
    Prog (groupSig D) rec var (Ty.group D) :=
  .bind (blockIdxProg n bs) fun bidx => .bind (blockRepsProg bs) fun reps =>
  .bind (.op1 .length bs) fun k => .bind (.op2 .add n k) fun nk =>
  .bind (mapList gs fun g => extendProg n bidx reps g) fun egs =>
  .bind (.op2 .pair nk egs) fun a₁ =>
  .bind (Prog.call (S := groupSig D) GroupOp.generate a₁) fun Ge =>
  .bind (.op1 .range k) fun ts => .bind (mapList ts fun t => .op2 .add n t) fun bp =>
  .bind (mkWindow nk bp) fun bw =>
  .bind (.op2 .pair Ge bw) fun a₂ =>
  .bind (Prog.call (S := groupSig D) GroupOp.kernel a₂) fun Ke =>
  .bind (.op1 .snd Ke) fun kd => .bind (.op1 .fst kd) fun kes =>
  .bind (mapList kes fun l => truncProg n l) fun kt =>
  .bind (.op2 .pair n kt) fun a₃ => Prog.call (S := groupSig D) GroupOp.generate a₃

/-- **The block-system reduction with its kernel**: compute the block kernel `K` by the induced
action, then branch over `G / K` and process the blocks in each branch. -/
def blockReduceProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (w : var Ty.win) (σ : var Ty.perm) (G : var (Ty.group D))
    (bs : var (.list (.list .nat))) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst G) fun n => .bind (.op1 .snd G) fun gd => .bind (.op1 .fst gd) fun gs =>
  .bind (blockKernelProg n gs bs) fun K => blockProg sub xy w σ G K bs

end Programs

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem sum_blockCost (bs : List (List ℕ)) :
    (bs.map fun b => 5 * b.length + 8 + 1).sum = 5 * bs.flatten.length + 9 * bs.length := by
  rw [List.length_flatten]
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    ring

theorem RunsWithin.blockIdxProg (n : ℕ) (bs : List (List ℕ)) :
    RunsWithin X body (Programs.blockIdxProg n bs) (blockIdx n bs)
      (2 * n + 6 * bs.flatten.length + 9 * bs.length + 6) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat)
    (b' := .prod .nat (.list (.prod .nat .nat))) (cf := fun b => 5 * b.length + 8)
    (f := fun (acc : (Ty.prod .nat (.list (.prod .nat .nat))).denote)
      (b : (Ty.list .nat).denote) =>
      Prog.bind (.op1 .fst acc) fun i => .bind (.op1 .snd acc) fun ws =>
      .bind (Programs.mapList (a' := .nat) b fun u => .op2 .pair u i) fun bw =>
      .bind (.op2 .append bw ws) fun ws' =>
      .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' => .op2 .pair i' ws')
    (F := blockWritesStep) bs (0, []) fun acc b _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.mapList_le (c := 1) fun u _ => RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map]
        omega
  have hsum := sum_blockCost bs
  have hlen : (blockWrites bs).length = bs.flatten.length := by
    have := (blockWrites_fold bs 0 []).2.1.length_eq
    simp only [List.length_map, List.map_nil, List.nil_append] at this
    exact this
  rw [hsum] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate]
    change _ + (_ + (_ + (5 * bs.flatten.length + 9 * bs.length + (1 + (n + 1 +
      (n + (blockWrites bs).length + 1)))))) ≤ _
    omega

theorem RunsWithin.blockRepsProg (bs : List (List ℕ)) :
    RunsWithin X body (Programs.blockRepsProg bs) (blockReps bs) (5 * bs.length + 2) := by
  apply RunsWithin.mono
  case h =>
    refine RunsWithin.mapList_le (a' := .list .nat) (b' := .nat) (c := 2)
      (F := fun b : (Ty.list .nat).denote => b.headD 0) fun b _ => ?_
    rcases b with _ | ⟨x, xs⟩
    · apply RunsWithin.mono
      case h => exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h => exact RunsWithin.caseList_cons (RunsWithin.ret _)
      case hc => omega
  case hc => omega

theorem RunsWithin.extendProg {n : ℕ} (bidx : Array ℕ) (reps : List ℕ) {g : PermData}
    (h₁ : g.1.size = n) (h₂ : g.2.size = n) :
    RunsWithin X body (Programs.extendProg n bidx reps g) (PermData.extendTo n bidx reps g)
      (6 * n + 14 * reps.length + 13) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 3) fun r _ => by
      refine RunsWithin.bind_le (c₂ := 2) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      exact RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 3) fun r _ => by
      refine RunsWithin.bind_le (c₂ := 2) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      exact RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, PermData.extendTo, get, Ty.default]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_append,
      Array.length_toList, h₁, h₂]
    omega

theorem RunsWithin.truncProg (n : ℕ) (g : PermData) :
    RunsWithin X body (Programs.truncProg n g) (PermData.truncTo n g) (11 * n + 10) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 1) fun i _ => RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := 1) fun i _ => RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range]
    omega

end Specs

/-! ### The block kernel -/

section Kernel

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The extended generators. -/
def extendGens (n : ℕ) (bs : List (List ℕ)) (gs : GensData) : GensData :=
  gs.map (PermData.extendTo n (blockIdx n bs) (blockReps bs))

/-- The extended group, as generated by the backend. -/
def extGroup (O : Oracle (groupSig D)) (n : ℕ) (bs : List (List ℕ)) (gs : GensData) :
    GroupData D.denote :=
  O.run GroupOp.generate (n + bs.length, extendGens n bs gs)

/-- The kernel of the extended group on the block points, as computed by the backend. -/
def extKernel (O : Oracle (groupSig D)) (n : ℕ) (bs : List (List ℕ)) (gs : GensData) :
    GroupData D.denote :=
  O.run GroupOp.kernel (extGroup O n bs gs, blockWin n bs.length)

/-- The block kernel, as generated by the backend from the truncated kernel generators. -/
def blockKernelModel (O : Oracle (groupSig D)) (n : ℕ) (bs : List (List ℕ)) (gs : GensData) :
    GroupData D.denote :=
  O.run GroupOp.generate (n, (extKernel O n bs gs).2.1.map (PermData.truncTo n))

/-- The cost of computing the block kernel, for degree `n`, `m` window points in `k` blocks,
`s` generators and `sK` kernel generators at degree `n + k`, with the three backend charges. -/
def blockKernelCost (n m k s sK Bge Bke Bgt : ℕ) : ℕ :=
  4 * n + 6 * m + 27 * k + s * (6 * n + 14 * k + 16) + sK * (11 * n + 13) + Bge + Bke + Bgt + 29

/-- The operations used to compute the block kernel. -/
def blockKernelOps (op : GroupOp) : Prop := op = .generate ∨ op = .kernel

/-- **The block kernel by the induced action.** -/
theorem RunsWithin.blockKernelProg (hO : MeetsContractOn DV blockKernelOps X.O)
    (hPre : ∀ op x, blockKernelOps op → GroupPre DV op x → X.Pre op x)
    {n : ℕ} {w : WinData} {bs : List (List ℕ)} {gs : GensData} (hw : w.Valid n)
    (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs)
    (hgs : GensData.AllValid n gs) {Bge Bke Bgt : ℕ}
    (hBge : X.B.call GroupOp.generate (n + bs.length, extendGens n bs gs)
      (extGroup X.O n bs gs) ≤ Bge)
    (hBke : X.B.call GroupOp.kernel (extGroup X.O n bs gs, blockWin n bs.length)
      (extKernel X.O n bs gs) ≤ Bke)
    (hBgt : X.B.call GroupOp.generate (n, (extKernel X.O n bs gs).2.1.map (PermData.truncTo n))
      (blockKernelModel X.O n bs gs) ≤ Bgt) :
    RunsWithin X body (Programs.blockKernelProg n gs bs) (blockKernelModel X.O n bs gs)
        (blockKernelCost n bs.flatten.length bs.length gs.length
          (extKernel X.O n bs gs).2.1.length Bge Bke Bgt) ∧
      (blockKernelModel X.O n bs gs).1 = n ∧
      GroupValid DV n (blockKernelModel X.O n bs gs).2.1 (blockKernelModel X.O n bs gs).2.2 ∧
      GensData.denote n (blockKernelModel X.O n bs gs).2.1 =
        blockKernel (GensData.denote n gs) bs := by
  -- the extended group
  have hegv := GensData.allValid_extendTo hw hbs hG hgs
  have hegden := GensData.denote_extendTo hw hbs hG hgs
  have hgpost := hO .generate (n + bs.length, extendGens n bs gs) (Or.inl rfl) hegv
  have hGe : extGroup X.O n bs gs = X.O.run GroupOp.generate (n + bs.length, extendGens n bs gs) :=
    rfl
  rcases hGe' : X.O.run GroupOp.generate (n + bs.length, extendGens n bs gs) with ⟨n₁, egs, d₁⟩
  rw [hGe'] at hgpost
  obtain ⟨hn₁, hGev, hGeden⟩ := hgpost
  change n₁ = n + bs.length at hn₁
  subst n₁
  change GensData.denote _ egs = GensData.denote _ (extendGens n bs gs) at hGeden
  -- the kernel on the block points
  have hkpre : GroupPre DV .kernel ((n + bs.length, egs, d₁), blockWin n bs.length) :=
    ⟨hGev, valid_blockWin n bs.length, by
      rw [hGeden, extendGens, hegden]
      exact isInvariant_blockWin hw hbs hG⟩
  have hkpost := hO .kernel _ (Or.inr rfl) hkpre
  have hKe : extKernel X.O n bs gs =
      X.O.run GroupOp.kernel ((n + bs.length, egs, d₁), blockWin n bs.length) := by
    rw [extKernel, hGe, hGe']
  rcases hKe' : X.O.run GroupOp.kernel ((n + bs.length, egs, d₁), blockWin n bs.length) with
    ⟨n₂, kes, e₂⟩
  rw [hKe'] at hkpost hKe
  obtain ⟨hn₂, hKev, hKeden⟩ := hkpost
  change n₂ = n + bs.length at hn₂
  subst n₂
  change GensData.denote _ kes = pointwiseStab (GensData.denote _ egs) _ at hKeden
  rw [hGeden, extendGens, hegden] at hKeden
  -- the truncated generators and the block kernel
  have htv := allValid_truncTo hw hbs hG hKev.1 hKeden
  have htden := denote_truncTo hw hbs hG hKev.1 hKeden
  have hfpost := hO .generate (n, kes.map (PermData.truncTo n)) (Or.inl rfl) htv
  have hmodel : blockKernelModel X.O n bs gs =
      X.O.run GroupOp.generate (n, kes.map (PermData.truncTo n)) := by
    rw [blockKernelModel, hKe]
  rw [hKe] at hBgt
  rw [hmodel] at hBgt ⊢
  rw [hKe]
  have hrun : RunsWithin X body (Programs.blockKernelProg n gs bs)
      (X.O.run GroupOp.generate (n, kes.map (PermData.truncTo n)))
      (blockKernelCost n bs.flatten.length bs.length gs.length kes.length Bge Bke Bgt) := by
    have hlr : (blockReps bs).length = bs.length := by simp [blockReps]
    have hmapE := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.perm)
      (xs := gs) (c := 6 * n + 14 * (blockReps bs).length + 13)
      (F := PermData.extendTo n (blockIdx n bs) (blockReps bs))
      (f := fun g => Programs.extendProg n (blockIdx n bs) (blockReps bs) g) fun g hg =>
        RunsWithin.extendProg _ _ (hgs g hg).size_fwd (hgs g hg).size_inv
    have hmapP := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
      (xs := List.range bs.length) (c := 1) (F := (n + ·))
      (f := fun t => Prog.op2 Prim.add n t) fun t _ => RunsWithin.prim _ _
    have hmapT := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.perm)
      (xs := kes) (c := 11 * n + 10) (F := PermData.truncTo n)
      (f := fun l => Programs.truncProg n l) fun l _ => RunsWithin.truncProg n l
    rw [hGe, hGe'] at hBge
    rw [hKe] at hBke
    rw [hGe, hGe'] at hBke
    have hGe2 : X.O.run GroupOp.generate
        (n + bs.length, gs.map (PermData.extendTo n (blockIdx n bs) (blockReps bs))) =
        (n + bs.length, egs, d₁) := hGe'
    have hKe2 : X.O.run GroupOp.kernel ((n + bs.length, egs, d₁),
        WinData.ofPoints (n + bs.length) ((List.range bs.length).map (n + ·))) =
        (n + bs.length, kes, e₂) := hKe'
    have hpairK : Prim.eval (Prim.pair (a := (groupSig D).res GroupOp.generate) (b := Ty.win))
        (Args.cons (n + bs.length, egs, d₁) (Args.cons
          (WinData.ofPoints (n + bs.length) ((List.range bs.length).map (n + ·))) Args.nil)) =
        ((n + bs.length, egs, d₁),
          WinData.ofPoints (n + bs.length) ((List.range bs.length).map (n + ·))) := rfl
    have hBge2 : X.B.call GroupOp.generate
        (n + bs.length, gs.map (PermData.extendTo n (blockIdx n bs) (blockReps bs)))
        (n + bs.length, egs, d₁) ≤ Bge := hBge
    have hBke2 : X.B.call GroupOp.kernel ((n + bs.length, egs, d₁),
        WinData.ofPoints (n + bs.length) ((List.range bs.length).map (n + ·)))
        (n + bs.length, kes, e₂) ≤ Bke := hBke
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.blockIdxProg n bs)
      run_step (RunsWithin.blockRepsProg bs)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hmapE
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hegv))
      simp only [Prim.eval]
      rw [hGe2]
      run_step (RunsWithin.prim _ _)
      run_step hmapP
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (hPre _ _ (Or.inr rfl) hkpre))
      rw [hpairK, hKe2]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hmapT
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.call (hPre _ _ (Or.inl rfl) htv)
    case hc =>
      rw [hpairK]
      simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_map, hlr]
      rw [hGe2, hKe2]
      generalize X.B.call GroupOp.generate
        (n + bs.length, gs.map (PermData.extendTo n (blockIdx n bs) (blockReps bs)))
        (n + bs.length, egs, d₁) = B₁ at hBge2 ⊢
      generalize X.B.call GroupOp.kernel ((n + bs.length, egs, d₁),
        WinData.ofPoints (n + bs.length) ((List.range bs.length).map (n + ·)))
        (n + bs.length, kes, e₂) = B₂ at hBke2 ⊢
      generalize X.B.call GroupOp.generate (n, kes.map (PermData.truncTo n))
        (X.O.run GroupOp.generate (n, kes.map (PermData.truncTo n))) = B₃ at hBgt ⊢
      simp only [blockKernelCost]
      clear * - hBge2 hBke2 hBgt
      simp only [Nat.add_assoc, Nat.reduceAdd] at *
      linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hrun
  · rcases hK' : X.O.run GroupOp.generate (n, kes.map (PermData.truncTo n)) with ⟨n₃, ks, e₃⟩
    rw [hK'] at hfpost
    exact hfpost.1
  · rcases hK' : X.O.run GroupOp.generate (n, kes.map (PermData.truncTo n)) with ⟨n₃, ks, e₃⟩
    rw [hK'] at hfpost
    obtain ⟨rfl, hKv, -⟩ := hfpost
    exact hKv
  · rcases hK' : X.O.run GroupOp.generate (n, kes.map (PermData.truncTo n)) with ⟨n₃, ks, e₃⟩
    rw [hK'] at hfpost
    obtain ⟨-, -, hKden⟩ := hfpost
    rw [hKden]
    exact htden

/-- The operations used by the block-system reduction. -/
def blockReduceOps (op : GroupOp) : Prop := op = .generate ∨ op = .kernel ∨ op = .cosetReps

/-- **The block-system reduction**, with the block kernel computed by the induced action.
The number of branches is `[G : K]` for `K` the block kernel. -/
theorem RunsWithin.blockReduceProg (hO : MeetsContractOn DV blockReduceOps X.O)
    (hPre : ∀ op x, blockReduceOps op → GroupPre DV op x → X.Pre op x)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {n : ℕ} {gs : GensData}
    {d : D.denote} {bs : List (List ℕ)} (hw : w.Valid n) (hσ : σd.Valid n)
    (hGv : GroupValid DV n gs d) (hWG : IsInvariant (GensData.denote n gs) (w.denote n))
    (hbs : IsBlockList w bs) (hG : PermutesBlocks (GensData.denote n gs) bs)
    {Cw : List ℕ → ℕ} {s Bge Bke Bgt Bcr Bgen : ℕ}
    (hBge : X.B.call GroupOp.generate (n + bs.length, extendGens n bs gs)
      (extGroup X.O n bs gs) ≤ Bge)
    (hBke : X.B.call GroupOp.kernel (extGroup X.O n bs gs, blockWin n bs.length)
      (extKernel X.O n bs gs) ≤ Bke)
    (hBgt : X.B.call GroupOp.generate (n, (extKernel X.O n bs gs).2.1.map (PermData.truncTo n))
      (blockKernelModel X.O n bs gs) ≤ Bgt)
    (hsub : SeqSub X body DV sub xy n bs Cw s
      (max s (blockKernelModel X.O n bs gs).2.1.length)
      (GensData.denote n (blockKernelModel X.O n bs gs).2.1))
    (hBcr : X.B.call GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)
      (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)) ≤ Bcr)
    (hB : ∀ hs : GensData, GensData.AllValid n hs →
      hs.length ≤ (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length *
        (max s (blockKernelModel X.O n bs gs).2.1.length + 1) →
      GensData.denote n hs ≤ GensData.denote n gs →
      X.B.call GroupOp.generate (n, hs) (X.O.run GroupOp.generate (n, hs)) ≤ Bgen) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Programs.blockReduceProg sub xy w σd (n, gs, d) bs) ans
        (3 + blockKernelCost n bs.flatten.length bs.length gs.length
            (extKernel X.O n bs gs).2.1.length Bge Bke Bgt +
          (2 + Bcr + (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length *
            (24 * n + blockBranchCost n Cw bs + max s (blockKernelModel X.O n bs gs).2.1.length +
              45) + Bgen + 19)) ∧
      AnsOK DV n (w.denote n) (PermData.denote n σd) (GensData.denote n gs) (xy.1.denote n)
        (xy.2.denote n) ans ∧
      (X.O.run GroupOp.cosetReps ((n, gs, d), blockKernelModel X.O n bs gs)).length *
          Nat.card (blockKernel (GensData.denote n gs) bs) = Nat.card (GensData.denote n gs) ∧
      ∀ sGen, (∀ hs, GensData.AllValid n hs → GensData.denote n hs ≤ GensData.denote n gs →
          (X.O.run GroupOp.generate (n, hs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  obtain ⟨hKrun, hKn, hKv, hKden⟩ := RunsWithin.blockKernelProg (X := X) (body := body)
    (fun op x hop hx => hO op x (by rcases hop with h | h <;> simp [blockReduceOps, h]) hx)
    (fun op x hop hx => hPre op x (by rcases hop with h | h <;> simp [blockReduceOps, h]) hx)
    hw hbs hG hGv.1 hBge hBke hBgt
  rcases hKm : blockKernelModel X.O n bs gs with ⟨n', ks, e⟩
  rw [hKm] at hKn hKv hKden hKrun hsub hBcr hB
  change n' = n at hKn
  subst n'
  obtain ⟨ans, hrun, hok, hcard, hgen⟩ := RunsWithin.blockProg (X := X) (body := body)
    (fun op x hop hx => hO op x (by rcases hop with h | h <;> simp [blockReduceOps, h]) hx)
    (fun op x hop hx => hPre op x (by rcases hop with h | h <;> simp [blockReduceOps, h]) hx)
    hw hσ hGv hWG hKv (le_of_eq hKden) hbs hsub hBcr hB
  refine ⟨ans, ?_, hok, by rw [← hKden]; exact hcard, hgen⟩
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hKrun
    exact hrun
  case hc =>
    simp only [Prim.cost]
    omega

end Kernel

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_blockKernelProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (blockKernelProg (D := D) n₁ g₁ bs₁)
      (blockKernelProg (D := D) n₂ g₂ bs₂) := by
  unfold blockKernelProg blockIdxProg blockRepsProg extendProg truncProg mkWindow mapList
  prog_wf

theorem wf_blockReduceProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm}
    {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {bs₁ : var₁ (.list (.list .nat))} {bs₂ : var₂ (.list (.list .nat))}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hbs : ⟨.list (.list .nat), bs₁, bs₂⟩ ∈ Γ) :
    Prog.Wf r Γ (blockReduceProg sub₁ xy₁ w₁ σ₁ G₁ bs₁)
      (blockReduceProg sub₂ xy₂ w₂ σ₂ G₂ bs₂) := by
  unfold blockReduceProg
  refine .bind (.prim _ (.cons hG .nil)) fun n₁ n₂ => .bind (.prim _ (.cons (by simp [hG]) .nil))
    fun gd₁ gd₂ => .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun gs₁ gs₂ =>
    .bind (wf_blockKernelProg (by simp) (List.Mem.head _) (by simp [hbs])) fun K₁ K₂ =>
    wf_blockProg (hsub.mono fun y hy => by simp [hy]) (by simp [hxy]) (by simp [hw])
      (by simp [hσ]) (by simp [hG]) (List.Mem.head _) (by simp [hbs])

end Wf

end GraphIso.Programs
