module

public import GraphIso.SoJTree.StepProg
public import GraphIso.SoJTree.Worklist
public import GraphIso.SoJTree.Measure
public import GraphIso.SplitJohnson.Bipartite
public import GraphIso.SplitJohnson.Main

/-!
# The Split-or-Johnson trees as costed programs

Stage 14d (`PLAN-14.md` §8): the worklist (`GraphIso/SoJTree/Worklist.lean`) instantiated with
`stepProg` (`GraphIso/SoJTree/StepProg.lean`).

* `bsojProg m t V₁ cs a` runs the frame `(V₁, cs, a, [])`; its output, decoded, is the leaf
  multiset of milestone 11's `bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a)`
  (`bsojProg_leafMs`), within `(stepK m |cs| t + 11)(|cs| + 2)·size + 14`
  (`RunsWithin.bsojProg`); under the hypotheses of `bipartite_split_or_johnson` this is at most
  `bsojPoly m · 2^(128 (⌈log₂ t⌉ + 2)²)` (`bsojProg_cost_le`).
* `sojProg m t c` runs `sojAtD` at every point (`sojAtInitProg`) and then the worklist on the
  frames; its output, decoded, is the leaf multiset of milestone 11's `soj (colOf m c) t`
  (`sojProg_leafMs`), within `300 (m+1)^4 + 30m + 40 + (stepK m t t + 11)(t + 2)·size` for
  `m ≤ 2t` (`RunsWithin.sojProg`); under the hypotheses of `split_or_johnson` this is at most
  `sojPoly m · 2^(129 (⌈log₂ m⌉ + 2)²)` (`sojProg_cost_le`).
* `sojAtProg m t c x` runs the whole tree `sojAt (colOf m c) t x`: the initialization
  `sojAtInitProg` (a leaf, or the frame of the `bsoj` call), then the worklist; its output,
  decoded, is the leaf multiset of `sojAt` (`sojAtProg_leafMs`), within
  `300 (m+1)^3 + 10m + 20 + (stepK m t t + 11)(t + 2)·size` for `m ≤ 2t`
  (`RunsWithin.sojAtProg`).
* Corollaries: the number of outputs is the count of the tree (`bsojProg_length`,
  `sojAtProg_length`, `sojProg_length`), and the decoded outputs are its reachable leaves
  (`bsojProg_reach`, `sojAtProg_reach`, `sojProg_reach`).
* **Leaf sizes**: every output of the worklist from frames with the invariant has size at most
  `outB m q` (`tr_worklist_outSize`, through the generic `tr_worklist_mem`); so the outputs of
  `bsojProg` have size at most `outB m |cs|` (`bsojProg_outSize`) and those of `sojAtProg` and
  `sojProg` at most `outB m t` (`sojAtProg_outSize`, `sojProg_outSize`).

The rank of a frame is its number of cells and its size the size of its tree. `sojAtD` picks the
pair of colours with the least `Nat.pair` code; the program compares pairs by the keys of
`tr_key` (`tr_lt_iff`), at constant cost whatever the colours.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Finset GraphIso GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.Cost GraphIso.Programs
  GraphIso.Sims

/-! ### Rank and size -/

/-- The rank of a frame: its number of cells. -/
def tr_rank (fr : FrameD) : ℕ := fr.cs.length

/-- The size of a frame: the size of its tree. -/
def tr_size (m t : ℕ) (fr : FrameD) : ℕ := (fr.tree m t).size

section Decode

variable {m t : ℕ}

theorem tr_children {fr : FrameD} (hfr : fr.Valid m) :
    ∀ ch ∈ (stepD m t fr).2, ch.Valid m ∧ tr_rank ch < tr_rank fr :=
  stepD_children hfr

theorem tr_size_step {fr : FrameD} (hfr : fr.Valid m) :
    stepWork m t fr + (stepD m t fr).1.length + ((stepD m t fr).2.map (tr_size m t)).sum ≤
      tr_size m t fr :=
  stepD_size hfr

theorem tr_one_le_size (fr : FrameD) : 1 ≤ tr_size m t fr := CTree.one_le_size _

theorem tr_map_sum {α β : Type*} (f : α → β) (l : List (Multiset α)) :
    (l.sum).map f = (l.map fun s => s.map f).sum := by
  induction l with
  | nil => simp
  | cons s l ih => simp [ih]

/-- **The outputs reached from a frame decode to the leaves of its tree.** -/
theorem tr_enumMs : ∀ (n : ℕ) (fr : FrameD), tr_rank fr = n → fr.Valid m →
    (enumMs (stepD m t) tr_rank fr).map (decodeOut m) = (fr.tree m t).leafMs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fr hn hfr
    rw [enumMs_eq (I := FrameD.Valid m) (fun fr h => tr_children h) hfr, stepD_leafMs hfr,
      Multiset.map_add, tr_map_sum, List.map_map]
    congr 1
    congr 1
    refine List.map_congr_left fun ch hch => ?_
    have hc := tr_children (t := t) hfr ch hch
    exact ih _ (hn ▸ hc.2) ch rfl hc.1

theorem tr_worklist_ms {stack : List FrameD} (hI : ∀ fr ∈ stack, fr.Valid m) (out : List OutD) :
    ((worklistD (stepD m t) tr_rank (tr_size m t) stack out).map (decodeOut m) :
        Multiset (Option (Out (Fin m)))) =
      (out.map (decodeOut m) : Multiset _) + (stack.map fun fr => (fr.tree m t).leafMs).sum := by
  have h := worklistD_ms (I := FrameD.Valid m) (w := stepWork m t)
    (fun fr h => tr_children h) (fun fr h => tr_size_step h) (fun fr _ => tr_one_le_size fr)
    hI out
  rw [← Multiset.map_coe, h, Multiset.map_add, tr_map_sum, List.map_map]
  simp only [Multiset.map_coe]
  congr 2
  exact List.map_congr_left fun fr hfr => tr_enumMs _ fr rfl (hI fr hfr)

end Decode

/-! ### `sojAt` on data, through keys of `Nat.pair`

`sojAtD` takes the pair of colours with the least `Nat.pair` code. Computing codes costs time
linear in the colours, so the program compares pairs by their keys instead: `Nat.pair a b` is
`M² + r` with `(M, r)` the key below and `r ≤ 2M`, so codes compare as keys do
lexicographically (`tr_lt_iff`). -/

section SojData

/-- The key `(M, r)` of `Nat.pair a b = M² + r`. -/
def tr_key (a b : ℕ) : ℕ × ℕ := if a < b then (b, a) else (a, a + b)

theorem tr_pair_key (a b : ℕ) :
    Nat.pair a b = (tr_key a b).1 * (tr_key a b).1 + (tr_key a b).2 ∧
      (tr_key a b).2 ≤ 2 * (tr_key a b).1 := by
  unfold tr_key Nat.pair
  split <;> constructor <;> (try simp) <;> omega

/-- Comparing pairs of colours by their codes, through the keys. -/
def tr_lt (p q : ℕ × ℕ) : Bool :=
  decide ((tr_key p.1 p.2).1 < (tr_key q.1 q.2).1) ||
    (decide ((tr_key p.1 p.2).1 = (tr_key q.1 q.2).1) &&
      decide ((tr_key p.1 p.2).2 < (tr_key q.1 q.2).2))

theorem tr_lt_iff (p q : ℕ × ℕ) : tr_lt p q = true ↔ Nat.pair p.1 p.2 < Nat.pair q.1 q.2 := by
  unfold tr_lt
  obtain ⟨hp, hp'⟩ := tr_pair_key p.1 p.2
  obtain ⟨hq, hq'⟩ := tr_pair_key q.1 q.2
  rw [hp, hq]
  generalize (tr_key p.1 p.2).1 = M at hp' ⊢
  generalize (tr_key p.1 p.2).2 = k at hp' ⊢
  generalize (tr_key q.1 q.2).1 = M' at hq' ⊢
  generalize (tr_key q.1 q.2).2 = k' at hq' ⊢
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · have : (M + 1) * (M + 1) ≤ M' * M' := Nat.mul_le_mul h h
      nlinarith
    · omega
  · intro h
    rcases lt_trichotomy M M' with h' | rfl | h'
    · exact .inl h'
    · exact .inr ⟨rfl, by omega⟩
    · have : (M' + 1) * (M' + 1) ≤ M * M := Nat.mul_le_mul h' h'
      nlinarith

/-- One step of the selection of the least pair. -/
def tr_selStep (best : Option (ℕ × ℕ)) (p : ℕ × ℕ) : Option (ℕ × ℕ) :=
  match best with
  | none => some p
  | some q => if tr_lt p q then some p else some q

/-- The pair with the least code. -/
def tr_selD (l : List (ℕ × ℕ)) : Option (ℕ × ℕ) := l.foldl tr_selStep none

theorem tr_selD_aux : ∀ (l : List (ℕ × ℕ)) (q : ℕ × ℕ),
    (l.foldl tr_selStep (some q)).map (fun p => Nat.pair p.1 p.2) =
      some ((l.map fun p => Nat.pair p.1 p.2).foldl min (Nat.pair q.1 q.2))
  | [], q => rfl
  | p :: l, q => by
    simp only [List.foldl_cons, List.map_cons]
    by_cases h : tr_lt p q = true
    · have h' := (tr_lt_iff p q).1 h
      rw [show tr_selStep (some q) p = some p by simp [tr_selStep, h], tr_selD_aux l p,
        min_eq_right h'.le]
    · have h' : Nat.pair q.1 q.2 ≤ Nat.pair p.1 p.2 := by
        by_contra hc
        exact h ((tr_lt_iff p q).2 (by omega))
      rw [show tr_selStep (some q) p = some q by simp [tr_selStep, h], tr_selD_aux l q,
        min_eq_left h']

/-- **The selection computes `optMin` of the codes.** -/
theorem tr_selD_spec (l : List (ℕ × ℕ)) :
    (tr_selD l).map (fun p => Nat.pair p.1 p.2) = optMin (l.map fun p => Nat.pair p.1 p.2) := by
  cases l with
  | nil => rfl
  | cons p l =>
    simp only [tr_selD, List.foldl_cons, List.map_cons, optMin]
    exact tr_selD_aux l p

/-- The pairs of colours of `sojAt`. -/
def tr_pairsD (m : ℕ) (c : Array ℕ) (x : ℕ) (big : List ℕ) : List (ℕ × ℕ) :=
  big.flatMap fun y => ((List.range m).filter fun z =>
    decide (get c (x * m + z) ∉ big.map (fun y' => get c (x * m + y')) ∧
      get c (y * m + z) ∉ big.map (fun y' => get c (x * m + y')))).map fun z =>
    (get c (x * m + z), get c (y * m + z))

theorem tr_sojPairsD (m : ℕ) (c : Array ℕ) (x : ℕ) (big : List ℕ) :
    sojPairsD m c x big = (tr_pairsD m c x big).map fun p => Nat.pair p.1 p.2 := by
  simp only [sojPairsD, tr_pairsD, List.map_flatMap, List.map_map]
  rfl

/-- **`sojAtD` through the selection by keys.** -/
theorem tr_sojAtD_eq (m t : ℕ) (c : Array ℕ) (x : ℕ) :
    sojAtD m t c x =
      if sojBigD m t c x = [] then
        .inl (partD (rowD m c x) (colBlkD m (List.range m) (rowD m c x)))
      else
        match tr_selD (tr_pairsD m c x (sojBigD m t c x)) with
        | none => .inl noneD
        | some q =>
          .inr (sojBigD m t c x, sojCellsD m c x q.1,
            sojRelD m c (sojCellsD m c x q.1) q.2, [(true, sojBigD m t c x, rowD m c x)]) := by
  unfold sojAtD
  split
  · rfl
  have h := tr_selD_spec (tr_pairsD m c x (sojBigD m t c x))
  rw [← tr_sojPairsD] at h
  rcases hs : tr_selD (tr_pairsD m c x (sojBigD m t c x)) with _ | q
  · rw [hs] at h
    simp only [Option.map_none] at h
    rw [← h]
  · rw [hs] at h
    simp only [Option.map_some] at h
    rw [← h]
    simp only [Nat.unpair_pair]

end SojData

/-! ### Properties of all outputs -/

section Outputs

variable {α β : Type} {F : α → List β × List α} {I : α → Prop} {ρ sz w : α → ℕ}
  {P : β → Prop}

theorem tr_mem_list_sum {γ : Type*} {o : β} (f : γ → Multiset β) :
    ∀ {L : List γ}, o ∈ (L.map f).sum → ∃ x ∈ L, o ∈ f x
  | [], h => by simp at h
  | x :: L, h => by
    rw [List.map_cons, List.sum_cons, Multiset.mem_add] at h
    rcases h with h | h
    · exact ⟨x, List.mem_cons_self, h⟩
    · obtain ⟨y, hy, hoy⟩ := tr_mem_list_sum f h
      exact ⟨y, List.mem_cons_of_mem _ hy, hoy⟩

/-- Every output reached from an `I`-frame satisfies `P`, if every frame's own outputs do. -/
theorem tr_enumMs_mem (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr)
    (hP : ∀ fr, I fr → ∀ o ∈ (F fr).1, P o) :
    ∀ (n : ℕ) (fr : α), ρ fr = n → I fr → ∀ o ∈ enumMs F ρ fr, P o := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro fr hn hfr o ho
    rw [enumMs_eq h₂ hfr, Multiset.mem_add] at ho
    rcases ho with ho | ho
    · exact hP fr hfr o (by simpa using ho)
    · obtain ⟨ch, hch, hos⟩ := tr_mem_list_sum (enumMs F ρ) ho
      have hc := h₂ fr hfr ch hch
      exact ih _ (hn ▸ hc.2) ch rfl hc.1 o hos

/-- **Every output of the worklist satisfies `P`**, if those of `out` and of every step of an
`I`-frame do. -/
theorem tr_worklist_mem (h₂ : ∀ fr, I fr → ∀ ch ∈ (F fr).2, I ch ∧ ρ ch < ρ fr)
    (h₃ : ∀ fr, I fr → w fr + (F fr).1.length + ((F fr).2.map sz).sum ≤ sz fr)
    (h₄ : ∀ fr, I fr → 1 ≤ sz fr) (hP : ∀ fr, I fr → ∀ o ∈ (F fr).1, P o)
    {stack : List α} (hI : ∀ fr ∈ stack, I fr) {out : List β} (hout : ∀ o ∈ out, P o) :
    ∀ o ∈ worklistD F ρ sz stack out, P o := by
  intro o ho
  have hms := worklistD_ms h₂ h₃ h₄ hI out
  have ho' : o ∈ ((worklistD F ρ sz stack out : List β) : Multiset β) := by simpa using ho
  rw [hms, Multiset.mem_add] at ho'
  rcases ho' with ho' | ho'
  · exact hout o (by simpa using ho')
  · obtain ⟨fr, hfr, hos⟩ := tr_mem_list_sum (enumMs F ρ) ho'
    exact tr_enumMs_mem h₂ hP _ fr rfl (hI fr hfr) o hos

end Outputs

/-- **The leaves produced from frames with the invariant are small.** -/
theorem tr_worklist_outSize {m q t : ℕ} {stack : List FrameD}
    (hI : ∀ fr ∈ stack, fr.ValidP m q t) {out : List OutD}
    (hout : ∀ o ∈ out, outSize o ≤ outB m q) :
    ∀ o ∈ worklistD (stepD m t) tr_rank (tr_size m t) stack out, outSize o ≤ outB m q :=
  tr_worklist_mem (I := FrameD.ValidP m q t) (w := stepWork m t)
    (fun _ h ch hch => ⟨stepD_validP h ch hch, (tr_children h.valid ch hch).2⟩)
    (fun _ h => tr_size_step h.valid) (fun fr _ => tr_one_le_size fr)
    (fun _ h => stepD_outSize h) hI hout

/-! ### The programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **`bsoj` as a program**: the worklist from the frame `(V₁, cs, a, [])`. -/
def bsojProg (m t : var .nat) (V₁ : var (.list .nat)) (cs : var (.list (.list .nat)))
    (a : var (.array .bool)) : Prog S rec var (.list outTy) :=
  .bind (.op0 .nil) fun nw => .bind (sp_frameProg V₁ cs a nw) fun fr =>
  .bind (.op0 .nil) fun e => .bind (.op2 .cons fr e) fun stack =>
  .bind (.op0 .nil) fun out => worklistProg (fun fr => stepProg m t fr) stack out

/-- The key of `Nat.pair a b`. -/
def tr_keyProg (a b : var .nat) : Prog S rec var (.prod .nat .nat) :=
  .bind (.op2 .natLt a b) fun lt =>
  .ite lt (.op2 .pair b a) (.bind (.op2 .add a b) fun s => .op2 .pair a s)

/-- `tr_lt`: compare two pairs of colours by their keys. -/
def tr_ltProg (p q : var (.prod .nat .nat)) : Prog S rec var .bool :=
  .bind (.op1 .fst p) fun a₁ => .bind (.op1 .snd p) fun b₁ =>
  .bind (.op1 .fst q) fun a₂ => .bind (.op1 .snd q) fun b₂ =>
  .bind (tr_keyProg a₁ b₁) fun k₁ => .bind (tr_keyProg a₂ b₂) fun k₂ =>
  .bind (.op1 .fst k₁) fun M₁ => .bind (.op1 .snd k₁) fun r₁ =>
  .bind (.op1 .fst k₂) fun M₂ => .bind (.op1 .snd k₂) fun r₂ =>
  .bind (.op2 .natLt M₁ M₂) fun l₁ => .bind (.op2 .natEq M₁ M₂) fun e =>
  .bind (.op2 .natLt r₁ r₂) fun l₂ => .bind (.op2 .and e l₂) fun c₂ => .op2 .or l₁ c₂

/-- `tr_selD`: the pair with the least code. -/
def tr_selProg (l : var (.list (.prod .nat .nat))) : Prog S rec var (.option (.prod .nat .nat)) :=
  .bind (.op0 .none) fun init => .foldList l init fun best p =>
    .caseOption best (.op1 .some p) fun q => .bind (tr_ltProg p q) fun lt =>
      .ite lt (.op1 .some p) (.op1 .some q)

/-- `rowD`. -/
def tr_rowProg (m : var .nat) (offs c : var (.array .nat)) (x : var .nat) :
    Prog S rec var (.array .nat) :=
  .bind (.op1 .range m) fun rm => .bind (mapList rm fun y => csColProg offs c x y) fun l =>
  .op1 .arrayOfList l

/-- `sojBigD`. -/
def tr_bigProg (m t : var .nat) (offs c : var (.array .nat)) (x : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .range m) fun rm => Toolkit.filterList rm fun y =>
    .bind (csColProg offs c x y) fun cy =>
    .bind (Toolkit.filterList rm fun z =>
      .bind (csColProg offs c x z) fun cz => .op2 .natEq cz cy) fun cls =>
    .bind (.op1 .length cls) fun n => .op2 .natLt t n

/-- `tr_pairsD`. -/
def tr_pairsProg (m : var .nat) (offs c : var (.array .nat)) (x : var .nat)
    (big : var (.list .nat)) : Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (mapList big fun y => csColProg offs c x y) fun aqua =>
  .bind (.op1 .range m) fun rm =>
  .bind (mapList big fun y =>
    .bind (Toolkit.filterList rm fun z =>
      .bind (csColProg offs c x z) fun cx => .bind (csColProg offs c y z) fun cy =>
      .bind (SoJProg.memProg cx aqua) fun i₁ => .bind (SoJProg.memProg cy aqua) fun i₂ =>
      .bind (.op1 .not i₁) fun n₁ => .bind (.op1 .not i₂) fun n₂ => .op2 .and n₁ n₂) fun zs =>
    mapList zs fun z => .bind (csColProg offs c x z) fun cx =>
      .bind (csColProg offs c y z) fun cy => .op2 .pair cx cy) fun rows =>
  sp_flattenProg rows

/-- `sojCellsD`. -/
def tr_cellsProg (m : var .nat) (offs c : var (.array .nat)) (x k : var .nat) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .range m) fun rm =>
  .bind (Toolkit.filterList rm fun y =>
    .bind (csColProg offs c x y) fun cy => .op2 .natEq cy k) fun ys =>
  mapList ys fun y => .bind (.op0 .nil) fun nl => .op2 .cons y nl

/-- `sojRelD`. -/
def tr_relProg (m : var .nat) (offs c : var (.array .nat)) (cells : var (.list (.list .nat)))
    (k : var .nat) : Prog S rec var (.array .bool) :=
  .bind (.op1 .range m) fun rm =>
  .bind (mapList rm fun z => mapList cells fun cell => anyList cell fun y =>
    .bind (csColProg offs c z y) fun cz => .op2 .natEq cz k) fun rows =>
  .bind (sp_flattenProg rows) fun l => .op1 .arrayOfList l

/-- The frame branch of `sojAtD`, as a split pair. -/
def tr_sojFrameProg (m : var .nat) (offs c : var (.array .nat)) (x : var .nat)
    (big : var (.list .nat)) (row : var (.array .nat)) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (tr_pairsProg m offs c x big) fun ps => .bind (tr_selProg ps) fun sel =>
  .caseOption sel (.bind noneProg fun n => sp_leafPair n) fun q =>
    .bind (.op1 .fst q) fun k₁ => .bind (.op1 .snd q) fun k₂ =>
    .bind (tr_cellsProg m offs c x k₁) fun cells => .bind (tr_relProg m offs c cells k₂) fun rel =>
    .bind (.op0 (.boolLit true)) fun tt => .bind (.op2 .pair big row) fun br =>
    .bind (.op2 .pair tt br) fun op => .bind (.op0 .nil) fun nl =>
    .bind (.op2 .cons op nl) fun ops => .bind (sp_frameProg big cells rel ops) fun fr =>
    sp_framePair fr

/-- **`sojAtD` as a program**, as a split pair: the leaf of `sojAt` or the frame of its `bsoj`
call (the initialization of `sojAtProg` and `sojProg`). -/
def sojAtInitProg (m t : var .nat) (offs c : var (.array .nat)) (x : var .nat) :
    Prog S rec var (.prod (.list outTy) (.list frameTy)) :=
  .bind (tr_rowProg m offs c x) fun row => .bind (tr_bigProg m t offs c x) fun big =>
  .caseList big
    (.bind (.op1 .range m) fun rm => .bind (colBlkProg m rm row) fun blk =>
      .bind (partProg row blk) fun p => sp_leafPair p)
    fun _ _ => tr_sojFrameProg m offs c x big row

/-- **`sojAt` as a program**: the initialization at `x`, then the worklist on its frame. -/
def sojAtProg (m t : var .nat) (c : var (.array .nat)) (x : var .nat) :
    Prog S rec var (.list outTy) :=
  .bind (csOffsProg m) fun offs => .bind (sojAtInitProg m t offs c x) fun pr =>
  .bind (.op1 .fst pr) fun ls => .bind (.op1 .snd pr) fun fs =>
  worklistProg (fun fr => stepProg m t fr) fs ls

/-- **`soj` as a program**: `sojAtD` at every point, then the worklist on the frames. -/
def sojProg (m t : var .nat) (c : var (.array .nat)) : Prog S rec var (.list outTy) :=
  .bind (csOffsProg m) fun offs => .bind (.op1 .range m) fun rm =>
  .bind (mapList rm fun x => sojAtInitProg m t offs c x) fun prs =>
  .bind (sp_catProg prs) fun pr => .bind (.op1 .fst pr) fun ls => .bind (.op1 .snd pr) fun fs =>
  worklistProg (fun fr => stepProg m t fr) fs ls

end Prog

/-! ### `bsoj` -/

section Bsoj

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem tr_tree_init (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a' : Array Bool) :
    FrameD.tree m t ((V₁, cs, a', []) : FrameD) =
      wrapT m [] (bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a')) := rfl

/-- **The output of `bsojProg` decodes to the leaves of `bsoj`.** -/
theorem bsojProg_leafMs {m t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a' : Array Bool}
    (hfr : FrameD.Valid m (V₁, cs, a', [])) :
    ((worklistD (stepD m t) tr_rank (tr_size m t) [(V₁, cs, a', [])] []).map (decodeOut m) :
        Multiset (Option (Out (Fin m)))) =
      (bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a')).leafMs := by
  rw [tr_worklist_ms (by simpa using hfr) []]
  simp only [List.map_nil, Multiset.coe_nil, zero_add, List.map_cons, List.sum_cons,
    List.sum_nil, add_zero]
  rw [tr_tree_init, leafMs_wrapT]
  exact Multiset.map_id' _

theorem bsojProg_length {m t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a' : Array Bool}
    (hfr : FrameD.Valid m (V₁, cs, a', [])) :
    (worklistD (stepD m t) tr_rank (tr_size m t) [(V₁, cs, a', [])] []).length =
      (bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a')).count := by
  rw [← CTree.card_leafMs, ← bsojProg_leafMs hfr]
  simp

theorem bsojProg_reach {m t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a' : Array Bool}
    (hfr : FrameD.Valid m (V₁, cs, a', [])) (o : Option (Out (Fin m))) :
    (∃ d ∈ worklistD (stepD m t) tr_rank (tr_size m t) [(V₁, cs, a', [])] [],
      decodeOut m d = o) ↔ (bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a')).Reach o := by
  rw [← CTree.mem_leafMs, ← bsojProg_leafMs hfr]
  simp

/-- **The leaves of `bsojProg` are small**: at most `outB m |cs|`. -/
theorem bsojProg_outSize {m t : ℕ} {V₁ : List ℕ} {cs : List (List ℕ)} {a' : Array Bool}
    (hfr : FrameD.Valid m (V₁, cs, a', [])) (hn : V₁.length ≤ 2 * t)
    (hcl : ∀ c ∈ cs, c.length ≤ m) :
    ∀ o ∈ worklistD (stepD m t) tr_rank (tr_size m t) [(V₁, cs, a', [])] [],
      outSize o ≤ outB m cs.length :=
  tr_worklist_outSize (fun fr hfr' => by
    rw [List.mem_singleton.1 hfr']
    exact ⟨hfr, hn, le_rfl, hcl, by simp [FrameD.wr], by simp [FrameD.wr, FrameD.cs]⟩)
    (by simp)

/-- **`bsojProg`'s cost**: the worklist's, with the rank `|cs|` and the size of `bsoj`. -/
theorem RunsWithin.bsojProg (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a' : Array Bool)
    (hfr : FrameD.Valid m (V₁, cs, a', [])) (hn : V₁.length ≤ 2 * t)
    (hcl : ∀ c ∈ cs, c.length ≤ m) :
    RunsWithin X body (SoJTree.bsojProg m t V₁ cs a')
      (worklistD (stepD m t) tr_rank (tr_size m t) [(V₁, cs, a', [])] [])
      ((stepK m cs.length t + 11) *
        ((cs.length + 2) * (bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a')).size) + 14) := by
  have hP : FrameD.ValidP m cs.length t (V₁, cs, a', []) :=
    ⟨hfr, hn, le_rfl, hcl, by simp [FrameD.wr], by simp [FrameD.wr, FrameD.cs]⟩
  have hwl := RunsWithin.worklistProg (X := X) (body := body) (φ := frameTy) (ω := outTy)
    (f := fun fr => SoJTree.stepProg m t fr) (F := stepD m t)
    (I := FrameD.ValidP m cs.length t) (ρ := tr_rank) (sz := tr_size m t)
    (w := stepWork m t) (K := stepK m cs.length t)
    (fun fr h => by simpa [Nat.add_assoc] using RunsWithin.stepProg m t fr h)
    (fun fr h ch hch => ⟨stepD_validP h ch hch, (tr_children h.valid ch hch).2⟩)
    (fun fr h => tr_size_step h.valid) (fun fr _ => tr_one_le_size fr)
    (stack := [(V₁, cs, a', [])]) (by simpa using hP) []
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.sp_frameProg _ _ _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hwl
  case hc =>
    simp only [Prim.cost, wlPot, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, tr_rank, tr_size, FrameD.cs, tr_tree_init, size_wrapT]
    omega

theorem stepK_mono {m q q' t t' : ℕ} (hq : q ≤ q') (ht : t ≤ t') : stepK m q t ≤ stepK m q' t' := by
  unfold stepK
  gcongr

/-- The polynomial factor of `bsojProg_cost_le`. -/
def bsojPoly (m : ℕ) : ℕ := (stepK m m m + 11) * (m + 2) * (4 * m + 4) + 14

theorem tr_card_famOf {m : ℕ} {cs : List (List ℕ)} (h : (cs.map (setOf m)).Nodup) :
    (famOf m cs).card = cs.length := by
  unfold famOf
  rw [List.toFinset_card_of_nodup h, List.length_map]

/-- **`bsojProg` within a polynomial times the count bound of `bipartite_split_or_johnson`.** -/
theorem bsojProg_cost_le (m t : ℕ) (V₁ : List ℕ) (cs : List (List ℕ)) (a' : Array Bool)
    (hfr : FrameD.Valid m (V₁, cs, a', [])) (hcl : ∀ c ∈ cs, c.length ≤ m)
    (hcells : ∀ s ∈ famOf m cs, s.Nonempty)
    (hdisj : ∀ s ∈ famOf m cs, ∀ s' ∈ famOf m cs, s ≠ s' → Disjoint s s')
    (hv : (famOf m cs).card ≤ t) (h₁ : (setOf m V₁).card + 2 ≤ 2 * t)
    (h₂ : t < (setOf m V₁).card)
    (htw : ∀ x ∈ setOf m V₁,
      (Coherent.twinCls (setOf m V₁) (famOf m cs) (relOf m cs a') x).card ≤ t) :
    RunsWithin X body (SoJTree.bsojProg m t V₁ cs a')
      (worklistD (stepD m t) tr_rank (tr_size m t) [(V₁, cs, a', [])] [])
      (bsojPoly m * 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2)) := by
  have hV : (setOf m V₁).card = V₁.length := card_setOf hfr.nodup hfr.lt
  have hC : (famOf m cs).card = cs.length := tr_card_famOf hfr.cells
  have hVm : V₁.length ≤ m := sp_length_le_of_lt hfr.nodup hfr.lt
  obtain ⟨hlive, hcount, -⟩ := bipartite_split_or_johnson hcells hdisj hv h₁ h₂ htw
  have hsize := CTree.size_le_of_live hlive
  have hheight := height_bsoj_le t (setOf m V₁) (famOf m cs) (relOf m cs a')
  have hcs : cs.length ≤ m := by omega
  have htm : t ≤ m := by omega
  have hrun := RunsWithin.bsojProg (X := X) (body := body) m t V₁ cs a' hfr (by omega) hcl
  refine hrun.mono ?_
  set T := bsoj t (setOf m V₁) (famOf m cs) (relOf m cs a')
  set E := 2 ^ (128 * (Nat.clog 2 t + 2) ^ 2)
  have hE : 1 ≤ E := Nat.one_le_two_pow
  have hK := stepK_mono (m := m) hcs htm
  have h₃ : T.size ≤ (4 * m + 4) * E := by
    have : 2 * (T.height + 1) ≤ 4 * m + 4 := by omega
    calc T.size ≤ 2 * (T.height + 1) * T.count := hsize
      _ ≤ (4 * m + 4) * E := Nat.mul_le_mul this hcount
  have h₄ : (stepK m cs.length t + 11) * ((cs.length + 2) * T.size) ≤
      (stepK m m m + 11) * ((m + 2) * ((4 * m + 4) * E)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) h₃)
  unfold bsojPoly
  clear_value E
  generalize stepK m m m = K at h₄ ⊢
  have e : (K + 11) * ((m + 2) * ((4 * m + 4) * E)) = (K + 11) * (m + 2) * (4 * m + 4) * E := by
    ring
  have e' : ((K + 11) * (m + 2) * (4 * m + 4) + 14) * E =
      (K + 11) * (m + 2) * (4 * m + 4) * E + 14 * E := by ring
  omega

end Bsoj

/-! ### `soj`: the small programs -/

section SojSmall

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem tr_fA {m : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) (y : ℕ) :
    fA (offsArr m) c x y = get c (x * m + y) := by
  simp only [fA, offsArr, get_offsets hx]

theorem tr_col {m : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) (y : ℕ) :
    RunsWithin X body (SoJProg.csColProg (offsArr m) c x y) (get c (x * m + y)) 3 :=
  (SoJProg.RunsWithin.csColProg (offsArr m) c x y).of_eq (tr_fA c hx y)

theorem RunsWithin.tr_keyProg (a' b' : ℕ) :
    RunsWithin X body (SoJTree.tr_keyProg a' b') (tr_key a' b') 4 := by
  by_cases h : a' < b'
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_pos (by simp [Prim.eval, h])
      exact RunsWithin.prim_le (by simp [Prim.eval, tr_key, h]) le_rfl
    case hc => simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.ite_neg (by simp [Prim.eval, h])
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval, tr_key, h]) le_rfl
    case hc => simp [Prim.cost]

theorem RunsWithin.tr_ltProg (p q : ℕ × ℕ) :
    RunsWithin X body (SoJTree.tr_ltProg p q) (tr_lt p q) 25 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.tr_keyProg p.1 p.2)
    run_step (RunsWithin.tr_keyProg q.1 q.2)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, tr_lt, Bool.beq_eq_decide_eq]) le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.tr_selProg (l : List (ℕ × ℕ)) :
    RunsWithin X body (SoJTree.tr_selProg l) (tr_selD l) (29 * l.length + 1) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .prod .nat .nat)
    (b' := .option (.prod .nat .nat)) (F := tr_selStep) (cf := fun _ => 28)
    (f := fun best p => Prog.caseOption best (.op1 .some p) fun q =>
      .bind (SoJTree.tr_ltProg p q) fun lt => .ite lt (.op1 .some p) (.op1 .some q)) l none
    fun best p _ => by
      rcases best with _ | q
      · exact (RunsWithin.caseOption_none (RunsWithin.prim_le rfl le_rfl)).mono
          (by simp [Prim.cost])
      · by_cases h : tr_lt p q = true
        · refine (RunsWithin.caseOption_some (RunsWithin.bind_le (RunsWithin.tr_ltProg p q)
            (RunsWithin.ite_pos h (RunsWithin.prim_le (by simp [Prim.eval, tr_selStep, h])
              le_rfl)) le_rfl)).mono (by simp [Prim.cost])
        · have h' : tr_lt p q = false := by simpa using h
          refine (RunsWithin.caseOption_some (RunsWithin.bind_le (RunsWithin.tr_ltProg p q)
            (RunsWithin.ite_neg h' (RunsWithin.prim_le (by simp [Prim.eval, tr_selStep, h'])
              le_rfl)) le_rfl)).mono (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, sum_map_const]
    omega

theorem RunsWithin.tr_rowProg {m : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJTree.tr_rowProg m (offsArr m) c x) (rowD m c x) (8 * m + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 3)
      (F := fun y => get c (x * m + y)) fun y _ => tr_col c hx y)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost, Prim.eval]
    omega

theorem RunsWithin.tr_bigProg {m : ℕ} (t : ℕ) (c : Array ℕ) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJTree.tr_bigProg m t (offsArr m) c x) (sojBigD m t c x)
      (m * (9 * m + 12) + m + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    refine (Toolkit.RunsWithin.filterList (a' := .nat) (c := 9 * m + 8)
      (P := fun y => decide (t < ((List.range m).filter fun z =>
        get c (x * m + z) = get c (x * m + y)).length)) fun y _ => ?_).of_eq rfl
    apply RunsWithin.mono
    case h =>
      run_step (tr_col c hx y)
      run_step (Toolkit.RunsWithin.filterList (a' := .nat) (c := 4)
        (P := fun z => decide (get c (x * m + z) = get c (x * m + y))) fun z _ =>
          RunsWithin.bind_le (tr_col c hx z)
            (RunsWithin.prim_le (by simp [Prim.eval, Bool.beq_eq_decide_eq]) le_rfl)
            (by simp [Prim.cost]))
      run_step (RunsWithin.prim_le rfl (c := m + 1) (by
        simp only [Prim.cost, Args.head]
        exact Nat.succ_le_succ ((List.length_filter_le _ _).trans (by simp [Prim.eval]))))
      exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, List.length_range]
      have : m * (4 + 4) = 8 * m := by ring
      omega
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range]
    have : m * (9 * m + 8 + 4) = m * (9 * m + 12) := by ring
    omega

theorem tr_length_pairsD (m : ℕ) (c : Array ℕ) (x : ℕ) (big : List ℕ) :
    (tr_pairsD m c x big).length ≤ big.length * m := by
  unfold tr_pairsD
  rw [List.length_flatMap]
  refine (sp_sum_le big _ fun y _ => ?_).trans le_rfl
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_range).le

theorem tr_sum_len_le {α β : Type*} (l : List α) (f : α → List β) (M : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ M) : ((l.map f).map List.length).sum ≤ l.length * M := by
  rw [List.map_map]
  exact sp_sum_le l _ h

theorem tr_filter_range_le (m : ℕ) (p : ℕ → Bool) : ((List.range m).filter p).length ≤ m :=
  (List.length_filter_le _ _).trans (List.length_range).le

theorem RunsWithin.tr_pairsProg {m : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) (big : List ℕ)
    (hbig : ∀ y ∈ big, y < m) (hbm : big.length ≤ m) :
    RunsWithin X body (SoJTree.tr_pairsProg m (offsArr m) c x big) (tr_pairsD m c x big)
      (60 * (m + 1) ^ 3) := by
  set aqua := big.map fun y => get c (x * m + y) with haqua
  have hal : aqua.length ≤ m := by rw [haqua, List.length_map]; exact hbm
  have hrow : ∀ y ∈ big, RunsWithin X body
      (Prog.bind (Toolkit.filterList (a' := .nat) (List.range m) fun z =>
        Prog.bind (SoJProg.csColProg (offsArr m) c x z) fun cx =>
        Prog.bind (SoJProg.csColProg (offsArr m) c y z) fun cy =>
        Prog.bind (SoJProg.memProg cx aqua) fun i₁ => Prog.bind (SoJProg.memProg cy aqua) fun i₂ =>
        Prog.bind (.op1 .not i₁) fun n₁ => Prog.bind (.op1 .not i₂) fun n₂ => .op2 .and n₁ n₂)
        fun zs => mapList zs fun z => Prog.bind (SoJProg.csColProg (offsArr m) c x z) fun cx =>
          Prog.bind (SoJProg.csColProg (offsArr m) c y z) fun cy => .op2 .pair cx cy)
      (((List.range m).filter fun z =>
        decide (get c (x * m + z) ∉ aqua ∧ get c (y * m + z) ∉ aqua)).map fun z =>
          (get c (x * m + z), get c (y * m + z)))
      (6 * (m * m) + 27 * m + 5) := fun y hy => by
    have hy' := hbig y hy
    apply RunsWithin.mono
    case h =>
      run_step (Toolkit.RunsWithin.filterList (a' := .nat) (c := 6 * aqua.length + 13)
        (P := fun z => decide (get c (x * m + z) ∉ aqua ∧ get c (y * m + z) ∉ aqua)) fun z _ => by
          apply RunsWithin.mono
          case h =>
            run_step (tr_col c hx z)
            run_step (tr_col c hy' z)
            run_step (SoJProg.RunsWithin.memProg _ aqua)
            run_step (SoJProg.RunsWithin.memProg _ aqua)
            run_step (RunsWithin.prim _ _)
            run_step (RunsWithin.prim _ _)
            exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
          case hc =>
            simp only [Prim.cost]
            omega)
      exact (RunsWithin.mapList_le (a' := .nat) (b' := .prod .nat .nat) (c := 7)
        (F := fun z => (get c (x * m + z), get c (y * m + z))) fun z _ =>
          RunsWithin.bind_le (tr_col c hx z) (RunsWithin.bind_le (tr_col c hy' z)
            (RunsWithin.prim_le rfl le_rfl) le_rfl) (by simp [Prim.cost])).mono
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (tr_filter_range_le m _)) _)
    case hc =>
      simp only [List.length_range]
      have h₁ : m * (6 * aqua.length + 13 + 4) ≤ m * (6 * m + 17) :=
        Nat.mul_le_mul_left _ (by omega)
      have e : m * (6 * m + 17) = 6 * (m * m) + 17 * m := by ring
      omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .nat) (c := 3)
      (F := fun y => get c (x * m + y)) fun y hy => tr_col c hx y)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .list (.prod .nat .nat)) hrow)
    refine ((RunsWithin.sp_flattenProg (t := .prod .nat .nat) _).mono
      (Nat.add_le_add_right (Nat.add_le_add_left (tr_sum_len_le _ _ m fun y _ => by
        rw [List.length_map]; exact tr_filter_range_le m _) _) _)).of_eq ?_
    simp only [tr_pairsD, List.flatMap_def, haqua]
  case hc =>
    simp only [Prim.cost, Args.head, List.length_map]
    have h₁ : big.length * (6 * (m * m) + 27 * m + 5 + 3) ≤ m * (6 * (m * m) + 27 * m + 8) :=
      Nat.mul_le_mul hbm (by omega)
    have h₂ : big.length * m ≤ m * m := Nat.mul_le_mul_right _ hbm
    have e : 60 * (m + 1) ^ 3 = 60 * (m * (m * m)) + 180 * (m * m) + 180 * m + 60 := by ring
    have e' : m * (6 * (m * m) + 27 * m + 8) = 6 * (m * (m * m)) + 27 * (m * m) + 8 * m := by
      ring
    omega

theorem RunsWithin.tr_cellsProg {m : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) (k : ℕ) :
    RunsWithin X body (SoJTree.tr_cellsProg m (offsArr m) c x k) (sojCellsD m c x k)
      (14 * m + 6) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (Toolkit.RunsWithin.filterList (a' := .nat) (c := 4)
      (P := fun y => decide (get c (x * m + y) = k)) fun y _ =>
        RunsWithin.bind_le (tr_col c hx y)
          (RunsWithin.prim_le (by simp [Prim.eval, Bool.beq_eq_decide_eq]) le_rfl)
          (by simp [Prim.cost]))
    exact (RunsWithin.mapList_le (a' := .nat) (b' := .list .nat) (c := 2) (F := fun y => [y])
      fun y _ => RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
        (by simp [Prim.cost])).mono
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ (tr_filter_range_le m _)) _)
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range]
    omega

theorem RunsWithin.tr_relProg {m : ℕ} (c : Array ℕ) (cells : List (List ℕ)) (k : ℕ)
    (hcl : cells.length ≤ m) (hcells : ∀ cell ∈ cells, cell.length ≤ 1) :
    RunsWithin X body (SoJTree.tr_relProg m (offsArr m) c cells k) (sojRelD m c cells k)
      (30 * (m + 1) ^ 2) := by
  have hz : ∀ z ∈ List.range m, RunsWithin X body
      (mapList (a' := .list .nat) cells fun cell => anyList cell fun y =>
        Prog.bind (SoJProg.csColProg (offsArr m) c z y) fun cz => .op2 .natEq cz k)
      (cells.map fun cell => cell.any fun y => get c (z * m + y) == k) (10 * m + 2) :=
    fun z hz => by
      have hz' := List.mem_range.1 hz
      refine (RunsWithin.mapList_le (c := 7) fun cell hcell => ?_).mono ?_
      · refine (RunsWithin.anyList_le (c := 4) (P := fun y => get c (z * m + y) == k)
          fun y _ => RunsWithin.bind_le (tr_col c hz' y)
            (RunsWithin.prim_le (by simp [Prim.eval]) le_rfl)
            (by simp [Prim.cost])).mono ?_
        have := hcells cell hcell
        omega
      · have : cells.length * (7 + 3) ≤ m * 10 := Nat.mul_le_mul hcl le_rfl
        omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (a' := .nat) (b' := .list .bool) hz)
    run_step ((RunsWithin.sp_flattenProg (t := .bool) _).mono (Nat.add_le_add_right
      (Nat.add_le_add_left (tr_sum_len_le _ _ m fun z _ => by
        rw [List.length_map]; exact hcl) _) _))
    exact RunsWithin.prim_le (by simp [Prim.eval, sojRelD, List.flatMap_def]) (c := m * m + 1)
      (by
        simp only [Prim.cost, Args.head, List.length_flatten, List.map_map, Function.comp_def,
          List.length_map, sum_map_const, Prim.eval, List.length_range]
        have := Nat.mul_le_mul_left m hcl
        omega)
  case hc =>
    simp only [Prim.cost, Args.head, Prim.eval, List.length_range, List.length_map]
    have e : 30 * (m + 1) ^ 2 = 30 * (m * m) + 60 * m + 30 := by ring
    have e' : m * (10 * m + 2 + 3) = 10 * (m * m) + 5 * m := by ring
    omega

theorem tr_sojCellsD_props (m : ℕ) (c : Array ℕ) (x k : ℕ) :
    (sojCellsD m c x k).length ≤ m ∧ ∀ cell ∈ sojCellsD m c x k, cell.length ≤ 1 := by
  refine ⟨by rw [sojCellsD, List.length_map]; exact tr_filter_range_le m _, fun cell h => ?_⟩
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 h
  simp

theorem RunsWithin.tr_sojFrameProg {m : ℕ} (t : ℕ) (c : Array ℕ) {x : ℕ} (hx : x < m) :
    RunsWithin X body
      (SoJTree.tr_sojFrameProg m (offsArr m) c x (sojBigD m t c x) (rowD m c x))
      (splitI [match tr_selD (tr_pairsD m c x (sojBigD m t c x)) with
        | none => .inl noneD
        | some q => .inr (sojBigD m t c x, sojCellsD m c x q.1,
            sojRelD m c (sojCellsD m c x q.1) q.2, [(true, sojBigD m t c x, rowD m c x)])])
      (200 * (m + 1) ^ 3) := by
  set big := sojBigD m t c x with hbigdef
  have hbig : ∀ y ∈ big, y < m := fun y hy => List.mem_range.1 (List.mem_filter.1 hy).1
  have hbm : big.length ≤ m := tr_filter_range_le m _
  have hps : (tr_pairsD m c x big).length ≤ m * m :=
    (tr_length_pairsD m c x big).trans (Nat.mul_le_mul_right _ hbm)
  have hsel := RunsWithin.tr_selProg (X := X) (body := body) (tr_pairsD m c x big)
  have e : 200 * (m + 1) ^ 3 = 60 * (m + 1) ^ 3 + 140 * (m + 1) ^ 3 := by ring
  have e₂ : (m + 1) ^ 3 = m * (m * m) + 3 * (m * m) + 3 * m + 1 := by ring
  have e₃ : 30 * (m + 1) ^ 2 = 30 * (m * m) + 60 * m + 30 := by ring
  rcases hs : tr_selD (tr_pairsD m c x big) with _ | q
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tr_pairsProg c hx big hbig hbm)
      run_step hsel
      rw [hs]
      apply RunsWithin.caseOption_none
      run_step RunsWithin.noneProg
      exact RunsWithin.sp_leafPair _
    case hc =>
      omega
  · obtain ⟨hcl, hcells⟩ := tr_sojCellsD_props m c x q.1
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tr_pairsProg c hx big hbig hbm)
      run_step hsel
      rw [hs]
      apply RunsWithin.caseOption_some
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.tr_cellsProg c hx q.1)
      run_step (RunsWithin.tr_relProg c (sojCellsD m c x q.1) q.2 hcl hcells)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sp_frameProg _ _ _ _)
      exact RunsWithin.sp_framePair _
    case hc =>
      simp only [Prim.cost]
      omega

/-- **`sojAtD` as a program**, as a split pair. -/
theorem RunsWithin.sojAtInitProg {m : ℕ} (t : ℕ) (c : Array ℕ) {x : ℕ} (hx : x < m) :
    RunsWithin X body (SoJTree.sojAtInitProg m t (offsArr m) c x) (splitI [sojAtD m t c x])
      (300 * (m + 1) ^ 3) := by
  rw [tr_sojAtD_eq]
  have e₂ : (m + 1) ^ 3 = m * (m * m) + 3 * (m * m) + 3 * m + 1 := by ring
  have hb₁ : m * (9 * m + 12) = 9 * (m * m) + 12 * m := by ring
  by_cases hb : sojBigD m t c x = []
  · rw [ite_eq_left hb]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tr_rowProg c hx)
      run_step (RunsWithin.tr_bigProg t c hx)
      rw [hb]
      apply RunsWithin.caseList_nil
      run_step (RunsWithin.prim _ _)
      run_step (SoJProg.RunsWithin.colBlkProg m _ _)
      run_step (RunsWithin.partProg _ _)
      exact RunsWithin.sp_leafPair _
    case hc =>
      simp only [Prim.cost, Args.head, Prim.eval, List.length_range, colBlkCost]
      have : m * (6 * m + 7) = 6 * (m * m) + 7 * m := by ring
      omega
  · rw [ite_eq_right hb]
    obtain ⟨y, ys, hys⟩ := List.exists_cons_of_ne_nil hb
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.tr_rowProg c hx)
      run_step (RunsWithin.tr_bigProg t c hx)
      rw [hys]
      apply RunsWithin.caseList_cons
      rw [← hys]
      exact RunsWithin.tr_sojFrameProg t c hx
    case hc =>
      omega

end SojSmall

/-! ### `soj` -/

section Soj

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem tr_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ n, ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, tr_sum_range g n,
      Finset.sum_range_succ]
    simp

theorem tr_optMin_mem {l : List ℕ} {p : ℕ} (h : optMin l = some p) : p ∈ l := by
  cases l with
  | nil => cases h
  | cons c cs =>
    simp only [optMin, Option.some.injEq] at h
    exact h ▸ foldl_min_mem cs c

/-- **The frames of `sojAtD` satisfy the invariant**, with `q = t` (the cells are the points of
a colour class of at most `t` points in the row of `x`). -/
theorem tr_sojAt_validP {m t : ℕ} {c : Array ℕ} {x : ℕ} (hx : x < m) (hmt : m ≤ 2 * t)
    {fr : FrameD} (h : sojAtD m t c x = .inr fr) : fr.ValidP m t t := by
  have hv := (sojAtD_frame c hx h).1
  unfold sojAtD at h
  split at h
  · cases h
  rename_i hb
  split at h
  · cases h
  rename_i p hp
  cases h
  have hbm : (sojBigD m t c x).length ≤ m := tr_filter_range_le m _
  have hp' := tr_optMin_mem hp
  obtain ⟨y, hy, hpy⟩ := List.mem_flatMap.1 hp'
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hpy
  obtain ⟨hzm, hzc⟩ := List.mem_filter.1 hz
  simp only [decide_eq_true_eq] at hzc
  have hzb : z ∉ sojBigD m t c x := fun hzb =>
    hzc.1 (List.mem_map.2 ⟨z, hzb, rfl⟩)
  have hcnt : ((List.range m).filter fun z' => get c (x * m + z') = get c (x * m + z)).length ≤
      t := by
    by_contra hc
    exact hzb (List.mem_filter.2 ⟨hzm, by simpa using hc⟩)
  have hcl : (sojCellsD m c x (Nat.unpair (Nat.pair (get c (x * m + z))
      (get c (y * m + z)))).1).length ≤ t := by
    rw [Nat.unpair_pair, sojCellsD, List.length_map]
    exact hcnt
  refine ⟨hv, hbm.trans hmt, hcl, fun cell hcell => ?_, fun op hop => ?_, ?_⟩
  · obtain ⟨y', -, rfl⟩ := List.mem_map.1 hcell
    simp only [List.length_singleton]
    omega
  · simp only [FrameD.wr, List.mem_singleton] at hop
    subst hop
    exact hbm
  · simp only [FrameD.wr, FrameD.cs, List.length_singleton]
    omega

theorem tr_soj_leafMs {m : ℕ} (c : Array ℕ) (t : ℕ) :
    (soj (colOf m c) t).leafMs =
      ((List.range m).map fun x =>
        if h : x < m then (sojAt (colOf m c) t ⟨x, h⟩).leafMs else 0).sum := by
  rw [tr_sum_range, ← Fin.sum_univ_eq_sum_range]
  unfold soj
  simp only [CTree.leafMs]
  show ∑ ch ∈ univ.image fun x => ([.inl x] : List (Fin m ⊕ Finset (Fin m))), _ = _
  rw [Finset.sum_image fun x _ y _ hxy => by simpa using hxy]
  exact Finset.sum_congr rfl fun x _ => by simp [x.isLt]

theorem tr_soj_size {m : ℕ} (c : Array ℕ) (t : ℕ) :
    ((List.range m).map fun x =>
        if h : x < m then (sojAt (colOf m c) t ⟨x, h⟩).size else 0).sum ≤
      (soj (colOf m c) t).size := by
  rw [tr_sum_range, ← Fin.sum_univ_eq_sum_range]
  unfold soj
  simp only [CTree.size]
  show _ ≤ 1 + ∑ ch ∈ univ.image fun x => ([.inl x] : List (Fin m ⊕ Finset (Fin m))), _
  rw [Finset.sum_image fun x _ y _ hxy => by simpa using hxy]
  have : ∑ x : Fin m, (if h : x.val < m then (sojAt (colOf m c) t ⟨x.val, h⟩).size else 0) ≤
      ∑ x : Fin m, ((sojAt (colOf m c) t x).size + 1) :=
    Finset.sum_le_sum fun x _ => by simp [x.isLt]
  dsimp only at this ⊢
  omega

theorem tr_items {m t : ℕ} (c : Array ℕ) : ∀ xs : List ℕ, (∀ x ∈ xs, x < m) →
    ((splitI (xs.map (sojAtD m t c))).1.map (decodeOut m) : Multiset _) +
        ((splitI (xs.map (sojAtD m t c))).2.map fun fr => (fr.tree m t).leafMs).sum =
      (xs.map fun x => if h : x < m then (sojAt (colOf m c) t ⟨x, h⟩).leafMs else 0).sum ∧
    ((splitI (xs.map (sojAtD m t c))).2.map fun fr => (fr.tree m t).size).sum ≤
      (xs.map fun x => if h : x < m then (sojAt (colOf m c) t ⟨x, h⟩).size else 0).sum ∧
    ∀ fr ∈ (splitI (xs.map (sojAtD m t c))).2, ∃ x, x < m ∧ sojAtD m t c x = .inr fr
  | [], _ => by simp
  | x :: xs, hxs => by
    have hx := hxs x List.mem_cons_self
    obtain ⟨ih₁, ih₂, ih₃⟩ := tr_items c xs fun y hy => hxs y (List.mem_cons_of_mem _ hy)
    rw [List.map_cons, show sojAtD m t c x :: xs.map (sojAtD m t c) =
      [sojAtD m t c x] ++ xs.map (sojAtD m t c) from rfl, splitI_append]
    simp only [List.map_cons, List.sum_cons, dite_eq_left hx]
    rcases hs : sojAtD m t c x with o | fr
    · have hl := sojAtD_leaf c hx hs
      simp only [splitI_inl, List.singleton_append, List.nil_append, List.map_cons, hl,
        CTree.leafMs, CTree.size]
      refine ⟨?_, by omega, ih₃⟩
      rw [← ih₁, ← Multiset.cons_coe, Multiset.cons_add, Multiset.singleton_add]
    · have hl := sojAtD_frame_leafMs c hx hs
      have hz := sojAtD_frame_size c hx hs
      simp only [splitI_inr, List.nil_append, List.singleton_append, List.map_cons,
        List.sum_cons, hl, hz]
      refine ⟨?_, by omega, fun fr' hfr' => ?_⟩
      · rw [← ih₁]
        abel
      · rcases List.mem_cons.1 hfr' with rfl | h
        · exact ⟨x, hx, hs⟩
        · exact ih₃ fr' h

/-- The items of `sojProg`: `sojAtD` at every point. -/
def tr_sojItems (m t : ℕ) (c : Array ℕ) : List Item := (List.range m).map (sojAtD m t c)

/-- **The output of `sojProg` decodes to the leaves of `soj`.** -/
theorem sojProg_leafMs (m t : ℕ) (c : Array ℕ) :
    ((worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2
        (splitI (tr_sojItems m t c)).1).map (decodeOut m) : Multiset (Option (Out (Fin m)))) =
      (soj (colOf m c) t).leafMs := by
  obtain ⟨h₁, -, h₃⟩ := tr_items (m := m) (t := t) c (List.range m)
    fun x hx => List.mem_range.1 hx
  rw [tr_worklist_ms (fun fr hfr => by
    obtain ⟨x, hx, hs⟩ := h₃ fr hfr
    exact (sojAtD_frame c hx hs).1), tr_soj_leafMs]
  exact h₁

theorem sojProg_length (m t : ℕ) (c : Array ℕ) :
    (worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2
        (splitI (tr_sojItems m t c)).1).length = (soj (colOf m c) t).count := by
  rw [← CTree.card_leafMs, ← sojProg_leafMs]
  simp

theorem sojProg_reach (m t : ℕ) (c : Array ℕ) (o : Option (Out (Fin m))) :
    (∃ d ∈ worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2
        (splitI (tr_sojItems m t c)).1, decodeOut m d = o) ↔ (soj (colOf m c) t).Reach o := by
  rw [← CTree.mem_leafMs, ← sojProg_leafMs]
  simp

theorem tr_wlPot_le {t : ℕ} {sz : FrameD → ℕ} :
    ∀ l : List FrameD, (∀ fr ∈ l, tr_rank fr ≤ t) →
      wlPot tr_rank sz l ≤ (t + 2) * (l.map sz).sum
  | [], _ => by simp [wlPot]
  | fr :: l, h => by
    have h₁ := h fr List.mem_cons_self
    have h₂ := tr_wlPot_le (sz := sz) l fun f hf => h f (List.mem_cons_of_mem _ hf)
    simp only [wlPot, List.map_cons, List.sum_cons] at h₂ ⊢
    have : (tr_rank fr + 2) * sz fr ≤ (t + 2) * sz fr := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_add]
    omega

theorem tr_sum_split_singleton {β : Type*} (L : List β) (F : β → Item) :
    ((L.map fun x => splitI [F x]).map fun pr => pr.1.length + pr.2.length).sum = L.length := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    rcases F x <;> simp <;> omega

/-- **The output of `sojAtProg` decodes to the leaves of `sojAt`.** -/
theorem sojAtProg_leafMs {m t : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) :
    ((worklistD (stepD m t) tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2
        (splitI [sojAtD m t c x]).1).map (decodeOut m) : Multiset (Option (Out (Fin m)))) =
      (sojAt (colOf m c) t ⟨x, hx⟩).leafMs := by
  obtain ⟨h₁, -, h₃⟩ := tr_items (m := m) (t := t) c [x] fun y hy => by
    rw [List.mem_singleton.1 hy]; exact hx
  rw [tr_worklist_ms (fun fr hfr => by
    obtain ⟨y, hy, hs⟩ := h₃ fr hfr
    exact (sojAtD_frame c hy hs).1)]
  simpa [hx] using h₁

theorem sojAtProg_length {m t : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) :
    (worklistD (stepD m t) tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2
        (splitI [sojAtD m t c x]).1).length = (sojAt (colOf m c) t ⟨x, hx⟩).count := by
  rw [← CTree.card_leafMs, ← sojAtProg_leafMs c hx]
  simp

theorem sojAtProg_reach {m t : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m)
    (o : Option (Out (Fin m))) :
    (∃ d ∈ worklistD (stepD m t) tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2
        (splitI [sojAtD m t c x]).1, decodeOut m d = o) ↔
      (sojAt (colOf m c) t ⟨x, hx⟩).Reach o := by
  rw [← CTree.mem_leafMs, ← sojAtProg_leafMs c hx]
  simp

/-- **`sojAtProg`'s cost**: the initialization, then the worklist with the size of `sojAt`. -/
theorem RunsWithin.sojAtProg (m t : ℕ) (c : Array ℕ) {x : ℕ} (hx : x < m) (hmt : m ≤ 2 * t) :
    RunsWithin X body (SoJTree.sojAtProg m t c x)
      (worklistD (stepD m t) tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2
        (splitI [sojAtD m t c x]).1)
      (300 * (m + 1) ^ 3 + 10 * m + 20 +
        (stepK m t t + 11) * ((t + 2) * (sojAt (colOf m c) t ⟨x, hx⟩).size)) := by
  obtain ⟨-, h₂, h₃⟩ := tr_items (m := m) (t := t) c [x] fun y hy => by
    rw [List.mem_singleton.1 hy]; exact hx
  have hP : ∀ fr ∈ (splitI [sojAtD m t c x]).2, fr.ValidP m t t := fun fr hfr => by
    obtain ⟨y, hy, hs⟩ := h₃ fr (by simpa using hfr)
    exact tr_sojAt_validP hy hmt hs
  have hwl := RunsWithin.worklistProg (X := X) (body := body) (φ := frameTy) (ω := outTy)
    (f := fun fr => SoJTree.stepProg m t fr) (F := stepD m t)
    (I := FrameD.ValidP m t t) (ρ := tr_rank) (sz := tr_size m t)
    (w := stepWork m t) (K := stepK m t t)
    (fun fr h => by simpa [Nat.add_assoc] using RunsWithin.stepProg m t fr h)
    (fun fr h ch hch => ⟨stepD_validP h ch hch, (tr_children h.valid ch hch).2⟩)
    (fun fr h => tr_size_step h.valid) (fun fr _ => tr_one_le_size fr) hP
    (splitI [sojAtD m t c x]).1
  have hpot : wlPot tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2 ≤
      (t + 2) * (sojAt (colOf m c) t ⟨x, hx⟩).size := by
    refine (tr_wlPot_le _ fun fr hfr => (hP fr hfr).cells).trans (Nat.mul_le_mul_left _ ?_)
    show ((splitI [sojAtD m t c x]).2.map fun fr => (fr.tree m t).size).sum ≤ _
    simpa [hx] using h₂
  apply RunsWithin.mono
  case h =>
    run_step (SoJProg.RunsWithin.csOffsProg m)
    run_step (RunsWithin.sojAtInitProg t c hx)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hwl
  case hc =>
    simp only [Prim.cost]
    have h₁ : (stepK m t t + 11) * wlPot tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2 ≤
        (stepK m t t + 11) * ((t + 2) * (sojAt (colOf m c) t ⟨x, hx⟩).size) :=
      Nat.mul_le_mul_left _ hpot
    omega

theorem tr_sojAtD_outSize {m t : ℕ} (c : Array ℕ) {x : ℕ} {o : OutD}
    (h : sojAtD m t c x = .inl o) : outSize o ≤ m := by
  unfold sojAtD at h
  split at h
  · cases h
    exact sp_outSize_partD fun l hl => (sp_colBlkD_le m _ _ l hl).trans (by simp)
  split at h
  · cases h
    exact sp_outSize_noneD m
  · cases h

/-- The pieces of the items of `sojProg`. -/
theorem tr_items_pieces {m t : ℕ} (c : Array ℕ) (hmt : m ≤ 2 * t) {xs : List ℕ}
    (hxs : ∀ x ∈ xs, x < m) :
    (∀ fr ∈ (splitI (xs.map (sojAtD m t c))).2, fr.ValidP m t t) ∧
      ∀ o ∈ (splitI (xs.map (sojAtD m t c))).1, outSize o ≤ outB m t := by
  refine ⟨fun fr hfr => ?_, fun o ho => ?_⟩
  · obtain ⟨x, hx, hs⟩ := (tr_items (m := m) (t := t) c xs hxs).2.2 fr hfr
    exact tr_sojAt_validP hx hmt hs
  · obtain ⟨x, -, hs⟩ := List.mem_map.1 (sp_mem_splitI_fst ho)
    exact (tr_sojAtD_outSize c hs).trans (by unfold outB; omega)

/-- **The leaves of `sojAtProg` are small**: at most `outB m t`. -/
theorem sojAtProg_outSize {m t : ℕ} (c : Array ℕ) {x : ℕ} (hx : x < m) (hmt : m ≤ 2 * t) :
    ∀ o ∈ worklistD (stepD m t) tr_rank (tr_size m t) (splitI [sojAtD m t c x]).2
      (splitI [sojAtD m t c x]).1, outSize o ≤ outB m t := by
  have h := tr_items_pieces (xs := [x]) c hmt fun y hy => by
    rw [List.mem_singleton.1 hy]; exact hx
  simp only [List.map_cons, List.map_nil] at h
  exact tr_worklist_outSize h.1 h.2

/-- **The leaves of `sojProg` are small**: at most `outB m t`. -/
theorem sojProg_outSize {m t : ℕ} (c : Array ℕ) (hmt : m ≤ 2 * t) :
    ∀ o ∈ worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2
      (splitI (tr_sojItems m t c)).1, outSize o ≤ outB m t := by
  have h := tr_items_pieces (xs := List.range m) c hmt fun y hy => List.mem_range.1 hy
  exact tr_worklist_outSize h.1 h.2

/-- **`sojProg`'s cost**: `sojAtD` at every point, then the worklist with the size of `soj`. -/
theorem RunsWithin.sojProg (m t : ℕ) (c : Array ℕ) (hmt : m ≤ 2 * t) :
    RunsWithin X body (SoJTree.sojProg m t c)
      (worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2
        (splitI (tr_sojItems m t c)).1)
      (300 * (m + 1) ^ 4 + 30 * m + 40 +
        (stepK m t t + 11) * ((t + 2) * (soj (colOf m c) t).size)) := by
  obtain ⟨-, h₂, h₃⟩ := tr_items (m := m) (t := t) c (List.range m)
    fun x hx => List.mem_range.1 hx
  have hP : ∀ fr ∈ (splitI (tr_sojItems m t c)).2, fr.ValidP m t t := fun fr hfr => by
    obtain ⟨x, hx, hs⟩ := h₃ fr hfr
    exact tr_sojAt_validP hx hmt hs
  have hwl := RunsWithin.worklistProg (X := X) (body := body) (φ := frameTy) (ω := outTy)
    (f := fun fr => SoJTree.stepProg m t fr) (F := stepD m t)
    (I := FrameD.ValidP m t t) (ρ := tr_rank) (sz := tr_size m t)
    (w := stepWork m t) (K := stepK m t t)
    (fun fr h => by simpa [Nat.add_assoc] using RunsWithin.stepProg m t fr h)
    (fun fr h ch hch => ⟨stepD_validP h ch hch, (tr_children h.valid ch hch).2⟩)
    (fun fr h => tr_size_step h.valid) (fun fr _ => tr_one_le_size fr) hP
    (splitI (tr_sojItems m t c)).1
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .prod (.list outTy) (.list frameTy)) (xs := List.range m) (c := 300 * (m + 1) ^ 3)
    (F := fun x => splitI [sojAtD m t c x])
    (f := fun x => SoJTree.sojAtInitProg m t (offsArr m) c x) fun x hx =>
      RunsWithin.sojAtInitProg t c (List.mem_range.1 hx)
  have hcat := RunsWithin.sp_catProg (X := X) (body := body)
    ((List.range m).map fun x => splitI [sojAtD m t c x])
  rw [sp_cat_splitI (List.range m) fun x => [sojAtD m t c x], flatMap_singleton_eq] at hcat
  have hpot : wlPot tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2 ≤
      (t + 2) * (soj (colOf m c) t).size := by
    refine (tr_wlPot_le _ fun fr hfr => (hP fr hfr).cells).trans (Nat.mul_le_mul_left _ ?_)
    exact h₂.trans (tr_soj_size c t)
  apply RunsWithin.mono
  case h =>
    run_step (SoJProg.RunsWithin.csOffsProg m)
    run_step (RunsWithin.prim _ _)
    run_step hmap
    run_step hcat
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hwl
  case hc =>
    simp only [Prim.cost, Args.head, List.length_range, List.length_map,
      tr_sum_split_singleton]
    have h₁ : (stepK m t t + 11) * wlPot tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2 ≤
        (stepK m t t + 11) * ((t + 2) * (soj (colOf m c) t).size) :=
      Nat.mul_le_mul_left _ hpot
    have e : 300 * (m + 1) ^ 4 = m * (300 * (m + 1) ^ 3) + 300 * (m + 1) ^ 3 := by ring
    have : 1 ≤ (m + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.mul_add] at *
    omega

/-- The polynomial factor of `sojProg_cost_le`. -/
def sojPoly (m : ℕ) : ℕ :=
  300 * (m + 1) ^ 4 + 30 * m + 40 + (stepK m m m + 11) * (m + 2) * (4 * m + 6)

/-- **`sojProg` within a polynomial times the count bound of `split_or_johnson`.** -/
theorem sojProg_cost_le (m t : ℕ) (c : Array ℕ) (hc : Coherent.IsCoherent2 (colOf m c))
    (hu : Coherent.IsUniprimitive univ (colOf m c)) (ht : m + 2 ≤ 2 * t) (ht' : t < m) :
    RunsWithin X body (SoJTree.sojProg m t c)
      (worklistD (stepD m t) tr_rank (tr_size m t) (splitI (tr_sojItems m t c)).2
        (splitI (tr_sojItems m t c)).1)
      (sojPoly m * 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2)) := by
  obtain ⟨hlive, hcount, -⟩ := split_or_johnson (Γ := Fin m) (t := t) hc hu
    (by simpa using ht) (by simpa using ht')
  simp only [Fintype.card_fin] at hcount
  have hsize := CTree.size_le_of_live hlive
  have hheight := height_soj_le (colOf m c) t
  simp only [Fintype.card_fin] at hheight
  refine (RunsWithin.sojProg m t c (by omega)).mono ?_
  set T := soj (colOf m c) t
  set E := 2 ^ (129 * (Nat.clog 2 m + 2) ^ 2)
  have hE : 1 ≤ E := Nat.one_le_two_pow
  have hK := stepK_mono (m := m) (show t ≤ m by omega) (show t ≤ m by omega)
  have h₃ : T.size ≤ (4 * m + 6) * E := by
    have : 2 * (T.height + 1) ≤ 4 * m + 6 := by omega
    calc T.size ≤ 2 * (T.height + 1) * T.count := hsize
      _ ≤ (4 * m + 6) * E := Nat.mul_le_mul this hcount
  have h₄ : (stepK m t t + 11) * ((t + 2) * T.size) ≤
      (stepK m m m + 11) * ((m + 2) * ((4 * m + 6) * E)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) h₃)
  unfold sojPoly
  clear_value E
  generalize stepK m m m = K at h₄ ⊢
  generalize 300 * (m + 1) ^ 4 = P
  have e : (K + 11) * ((m + 2) * ((4 * m + 6) * E)) = (K + 11) * (m + 2) * (4 * m + 6) * E := by
    ring
  have e' : (P + 30 * m + 40 + (K + 11) * (m + 2) * (4 * m + 6)) * E =
      P * E + 30 * m * E + 40 * E + (K + 11) * (m + 2) * (4 * m + 6) * E := by ring
  have h₅ : P ≤ P * E := Nat.le_mul_of_pos_right _ hE
  have h₆ : 30 * m ≤ 30 * m * E := Nat.le_mul_of_pos_right _ hE
  omega

end Soj

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_tr_selProg {l₁ : var₁ (.list (.prod .nat .nat))} {l₂ : var₂ (.list (.prod .nat .nat))}
    (hl : ⟨.list (.prod .nat .nat), l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tr_selProg l₁) (tr_selProg l₂) := by
  unfold tr_selProg tr_ltProg tr_keyProg
  prog_wf

theorem wf_tr_rowProg {m₁ x₁ : var₁ .nat} {m₂ x₂ : var₂ .nat} {o₁ c₁ : var₁ (.array .nat)}
    {o₂ c₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tr_rowProg m₁ o₁ c₁ x₁) (tr_rowProg m₂ o₂ c₂ x₂) := by
  unfold tr_rowProg mapList csColProg
  prog_wf

theorem wf_tr_bigProg {m₁ t₁ x₁ : var₁ .nat} {m₂ t₂ x₂ : var₂ .nat}
    {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tr_bigProg m₁ t₁ o₁ c₁ x₁) (tr_bigProg m₂ t₂ o₂ c₂ x₂) := by
  unfold tr_bigProg Toolkit.filterList csColProg
  prog_wf

theorem wf_tr_pairsProg {m₁ x₁ : var₁ .nat} {m₂ x₂ : var₂ .nat} {o₁ c₁ : var₁ (.array .nat)}
    {o₂ c₂ : var₂ (.array .nat)} {b₁ : var₁ (.list .nat)} {b₂ : var₂ (.list .nat)}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) (hb : ⟨.list .nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tr_pairsProg m₁ o₁ c₁ x₁ b₁)
      (tr_pairsProg m₂ o₂ c₂ x₂ b₂) := by
  unfold tr_pairsProg mapList Toolkit.filterList csColProg SoJProg.memProg anyList
    sp_flattenProg
  prog_wf

theorem wf_tr_cellsProg {m₁ x₁ k₁ : var₁ .nat} {m₂ x₂ k₂ : var₂ .nat}
    {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ)
    (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tr_cellsProg m₁ o₁ c₁ x₁ k₁)
      (tr_cellsProg m₂ o₂ c₂ x₂ k₂) := by
  unfold tr_cellsProg mapList Toolkit.filterList csColProg
  prog_wf

theorem wf_tr_relProg {m₁ k₁ : var₁ .nat} {m₂ k₂ : var₂ .nat} {o₁ c₁ : var₁ (.array .nat)}
    {o₂ c₂ : var₂ (.array .nat)} {l₁ : var₁ (.list (.list .nat))} {l₂ : var₂ (.list (.list .nat))}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hl : ⟨.list (.list .nat), l₁, l₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tr_relProg m₁ o₁ c₁ l₁ k₁) (tr_relProg m₂ o₂ c₂ l₂ k₂) := by
  unfold tr_relProg mapList anyList csColProg sp_flattenProg
  prog_wf

theorem wf_sojAtInitProg {m₁ t₁ x₁ : var₁ .nat} {m₂ t₂ x₂ : var₂ .nat}
    {o₁ c₁ : var₁ (.array .nat)} {o₂ c₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sojAtInitProg m₁ t₁ o₁ c₁ x₁)
      (sojAtInitProg m₂ t₂ o₂ c₂ x₂) := by
  unfold sojAtInitProg tr_sojFrameProg
  refine .bind (wf_tr_rowProg hm ho hc hx) fun _ _ =>
    .bind (wf_tr_bigProg (by simp [hm]) (by simp [ht]) (by simp [ho]) (by simp [hc])
      (by simp [hx])) fun _ _ => .caseList (by simp) ?_ fun _ _ _ _ => ?_
  · exact .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
      .bind (wf_colBlkProg (by simp [hm]) (by simp) (by simp)) fun _ _ =>
      .bind (wf_partProg (by simp) (by simp)) fun _ _ => wf_sp_leafPair (by simp)
  refine .bind (wf_tr_pairsProg (by simp [hm]) (by simp [ho]) (by simp [hc]) (by simp [hx])
    (by simp)) fun _ _ => .bind (wf_tr_selProg (by simp)) fun _ _ =>
    .caseOption (by simp) (.bind wf_noneProg fun _ _ => wf_sp_leafPair (by simp))
    fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_tr_cellsProg (by simp [hm]) (by simp [ho]) (by simp [hc]) (by simp [hx])
      (by simp)) fun _ _ =>
    .bind (wf_tr_relProg (by simp [hm]) (by simp [ho]) (by simp [hc]) (by simp) (by simp))
    fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (wf_sp_frameProg (by simp) (by simp) (by simp) (by simp)) fun _ _ =>
    wf_sp_framePair (by simp)

theorem wf_bsojProg {m₁ t₁ : var₁ .nat} {m₂ t₂ : var₂ .nat} {V₁ : var₁ (.list .nat)}
    {V₂ : var₂ (.list .nat)} {c₁ : var₁ (.list (.list .nat))} {c₂ : var₂ (.list (.list .nat))}
    {a₁ : var₁ (.array .bool)} {a₂ : var₂ (.array .bool)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) (hV : ⟨.list .nat, V₁, V₂⟩ ∈ Γ)
    (hc : ⟨.list (.list .nat), c₁, c₂⟩ ∈ Γ) (ha : ⟨.array .bool, a₁, a₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (bsojProg m₁ t₁ V₁ c₁ a₁) (bsojProg m₂ t₂ V₂ c₂ a₂) := by
  unfold bsojProg
  exact .bind (.prim _ .nil) fun _ _ =>
    .bind (wf_sp_frameProg (by simp [hV]) (by simp [hc]) (by simp [ha]) (by simp)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ =>
    wf_worklistProg (fun Γ' hΓ x₁ x₂ hx => wf_stepProg (hΓ (by simp [hm])) (hΓ (by simp [ht])) hx)
      (by simp) (by simp)

theorem wf_sojAtProg {m₁ t₁ x₁ : var₁ .nat} {m₂ t₂ x₂ : var₂ .nat} {c₁ : var₁ (.array .nat)}
    {c₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hx : ⟨.nat, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sojAtProg m₁ t₁ c₁ x₁) (sojAtProg m₂ t₂ c₂ x₂) := by
  unfold sojAtProg
  exact .bind (by unfold csOffsProg; prog_wf) fun _ _ =>
    .bind (wf_sojAtInitProg (by simp [hm]) (by simp [ht]) (by simp) (by simp [hc]) (by simp [hx]))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    wf_worklistProg (fun Γ' hΓ x₁ x₂ hx => wf_stepProg (hΓ (by simp [hm])) (hΓ (by simp [ht])) hx)
      (by simp) (by simp)

theorem wf_sojProg {m₁ t₁ : var₁ .nat} {m₂ t₂ : var₂ .nat} {c₁ : var₁ (.array .nat)}
    {c₂ : var₂ (.array .nat)} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ)
    (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sojProg m₁ t₁ c₁) (sojProg m₂ t₂ c₂) := by
  unfold sojProg
  exact .bind (by unfold csOffsProg; prog_wf) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hm]) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun Γ' hΓ x₁ x₂ hx =>
      wf_sojAtInitProg (hΓ (by simp [hm])) (hΓ (by simp [ht])) (hΓ (by simp)) (hΓ (by simp [hc]))
        hx)
    fun _ _ => .bind (wf_sp_catProg (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    wf_worklistProg (fun Γ' hΓ x₁ x₂ hx => wf_stepProg (hΓ (by simp [hm])) (hΓ (by simp [ht])) hx)
      (by simp) (by simp)

end Wf

end GraphIso.SoJTree
