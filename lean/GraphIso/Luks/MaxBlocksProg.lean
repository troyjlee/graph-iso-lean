module

public import GraphIso.Luks.Primitive
public import GraphIso.Sims.SiftProg
public import Mathlib.Tactic.Linarith

/-!
# Maximal block systems in the cost language

* `closureProg gs pts cl u v` computes `closure gs pts cl u v` at cost at most
  `closureCost n m s` for degree `n`, window size `m` and `s` generators
  (`RunsWithin.closureProg`). The loop is paid by the potential
  `12 |pending| + (n + 8 m + 21 s + 18) · leaders + 5`: dropping a pair costs `11`, and a merge
  costs `n + 8 m + 9 s + 17` (one relabelling pass and one array update, and the images of the
  pair) while removing one leader and queueing `s` pairs.
* `maxBlocksProg n gs pts` computes `maxBlocks n gs pts` at cost at most
  `maxBlocksCost n m s` (`RunsWithin.maxBlocksProg`): one closure and one single-class test for
  each window point, and the block list by filtering the window once per leader.

The programs make no backend calls.
-/

@[expose] public section

namespace GraphIso

namespace Cost.Ty

/-- Closure states: labels and pending pairs. -/
abbrev cstate : Ty := .prod (.array .nat) (.list (.prod .nat .nat))

end Cost.Ty

namespace Luks

open Equiv Cost Programs Sims

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The elements of a list satisfying a Boolean program, in order. -/
def filterList {a' : Ty} (xs : var (.list a')) (p : var a' → Prog S rec var .bool) :
    Prog S rec var (.list a') :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList xs nil fun acc x => .bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc))
    fun racc => .op1 .reverse racc

/-- The images of the pair `(a, b)` under the generators. -/
def pairImagesProg (gs : var Ty.gens) (a b : var .nat) : Prog S rec var (.list (.prod .nat .nat)) :=
  mapList gs fun g =>
    .bind (permApply g a) fun ga => .bind (permApply g b) fun gb => .op2 .pair ga gb

/-- Relabel the class `cb` to `ca` on the window points. -/
def relabelProg (cl : var (.array .nat)) (pts : var (.list .nat)) (cb ca : var .nat) :
    Prog S rec var (.array .nat) :=
  .bind (mapList pts fun p => .bind (.op2 .arrayGet cl p) fun lp => .bind (.op2 .natEq lp cb)
      fun e => .ite e (.op2 .pair p ca) (.op2 .pair p lp)) fun ws =>
  .op2 .arrayUpdate cl ws

/-- One closure step. -/
def closeBody (gs : var Ty.gens) (pts : var (.list .nat)) (st : var Ty.cstate) :
    Prog S rec var (.option Ty.cstate) :=
  .bind (.op1 .fst st) fun cl => .bind (.op1 .snd st) fun pend =>
  .caseList pend (.op0 .none) fun ab rest =>
    .bind (.op1 .fst ab) fun a => .bind (.op1 .snd ab) fun b =>
    .bind (.op2 .arrayGet cl a) fun ca => .bind (.op2 .arrayGet cl b) fun cb =>
    .bind (.op2 .natEq ca cb) fun e =>
    .ite e (.bind (.op2 .pair cl rest) fun st' => .op1 .some st')
      (.bind (relabelProg cl pts cb ca) fun cl' =>
        .bind (pairImagesProg gs a b) fun imgs =>
        .bind (.op2 .append imgs rest) fun pend' =>
        .bind (.op2 .pair cl' pend') fun st' => .op1 .some st')

/-- The closure of the labels `cl` and the pair `(u, v)`. -/
def closureProg (gs : var Ty.gens) (pts : var (.list .nat)) (cl : var (.array .nat))
    (u v : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op2 .pair u v) fun uv => .bind (.op0 .nil) fun nl => .bind (.op2 .cons uv nl) fun pend =>
  .bind (.op2 .pair cl pend) fun st₀ =>
  .bind (.loop st₀ fun st => closeBody gs pts st) fun fin => .op1 .fst fin

/-- Every window point has the label of `u`. -/
def oneClassProg (cl : var (.array .nat)) (pts : var (.list .nat)) (u : var .nat) :
    Prog S rec var .bool :=
  .bind (.op2 .arrayGet cl u) fun lu =>
  allList pts fun p => .bind (.op2 .arrayGet cl p) fun lp => .op2 .natEq lp lu

/-- The discrete partition. -/
def discreteProg (n : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun l => .op1 .arrayOfList l

/-- One step of the maximal pass. -/
def mbBody (gs : var Ty.gens) (pts : var (.list .nat)) (u : var .nat) (cl : var (.array .nat))
    (v : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op2 .arrayGet cl v) fun lv => .bind (.op2 .arrayGet cl u) fun lu =>
  .bind (.op2 .natEq lv lu) fun e =>
  .ite e (.ret cl)
    (.bind (closureProg gs pts cl u v) fun c => .bind (oneClassProg c pts u) fun one =>
      .ite one (.ret cl) (.ret c))

/-- The window points labelling themselves. -/
def leadersProg (cl : var (.array .nat)) (pts : var (.list .nat)) : Prog S rec var (.list .nat) :=
  filterList pts fun p => .bind (.op2 .arrayGet cl p) fun lp => .op2 .natEq lp p

/-- The classes, one per leader. -/
def blocksOfProg (cl : var (.array .nat)) (pts : var (.list .nat)) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (leadersProg cl pts) fun ls =>
  mapList ls fun l => filterList pts fun p => .bind (.op2 .arrayGet cl p) fun lp => .op2 .natEq lp l

/-- The maximal block system for the first window point. -/
def maxBlocksProg (n : var .nat) (gs : var Ty.gens) (pts : var (.list .nat)) :
    Prog S rec var (.list (.list .nat)) :=
  .caseList pts (.op0 .nil) fun u _ =>
    .bind (discreteProg n) fun d =>
    .bind (.foldList pts d fun cl v => mbBody gs pts u cl v) fun cl => blocksOfProg cl pts

end Prog

/-! ### Costs -/

/-- The cost bound of the closure: degree `n`, window size `m`, `s` generators. -/
def closureCost (n m s : ℕ) : ℕ := m * (n + 8 * m + 21 * s + 18) + 22

/-- The cost bound of one step of the maximal pass. -/
def mbCost (n m s : ℕ) : ℕ := closureCost n m s + 4 * m + 7

/-- The cost bound of the maximal block system. -/
def maxBlocksCost (n m s : ℕ) : ℕ := m * (mbCost n m s + 1) + m * (12 * m + 13) + 2 * n + 10

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}
  {n : ℕ} {gs : GensData} {pts : List ℕ}

private theorem fold_filter_spec {a' : Ty} {p : a'.denote → Prog S (a, b) Ty.denote .bool}
    {P : a'.denote → Bool} {c : ℕ} :
    ∀ (xs : List a'.denote) (acc : List a'.denote),
      (∀ x ∈ xs, RunsWithin X body (p x) (P x) c) →
      RunsWithin X body
        (.foldList xs acc fun acc x => .bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc))
        ((xs.filter P).reverse ++ acc) (xs.length * (c + 3))
  | [], acc, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, acc, hp => by
    have h₁ : RunsWithin X body (.bind (p x) fun c => .ite c (.op2 .cons x acc) (.ret acc))
        (if P x then x :: acc else acc) (c + 2) := by
      refine (hp x List.mem_cons_self).bind ?_
      cases P x
      · exact (RunsWithin.ite_false (RunsWithin.ret _)).mono (by omega)
      · exact RunsWithin.ite_true (RunsWithin.prim _ _)
    have h₂ := fold_filter_spec xs (if P x then x :: acc else acc)
      fun y hy => hp y (List.mem_cons_of_mem _ hy)
    have h := RunsWithin.foldList_cons h₁ h₂
    have e₁ : ((x :: xs).filter P).reverse ++ acc =
        (xs.filter P).reverse ++ (if P x then x :: acc else acc) := by
      cases hPx : P x <;> simp [hPx]
    have e₂ : (x :: xs).length * (c + 3) = 1 + (c + 2) + xs.length * (c + 3) := by
      simp only [List.length_cons, Nat.succ_mul]
      omega
    rw [e₁, e₂]
    exact h

theorem RunsWithin.filterList {a' : Ty} {xs : List a'.denote}
    {p : a'.denote → Prog S (a, b) Ty.denote .bool} {P : a'.denote → Bool} {c : ℕ}
    (hp : ∀ x ∈ xs, RunsWithin X body (p x) (P x) c) :
    RunsWithin X body (Luks.filterList xs p) (xs.filter P) (xs.length * (c + 4) + 2) := by
  refine RunsWithin.bind_le (c₂ := xs.length * (c + 3) + (xs.length + 1)) (RunsWithin.prim _ _)
    ?_ (by simp only [Prim.cost, Nat.mul_add]; omega)
  refine RunsWithin.bind_le (c₂ := xs.length + 1) (fold_filter_spec xs [] hp) ?_ le_rfl
  refine RunsWithin.prim_le (by simp [Prim.eval]) ?_
  simp only [Prim.cost, Args.head_cons, List.append_nil, List.length_reverse]
  have := List.length_filter_le P xs
  omega

theorem RunsWithin.pairImagesProg (gs : GensData) (a' b' : ℕ) :
    RunsWithin X body (Luks.pairImagesProg gs a' b') (pairImages gs a' b')
      (gs.length * 8 + 2) := by
  refine (RunsWithin.mapList_le (c := 5) fun g _ => ?_).mono le_rfl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.permApply g a')
    run_step (RunsWithin.permApply g b')
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.relabelProg (cl : Array ℕ) (pts : List ℕ) (cb ca : ℕ) :
    RunsWithin X body (Luks.relabelProg cl pts cb ca) (relabel cl pts cb ca)
      (cl.size + 8 * pts.length + 3) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .prod .nat .nat)
    (xs := pts) (c := 4) (F := fun p => (p, newLabel cl cb ca p))
    (f := fun p => Prog.bind (.op2 .arrayGet cl p) fun lp => .bind (.op2 .natEq lp cb)
      fun e => .ite e (.op2 .pair p ca) (.op2 .pair p lp)) fun p _ => by
    by_cases h : get cl p = cb
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (get cl p == cb) = true by simpa using h) _
        exact RunsWithin.prim_le (by simp only [newLabel, h, ↓reduceIte]; rfl) le_rfl
      case hc =>
        simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (get cl p == cb) = false by simpa using h) _
        exact RunsWithin.prim_le (by simp only [newLabel, h, ↓reduceIte]; rfl) le_rfl
      case hc =>
        simp [Prim.cost]
  apply RunsWithin.mono
  case h =>
    run_step hmap
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, Args.tail_cons, List.length_map]
    omega

theorem RunsWithin.closeBody_nil (cl : Array ℕ) :
    RunsWithin X body (Luks.closeBody gs pts (cl, [])) none 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.closeBody_drop {cl : Array ℕ} {a' b' : ℕ} {rest : List (ℕ × ℕ)}
    (h : get cl a' = get cl b') :
    RunsWithin X body (Luks.closeBody gs pts (cl, (a', b') :: rest)) (some (cl, rest)) 11 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.caseList_cons _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.ite_pos (show (get cl a' == get cl b') = true by simpa using h) _
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.closeBody_merge {cl : Array ℕ} {a' b' : ℕ} {rest : List (ℕ × ℕ)}
    (h : get cl a' ≠ get cl b') :
    RunsWithin X body (Luks.closeBody gs pts (cl, (a', b') :: rest))
      (some (relabel cl pts (get cl b') (get cl a'), pairImages gs a' b' ++ rest))
      (cl.size + 8 * pts.length + 9 * gs.length + 17) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.caseList_cons _
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_with RunsWithin.ite_neg (show (get cl a' == get cl b') = false by simpa using h) _
    run_step (RunsWithin.relabelProg cl pts (get cl b') (get cl a'))
    run_step (RunsWithin.pairImagesProg gs a' b')
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, pairImages, List.length_map]
    omega

/-- The potential of the closure loop. -/
def closePot (n m s : ℕ) (pts : List ℕ) (st : CState) : ℕ :=
  12 * st.2.length + (n + 8 * m + 21 * s + 18) * (leaders st.1 pts).length + 5

/-- **The closure costs at most `closureCost n m s`.** -/
theorem RunsWithin.closureProg (hW : Win n gs pts) {cl : Array ℕ} (hcl : LabelsOK n pts cl)
    (hst : Stable gs pts cl) {u v : ℕ} (hu : u ∈ pts) (hv : v ∈ pts) :
    RunsWithin X body (Luks.closureProg gs pts cl u v) (closure gs pts cl u v)
      (closureCost n pts.length gs.length) := by
  set Φ := closePot n pts.length gs.length pts with hΦ
  have hI₀ := cinv_init hW hcl hst hu hv
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (f := Luks.closeBody gs pts)
    (F := closeStep gs pts) (I := CInv n gs pts u v) (Φ := Φ) (fun st hst => by
      obtain ⟨cl', pend⟩ := st
      rcases pend with _ | ⟨⟨a', b'⟩, rest⟩
      · refine ⟨4, RunsWithin.closeBody_nil cl', fun _ => by simp [hΦ, closePot], ?_⟩
        intro st' h
        simp [closeStep] at h
      · have hcl' : LabelsOK n pts cl' := hst.labels
        have hsize : cl'.size = n := hcl'.size
        have hab : a' ∈ pts ∧ b' ∈ pts := hst.pend (a', b') List.mem_cons_self
        by_cases he : get cl' a' = get cl' b'
        · refine ⟨11, RunsWithin.closeBody_drop he |>.of_eq (by simp [closeStep, he]),
            fun h => by simp [closeStep, he] at h, fun st' h => ?_⟩
          simp only [closeStep, he, ↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨(closeStep_drop hst rfl he).1, ?_⟩
          simp only [hΦ, closePot, List.length_cons]
          omega
        · refine ⟨_, RunsWithin.closeBody_merge he |>.of_eq (by simp [closeStep, he]),
            fun h => by simp [closeStep, he] at h, fun st' h => ?_⟩
          simp only [closeStep, he, ↓reduceIte, Option.some.injEq] at h
          subst h
          refine ⟨(closeStep_merge hW hst rfl he).1, ?_⟩
          have hlead := leaders_merge hW hcl' hab.1 hab.2 he
          simp only [hΦ, closePot, List.length_cons, List.length_append, pairImages,
            List.length_map, hsize]
          rw [← hlead]
          set L' := (leaders (relabel cl' pts (get cl' b') (get cl' a')) pts).length
          have e : (n + 8 * pts.length + 21 * gs.length + 18) * (L' + 1) =
              (n + 8 * pts.length + 21 * gs.length + 18) * L' +
                (n + 8 * pts.length + 21 * gs.length + 18) := by ring
          rw [e]
          omega)
    (closeFuel gs.length pts.length + Φ (cl, [(u, v)]) + 1) (cl, [(u, v)]) hI₀ (by omega)
  have hpot : cpot gs.length pts (cl, [(u, v)]) < closeFuel gs.length pts.length := by
    have := Nat.mul_le_mul_left (gs.length + 1) (leaders_length_le (pts := pts) cl)
    simp only [cpot, closeFuel, List.length_singleton]
    omega
  obtain ⟨-, hnil, -, -⟩ := iter_closeStep hW _ _ hI₀ hpot
  have hfix : closeStep gs pts (iter (closeStep gs pts) (closeFuel gs.length pts.length)
      (cl, [(u, v)])) = none := by
    generalize iter (closeStep gs pts) (closeFuel gs.length pts.length) (cl, [(u, v)]) = st
      at hnil ⊢
    obtain ⟨c, p⟩ := st
    simp only at hnil
    subst hnil
    rfl
  rw [iter_eq_of_fix _ _ hfix _ (by omega)] at hloop
  have hL := leaders_length_le (pts := pts) cl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hloop
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have := Nat.mul_le_mul_left (n + 8 * pts.length + 21 * gs.length + 18) hL
    simp only [Prim.cost, hΦ, closePot, closureCost, List.length_singleton]
    rw [Nat.mul_comm pts.length]
    omega

theorem RunsWithin.oneClassProg (cl : Array ℕ) (pts : List ℕ) (u : ℕ) :
    RunsWithin X body (Luks.oneClassProg cl pts u) (oneClass cl pts u) (4 * pts.length + 2) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.allList_le (c := 2) fun p _ =>
      ((RunsWithin.prim _ _).bind (RunsWithin.prim _ _)).mono (by simp [Prim.cost])
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.discreteProg (n : ℕ) :
    RunsWithin X body (Luks.discreteProg n) (discrete n) (2 * n + 2) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range]
    omega

theorem RunsWithin.mbBody (hW : Win n gs pts) {u v : ℕ} (hu : u ∈ pts) (hv : v ∈ pts)
    {cl : Array ℕ} (hcl : LabelsOK n pts cl) (hst : Stable gs pts cl) :
    RunsWithin X body (Luks.mbBody gs pts u cl v) (mbStep gs pts u cl v)
      (mbCost n pts.length gs.length) := by
  by_cases h₁ : get cl v = get cl u
  · have e : mbStep gs pts u cl v = cl := by simp [mbStep, h₁]
    rw [e]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.ite_pos (show (get cl v == get cl u) = true by simpa using h₁)
        (RunsWithin.ret _)
    case hc =>
      simp only [Prim.cost, mbCost]
      omega
  · have hcl := RunsWithin.closureProg (X := X) (body := body) hW hcl hst hu hv
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (get cl v == get cl u) = false by simpa using h₁) _
      run_step hcl
      run_step (RunsWithin.oneClassProg _ pts u)
      by_cases h₂ : oneClass (closure gs pts cl u v) pts u = true
      · exact (RunsWithin.ite_pos h₂ (RunsWithin.ret _)).of_eq (by simp [mbStep, h₁, h₂])
      · exact (RunsWithin.ite_neg (Bool.eq_false_iff.2 h₂) (RunsWithin.ret _)).of_eq
          (by simp [mbStep, h₁, h₂])
    case hc =>
      simp only [Prim.cost, mbCost]
      omega

theorem RunsWithin.leadersProg (cl : Array ℕ) (pts : List ℕ) :
    RunsWithin X body (Luks.leadersProg cl pts) (leaders cl pts) (6 * pts.length + 2) := by
  refine (RunsWithin.filterList (c := 2) fun p _ =>
    ((RunsWithin.prim _ _).bind (RunsWithin.prim _ _)).mono (by simp [Prim.cost])).mono ?_
  omega

theorem RunsWithin.blocksOfProg (cl : Array ℕ) (pts : List ℕ) :
    RunsWithin X body (Luks.blocksOfProg cl pts) (blocksOf cl pts)
      (pts.length * (12 * pts.length + 13) + 4) := by
  have hls := leaders_length_le (pts := pts) cl
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := leaders cl pts) (c := 6 * pts.length + 2)
    (F := fun l => pts.filter fun p => get cl p == l)
    (f := fun l => Luks.filterList pts fun p =>
      Prog.bind (.op2 .arrayGet cl p) fun lp => .op2 .natEq lp l) fun l _ =>
    (RunsWithin.filterList (c := 2) fun p _ =>
      ((RunsWithin.prim _ _).bind (RunsWithin.prim _ _)).mono (by simp [Prim.cost])).mono
        (by omega)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.leadersProg cl pts)
    exact hmap
  case hc =>
    have := Nat.mul_le_mul_right (6 * pts.length + 2 + 3) hls
    nlinarith

/-- **The maximal block system costs at most `maxBlocksCost n m s`.** -/
theorem RunsWithin.maxBlocksProg (hW : Win n gs pts) :
    RunsWithin X body (Luks.maxBlocksProg n gs pts) (maxBlocks n gs pts)
      (maxBlocksCost n pts.length gs.length) := by
  rcases hpts : pts with _ | ⟨u, rest⟩
  · apply RunsWithin.mono
    case h => exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
    case hc =>
      simp [Prim.cost, maxBlocksCost]
  · subst hpts
    have hu : u ∈ u :: rest := List.mem_cons_self
    have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := .nat) (b' := .array .nat)
      (f := fun cl v => Luks.mbBody gs (u :: rest) u cl v) (F := mbStep gs (u :: rest) u)
      (I := fun cl => LabelsOK n (u :: rest) cl ∧ Stable gs (u :: rest) cl)
      (c := mbCost n (u :: rest).length gs.length)
      (u :: rest) (discrete n) (fun cl hcl v hv => ⟨RunsWithin.mbBody hW hu hv hcl.1 hcl.2, by
        unfold mbStep
        split
        · exact hcl
        · split
          · exact hcl
          · obtain ⟨h₁, h₂, -⟩ := closure_spec hW hcl.1 hcl.2 hu hv
            exact ⟨h₁, h₂⟩⟩) ⟨labelsOK_discrete hW, stable_discrete hW⟩).1
    apply RunsWithin.mono
    case h =>
      run_with RunsWithin.caseList_cons _
      run_step (RunsWithin.discreteProg n)
      run_step hfold
      exact RunsWithin.blocksOfProg _ _
    case hc =>
      simp only [maxBlocksCost]
      nlinarith

end Specs

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_closureProg {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {u₁ v₁ : var₁ .nat} {u₂ v₂ : var₂ .nat} (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ)
    (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (closureProg g₁ p₁ c₁ u₁ v₁)
      (closureProg g₂ p₂ c₂ u₂ v₂) := by
  unfold closureProg closeBody relabelProg pairImagesProg permApply mapList
  prog_wf

theorem wf_mbBody {g₁ : var₁ Ty.gens} {g₂ : var₂ Ty.gens} {p₁ : var₁ (.list .nat)}
    {p₂ : var₂ (.list .nat)} {c₁ : var₁ (.array .nat)} {c₂ : var₂ (.array .nat)}
    {u₁ v₁ : var₁ .nat} {u₂ v₂ : var₂ .nat} (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ)
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ) (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ)
    (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (mbBody g₁ p₁ u₁ c₁ v₁) (mbBody g₂ p₂ u₂ c₂ v₂) := by
  unfold mbBody
  refine .bind (.prim _ (.cons hc (.cons hv .nil))) fun lv₁ lv₂ =>
    .bind (.prim _ (.cons (by simp [hc]) (.cons (by simp [hu]) .nil))) fun lu₁ lu₂ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun e₁ e₂ =>
    .ite (List.Mem.head _) (.ret (by simp [hc])) ?_
  refine .bind (wf_closureProg (by simp [hg]) (by simp [hp]) (by simp [hc]) (by simp [hu])
    (by simp [hv])) fun d₁ d₂ => .bind ?_ fun o₁ o₂ =>
      .ite (List.Mem.head _) (.ret (by simp [hc])) (.ret (by simp))
  unfold oneClassProg allList
  prog_wf

theorem wf_maxBlocksProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {g₁ : var₁ Ty.gens}
    {g₂ : var₂ Ty.gens} {p₁ : var₁ (.list .nat)} {p₂ : var₂ (.list .nat)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hg : ⟨Ty.gens, g₁, g₂⟩ ∈ Γ) (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (maxBlocksProg n₁ g₁ p₁) (maxBlocksProg n₂ g₂ p₂) := by
  unfold maxBlocksProg
  refine .caseList hp (.prim _ .nil) fun u₁ u₂ t₁ t₂ => ?_
  refine .bind (by unfold discreteProg; prog_wf) fun d₁ d₂ =>
    .bind (.foldList (by simp [hp]) (List.Mem.head _) fun c₁ c₂ v₁ v₂ =>
      wf_mbBody (by simp [hg]) (by simp [hp]) (List.Mem.head _) (by simp)
        (by simp)) fun c₁ c₂ => ?_
  unfold blocksOfProg leadersProg filterList mapList
  prog_wf

end Wf

end Luks

end GraphIso
