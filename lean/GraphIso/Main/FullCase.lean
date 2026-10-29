module

public import GraphIso.Main.FullProg

/-!
# The full procedure: the dispatch at the Schreier–Sims backend

Stage 14j-5d, items 2 and 3 (`PLAN-14.md` §14.9). The values of the dispatcher's tests, the case
it takes (`mainCase`, computed from the data), the run of each branch of the hinted dispatch at
`ssCtx`, and the facts the step corollaries of stage 14j-5c need, proved from the tests:

* `normLabD`: the normalized labels; they agree with the labels below `n`, so the hint and the
  instance's validity are unchanged (`HintValid.normLab`, `HInstValid.normLab`).
* `orbits_trans_iff`: a window is transitive iff its orbit partition has at most one orbit;
  more than one base orbit is M1's condition.
* `m5OkD_iff`, `m4OkD_iff`: the numeric tests.
* `MainCase`, `hintCase`, `bigCase`, `mainCase`: the case the dispatcher takes.
* `RunsWithin.hintProg_m1` … `RunsWithin.bigProg_m4_m3`: each branch of the hinted dispatch runs
  its step after the tests, at the tests' cost.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion Sims

/-! ### The tests' values -/

section Data

/-- **The normalized labels**: the labels at the string positions `0, …, n − 1`. -/
def normLabD (n : ℕ) (L : LabelData) : LabelData :=
  ((List.range n).map fun i => L.getD i []).toArray

theorem normLabD_size (n : ℕ) (L : LabelData) : (normLabD n L).size = n := by
  simp [normLabD]

theorem normLabD_getD {n i : ℕ} (L : LabelData) (hi : i < n) :
    (normLabD n L).getD i [] = L.getD i [] := by
  simp [normLabD, hi]

/-- M5's numeric test: `5 ≤ k`, `2k ≤ m` and `12 ≤ m`. -/
def m5OkD (k m : ℕ) : Bool := decide (4 < k) && !decide (m < k + k) && decide (11 < m)

theorem m5OkD_iff {k m : ℕ} : m5OkD k m = true ↔ 5 ≤ k ∧ 2 * k ≤ m ∧ 12 ≤ m := by
  simp only [m5OkD, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt]
  omega

/-- M4's numeric test: `4 + j ≤ m` and `2j ≤ m`, with `j = dg − 1`. -/
def m4OkD (dg m : ℕ) : Bool := !decide (m < 4 + (dg - 1)) && !decide (m < dg - 1 + (dg - 1))

theorem m4OkD_iff {dg m : ℕ} : m4OkD dg m = true ↔ 4 + (dg - 1) ≤ m ∧ 2 * (dg - 1) ≤ m := by
  simp only [m4OkD, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  omega

/-- **The structure state of M5**: tag `0`, no structure. -/
abbrev noStD : ℕ × CJData := Ty.default stTy

theorem noStD_fst : noStD.1 ≠ 2 := by decide

end Data

/-! ### The tests' programs -/

section SmallRuns

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.normLabProg (n : ℕ) (L : LabelData) :
    RunsWithin X body (Main.normLabProg n L) (normLabD n L) (6 * n + 4) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .list .nat)
    (xs := List.range n) (c := 1) (F := fun i => L.getD i [])
    (f := fun i => Prog.op2 Prim.arrayGet L i) fun i _ => RunsWithin.prim_le rfl le_rfl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_range, List.length_map]
    omega

theorem RunsWithin.noStProg : RunsWithin X body Main.noStProg noStD 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost, Prim.eval]

theorem RunsWithin.m5OkProg (k m : ℕ) : RunsWithin X body (Main.m5OkProg k m) (m5OkD k m) 9 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, m5OkD, Bool.and_assoc]) le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.m4OkProg (dg m : ℕ) :
    RunsWithin X body (Main.m4OkProg dg m) (m4OkD dg m) 10 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, m4OkD]) le_rfl
  case hc => simp [Prim.cost]

end SmallRuns

/-! ### Facts on the data -/

section Facts

/-- **A generator keeps an invariant window.** -/
theorem get_mem_of_invariant {N : ℕ} {gs : GensData} {w : WinData} (hw : w.Valid N)
    (hgs : GensData.AllValid N gs) (hinv : IsInvariant (GensData.denote N gs) (w.denote N))
    {g : PermData} (hg : g ∈ gs) {i : ℕ} (hi : i ∈ w.1) : get g.1 i ∈ w.1 := by
  have h := hinv (PermData.denote N g) (GensData.mem_denote_of_mem hg) ⟨i, hw.lt i hi⟩
    (WinData.mem_denote.2 hi)
  rw [WinData.mem_denote, PermData.val_denote_apply (hgs g hg)] at h
  exact h

/-- **The normalized labels are a hint** when the labels are: they agree on the window. -/
theorem _root_.GraphIso.Toolkit.HintValid.normLab {n N : ℕ} {gs : GensData} {w : WinData}
    {L : LabelData}
    (h : HintValid n N gs w L) (hw : w.Valid N) (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (w.denote N)) :
    HintValid n N gs w (normLabD n L) := by
  have e : ∀ i ∈ w.1, (normLabD n L).getD i [] = L.getD i [] := fun i hi =>
    normLabD_getD L (h.win_lt i hi)
  refine ⟨h.le, h.base_inv, h.win_lt, fun i hi => ?_, fun i hi => ?_, fun g hg i hi => ?_, ?_⟩
  · rw [e i hi]
    exact h.lab_lt i hi
  · rw [e i hi]
    exact h.lab_nodup i hi
  · rw [e i hi, e _ (get_mem_of_invariant hw hgs hinv hg hi)]
    exact h.equivar g hg i hi
  · obtain ⟨i, hi, j, hj, hne⟩ := h.nonconst
    exact ⟨i, hi, j, hj, by rw [e i hi, e j hj]; exact hne⟩

/-- **The instance with normalized labels is valid**, and has the same measure. -/
theorem HInstValid.normLab {DV : ℕ → GensData → Unit → Prop} {xy : StrData × StrData}
    {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit)) :
    HInstValid DV (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) : HInstData Ty.unit) := by
  refine ⟨hI.valid, hI.le, hI.base_inv, hI.win_lt, hI.faithful, fun L' hL' => ?_⟩
  cases hL'
  obtain ⟨hh, htr⟩ := hI.hint L rfl
  exact ⟨hh.normLab hI.valid.win hI.valid.group.1 hI.valid.invariant, htr⟩

/-- **Transitivity from the orbit partition**: a window is transitive iff it has at most one
orbit. -/
theorem orbits_trans_iff {N : ℕ} {G : Subgroup (Perm (Fin N))} {w : WinData} {os : List (List ℕ)}
    (hw : w.Valid N) (hos : IsOrbitPartition G w os) :
    IsTransOn G (w.denote N) ↔ os.length ≤ 1 := by
  constructor
  · intro htr
    by_contra hlt
    obtain ⟨o₀, o₁, rest, rfl⟩ : ∃ o₀ o₁ rest, os = o₀ :: o₁ :: rest := by
      rcases os with _ | ⟨o₀, _ | ⟨o₁, rest⟩⟩
      · simp at hlt
      · simp at hlt
      · exact ⟨o₀, o₁, rest, rfl⟩
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (hos.2 o₀ List.mem_cons_self).1
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _
      (hos.2 o₁ (List.mem_cons_of_mem _ List.mem_cons_self)).1
    have hmem : ∀ o ∈ o₀ :: o₁ :: rest, ∀ x ∈ o, x ∈ w.1 := fun o ho x hx =>
      hos.1.mem_iff.1 (List.mem_flatten.2 ⟨o, ho, hx⟩)
    have huw := hmem o₀ List.mem_cons_self u hu
    have hvw := hmem o₁ (List.mem_cons_of_mem _ List.mem_cons_self) v hv
    obtain ⟨g, hg, hgu⟩ := htr ⟨u, hw.lt u huw⟩ (WinData.mem_denote.2 huw) ⟨v, hw.lt v hvw⟩
      (WinData.mem_denote.2 hvw)
    have hv₀ : v ∈ o₀ := ((hos.2 o₀ List.mem_cons_self).2 u hu v).2
      ⟨hw.lt u huw, hw.lt v hvw, g, hg, hgu⟩
    have hnd : (o₀ :: o₁ :: rest).flatten.Nodup := hos.1.nodup_iff.2 hw.nodup
    simp only [List.flatten_cons] at hnd
    have hd := (List.nodup_append.1 hnd).2.2
    exact hd v hv₀ v (List.mem_append_left _ hv) rfl
  · intro h1 u hu v hv
    rcases os with _ | ⟨o, _ | ⟨o', rest⟩⟩
    · have : w.1 = [] := List.Perm.eq_nil hos.1.symm
      exact absurd (show u.val ∈ w.1 from hu) (by rw [this]; simp)
    · obtain ⟨hi, hj, g, hg, hgu⟩ := ((hos.transitive_of_singleton hu) v.val).1 hv
      exact ⟨g, hg, by simpa using hgu⟩
    · simp at h1

/-- **The base is transitive** iff its orbit partition has at most one orbit. -/
theorem base_trans_iff {n N : ℕ} {gs : GensData} {os : List (List ℕ)}
    (hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N) os) :
    IsTransOn (GensData.denote N gs) (baseSet n N) ↔ os.length ≤ 1 := by
  rw [← baseWin_denote]
  exact orbits_trans_iff (baseWin_valid n N) hos

end Facts

/-! ### The case the dispatcher takes -/

section Cases

/-- The cases of the dispatcher. -/
inductive MainCase
  | base | chain | m0 | m1 | m2a | m2b | m3 | m4 | m5
  deriving DecidableEq, Repr

/-- **The large-base case**, with thresholds `k` and `ℓ`: M3 on a base of at most `ℓ` points;
otherwise M5 for a giant meeting M5's numeric test, M4 for a non-giant meeting M4's, M3 in the
other cases. -/
def bigCase (k ℓ n N : ℕ) (gs : GensData) : MainCase :=
  if ℓ < N - n then
    if m4Deg ssCtx.O n (N, gs, ()) = N - n - 2 then (if m5OkD k (N - n) then .m5 else .m3)
    else if m4OkD (m4Deg ssCtx.O n (N, gs, ())) (N - n) then .m4 else .m3
  else .m3

/-- **The hinted case**: M1 on more than one base orbit; M2a or M2b on proper maximal blocks;
the large-base case otherwise. -/
def hintCase (k ℓ n N : ℕ) (gs : GensData) (w : WinData) (L : LabelData) : MainCase :=
  if 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length then .m1
  else if blkOKD (N - n) (mbD n N gs) then
    (if neqD n N (mbD n N gs) (normLabD n L) w.1 then .m2a else .m2b)
  else bigCase k ℓ n N gs

/-- **The case the dispatcher takes** on an instance, for the thresholds `kf`, `ℓf`. -/
def mainCase (kf ℓf : ℕ → ℕ) : HInstData Ty.unit → MainCase
  | ((_, w, _, N, gs, _), n₀, n, lab) =>
    if GensData.fixesB gs w then .base else
    match lab with
    | none => if 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), w)).length then .chain else .m0
    | some L => hintCase (kf n₀) (ℓf n₀) n N gs w L

/-- **The children's predicate of each case**, for a parent with `p` window points and base
`m`: the chain rule's, M0's (`FreeChild` with base `2p + 1`), M1's and M2a's (`FreeChild`), and
`StepChild` for the others. -/
def casePred : MainCase → ℕ → ℕ → ℕ × Option ℕ → Prop
  | .chain, p, _ => ChainChild p
  | .m0, p, _ => FreeChild p (2 * p + 1)
  | .m1, p, m => FreeChild p m
  | .m2a, p, m => FreeChild p m
  | _, p, m => StepChild p m

end Cases

/-! ### The branches of the hinted dispatch -/

section Branches

/-- The cost of the hinted dispatch's prefix: normalizing the labels, the base window and its
orbits, for `n` string positions, degree `N` and `g` generators. -/
def hintPreCost (n N g : ℕ) : ℕ := 6 * n + baseWinCost n N + orbitsCost N g (N - n) + (N - n) + 30

/-- The cost of the block test: the maximal blocks of the base and `blkOKProg`. -/
def blkTestCost (n N g : ℕ) : ℕ := baseBlocksCost N (N - n) g + (N - n) + 10

/-- The cost of the equidistribution test on `p` window points. -/
def neqTestCost (n N p : ℕ) : ℕ := neqCost N (N - n) (N - n) (N - n) p (N - n) + 2

/-- The cost of the large-base tests: the thresholds (`t`), the degree of transitivity with the
charges of `ssBoundsS N s` and the numeric tests. -/
def bigTestCost (n N s t : ℕ) : ℕ :=
  t + degreeCost N (N - n - 2) (orbitsCost N s N + 5) (stabCost N s + 5) + 30

variable {thr : ThrProg Ty.unit}
  {body : (hinstTy Ty.unit).denote →
    Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit)}
  {sub : HInstData Ty.unit →
    Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit)}
  {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData} {n₀ n : ℕ}
  {L : LabelData} {ans : AnswerData Ty.unit} {c : ℕ}

/-- **M1's branch**: more than one base orbit. -/
theorem RunsWithin.hintProg_m1 (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hsplit : 2 ≤ (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length)
    (h : RunsWithin ssCtx body (Main.m1StepProg sub
      (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) : HInstData Ty.unit) (normLabD n L))
      ans c) :
    RunsWithin ssCtx body
      (Main.hintProg thr sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) L)
      ans (c + hintPreCost n N gs.length) := by
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)) := ss_baseOrbits hgs hb
  have hlen := IsOrbitPartition.length_le_win hos
  rw [baseWin_length] at hlen
  have hbo := ss_hint_hBo N n gs ()
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.normLabProg n L)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.baseWinProg n N)
    run_step (RunsWithin.prim _ _)
    run_step ((RunsWithin.call (X := ssCtx) (op := GroupOp.orbits)
      (x := ((N, gs, ()), baseWin n N))
      ⟨⟨hgs, trivial⟩, baseWin_valid n N, by rw [baseWin_denote]; exact hb⟩).mono hbo)
    run_step (RunsWithin.prim_le (c := N - n + 1) rfl (Nat.add_le_add_right hlen 1))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim_le (v := true)
      (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length) = true
        from decide_eq_true (by omega)) le_rfl)
    exact RunsWithin.ite_true h
  case hc =>
    simp only [Prim.cost]
    unfold hintPreCost
    clear * -
    omega

theorem neqCost_mono {N m f f' k k' p T : ℕ} (hf : f ≤ f') (hk : k ≤ k') :
    neqCost N m f k p T ≤ neqCost N m f' k' p T := by
  unfold neqCost equidistCost
  gcongr

/-- The common facts of the block branches: the base orbit partition has at most one orbit. -/
theorem hint_noSplit_cost (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) :
    (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ N - n ∧
      ((mbD n N gs).headD []).length ≤ N - n := by
  have hos : IsOrbitPartition (GensData.denote N gs) (baseWin n N)
      (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)) := ss_baseOrbits hgs hb
  have hlen := IsOrbitPartition.length_le_win hos
  rw [baseWin_length] at hlen
  have hhd := dv_headD_len (N := N) (gs := gs) (pts := basePts n N)
  rw [length_basePts] at hhd
  exact ⟨hlen, hhd⟩

/-- **The block branches**: one base orbit, proper maximal blocks, and the equidistribution
test with value `ne`; the continuation `k` is M2a's or M2b's step. -/
theorem RunsWithin.hintProg_blocks (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ 1)
    (hok : blkOKD (N - n) (mbD n N gs) = true)
    (hfl : (mbD n N gs).flatten.length ≤ N - n) (hbl : (mbD n N gs).length ≤ N - n)
    (hT : ∀ u ∈ w.1, ((normLabD n L).getD u []).length ≤ N - n)
    (h : RunsWithin ssCtx body
      (Prog.ite (neqD n N (mbD n N gs) (normLabD n L) w.1)
        (Main.m2aStepProg sub (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) :
          HInstData Ty.unit) (normLabD n L) (mbD n N gs))
        (Main.m2bStepProg sub (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) :
          HInstData Ty.unit) (mbD n N gs))) ans c) :
    RunsWithin ssCtx body
      (Main.hintProg thr sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) L)
      ans (c + hintPreCost n N gs.length + blkTestCost n N gs.length +
        neqTestCost n N w.1.length) := by
  obtain ⟨hlen, hhd⟩ := hint_noSplit_cost hgs hb
  have hbo := ss_hint_hBo N n gs ()
  have hbb := RunsWithin.baseBlocksProg (D := Ty.unit) (X := ssCtx) (body := body) (d := ()) hgs hb
  have hk := RunsWithin.blkOKProg (X := ssCtx) (body := body) (N - n) (mbD n N gs)
  rw [hok] at hk
  have hne := (RunsWithin.neqProg (X := ssCtx) (body := body) n N (mbD n N gs) (normLabD n L)
    w.1 hT).mono (neqCost_mono hfl hbl)
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.normLabProg n L)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.baseWinProg n N)
    run_step (RunsWithin.prim _ _)
    run_step ((RunsWithin.call (X := ssCtx) (op := GroupOp.orbits)
      (x := ((N, gs, ()), baseWin n N))
      ⟨⟨hgs, trivial⟩, baseWin_valid n N, by rw [baseWin_denote]; exact hb⟩).mono hbo)
    run_step (RunsWithin.prim_le (c := N - n + 1) rfl (Nat.add_le_add_right hlen 1))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim_le (v := false)
      (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length) = false
        from decide_eq_false (by omega)) le_rfl)
    apply RunsWithin.ite_false
    run_step hbb
    run_step (hk.mono (c' := N - n + 8) (by omega))
    apply RunsWithin.ite_true
    run_step (RunsWithin.prim _ _)
    run_step hne
    exact h
  case hc =>
    simp only [Prim.cost]
    unfold hintPreCost blkTestCost neqTestCost
    clear * -
    omega

/-- **M2a's branch**: proper maximal blocks, some window label not equidistributed. -/
theorem RunsWithin.hintProg_m2a (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ 1)
    (hok : blkOKD (N - n) (mbD n N gs) = true)
    (hfl : (mbD n N gs).flatten.length ≤ N - n) (hbl : (mbD n N gs).length ≤ N - n)
    (hT : ∀ u ∈ w.1, ((normLabD n L).getD u []).length ≤ N - n)
    (hne : neqD n N (mbD n N gs) (normLabD n L) w.1 = true)
    (h : RunsWithin ssCtx body (Main.m2aStepProg sub
      (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) : HInstData Ty.unit) (normLabD n L)
      (mbD n N gs)) ans c) :
    RunsWithin ssCtx body
      (Main.hintProg thr sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) L)
      ans (c + 1 + hintPreCost n N gs.length + blkTestCost n N gs.length +
        neqTestCost n N w.1.length) :=
  (RunsWithin.hintProg_blocks hgs hb hone hok hfl hbl hT
    (by rw [hne]; exact RunsWithin.ite_true h)).mono (by omega)

/-- **M2b's branch**: proper maximal blocks, every window label equidistributed. -/
theorem RunsWithin.hintProg_m2b (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ 1)
    (hok : blkOKD (N - n) (mbD n N gs) = true)
    (hfl : (mbD n N gs).flatten.length ≤ N - n) (hbl : (mbD n N gs).length ≤ N - n)
    (hT : ∀ u ∈ w.1, ((normLabD n L).getD u []).length ≤ N - n)
    (hne : neqD n N (mbD n N gs) (normLabD n L) w.1 = false)
    (h : RunsWithin ssCtx body (Main.m2bStepProg sub
      (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) : HInstData Ty.unit) (mbD n N gs))
      ans c) :
    RunsWithin ssCtx body
      (Main.hintProg thr sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) L)
      ans (c + 1 + hintPreCost n N gs.length + blkTestCost n N gs.length +
        neqTestCost n N w.1.length) :=
  (RunsWithin.hintProg_blocks hgs hb hone hok hfl hbl hT
    (by rw [hne]; exact RunsWithin.ite_false h)).mono (by omega)

/-- **The large-base branch**: one base orbit, no proper maximal blocks. -/
theorem RunsWithin.hintProg_big (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hone : (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length ≤ 1)
    (hok : blkOKD (N - n) (mbD n N gs) = false)
    (h : RunsWithin ssCtx body (Main.bigProg thr sub
      (((xy, w, σd, N, gs, ()), n₀, n, some (normLabD n L)) : HInstData Ty.unit) (normLabD n L)
      n₀ n (N - n) (N, gs, ())) ans c) :
    RunsWithin ssCtx body
      (Main.hintProg thr sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) L)
      ans (c + hintPreCost n N gs.length + blkTestCost n N gs.length) := by
  obtain ⟨hlen, hhd⟩ := hint_noSplit_cost hgs hb
  have hbo := ss_hint_hBo N n gs ()
  have hbb := RunsWithin.baseBlocksProg (D := Ty.unit) (X := ssCtx) (body := body) (d := ()) hgs hb
  have hk := RunsWithin.blkOKProg (X := ssCtx) (body := body) (N - n) (mbD n N gs)
  rw [hok] at hk
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.normLabProg n L)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.baseWinProg n N)
    run_step (RunsWithin.prim _ _)
    run_step ((RunsWithin.call (X := ssCtx) (op := GroupOp.orbits)
      (x := ((N, gs, ()), baseWin n N))
      ⟨⟨hgs, trivial⟩, baseWin_valid n N, by rw [baseWin_denote]; exact hb⟩).mono hbo)
    run_step (RunsWithin.prim_le (c := N - n + 1) rfl (Nat.add_le_add_right hlen 1))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim_le (v := false)
      (show decide (1 < (ssCtx.O.run GroupOp.orbits ((N, gs, ()), baseWin n N)).length) = false
        from decide_eq_false (by omega)) le_rfl)
    apply RunsWithin.ite_false
    run_step hbb
    run_step (hk.mono (c' := N - n + 8) (by omega))
    exact RunsWithin.ite_false h
  case hc =>
    simp only [Prim.cost]
    unfold hintPreCost blkTestCost
    clear * -
    omega

end Branches

section BigBranches

variable {thr : ThrProg Ty.unit} {kf ℓf cT : ℕ → ℕ}
  {body : (hinstTy Ty.unit).denote →
    Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit)}
  {sub : HInstData Ty.unit →
    Prog (groupSig Ty.unit) (hinstTy Ty.unit, Ty.answer Ty.unit) Ty.denote (Ty.answer Ty.unit)}
  {I : HInstData Ty.unit} {L : LabelData} {N : ℕ} {gs : GensData} {n₀ n s : ℕ}
  {ans : AnswerData Ty.unit} {c : ℕ}

/-- **A base of at most `ℓ` points**: M3. -/
theorem RunsWithin.bigProg_small (hT : ThrSpec thr kf ℓf cT) (hℓ : ¬ ℓf n₀ < N - n)
    (h : RunsWithin ssCtx body (Main.m3Prog sub I) ans c) :
    RunsWithin ssCtx body (Main.bigProg thr sub I L n₀ n (N - n) (N, gs, ())) ans
      (c + bigTestCost n N s (cT n₀)) := by
  apply RunsWithin.mono
  case h =>
    run_step (hT.run body n₀)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim_le (v := false)
      (show decide (ℓf n₀ < N - n) = false from decide_eq_false hℓ) le_rfl)
    exact RunsWithin.ite_false h
  case hc =>
    simp only [Prim.cost]
    unfold bigTestCost
    clear * -
    omega

/-- **The degree of transitivity** of a base larger than `ℓ`, with the giant test's value. -/
theorem RunsWithin.bigProg_deg (hT : ThrSpec thr kf ℓf cT) (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hs : gs.length ≤ s)
    (hN : N * N ≤ s) (hℓ : ℓf n₀ < N - n)
    (h : RunsWithin ssCtx body (Prog.ite (m4Deg ssCtx.O n (N, gs, ()) == N - n - 2)
      (Prog.bind (Main.m5OkProg (kf n₀) (N - n)) fun ok =>
        Prog.ite ok (Prog.bind Main.noStProg fun st => Main.m5StepCJProg sub I L (kf n₀) st)
          (Main.m3Prog sub I))
      (Prog.bind (Main.m4OkProg (m4Deg ssCtx.O n (N, gs, ())) (N - n)) fun ok =>
        Prog.ite ok (Main.m4StepProg sub I) (Main.m3Prog sub I))) ans c) :
    RunsWithin ssCtx body (Main.bigProg thr sub I L n₀ n (N - n) (N, gs, ())) ans
      (c + (cT n₀ + degreeCost N (N - n - 2) (orbitsCost N s N + 5) (stabCost N s + 5) + 9)) := by
  have hdeg : RunsWithin ssCtx body (Toolkit.degreeProg n (N - n - 2) (N, gs, ()))
      (m4Deg ssCtx.O n (N, gs, ()))
      (degreeCost N (N - n - 2) (orbitsCost N s N + 5) (stabCost N s + 5)) :=
    RunsWithin.degreeProg (fun op x _ hx => ssOracle_meets op x hx) (fun _ _ _ h => h)
      (ssBoundsS N s ⊤ hN) ⟨hgs, trivial⟩ hs le_top hb hn
  apply RunsWithin.mono
  case h =>
    run_step (hT.run body n₀)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim_le (v := true)
      (show decide (ℓf n₀ < N - n) = true from decide_eq_true hℓ) le_rfl)
    apply RunsWithin.ite_true
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hdeg
    run_step (RunsWithin.prim _ _)
    exact h
  case hc =>
    simp only [Prim.cost]
    clear * -
    omega

/-- **M5's branch**: a giant base meeting M5's numeric test. -/
theorem RunsWithin.bigProg_m5 (hT : ThrSpec thr kf ℓf cT) (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hs : gs.length ≤ s)
    (hN : N * N ≤ s) (hℓ : ℓf n₀ < N - n) (hgi : m4Deg ssCtx.O n (N, gs, ()) = N - n - 2)
    (hok : m5OkD (kf n₀) (N - n) = true)
    (h : RunsWithin ssCtx body (Main.m5StepCJProg sub I L (kf n₀) noStD) ans c) :
    RunsWithin ssCtx body (Main.bigProg thr sub I L n₀ n (N - n) (N, gs, ())) ans
      (c + bigTestCost n N s (cT n₀)) := by
  have h5 := RunsWithin.m5OkProg (X := ssCtx) (body := body) (kf n₀) (N - n)
  rw [hok] at h5
  refine (RunsWithin.bigProg_deg (c := 1 + (9 + (1 + (4 + c)))) hT hgs hb hn hs hN hℓ ?_).mono
    (by unfold bigTestCost; omega)
  rw [show (m4Deg ssCtx.O n (N, gs, ()) == N - n - 2) = true from beq_iff_eq.2 hgi]
  exact RunsWithin.ite_true (RunsWithin.step h5
    (RunsWithin.ite_true (RunsWithin.step RunsWithin.noStProg h)))

/-- A giant base failing M5's numeric test: M3. -/
theorem RunsWithin.bigProg_m5_m3 (hT : ThrSpec thr kf ℓf cT) (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hs : gs.length ≤ s)
    (hN : N * N ≤ s) (hℓ : ℓf n₀ < N - n) (hgi : m4Deg ssCtx.O n (N, gs, ()) = N - n - 2)
    (hok : m5OkD (kf n₀) (N - n) = false)
    (h : RunsWithin ssCtx body (Main.m3Prog sub I) ans c) :
    RunsWithin ssCtx body (Main.bigProg thr sub I L n₀ n (N - n) (N, gs, ())) ans
      (c + bigTestCost n N s (cT n₀)) := by
  have h5 := RunsWithin.m5OkProg (X := ssCtx) (body := body) (kf n₀) (N - n)
  rw [hok] at h5
  refine (RunsWithin.bigProg_deg (c := 1 + (9 + (1 + c))) hT hgs hb hn hs hN hℓ ?_).mono
    (by unfold bigTestCost; omega)
  rw [show (m4Deg ssCtx.O n (N, gs, ()) == N - n - 2) = true from beq_iff_eq.2 hgi]
  exact RunsWithin.ite_true (RunsWithin.step h5 (RunsWithin.ite_false h))

/-- **M4's branch**: a base that is not a giant, meeting M4's numeric test. -/
theorem RunsWithin.bigProg_m4 (hT : ThrSpec thr kf ℓf cT) (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hs : gs.length ≤ s)
    (hN : N * N ≤ s) (hℓ : ℓf n₀ < N - n) (hgi : m4Deg ssCtx.O n (N, gs, ()) ≠ N - n - 2)
    (hok : m4OkD (m4Deg ssCtx.O n (N, gs, ())) (N - n) = true)
    (h : RunsWithin ssCtx body (Main.m4StepProg sub I) ans c) :
    RunsWithin ssCtx body (Main.bigProg thr sub I L n₀ n (N - n) (N, gs, ())) ans
      (c + bigTestCost n N s (cT n₀)) := by
  have h4 := RunsWithin.m4OkProg (X := ssCtx) (body := body) (m4Deg ssCtx.O n (N, gs, ())) (N - n)
  rw [hok] at h4
  refine (RunsWithin.bigProg_deg (c := 1 + (10 + (1 + c))) hT hgs hb hn hs hN hℓ ?_).mono
    (by unfold bigTestCost; omega)
  rw [show (m4Deg ssCtx.O n (N, gs, ()) == N - n - 2) = false from beq_eq_false_iff_ne.2 hgi]
  exact RunsWithin.ite_false (RunsWithin.step h4 (RunsWithin.ite_true h))

/-- A base that is not a giant, failing M4's numeric test: M3. -/
theorem RunsWithin.bigProg_m4_m3 (hT : ThrSpec thr kf ℓf cT) (hgs : GensData.AllValid N gs)
    (hb : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hs : gs.length ≤ s)
    (hN : N * N ≤ s) (hℓ : ℓf n₀ < N - n) (hgi : m4Deg ssCtx.O n (N, gs, ()) ≠ N - n - 2)
    (hok : m4OkD (m4Deg ssCtx.O n (N, gs, ())) (N - n) = false)
    (h : RunsWithin ssCtx body (Main.m3Prog sub I) ans c) :
    RunsWithin ssCtx body (Main.bigProg thr sub I L n₀ n (N - n) (N, gs, ())) ans
      (c + bigTestCost n N s (cT n₀)) := by
  have h4 := RunsWithin.m4OkProg (X := ssCtx) (body := body) (m4Deg ssCtx.O n (N, gs, ())) (N - n)
  rw [hok] at h4
  refine (RunsWithin.bigProg_deg (c := 1 + (10 + (1 + c))) hT hgs hb hn hs hN hℓ ?_).mono
    (by unfold bigTestCost; omega)
  rw [show (m4Deg ssCtx.O n (N, gs, ()) == N - n - 2) = false from beq_eq_false_iff_ne.2 hgi]
  exact RunsWithin.ite_false (RunsWithin.step h4 (RunsWithin.ite_false h))

end BigBranches

end GraphIso.Main
