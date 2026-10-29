module

public import GraphIso.Coherent.DesignProg
public import Mathlib.Tactic.Positivity

/-!
# Weisfeiler–Leman and the Design Lemma: checked entries

Two closed procedures over the empty backend signature, with their main theorems:

* **`wlChecked`** on `(k, m, col)`: `none` exactly when `col` is not an array of `m^k` colours;
  otherwise the `k`-ary Weisfeiler–Leman refinement of the colouring `toFun col` of the
  `k`-tuples of `Fin m`, as an array indexed by codes, and its colour list (`wl_checked`). The
  model `wl` is a coherent configuration refining the input (`wl_isCoherent`, `wl_refines`),
  canonical (`wl_relabel`), with the isomorphisms of the input (`wl_iso_iff`).
* **`descentChecked`** on `(k, m, t, col)`: `none` exactly when the input is invalid (`k < 2`,
  `2 t < m`, or `col` not of size `m^k`); `some none` only if the input has more than `t`
  pairwise twins; otherwise `some (some (xd, col₁))` with `xd` the digits of a list `x` of fewer
  than `k` points at which the Design Lemma's conclusion holds for the refinement, and `col₁`
  the individualized vertex colouring at `x` (`descent_checked`).

The costs are at most `720 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)` and
`1000 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)`, polynomial in `m` for every fixed `k`, and
`m^{O(k)}` when `k ≤ m`.
-/

@[expose] public section

namespace GraphIso.Coherent

open Cost Programs Sims Finset

/-- The input of the refinement: `k`, `m` and the colouring. -/
abbrev wlInTy : Ty := .prod .nat (.prod .nat (.array .nat))

/-- The output of the refinement: the stable colouring and its colour list. -/
abbrev wlOutTy : Ty := .prod (.array .nat) (.list .nat)

/-- The input of the descent: `k`, `m`, the threshold `t` and the colouring. -/
abbrev descentInTy : Ty := .prod .nat (.prod .nat (.prod .nat (.array .nat)))

/-- The output of the descent: a list of points and its vertex colouring, if found. -/
abbrev descentOutTy : Ty := .option (.prod (.list .nat) (.array .nat))

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- `m ^ k`, by repeated multiplication. -/
def powProg (m k : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .range k) fun rk => .bind (.op0 (.natLit 1)) fun one =>
  .foldList rk one fun acc _ => mulNProg m acc

end Prog

/-- **The checked Weisfeiler–Leman entry.** -/
def wlChecked : Proc Signature.empty wlInTy (.option wlOutTy) := fun _ inp =>
  .bind (.op1 .fst inp) fun k => .bind (.op1 .snd inp) fun r => .bind (.op1 .fst r) fun m =>
  .bind (.op1 .snd r) fun col => .bind (powProg m k) fun N =>
  .bind (.op1 .arraySize col) fun sz => .bind (.op2 .natEq sz N) fun ok =>
  .ite ok (.bind (wlProg k m col) fun res => .op1 .some res) (.op0 .none)

/-- **The checked descent entry**: the refinement, then the Design Lemma search. -/
def descentChecked : Proc Signature.empty descentInTy (.option descentOutTy) := fun _ inp =>
  .bind (.op1 .fst inp) fun k => .bind (.op1 .snd inp) fun r₁ => .bind (.op1 .fst r₁) fun m =>
  .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun t => .bind (.op1 .snd r₂) fun col =>
  .bind (powProg m k) fun N => .bind (.op1 .arraySize col) fun sz =>
  .bind (.op2 .natEq sz N) fun ok₁ => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .natLt k two) fun small => .bind (.op1 .not small) fun ok₂ =>
  .bind (.op2 .add t t) fun t₂ => .bind (.op2 .natLt t₂ m) fun thin =>
  .bind (.op1 .not thin) fun ok₃ => .bind (.op2 .and ok₁ ok₂) fun ok₁₂ =>
  .bind (.op2 .and ok₁₂ ok₃) fun ok =>
  .ite ok
    (.bind (wlProg k m col) fun res => .bind (.op1 .fst res) fun c =>
      .bind (searchProg c k m t) fun found => .op1 .some found)
    (.op0 .none)

theorem wlChecked_wf {var₁ var₂ : Ty → Type} (x₁ : var₁ wlInTy) (x₂ : var₂ wlInTy) :
    Prog.Wf true [⟨wlInTy, x₁, x₂⟩] (wlChecked var₁ x₁) (wlChecked var₂ x₂) := by
  unfold wlChecked powProg mulNProg
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind ?_ fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) (.bind (wf_wlProg (by simp) (by simp) (by simp)) fun _ _ =>
      .prim _ (.cons (by simp) .nil)) (.prim _ .nil)
  prog_wf

theorem descentChecked_wf {var₁ var₂ : Ty → Type} (x₁ : var₁ descentInTy)
    (x₂ : var₂ descentInTy) :
    Prog.Wf true [⟨descentInTy, x₁, x₂⟩] (descentChecked var₁ x₁) (descentChecked var₂ x₂) := by
  unfold descentChecked powProg mulNProg
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind ?_ fun _ _ => ?_
  · prog_wf
  · refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil)))
      fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .ite (by simp) (.bind (wf_wlProg (by simp) (by simp) (by simp)) fun _ _ =>
        .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
        .bind (wf_searchProg (by simp) (by simp) (by simp) (by simp)) fun _ _ =>
        .prim _ (.cons (by simp) .nil)) (.prim _ .nil)

/-! ### Costs -/

/-- The cost of `m ^ k`. -/
def powCost (k m : ℕ) : ℕ := k * (3 * m + 3) + k + 2

/-- The cost of the checked refinement. -/
def wlCheckedCost (k m : ℕ) : ℕ := powCost k m + wlCost k m + 8

/-- The cost of the checked descent. -/
def descentCheckedCost (k m : ℕ) : ℕ := powCost k m + wlCost k m + searchCost k m + 22

/-! ### Closed forms

With `A = m^k + 1`, `M = (m + 2)(k + 2)` and `K = k^k`: a signature costs at most `50 M² (K + 1)`,
comparing two at most `38 M (K + 1)`, ranking `N ≤ A` of them at most `A² (2 ce + 50)`, a round
at most `210 A² M² (K + 1)`, and the `A` rounds at most `489 A³ M² (K + 1)`; the tables cost at
most `114 A M² (K + 1)` and the search at most `141 A M²`. The arguments `N` and `K` of the
intermediate bounds are free; they are `m^k` and `k^k` in the programs. -/

section Bounds

variable (m k N K : ℕ)

theorem mk_facts : m + k + 2 ≤ (m + 2) * (k + 2) ∧ m * k ≤ (m + 2) * (k + 2) ∧
    m * m * k ≤ (m + 2) * (k + 2) * ((m + 2) * (k + 2)) ∧
    m * k * k ≤ (m + 2) * (k + 2) * ((m + 2) * (k + 2)) ∧
    m * m * k * k ≤ (m + 2) * (k + 2) * ((m + 2) * (k + 2)) ∧
    k * k ≤ (m + 2) * (k + 2) * ((m + 2) * (k + 2)) ∧
    m * m ≤ (m + 2) * (k + 2) * ((m + 2) * (k + 2)) := by
  refine ⟨by nlinarith, by nlinarith, ?_, ?_, ?_, ?_, ?_⟩ <;>
    nlinarith [Nat.zero_le (m * k), Nat.zero_le (m * m * k), Nat.zero_le (m * k * k)]

theorem ceSig_le : ceSig k m K ≤ 38 * ((m + 2) * (k + 2)) * (K + 1) := by
  unfold ceSig
  nlinarith [Nat.zero_le (m * K), Nat.zero_le (m * k), Nat.zero_le (m * k * K),
    Nat.zero_le (k * K)]

theorem sigCost_le : sigCost k m K ≤ 50 * ((m + 2) * (k + 2)) ^ 2 * (K + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := mk_facts m k
  unfold sigCost
  nlinarith [Nat.zero_le (m * K), Nat.zero_le (m * k), Nat.zero_le (m * m * k * K), Nat.zero_le K,
    Nat.zero_le (((m + 2) * (k + 2)) ^ 2 * K)]

theorem rankCost_le (ce : ℕ) : rankCost N ce ≤ (N + 1) ^ 2 * (2 * ce + 50) := by
  unfold rankCost
  nlinarith [Nat.zero_le (N * N * ce), Nat.zero_le (N * ce), Nat.zero_le ce]

theorem roundCost_le :
    roundCost N k m K ≤ 210 * (N + 1) ^ 2 * ((m + 2) * (k + 2)) ^ 2 * (K + 1) := by
  have h1 := sigCost_le m k K
  have h2 := ceSig_le m k K
  have h3 := rankCost_le N (ceSig k m K)
  set M := (m + 2) * (k + 2) with hM
  set A := N + 1 with hA
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  have hA1 : 1 ≤ A := by omega
  have hK1 : 1 ≤ K + 1 := by omega
  unfold roundCost
  have e1 : N * (sigCost k m K + 3) ≤ A * (50 * M ^ 2 * (K + 1) + 3) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : A ^ 2 * (2 * ceSig k m K + 50) ≤ A ^ 2 * (2 * (38 * M * (K + 1)) + 50) :=
    Nat.mul_le_mul_left _ (by omega)
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hAA : A ≤ A ^ 2 := by nlinarith
  nlinarith [Nat.mul_le_mul hAA (Nat.mul_le_mul_right (K + 1) hMM),
    Nat.zero_le (A ^ 2 * M ^ 2 * K), Nat.zero_le (A * M ^ 2 * K)]

theorem initCost_le : initCost N k ≤ 273 * (N + 1) ^ 2 * ((m + 2) * (k + 2)) ^ 2 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := mk_facts m k
  have h3 := rankCost_le N (ceSig0 k)
  set M := (m + 2) * (k + 2) with hM
  set A := N + 1 with hA
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  have hA1 : 1 ≤ A := by omega
  have e : ceSig0 k ≤ 98 * M ^ 2 := by unfold ceSig0; nlinarith
  have e2 : A ^ 2 * (2 * ceSig0 k + 50) ≤ A ^ 2 * (2 * (98 * M ^ 2) + 50) :=
    Nat.mul_le_mul_left _ (by omega)
  have hMM : 1 ≤ M ^ 2 := by nlinarith
  have hAA : A ≤ A ^ 2 := by nlinarith
  unfold initCost
  nlinarith [Nat.mul_le_mul hAA hMM, Nat.zero_le (A ^ 2 * M ^ 2)]

theorem infoCost_le :
    infoCost k m ≤ 114 * (m ^ k + 1) * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := mk_facts m k
  set M := (m + 2) * (k + 2) with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  have hMM : M ≤ M ^ 2 := by nlinarith
  generalize hN : m ^ k = N
  generalize hK : k ^ k = K
  have p2 : tupsCost k m ≤ 12 * (N + 1) * M := by
    unfold tupsCost extCost
    rw [hN]
    nlinarith [Nat.zero_le (N * m * k), Nat.zero_le (N * k), Nat.zero_le (N * M)]
  have p4 : tupsCost k k ≤ 15 * M ^ 2 * (K + 1) := by
    unfold tupsCost extCost
    rw [hK]
    nlinarith [Nat.zero_le (K * k * k), Nat.zero_le (K * k), Nat.zero_le (K * M ^ 2)]
  have p6 : pwTabCost k m ≤ 32 * M := by unfold pwTabCost; nlinarith
  have p8 : infoAtCost k m K + 3 ≤ 45 * M ^ 2 * (K + 1) := by
    unfold infoAtCost
    nlinarith [Nat.zero_le (K * k), Nat.zero_le (K * M), Nat.zero_le (K * M ^ 2)]
  have p8' : N * (infoAtCost k m K + 3) ≤ (N + 1) * (45 * M ^ 2 * (K + 1)) :=
    Nat.mul_le_mul (by omega) p8
  have p5 : K * (k + 4) ≤ 2 * M * (K + 1) := by nlinarith [Nat.zero_le (K * k)]
  unfold infoCost
  rw [hN, hK]
  nlinarith [Nat.zero_le (N * M), Nat.zero_le (N * M ^ 2 * K), Nat.zero_le (M ^ 2 * K),
    Nat.zero_le (N * M ^ 2), Nat.zero_le (M * K), Nat.zero_le (N * K)]

theorem wlRunCost_le :
    wlRunCost k m ≤ 489 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) := by
  have h1 := initCost_le m k (m ^ k)
  have h2 := roundCost_le m k (m ^ k) (k ^ k)
  set M := (m + 2) * (k + 2) with hM
  set A := m ^ k + 1 with hA
  set Kp := k ^ k + 1 with hKp
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  have hA1 : 1 ≤ A := by omega
  have hK1 : 1 ≤ Kp := by omega
  unfold wlRunCost
  have e : (m ^ k + 1) * (roundCost (m ^ k) k m (k ^ k) + 2) ≤
      A * (210 * A ^ 2 * M ^ 2 * Kp + 2) := Nat.mul_le_mul le_rfl (by omega)
  have f1 : A ^ 2 * M ^ 2 ≤ A ^ 3 * M ^ 2 * Kp := by
    have : A ^ 2 ≤ A ^ 3 := Nat.pow_le_pow_right hA1 (by omega)
    nlinarith [Nat.zero_le (A ^ 3 * M ^ 2)]
  have f2 : A ≤ A ^ 3 * M ^ 2 * Kp := by
    have : A ≤ A ^ 3 := by nlinarith
    have : 1 ≤ M ^ 2 * Kp := by nlinarith
    nlinarith
  nlinarith

theorem searchCost_le : searchCost k m ≤ 141 * (m ^ k + 1) * ((m + 2) * (k + 2)) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := mk_facts m k
  set M := (m + 2) * (k + 2) with hM
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  generalize hN : m ^ k = N
  have g : k * (goodCost k m + 7) ≤ 84 * M ^ 2 := by
    unfold goodCost
    nlinarith [Nat.zero_le (m * k), Nat.zero_le (m * m * k * k)]
  have t : k * tupsBound k m ≤ 20 * (N + 1) * M ^ 2 := by
    unfold tupsBound extCost
    rw [hN]
    nlinarith [Nat.zero_le (N * k * k * m), Nat.zero_le (N * k * k), Nat.zero_le (N * M ^ 2)]
  have p6 : pwTabCost k m ≤ 32 * M := by unfold pwTabCost; nlinarith
  have e : k * ((N + 1) * (goodCost k m + 7)) ≤ (N + 1) * (84 * M ^ 2) := by
    rw [Nat.mul_left_comm]
    exact Nat.mul_le_mul_left _ g
  unfold searchCost
  rw [hN]
  nlinarith [Nat.zero_le (N * M ^ 2)]

theorem powCost_le : powCost k m ≤ 9 * ((m + 2) * (k + 2)) := by
  unfold powCost
  nlinarith

end Bounds

/-- **The closed form of the refinement's cost.** -/
theorem wlCheckedCost_le (k m : ℕ) :
    wlCheckedCost k m ≤ 720 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) := by
  have h1 := infoCost_le m k
  have h2 := wlRunCost_le m k
  have h3 := powCost_le m k
  set M := (m + 2) * (k + 2) with hM
  set A := m ^ k + 1 with hA
  set Kp := k ^ k + 1 with hKp
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  have hA1 : 1 ≤ A := by omega
  have hK1 : 1 ≤ Kp := by omega
  have hA3 : A ≤ A ^ 3 := by simpa using Nat.pow_le_pow_right hA1 (by norm_num : 1 ≤ 3)
  have hX1 : 1 ≤ A ^ 3 * Kp := Nat.mul_le_mul (Nat.one_le_pow _ _ hA1) hK1
  have hMM : M ≤ M ^ 2 := by nlinarith
  have f : A * (M ^ 2 * Kp) ≤ A ^ 3 * (M ^ 2 * Kp) := Nat.mul_le_mul_right _ hA3
  have g : M ≤ A ^ 3 * (M ^ 2 * Kp) := by nlinarith
  have h1' : infoCost k m ≤ 114 * (A * (M ^ 2 * Kp)) := by simpa [Nat.mul_assoc] using h1
  have h2' : wlRunCost k m ≤ 489 * (A ^ 3 * (M ^ 2 * Kp)) := by
    simpa [Nat.mul_assoc] using h2
  have goal : 720 * A ^ 3 * M ^ 2 * Kp = 720 * (A ^ 3 * (M ^ 2 * Kp)) := by ring
  rw [goal]
  unfold wlCheckedCost wlCost
  omega

/-- **The closed form of the descent's cost.** -/
theorem descentCheckedCost_le (k m : ℕ) :
    descentCheckedCost k m ≤ 1000 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) := by
  have h1 := infoCost_le m k
  have h2 := wlRunCost_le m k
  have h3 := powCost_le m k
  have h4 := searchCost_le m k
  set M := (m + 2) * (k + 2) with hM
  set A := m ^ k + 1 with hA
  set Kp := k ^ k + 1 with hKp
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by rw [hM]; positivity)
  have hA1 : 1 ≤ A := by omega
  have hK1 : 1 ≤ Kp := by omega
  have hA3 : A ≤ A ^ 3 := by simpa using Nat.pow_le_pow_right hA1 (by norm_num : 1 ≤ 3)
  have hX1 : 1 ≤ A ^ 3 * Kp := Nat.mul_le_mul (Nat.one_le_pow _ _ hA1) hK1
  have hMM : M ≤ M ^ 2 := by nlinarith
  have f : A * (M ^ 2 * Kp) ≤ A ^ 3 * (M ^ 2 * Kp) := Nat.mul_le_mul_right _ hA3
  have f' : A * M ^ 2 ≤ A * (M ^ 2 * Kp) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hK1)
  have g : M ≤ A ^ 3 * (M ^ 2 * Kp) := by nlinarith
  have h1' : infoCost k m ≤ 114 * (A * (M ^ 2 * Kp)) := by simpa [Nat.mul_assoc] using h1
  have h2' : wlRunCost k m ≤ 489 * (A ^ 3 * (M ^ 2 * Kp)) := by
    simpa [Nat.mul_assoc] using h2
  have h4' : searchCost k m ≤ 141 * (A * M ^ 2) := by simpa [Nat.mul_assoc] using h4
  have goal : 1000 * A ^ 3 * M ^ 2 * Kp = 1000 * (A ^ 3 * (M ^ 2 * Kp)) := by ring
  rw [goal]
  unfold descentCheckedCost wlCost
  omega

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.powProg (m k : ℕ) :
    RunsWithin X body (Coherent.powProg m k) (m ^ k) (powCost k m) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 3 * m + 2) (F := fun acc _ => m * acc)
    (f := fun acc _ => Coherent.mulNProg m acc) (List.range k) 1
    fun acc _ _ => RunsWithin.mulNProg m acc
  rw [sum_map_const, List.length_range, show 3 * m + 2 + 1 = 3 * m + 3 from rfl] at hfold
  have hv : ∀ n, (List.range n).foldl (fun acc _ => m * acc) 1 = m ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.range_succ, List.foldl_append, ih]; simp [pow_succ, Nat.mul_comm]
  rw [hv] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc => simp only [Prim.cost, Args.head_cons, powCost]; omega

end Specs

/-- **The checked refinement**, against any context. -/
theorem RunsWithin.wlChecked {X : Ctx Signature.empty}
    {body : wlInTy.denote → Prog Signature.empty (wlInTy, .option wlOutTy) Ty.denote
      (.option wlOutTy)} (k m : ℕ) (col : Array ℕ) :
    ∃ r, RunsWithin X body (wlChecked Ty.denote (k, m, col)) r (wlCheckedCost k m) ∧
      (r = none ↔ col.size ≠ m ^ k) ∧ ∀ res, r = some res → res = wlA k m col := by
  by_cases hsz : col.size = m ^ k
  · refine ⟨some (wlA k m col), ?_, by simp [hsz], fun res h => (Option.some.inj h).symm⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.powProg m k)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (col.size == m ^ k) = true by simpa using hsz) _
      run_step (RunsWithin.wlProg k m col)
      exact RunsWithin.prim _ _
    case hc => simp only [Prim.cost, wlCheckedCost]; omega
  · refine ⟨none, ?_, by simp [hsz], fun res h => by cases h⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.powProg m k)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (col.size == m ^ k) = false by simpa using hsz) _
      exact RunsWithin.prim _ _
    case hc => simp only [Prim.cost, wlCheckedCost]; omega

/-- **The `k`-ary Weisfeiler–Leman refinement as a costed program.** On every input
`(k, m, col)` the checked entry returns `none` exactly when `col` is not an array of `m ^ k`
colours, and otherwise the array of the refinement `wl k m (toFun col)` of the colouring of the
`k`-tuples of `Fin m` that `col` stores (indexed by codes), together with its colour list, at a
cost of at most `720 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)`. The refinement is a coherent
configuration refining the input (`wl_isCoherent`, `wl_refines`), canonical (`wl_relabel`), and
has the isomorphisms of the input (`wl_iso_iff`). -/
theorem wl_checked (k m : ℕ) (col : Array ℕ) :
    ∃ (r : Option (Array ℕ × List ℕ)) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (wlChecked Ty.denote) (wlChecked Ty.denote (k, m, col)) r tr ∧
      Trace.localCost tr ≤ 720 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) ∧
      (r = none ↔ col.size ≠ m ^ k) ∧
      ∀ res, r = some res → res.1.size = m ^ k ∧ toFun res.1 = (wl k m (toFun col)).1 ∧
        res.2 = (wl k m (toFun col)).2 := by
  obtain ⟨r, ⟨tr, hrun, hc, -⟩, hnone, hsome⟩ :=
    RunsWithin.wlChecked (X := Ctx.empty) (body := wlChecked Ty.denote) k m col
  refine ⟨r, tr, hrun, ?_, hnone, fun res h => ?_⟩
  · rw [Trace.cost_empty] at hc
    exact hc.trans (wlCheckedCost_le k m)
  · rw [hsome res h, wlA_eq]
    exact ⟨size_arrOf _, toFun_arrOf _, rfl⟩

/-- **The checked descent**, against any context. -/
theorem RunsWithin.descentChecked {X : Ctx Signature.empty}
    {body : descentInTy.denote → Prog Signature.empty (descentInTy, .option descentOutTy) Ty.denote
      (.option descentOutTy)} (k m t : ℕ) (col : Array ℕ) :
    ∃ r, RunsWithin X body (descentChecked Ty.denote (k, m, t, col)) r (descentCheckedCost k m) ∧
      (r = none ↔ ¬ (2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k)) ∧
      ∀ res, r = some res → res = searchA (wlA k m col).1 k m t := by
  have hok : ((col.size == m ^ k && !decide (k < 2)) && !decide (t + t < m)) = true ↔
      (2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k) := by
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    omega
  by_cases hv : 2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k
  · refine ⟨some (searchA (wlA k m col).1 k m t), ?_, by simp [hv],
      fun res h => (Option.some.inj h).symm⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.powProg m k)
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
      run_with RunsWithin.ite_pos (by simpa [Prim.eval] using hok.2 hv) _
      run_step (RunsWithin.wlProg k m col)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.searchProg _ k m t)
      exact RunsWithin.prim _ _
    case hc => simp only [Prim.cost, descentCheckedCost]; omega
  · refine ⟨none, ?_, by simp [hv], fun res h => by cases h⟩
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.powProg m k)
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
      run_with RunsWithin.ite_neg (by simpa [Prim.eval] using mt hok.1 hv) _
      exact RunsWithin.prim _ _
    case hc => simp only [Prim.cost, descentCheckedCost]; omega

/-- **Descent from a relational structure: the Design Lemma as an algorithm.** On every input
`(k, m, t, col)`, the checked entry returns `none` exactly when the input is invalid (`k < 2`,
`2 t < m`, or `col` not an array of `m ^ k` colours). Otherwise, with `c` the `k`-ary
Weisfeiler–Leman refinement of the colouring `toFun col` of the `k`-tuples of `Fin m`:
* `some none` only if `toFun col` has a set of more than `t` pairwise twins;
* `some (some (xd, col₁))` with `xd` the points of a list `x` of fewer than `k` points at which
  the Design Lemma's conclusion holds for `c` (`DesignGood`: the vertex colouring individualized
  at `x` has no class of more than `t` points, or `x` has fewer than `k − 1` points and the
  individualized 2-skeleton is not a clique on such a class), and `col₁` that vertex colouring.
The outcome at `x` is canonical relative to `x` (`skel1_wl_relabel`), and the restricted
2-skeleton is a classical coherent configuration (`isCoherent2_wl_skel2`). The cost is at most
`1000 (m^k + 1)³ ((m + 2)(k + 2))² (k^k + 1)`. -/
theorem descent_checked (k m t : ℕ) (col : Array ℕ) :
    ∃ (r : Option (Option (List ℕ × Array ℕ))) (tr : Trace Signature.empty),
      Runs Ctx.empty.O (descentChecked Ty.denote) (descentChecked Ty.denote (k, m, t, col)) r tr ∧
      Trace.localCost tr ≤ 1000 * (m ^ k + 1) ^ 3 * ((m + 2) * (k + 2)) ^ 2 * (k ^ k + 1) ∧
      (r = none ↔ ¬ (2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k)) ∧
      (r = some none → ∃ T : Finset (Fin m), t < T.card ∧
        ∀ u ∈ T, ∀ v ∈ T, IsTwin (toFun (k := k) col) u v) ∧
      ∀ xd col₁, r = some (some (xd, col₁)) → ∃ x : List (Fin m), xd = x.map Fin.val ∧
        x.length < k ∧
        col₁ = ((List.finRange m).map fun u => skel1 (wl k m (toFun col)).1 x u).toArray ∧
        DesignGood (wl k m (toFun col)).1 t x := by
  obtain ⟨r, ⟨tr, hrun, hc, -⟩, hnone, hsome⟩ :=
    RunsWithin.descentChecked (X := Ctx.empty) (body := descentChecked Ty.denote) k m t col
  have hcarr : (wlA k m col).1 = arrOf k m (wl k m (toFun col)).1 := by rw [wlA_eq]
  have hfun : toFun (k := k) (wlA k m col).1 = (wl k m (toFun col)).1 := by
    rw [hcarr, toFun_arrOf]
  refine ⟨r, tr, hrun, ?_, hnone, fun h => ?_, fun xd col₁ h => ?_⟩
  · rw [Trace.cost_empty] at hc
    exact hc.trans (descentCheckedCost_le k m)
  · have hv : 2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k := by
      by_contra hv
      rw [← hnone] at hv
      rw [hv] at h
      cases h
    have hs := (hsome _ h).symm
    by_contra hT
    push Not at hT
    obtain ⟨x, hx, hgood⟩ := design_lemma (V := Fin m) (t := t) hv.1 (wl_isCoherent (toFun col))
      (by simpa using hv.2.1) fun T hT' => by
        refine not_lt.1 fun hlt => ?_
        obtain ⟨u, hu, v, hv', hnt⟩ := hT T hlt
        exact hnt ((isTwin_wl_iff _ u v).1 (hT' u hu v hv'))
    have := searchA_eq_none hs x hx
    rw [← Bool.not_eq_true, goodA_iff _ hv.2.1, hfun] at this
    exact this hgood
  · have hv : 2 ≤ k ∧ m ≤ 2 * t ∧ col.size = m ^ k := by
      by_contra hv
      rw [← hnone] at hv
      rw [hv] at h
      cases h
    obtain ⟨x, hx, rfl, hgood, rfl⟩ := searchA_eq_some (hsome _ h).symm
    refine ⟨x, rfl, hx, ?_, ?_⟩
    · rw [List.length_map, col1A_eq, hfun]
    · rwa [goodA_iff _ hv.2.1, hfun] at hgood

/-- The individualized 2-skeleton of the refinement, restricted to a vertex colour class, is a
classical coherent configuration. -/
theorem isCoherent2_wl_skel2 {k m : ℕ} (c : Tup k m → ℕ) {x : List (Fin m)}
    (hx : x.length + 2 ≤ k) (κ : ℕ) :
    IsCoherent2 (fun u v : {w // skel2 (wl k m c).1 x w w = κ} => skel2 (wl k m c).1 x u v) :=
  isCoherent2_restrict (isCoherent2_skel2 (wl_isCoherent c) hx) κ

/-- **The outcome at `x` is canonical relative to `x`**: relabelling the input structure by `π`
and the individualized points by `π` leaves the individualized vertex colouring of the
refinement unchanged. -/
theorem skel1_wl_relabel {k m : ℕ} (c : Tup k m → ℕ) (π : Equiv.Perm (Fin m))
    (x : List (Fin m)) (u : Fin m) :
    skel1 (wl k m (fun y => c (⇑π⁻¹ ∘ y))).1 (x.map π) (π u) = skel1 (wl k m c).1 x u := by
  rw [wl_relabel]
  exact skel1_relabel _ π x u

end GraphIso.Coherent
