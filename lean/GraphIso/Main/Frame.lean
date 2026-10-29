module

public import GraphIso.Main.HInst
public import GraphIso.Recursion.Potential
public import GraphIso.Toolkit.Labels

/-!
# The macro-step framework

Stage 14j-2 (`PLAN-14.md` §14.2). Every macro-step of the main recursion is a program with a
**hinted sub-solver** `sub` as a parameter (stage 14j-5 instantiates it with `.recur`). Its
specification has four parts:

* the run, with an explicit cost: the sum of the children's costs `C x.1 x.2` over a list `ch`
  of their measures, plus the work;
* an answer correct for the parent (`InstData.OK`);
* the children's list `ch` of measures `(window size, base)`, with the sum of the window sizes
  at most `c · n` (`c` the branching factor, `n` the parent's window size), nonempty windows,
  and a predicate on each child: `StepChild` (the hypothesis of `pot_step`), `FreeChild` (that
  of `pot_free`) or `ChainChild` (the chain rule);
* each predicate implies a smaller measure (`MeasLt`, lexicographic on `hmeasure`), for the
  well-founded induction of stage 14j-5.

Definitions:

* `HInstData.baseOpt`: the base size of the hint, `none` without one (the argument of `potO`).
* `HSubSolves`: `sub` solves every valid hinted instance satisfying `P` within `C` of its
  measure, with at most `s` output generators.
* `SizeChild sC I J`: the size facts a child keeps (the same `n₀`, at most the parent's string
  positions, degree at most `max N (2 n)`, at most `sC` generators), from which stage 14j-6
  bounds the degrees. Each step names its `sC` from the bounds it has for the generator lists
  it passes to the sub-solver.
* `MeasLt`, `StepChild`, `FreeChild`, `ChainChild`, `ChildList`.

The contract repair of stage 14j-5a (`PLAN-14.md` §14.6) added the generator bound `gens_le`
of `SizeChild` and the positive windows `pos` of `ChildList`. With them, one bound is closed
under the recursion (`SizeChild.closed`): a child of a parent with at most `nB` string
positions, degree at most `NB ≥ 2 nB` and at most `sG` generators has the same bounds when the
step's `sC` is at most `sG`. A child list has at most `c · n` children (`ChildList.length_le`).

**The label invariant** (stage 14j-6a, `PLAN-14.md` §14.10). `LabInv J`: at most `n₀` string
positions, and a hint's base `m ≤ n₀` with labels of length `t` (`labLen`) such that
`t (⌊log₂ m⌋ + 1)² ≤ 2 (⌊log₂ n₀⌋ + 1)²` whenever `m > ell0 n₀ = max 2¹¹ ((⌊log₂ n₀⌋ + 1)³)`
(`LabInvAt`). `SizeChild`'s field `lab` carries it from a parent to its children
(`SizeChild.lab_closed`). It survives a smaller base with shorter labels (`LabInvAt.mono`),
labels of length one (`LabInvAt.of_le_one`), and a Johnson step whose labels grow by the factor
`s` (`LabInvAt.johnson`, from `johnson_step_label`). The entry's instance has it
(`LabInv.entry`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Toolkit

variable {D : Ty}

/-- **The base of a hinted instance** as the potential sees it: the size `N − n` of the base,
or `none` without a hint. -/
def HInstData.baseOpt (I : HInstData D) : Option ℕ := I.lab.map fun _ => I.inst.degree - I.n

theorem hmeasure_eq (I : HInstData D) :
    hmeasure I = (I.winSize, I.baseOpt.getD (2 * I.winSize + 1)) := by
  unfold hmeasure HInstData.baseOpt
  cases I.lab <;> rfl

/-- **The order of the recursion**: lexicographic on `(window size, base)`. -/
def MeasLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- **Hinted sub-solvers.** `sub` solves every valid hinted instance `J` with `P J`, within
`C` of its measure `(J.winSize, J.baseOpt)`, with a correct answer of at most `s` generators. -/
def HSubSolves {a b : Ty} (X : Ctx (groupSig D))
    (body : a.denote → Prog (groupSig D) (a, b) Ty.denote b)
    (DV : ℕ → GensData → D.denote → Prop)
    (sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D))
    (P : HInstData D → Prop) (C : ℕ → Option ℕ → ℕ) (s : ℕ) : Prop :=
  ∀ J, HInstValid DV J → P J → ∃ ans : AnswerData D,
    RunsWithin X body (sub J) ans (C J.winSize J.baseOpt) ∧ J.inst.OK DV ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s

/-! ### The label invariant -/

/-- **The invariant's threshold** `max 2¹¹ ((⌊log₂ n₀⌋ + 1)³)`, as `johnson_step_label` needs. -/
def ell0 (n₀ : ℕ) : ℕ := max (2 ^ 11) ((Recursion.lam n₀ + 1) ^ 3)

/-- **The label invariant at a base** of `m` points with labels of length `t`: `m ≤ n₀`, and
for `m > ell0 n₀`, `t (⌊log₂ m⌋ + 1)² ≤ 2 (⌊log₂ n₀⌋ + 1)²`. -/
def LabInvAt (n₀ m t : ℕ) : Prop :=
  m ≤ n₀ ∧ (ell0 n₀ < m → t * (Recursion.lam m + 1) ^ 2 ≤ 2 * (Recursion.lam n₀ + 1) ^ 2)

/-- **The label invariant** (`PLAN-14.md` §5 item 8, §14.10): at most `n₀` string positions,
and a hint's base `N − n` and label length within `LabInvAt`. -/
structure LabInv (J : HInstData D) : Prop where
  n_le : J.n ≤ J.n₀
  hint : ∀ L, J.lab = some L → LabInvAt J.n₀ (J.inst.degree - J.n) (labLen L)

/-- A smaller base with shorter labels. -/
theorem LabInvAt.mono {n₀ m t m' t' : ℕ} (h : LabInvAt n₀ m t) (hm : m' ≤ m) (ht : t' ≤ t) :
    LabInvAt n₀ m' t' := by
  refine ⟨hm.trans h.1, fun h' => ?_⟩
  have hl : (Recursion.lam m' + 1) ^ 2 ≤ (Recursion.lam m + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (Recursion.lam_mono hm) 1) 2
  exact (Nat.mul_le_mul ht hl).trans (h.2 (by omega))

/-- Labels of length at most one, on a base of at most `n₀` points. -/
theorem LabInvAt.of_le_one {n₀ m t : ℕ} (hm : m ≤ n₀) (ht : t ≤ 1) : LabInvAt n₀ m t := by
  refine ⟨hm, fun _ => ?_⟩
  have hl : (Recursion.lam m + 1) ^ 2 ≤ (Recursion.lam n₀ + 1) ^ 2 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (Recursion.lam_mono hm) 1) 2
  calc t * (Recursion.lam m + 1) ^ 2 ≤ 1 * (Recursion.lam n₀ + 1) ^ 2 := Nat.mul_le_mul ht hl
    _ ≤ 2 * (Recursion.lam n₀ + 1) ^ 2 := Nat.mul_le_mul_right _ (by norm_num)

theorem le_choose_two {m : ℕ} (hm : 3 ≤ m) : m ≤ m.choose 2 := by
  rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by norm_num)]
  exact Nat.mul_le_mul_left m (by omega)

/-- **Through a Johnson step**: from a base of `m` points to `m'` cells with `C(m', s) ≤ m`,
`2 ≤ s` and `2s ≤ m'`, with labels at most `s` times longer (`johnson_step_label`). -/
theorem LabInvAt.johnson {n₀ m t m' s t' : ℕ} (h : LabInvAt n₀ m t) (hC : m'.choose s ≤ m)
    (hs : 2 ≤ s) (hs' : 2 * s ≤ m') (ht : t' ≤ t * s) : LabInvAt n₀ m' t' := by
  have hm' : m' ≤ m :=
    (le_choose_two (by omega)).trans ((Recursion.choose_two_le_choose hs hs').trans hC)
  refine ⟨hm'.trans h.1, fun h' => ?_⟩
  have hJ := Recursion.johnson_step_label hC hs hs' h' (le_max_left _ _) (le_max_right _ _) h.1
  calc t' * (Recursion.lam m' + 1) ^ 2 ≤ t * s * (Recursion.lam m' + 1) ^ 2 :=
        Nat.mul_le_mul_right _ ht
    _ = t * (s * (Recursion.lam m' + 1) ^ 2) := by ring
    _ ≤ t * (Recursion.lam m + 1) ^ 2 := Nat.mul_le_mul_left _ hJ
    _ ≤ 2 * (Recursion.lam n₀ + 1) ^ 2 := h.2 (by omega)

/-- An instance without a hint. -/
theorem LabInv.of_none {J : HInstData D} (hn : J.n ≤ J.n₀) (h : J.lab = none) : LabInv J :=
  ⟨hn, fun L hL => by rw [h] at hL; cases hL⟩

/-- **The entry's instance has the label invariant**: `mainEntry` (and `miniEntry`) recurse on
`(J, N, N, none)`, with `n = n₀` and no hint. -/
theorem LabInv.entry (J : InstData D) (N : ℕ) : LabInv ((J, (N, (N, none))) : HInstData D) :=
  LabInv.of_none le_rfl rfl

/-- **A child with the parent's invariant**: the same `n₀`, at most the parent's string
positions, and a hint only where the parent has one, on a base no larger, with labels no longer
(or within `LabInvAt` directly). -/
theorem LabInv.of_le {I J : HInstData D} (hI : LabInv I) (hn₀ : J.n₀ = I.n₀) (hn : J.n ≤ I.n)
    (hh : ∀ L', J.lab = some L' → ∃ L, I.lab = some L ∧
      J.inst.degree - J.n ≤ I.inst.degree - I.n ∧ labLen L' ≤ labLen L) : LabInv J := by
  refine ⟨hn₀ ▸ hn.trans hI.n_le, fun L' hL' => ?_⟩
  obtain ⟨L, hL, hm, ht⟩ := hh L' hL'
  rw [hn₀]
  exact (hI.hint L hL).mono hm ht

/-- **The size facts of a child**: the same original size, at most the parent's string
positions, degree at most `max N (2 n)`, at most `sC` generators, and the label invariant
(stage 14j-6a, `PLAN-14.md` §14.10) if the parent has it. -/
structure SizeChild (sC : ℕ) (I J : HInstData D) : Prop where
  n₀ : J.n₀ = I.n₀
  n_le : J.n ≤ I.n
  degree_le : J.inst.degree ≤ max I.inst.degree (2 * I.n)
  gens_le : J.inst.2.2.2.gens.length ≤ sC
  lab : LabInv I → LabInv J

/-- **A child without a hint** has the label invariant when its parent does. -/
theorem SizeChild.lab_none {I J : HInstData D} (h₀ : J.n₀ = I.n₀) (hn : J.n ≤ I.n)
    (hJ : J.lab = none) : LabInv I → LabInv J :=
  fun hI => LabInv.of_none (h₀ ▸ hn.trans hI.n_le) hJ

/-- **A kept-or-halved child**, the hypothesis of `pot_step` for a parent with `n` window points
and base `m`: at most `n` points, and a hint with base at most `3m/4`, or no hint on at most
`n/2` points. -/
def StepChild (n m : ℕ) (x : ℕ × Option ℕ) : Prop :=
  x.1 ≤ n ∧ ((∃ m', x.2 = some m' ∧ 4 * m' ≤ 3 * m) ∨ (x.2 = none ∧ 2 * x.1 ≤ n))

/-- **A free child**, the hypothesis of `pot_free`: at most `n` points, and a hint with a base
at most `m` that shrinks the base or the window, or no hint on at most `n/2` points. The window
bound is part of the predicate, so that a sub-solver hypothesis quantified over it only covers
instances of smaller measure (round 1 of the 14j-2 audit, finding F1). -/
def FreeChild (n m : ℕ) (x : ℕ × Option ℕ) : Prop :=
  x.1 ≤ n ∧ ((∃ m', x.2 = some m' ∧ m' ≤ m ∧ (m' < m ∨ x.1 < n)) ∨ (x.2 = none ∧ 2 * x.1 ≤ n))

/-- **A chain child**: no hint, on a proper part of the window. -/
def ChainChild (n : ℕ) (x : ℕ × Option ℕ) : Prop := x.2 = none ∧ x.1 < n

/-- **The children of a step**: the window sizes sum to at most `c · n`, each child satisfies
`pred`, and every child's window is nonempty. -/
structure ChildList (n c : ℕ) (pred : ℕ × Option ℕ → Prop) (ch : List (ℕ × Option ℕ)) :
    Prop where
  sum_le : (ch.map Prod.fst).sum ≤ c * n
  pred : ∀ x ∈ ch, pred x
  pos : ∀ x ∈ ch, 1 ≤ x.1

/-- **The number of children** is at most `c · n`: every window has a point. -/
theorem ChildList.length_le {n c : ℕ} {pred : ℕ × Option ℕ → Prop} {ch : List (ℕ × Option ℕ)}
    (h : ChildList n c pred ch) : ch.length ≤ c * n := by
  have key : ∀ l : List (ℕ × Option ℕ), (∀ x ∈ l, 1 ≤ x.1) → l.length ≤ (l.map Prod.fst).sum := by
    intro l hl
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have h1 := hl x List.mem_cons_self
      have h2 := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      omega
  exact (key ch h.pos).trans h.sum_le

/-- A larger factor. -/
theorem ChildList.mono_factor {wl c c' : ℕ} {P : ℕ × Option ℕ → Prop} {ch : List (ℕ × Option ℕ)}
    (h : ChildList wl c P ch) (hc : c ≤ c') : ChildList wl c' P ch :=
  ⟨h.sum_le.trans (Nat.mul_le_mul_right _ hc), h.pred, h.pos⟩

/-- **The size facts are closed under the recursion**: if the parent has at most `nB` string
positions and degree at most `NB` with `2 nB ≤ NB`, and the step's bound `sC` is at most `sG`,
then the child has at most `nB` string positions, degree at most `NB` and at most `sG`
generators. -/
theorem SizeChild.closed {sC sG nB NB : ℕ} {I J : HInstData D} (h : SizeChild sC I J)
    (hn : I.n ≤ nB) (hN : I.inst.degree ≤ NB) (h2 : 2 * nB ≤ NB) (hs : sC ≤ sG) :
    J.n ≤ nB ∧ J.inst.degree ≤ NB ∧ J.inst.2.2.2.gens.length ≤ sG :=
  ⟨h.n_le.trans hn, h.degree_le.trans (max_le hN (by omega)), h.gens_le.trans hs⟩

/-- **A hinted window has a point**: its labels are not constant (`HintValid.nonconst`). -/
theorem HInstValid.win_pos {DV : ℕ → GensData → D.denote → Prop} {I : HInstData D}
    {L : LabelData} (h : HInstValid DV I) (hL : I.lab = some L) : 1 ≤ I.winSize := by
  obtain ⟨i, hi, -⟩ := (h.hint L hL).1.nonconst
  exact List.length_pos_of_mem hi

/-- An element of a list of numbers is at most their maximum. -/
theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- **The largest of `f 0, …, f k`**, for generator bounds indexed by the degree. -/
def supTo (f : ℕ → ℕ) (k : ℕ) : ℕ := ((List.range (k + 1)).map f).foldr max 0

theorem le_supTo {f : ℕ → ℕ} {k M : ℕ} (h : M ≤ k) : f M ≤ supTo f k :=
  le_foldr_max (List.mem_map.2 ⟨M, List.mem_range.2 (by omega), rfl⟩)

/-- A larger generator bound. -/
theorem SizeChild.mono {sC sC' : ℕ} {I J : HInstData D} (h : SizeChild sC I J) (hs : sC ≤ sC') :
    SizeChild sC' I J :=
  ⟨h.n₀, h.n_le, h.degree_le, h.gens_le.trans hs, h.lab⟩

/-- **The label invariant is closed under the recursion**: a child of a parent with `LabInv`
has `LabInv`. -/
theorem SizeChild.lab_closed {sC : ℕ} {I J : HInstData D} (h : SizeChild sC I J)
    (hI : LabInv I) : LabInv J :=
  h.lab hI

/-! ### The children's predicates decrease the measure -/

theorem StepChild.measLt {n m : ℕ} {x : ℕ × Option ℕ} (h : StepChild n m x) (hn : 1 ≤ n)
    (hm : 1 ≤ m) : MeasLt (x.1, x.2.getD (2 * x.1 + 1)) (n, m) := by
  obtain ⟨hx, ⟨m', he, hm'⟩ | ⟨he, h2⟩⟩ := h
  · rw [he]
    simp only [MeasLt, Option.getD_some]
    omega
  · simp only [MeasLt]
    omega

theorem FreeChild.measLt {n m : ℕ} {x : ℕ × Option ℕ} (h : FreeChild n m x) (hn : 1 ≤ n) :
    MeasLt (x.1, x.2.getD (2 * x.1 + 1)) (n, m) := by
  obtain ⟨hx, ⟨m', he, hm', hlt⟩ | ⟨he, h2⟩⟩ := h
  · rw [he]
    simp only [MeasLt, Option.getD_some]
    omega
  · simp only [MeasLt]
    omega

theorem ChainChild.measLt {n m : ℕ} {x : ℕ × Option ℕ} (h : ChainChild n x) :
    MeasLt (x.1, x.2.getD (2 * x.1 + 1)) (n, m) := Or.inl h.2

end GraphIso.Main
