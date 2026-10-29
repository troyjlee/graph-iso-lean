module

public import GraphIso.Toolkit.Base
public import GraphIso.Recursion.Primitive
public import GraphIso.Solver.Cost
public import GraphIso.Programs.Window

/-!
# The degree of transitivity of the base action

`PLAN-14.md` §6 item 4. The base action `ψ(G)` of a group of degree `N` on its base positions
`[n, N)` is tested by iterated pointwise stabilizers: after `j` rounds the group is the
pointwise stabilizer of the first `j` base points, and the round continues if it is transitive
on the remaining base points.

* `StabTrans P i`: the pointwise stabilizer of the first `i` points of `Fin m` is transitive on
  the rest. `isMultiplyPretransitive_of_stabTrans` and `stabTrans_of_isMultiplyPretransitive`
  relate it to `IsMultiplyPretransitive`.
* `degreeProg n cap G` computes `degreeModel`, which is `min(cap, d)` for the degree of
  transitivity `d` of the base action (`RunsWithin.degreeProg`). Each round builds the window
  of the remaining base points and calls `orbits`, and on a single orbit `stabilizer`.
* `giantProg n G` decides `Alt(base) ≤ ψ(G)` through `alt_le_iff`, with `cap = m - 2`.
-/

@[expose] public section

namespace GraphIso.Toolkit

open Equiv MulAction Cost Programs GraphIso.Solver

/-! ### Transitivity through pointwise stabilizers -/

section Math

variable {m : ℕ}

/-- The pointwise stabilizer of the first `i` points of `Fin m` acts transitively on the
others. -/
def StabTrans (P : Subgroup (Perm (Fin m))) (i : ℕ) : Prop :=
  ∀ γ δ : Fin m, i ≤ γ.val → i ≤ δ.val → ∃ p ∈ P, (∀ j : Fin m, j.val < i → p j = j) ∧ p γ = δ

/-- The first `r` points as an embedding. -/
def firstEmb {r : ℕ} (hr : r ≤ m) : Fin r ↪ Fin m := Fin.castLEEmb hr

/-- Every injective `r`-tuple is moved onto the first `r` points. -/
theorem exists_smul_firstEmb (P : Subgroup (Perm (Fin m))) {r : ℕ} (hr : r ≤ m)
    (h : ∀ i < r, StabTrans P i) (x : Fin r ↪ Fin m) :
    ∃ p ∈ P, ∀ i : Fin r, p (x i) = firstEmb hr i := by
  suffices H : ∀ k ≤ r, ∃ p ∈ P, ∀ i : Fin r, i.val < k → p (x i) = firstEmb hr i by
    obtain ⟨p, hp, hpx⟩ := H r le_rfl
    exact ⟨p, hp, fun i => hpx i i.2⟩
  intro k hk
  induction k with
  | zero => exact ⟨1, P.one_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    obtain ⟨p, hp, hpx⟩ := ih (by omega)
    set γ := p (x ⟨k, by omega⟩) with hγ
    have hkγ : k ≤ γ.val := by
      by_contra hlt
      have hlt : γ.val < k := Nat.lt_of_not_le hlt
      have hlt' : γ.val < r := by omega
      have e := hpx ⟨γ.val, hlt'⟩ hlt
      have : p (x ⟨k, by omega⟩) = p (x ⟨γ.val, hlt'⟩) := by
        rw [← hγ, e]
        ext
        simp [firstEmb]
      have := x.injective (p.injective this)
      simp only [Fin.mk.injEq] at this
      omega
    obtain ⟨q, hq, hqfix, hqγ⟩ := h k (by omega) γ (firstEmb hr ⟨k, by omega⟩) hkγ
      (by simp [firstEmb])
    refine ⟨q * p, P.mul_mem hq hp, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
    · rw [Perm.mul_apply, hpx i hi]
      exact hqfix _ (by simp [firstEmb, hi])
    · have hi' : i = ⟨k, by omega⟩ := Fin.ext hi
      rw [hi', Perm.mul_apply, ← hγ, hqγ]

/-- **Transitivity from pointwise stabilizers**: if for each `i < r` the pointwise stabilizer
of the first `i` points is transitive on the others, then `P` is `r`-transitive. -/
theorem isMultiplyPretransitive_of_stabTrans (P : Subgroup (Perm (Fin m))) {r : ℕ}
    (hr : r ≤ m) (h : ∀ i < r, StabTrans P i) : IsMultiplyPretransitive P (Fin m) r := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨p, hp, hpx⟩ := exists_smul_firstEmb P hr h x
  obtain ⟨q, hq, hqy⟩ := exists_smul_firstEmb P hr h y
  refine ⟨⟨q⁻¹ * p, P.mul_mem (P.inv_mem hq) hp⟩, Function.Embedding.ext fun i => ?_⟩
  change (q⁻¹ * p) (x i) = y i
  rw [Perm.mul_apply, hpx i, ← hqy i]
  simp

/-- The tuple of the first `r` points followed by `γ`. -/
def snocTuple {r : ℕ} (γ : Fin m) (hγ : r ≤ γ.val) : Fin (r + 1) ↪ Fin m where
  toFun i := if h : i.val < r then ⟨i.val, by omega⟩ else γ
  inj' i j hij := by
    simp only at hij
    split_ifs at hij with hi hj hj
    · exact Fin.ext (by simpa using congrArg Fin.val hij)
    · have := congrArg Fin.val hij
      simp only at this
      omega
    · have := congrArg Fin.val hij
      simp only at this
      omega
    · exact Fin.ext (by omega)

theorem snocTuple_apply {r : ℕ} (γ : Fin m) (hγ : r ≤ γ.val) (i : Fin (r + 1)) :
    snocTuple γ hγ i = if h : i.val < r then ⟨i.val, by omega⟩ else γ := rfl

/-- **Pointwise stabilizers from transitivity**: an `(r + 1)`-transitive group has a pointwise
stabilizer of the first `r` points transitive on the others. -/
theorem stabTrans_of_isMultiplyPretransitive (P : Subgroup (Perm (Fin m))) {r : ℕ}
    (h : IsMultiplyPretransitive P (Fin m) (r + 1)) : StabTrans P r := by
  intro γ δ hγ hδ
  obtain ⟨⟨p, hp⟩, hpx⟩ := h.exists_smul_eq (snocTuple γ hγ) (snocTuple δ hδ)
  have happ : ∀ i : Fin (r + 1), p (snocTuple γ hγ i) = snocTuple δ hδ i := fun i =>
    congrArg (fun e : Fin (r + 1) ↪ Fin m => e i) hpx
  refine ⟨p, hp, fun j hj => ?_, ?_⟩
  · have := happ ⟨j.val, by omega⟩
    rw [snocTuple_apply, snocTuple_apply] at this
    simpa [hj] using this
  · have := happ (Fin.last r)
    rw [snocTuple_apply, snocTuple_apply] at this
    simpa using this

end Math

/-! ### The base positions and pointwise stabilizers -/

section Base

variable {N : ℕ}

/-- The pointwise stabilizer of the base positions `[n, n + j)`. -/
def fixFirst (G : Subgroup (Perm (Fin N))) (n j : ℕ) : Subgroup (Perm (Fin N)) :=
  pointwiseStab G {u | n ≤ u.val ∧ u.val < n + j}

theorem fixFirst_zero (G : Subgroup (Perm (Fin N))) (n : ℕ) : fixFirst G n 0 = G := by
  ext g
  simp only [fixFirst, pointwiseStab, Subgroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun u hu => by omega⟩

theorem fixFirst_le (G : Subgroup (Perm (Fin N))) (n j : ℕ) : fixFirst G n j ≤ G :=
  fun _ h => h.1

/-- One more stabilized point. -/
theorem pointStab_fixFirst (G : Subgroup (Perm (Fin N))) (n j : ℕ) (h : n + j < N) :
    pointStab (fixFirst G n j) ⟨n + j, h⟩ = fixFirst G n (j + 1) := by
  ext g
  rw [mem_pointStab]
  simp only [fixFirst, pointwiseStab, Subgroup.mem_mk, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hg, hfix⟩, hgj⟩
    refine ⟨hg, fun u hu => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show u.val < n + j + 1 by omega) with hlt | heq
    · exact hfix u ⟨hu.1, hlt⟩
    · have : u = ⟨n + j, h⟩ := Fin.ext heq
      rw [this, hgj]
  · rintro ⟨hg, hfix⟩
    exact ⟨⟨hg, fun u hu => hfix u ⟨hu.1, by omega⟩⟩, hfix _ ⟨by simp, by simp⟩⟩

/-- The positions `[n + j, N)` are invariant under the pointwise stabilizer of `[n, n + j)` of a
group preserving the base. -/
theorem isInvariant_basePts {G : Subgroup (Perm (Fin N))} {n : ℕ}
    (hinv : IsInvariant G (baseSet n N)) (j : ℕ) :
    IsInvariant (fixFirst G n j) ((WinData.ofPoints N (basePts (n + j) N)).denote N) := by
  intro g hg u hu
  simp only [WinData.denote_ofPoints, Set.mem_ofPred_eq, mem_basePts] at hu ⊢
  refine ⟨?_, (g u).2⟩
  have hbase : n ≤ (g u).val := hinv g hg.1 u (show n ≤ u.val by omega)
  by_contra hlt
  have hfix := hg.2 (g u) ⟨hbase, by omega⟩
  have : g u = u := g.injective hfix
  rw [this] at hlt
  omega

/-- Transitivity of `fixFirst` on the remaining base positions is `StabTrans` of the base
action. -/
theorem sameOrbit_iff_stabTrans {G : Subgroup (Perm (Fin N))} {n : ℕ}
    (hinv : IsInvariant G (baseSet n N)) (j : ℕ) :
    (∀ a ∈ basePts (n + j) N, ∀ b ∈ basePts (n + j) N, SameOrbit (fixFirst G n j) a b) ↔
      StabTrans (baseHom G n hinv).range j := by
  constructor
  · intro h γ δ hγ hδ
    obtain ⟨_, _, g, hg, hgab⟩ := h (n + γ.val) (mem_basePts.2 ⟨by omega, by omega⟩)
      (n + δ.val) (mem_basePts.2 ⟨by omega, by omega⟩)
    refine ⟨baseHom G n hinv ⟨g, hg.1⟩, ⟨_, rfl⟩, fun j' hj' => ?_, ?_⟩
    · apply Fin.ext
      have e := baseHom_apply (hG := hinv) ⟨g, hg.1⟩ j'
      have hfix := hg.2 (basePos j') ⟨by simp [basePos], by simp [basePos]; omega⟩
      rw [hfix] at e
      have := congrArg Fin.val e
      simp only [basePos] at this
      omega
    · apply Fin.ext
      have e := baseHom_apply (hG := hinv) ⟨g, hg.1⟩ γ
      have hγp : basePos (n := n) (N := N) γ = ⟨n + γ.val, by omega⟩ := rfl
      rw [hγp, hgab] at e
      have := congrArg Fin.val e
      simp only [basePos] at this
      omega
  · intro h a ha b hb
    rw [mem_basePts] at ha hb
    obtain ⟨p, ⟨g, rfl⟩, hpfix, hpab⟩ :=
      h ⟨a - n, by omega⟩ ⟨b - n, by omega⟩ (by simp; omega) (by simp; omega)
    refine ⟨by omega, by omega, g.1, ⟨g.2, fun u hu => ?_⟩, ?_⟩
    · have hu' : n ≤ u.val ∧ u.val < n + j := hu
      have e := baseHom_apply (hG := hinv) g ⟨u.val - n, by omega⟩
      rw [hpfix _ (by simp; omega)] at e
      have hu' : basePos (n := n) (N := N) ⟨u.val - n, by omega⟩ = u := by
        ext
        simp only [basePos]
        omega
      rw [hu'] at e
      exact e.symm
    · have e := baseHom_apply (hG := hinv) g ⟨a - n, by omega⟩
      rw [hpab] at e
      have ha' : basePos (n := n) (N := N) ⟨a - n, by omega⟩ = ⟨a, by omega⟩ := by
        ext
        simp only [basePos]
        omega
      have hb' : basePos (n := n) (N := N) ⟨b - n, by omega⟩ = ⟨b, by omega⟩ := by
        ext
        simp only [basePos]
        omega
      rw [ha', hb'] at e
      exact e.symm

end Base

/-! ### The degree program -/

/-- States of the degree loop: completed rounds, the stop flag, the current group. -/
abbrev dstate (D : Ty) : Ty := .prod .nat (.prod .bool (Ty.group D))

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The positions `a, a + 1, …, a + k - 1`. -/
def rangeFromProg (a k : var .nat) : Prog S rec var (.list .nat) :=
  .bind (.op1 .range k) fun is => mapList is fun i => .op2 .add a i

/-- Whether a list has exactly one element. -/
def singletonProg {a' : Ty} (os : var (.list a')) : Prog S rec var .bool :=
  .caseList os (.op0 (.boolLit false)) fun _ rest =>
    .caseList rest (.op0 (.boolLit true)) fun _ _ => .op0 (.boolLit false)

/-- Stabilize the next base position `b` and count the round. -/
def stabStepProg (cnt b : var .nat) (H : var (Ty.group D)) :
    Prog (groupSig D) rec var (dstate D) :=
  .bind (.op2 .pair H b) fun Hb =>
  .bind (Prog.call (S := groupSig D) GroupOp.stabilizer Hb) fun H' =>
  .bind (.op0 (.natLit 1)) fun o => .bind (.op2 .add cnt o) fun cnt' =>
  .bind (.op0 (.boolLit false)) fun f => .bind (.op2 .pair f H') fun r' => .op2 .pair cnt' r'

/-- Stop with the current count. -/
def stopProg (cnt : var .nat) (H : var (Ty.group D)) : Prog (groupSig D) rec var (dstate D) :=
  .bind (.op0 (.boolLit true)) fun t => .bind (.op2 .pair t H) fun r' => .op2 .pair cnt r'

/-- One round from `cnt` completed rounds: if `H` is transitive on the remaining base positions,
stabilize the next one; otherwise stop. -/
def roundProg (n cnt : var .nat) (H : var (Ty.group D)) : Prog (groupSig D) rec var (dstate D) :=
  .bind (.op1 .fst H) fun N => .bind (.op2 .add n cnt) fun b =>
  .bind (.op2 .sub N b) fun k => .bind (rangeFromProg b k) fun rem =>
  .bind (mkWindow N rem) fun w => .bind (.op2 .pair H w) fun Hw =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits Hw) fun os =>
  .bind (singletonProg os) fun one =>
  .ite one (stabStepProg cnt b H) (stopProg cnt H)

/-- One step of the loop: nothing once stopped, otherwise a round. -/
def degBody (n : var .nat) (st : var (dstate D)) : Prog (groupSig D) rec var (dstate D) :=
  .bind (.op1 .snd st) fun rest => .bind (.op1 .fst rest) fun done =>
  .ite done (.ret st)
    (.bind (.op1 .fst st) fun cnt => .bind (.op1 .snd rest) fun H => roundProg n cnt H)

/-- The degree of transitivity of the base action, capped at `cap`. -/
def degreeProg (n cap : var .nat) (G : var (Ty.group D)) : Prog (groupSig D) rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.boolLit false)) fun f =>
  .bind (.op2 .pair f G) fun r₀ => .bind (.op2 .pair z r₀) fun st₀ =>
  .bind (.op1 .range cap) fun is =>
  .bind (.foldList is st₀ fun st _ => degBody n st) fun fin => .op1 .fst fin

/-- The giant test: is the base action `(m - 2)`-transitive? -/
def giantProg (n : var .nat) (G : var (Ty.group D)) : Prog (groupSig D) rec var .bool :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .sub m two) fun cap =>
  .bind (degreeProg n cap G) fun r => .op2 .natEq r cap

end Programs

/-! ### Models -/

section Models

variable {D : Ty}

/-- Whether a list has exactly one element. -/
def isSingle {α : Type} : List α → Bool
  | [_] => true
  | _ => false

/-- One round of the degree loop, with the backend's results. -/
def degStep (O : Oracle (groupSig D)) (n : ℕ) (st : ℕ × Bool × GroupData D.denote) :
    ℕ × Bool × GroupData D.denote :=
  if st.2.1 then st
  else if isSingle (O.run .orbits (st.2.2, WinData.ofPoints st.2.2.1 (basePts (n + st.1) st.2.2.1)))
    then (st.1 + 1, false, O.run .stabilizer (st.2.2, n + st.1))
    else (st.1, true, st.2.2)

/-- The model of `degreeProg`. -/
def degreeModel (O : Oracle (groupSig D)) (n cap : ℕ) (G : GroupData D.denote) : ℕ :=
  ((List.range cap).foldl (fun st _ => degStep O n st) (0, false, G)).1

/-- The model of `giantProg`. -/
def giantModel (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : Bool :=
  degreeModel O n (G.1 - n - 2) G == G.1 - n - 2

end Models

/-! ### Costs -/

/-- The cost of one round at degree `N`, with the `orbits` and `stabilizer` charges. -/
def degRound (N Borb Bstab : ℕ) : ℕ := 12 * N + Borb + Bstab + 40

/-- The cost of `degreeProg` with `cap` rounds. -/
def degreeCost (N cap Borb Bstab : ℕ) : ℕ := cap * (degRound N Borb Bstab + 1) + cap + 7

/-- The operations the degree program calls. -/
def degreeOps (op : GroupOp) : Prop := op = .orbits ∨ op = .stabilizer

/-! ### Specs of the helpers -/

section HelperSpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.rangeFromProg (b k : ℕ) :
    RunsWithin X body (Toolkit.rangeFromProg b k) ((List.range k).map (b + ·)) (5 * k + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.mapList_le (c := 1) fun i _ => RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range]
    omega

theorem RunsWithin.singletonProg {a' : Ty} (os : List a'.denote) :
    RunsWithin X body (Toolkit.singletonProg os) (isSingle os) 3 := by
  rcases os with _ | ⟨o, _ | ⟨o', rest⟩⟩
  · exact (RunsWithin.caseList_nil (RunsWithin.prim _ _)).mono (by simp [Prim.cost])
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_nil (RunsWithin.prim _ _))).mono
      (by simp [Prim.cost])
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_cons (RunsWithin.prim _ _))).mono
      (by simp [Prim.cost])

end HelperSpecs

/-! ### The loop invariant and the meaning of a round -/

section Rounds

variable {D : Ty} {DV : ℕ → GensData → D.denote → Prop} {N s n : ℕ}

/-- The invariant of the degree loop: the current group, valid with at most `s` generators, is
the pointwise stabilizer of the first `j` base positions. -/
structure DegInv (DV : ℕ → GensData → D.denote → Prop) (N s : ℕ) (G : Subgroup (Perm (Fin N)))
    (n : ℕ) (st : ℕ × Bool × GroupData D.denote) : Prop where
  deg : st.2.2.1 = N
  valid : GroupValid DV N st.2.2.2.1 st.2.2.2.2
  gens : st.2.2.2.1.length ≤ s
  den : GensData.denote N st.2.2.2.1 = fixFirst G n st.1
  le : n + st.1 ≤ N

/-- The first `j` base positions are stabilized transitively on the rest. -/
def TransAt (G : Subgroup (Perm (Fin N))) (n j : ℕ) : Prop :=
  ∀ a ∈ basePts (n + j) N, ∀ b ∈ basePts (n + j) N, SameOrbit (fixFirst G n j) a b

/-- A single orbit means transitivity. -/
theorem transAt_of_single {G : Subgroup (Perm (Fin N))} {n j : ℕ} {H : Subgroup (Perm (Fin N))}
    (hH : H = fixFirst G n j) {os : List (List ℕ)}
    (hos : IsOrbitPartition H (WinData.ofPoints N (basePts (n + j) N)) os)
    (h : isSingle os = true) : TransAt G n j := by
  subst hH
  rcases os with _ | ⟨o, _ | ⟨o', rest⟩⟩
  · simp [isSingle] at h
  · intro a ha b hb
    have hperm : o.Perm (basePts (n + j) N) := by simpa using hos.1
    have ha' : a ∈ o := hperm.mem_iff.2 ha
    have hb' : b ∈ o := hperm.mem_iff.2 hb
    exact ((hos.2 o List.mem_cons_self).2 a ha' b).1 hb'
  · simp [isSingle] at h

/-- No single orbit means intransitivity, or no remaining position. -/
theorem not_transAt_of_not_single {G : Subgroup (Perm (Fin N))} {n j : ℕ}
    {H : Subgroup (Perm (Fin N))} (hH : H = fixFirst G n j) (hle : n + j ≤ N)
    {os : List (List ℕ)} (hos : IsOrbitPartition H (WinData.ofPoints N (basePts (n + j) N)) os)
    (h : isSingle os = false) : ¬ TransAt G n j ∨ n + j = N := by
  subst hH
  rcases os with _ | ⟨o, _ | ⟨o', rest⟩⟩
  · right
    have hperm := hos.1
    simp only [List.flatten_nil, WinData.ofPoints_fst] at hperm
    have := hperm.length_eq
    rw [length_basePts] at this
    simp only [List.length_nil] at this
    omega
  · simp [isSingle] at h
  · left
    intro htr
    obtain ⟨hne, hoo⟩ := hos.2 o List.mem_cons_self
    obtain ⟨hne', -⟩ := hos.2 o' (by simp)
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil o hne
    obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil o' hne'
    have hperm := hos.1
    simp only [WinData.ofPoints_fst] at hperm
    have hmem : ∀ x, x ∈ (o :: o' :: rest).flatten → x ∈ basePts (n + j) N :=
      fun x hx => hperm.mem_iff.1 hx
    have ha' := hmem a (List.mem_flatten.2 ⟨o, List.mem_cons_self, ha⟩)
    have hb' := hmem b (List.mem_flatten.2 ⟨o', by simp, hb⟩)
    have hbo : b ∈ o := ((hoo a ha b).2 (htr a ha' b hb'))
    have hnd : (o :: o' :: rest).flatten.Nodup := hperm.nodup_iff.2 (basePts_nodup _ _)
    rw [List.nodup_flatten] at hnd
    have hdisj := (List.pairwise_cons.1 hnd.2).1 o' (by simp)
    exact List.disjoint_left.1 hdisj hbo hb

end Rounds

/-! ### Specs of the round -/

section RoundSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}

theorem RunsWithin.stopProg (cnt : ℕ) (H : GroupData D.denote) :
    RunsWithin X body (Toolkit.stopProg cnt H) (cnt, true, H) 3 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc => simp [Prim.cost]

theorem RunsWithin.stabStepProg (cnt b : ℕ) (H : GroupData D.denote)
    (hP : X.Pre GroupOp.stabilizer (H, b)) :
    RunsWithin X body (Toolkit.stabStepProg cnt b H)
      (cnt + 1, false, X.O.run GroupOp.stabilizer (H, b))
      (X.B.call GroupOp.stabilizer (H, b) (X.O.run GroupOp.stabilizer (H, b)) + 6) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call hP)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval]
    omega

/-- **One round**, given the preconditions of its calls. -/
theorem RunsWithin.roundProg {n cnt N : ℕ} {gs : GensData} {d : D.denote}
    (hPo : X.Pre GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + cnt) N)))
    (hPs : isSingle (X.O.run GroupOp.orbits ((N, gs, d),
      WinData.ofPoints N (basePts (n + cnt) N))) = true →
        X.Pre GroupOp.stabilizer ((N, gs, d), n + cnt)) {Cs : ℕ}
    (hCs : isSingle (X.O.run GroupOp.orbits ((N, gs, d),
      WinData.ofPoints N (basePts (n + cnt) N))) = true →
        X.B.call GroupOp.stabilizer ((N, gs, d), n + cnt)
          (X.O.run GroupOp.stabilizer ((N, gs, d), n + cnt)) ≤ Cs) :
    RunsWithin X body (Toolkit.roundProg n cnt (N, gs, d)) (degStep X.O n (cnt, false, (N, gs, d)))
      (12 * N + X.B.call GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + cnt) N))
          (X.O.run GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + cnt) N))) +
        Cs + 30) := by
  have hrem := RunsWithin.rangeFromProg (X := X) (body := body) (n + cnt) (N - (n + cnt))
  have hw := RunsWithin.mkWindow (X := X) (body := body) N (basePts (n + cnt) N)
  have hlen : (basePts (n + cnt) N).length ≤ N := by rw [length_basePts]; omega
  generalize hos : X.O.run GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + cnt) N))
    = os at hPs hCs
  have hsingle := RunsWithin.singletonProg (X := X) (body := body) os
  have hlen' := length_basePts (n + cnt) N
  cases hs : isSingle os
  · have hstop := RunsWithin.stopProg (X := X) (body := body) cnt (N, gs, d)
    have hval : degStep X.O n (cnt, false, (N, gs, d)) = (cnt, true, (N, gs, d)) := by
      simp [degStep, hos, hs]
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrem
      run_step hw
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call hPo)
      simp only [Prim.eval]
      rw [hos]
      run_step hsingle
      rw [hs]
      exact RunsWithin.ite_false hstop
    case hc =>
      simp only [Prim.cost, Prim.eval, hos]
      omega
  · have hstab := RunsWithin.stabStepProg (X := X) (body := body) cnt (n + cnt) (N, gs, d)
      (hPs hs)
    have hval : degStep X.O n (cnt, false, (N, gs, d)) =
        (cnt + 1, false, X.O.run GroupOp.stabilizer ((N, gs, d), n + cnt)) := by
      simp only [degStep, hos, hs, Bool.false_eq_true, ↓reduceIte]
      rfl
    rw [hval]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hrem
      run_step hw
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call hPo)
      simp only [Prim.eval]
      rw [hos]
      run_step hsingle
      rw [hs]
      exact RunsWithin.ite_true hstab
    case hc =>
      have := hCs hs
      simp only [Prim.cost, Prim.eval, hos]
      omega

end RoundSpecs

/-! ### The loop -/

section LoopSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The preconditions and results of the backend calls of a round, under the invariant. -/
theorem degRound_facts (hO : MeetsContractOn DV degreeOps X.O) {N s n : ℕ}
    {G₀ G : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hGG₀ : G ≤ G₀)
    (hinv : IsInvariant G (baseSet n N)) {j : ℕ} {gs : GensData} {d : D.denote}
    (hst : DegInv DV N s G n (j, false, (N, gs, d))) :
    GroupPre DV GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + j) N)) ∧
      IsOrbitPartition (fixFirst G n j) (WinData.ofPoints N (basePts (n + j) N))
        (X.O.run GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + j) N))) ∧
      X.B.call GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + j) N))
        (X.O.run GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + j) N))) ≤ B.Borb ∧
      (isSingle (X.O.run GroupOp.orbits ((N, gs, d),
        WinData.ofPoints N (basePts (n + j) N))) = true →
        GroupPre DV GroupOp.stabilizer ((N, gs, d), n + j) ∧
        X.B.call GroupOp.stabilizer ((N, gs, d), n + j)
          (X.O.run GroupOp.stabilizer ((N, gs, d), n + j)) ≤ B.Bstab ∧
        DegInv DV N s G n (j + 1, false, X.O.run GroupOp.stabilizer ((N, gs, d), n + j))) := by
  have hval : GroupValid DV N gs d := hst.valid
  have hgs : gs.length ≤ s := hst.gens
  have hden : GensData.denote N gs = fixFirst G n j := hst.den
  have hle : n + j ≤ N := hst.le
  have hG₀ : GensData.denote N gs ≤ G₀ := hden ▸ (fixFirst_le G n j).trans hGG₀
  have hpre : GroupPre DV GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + j) N)) :=
    ⟨hval, WinData.valid_ofPoints (basePts_nodup _ _) (fun i hi => (mem_basePts.1 hi).2),
      by rw [hden]; exact isInvariant_basePts hinv j⟩
  have hpost := hO GroupOp.orbits _ (Or.inl rfl) hpre
  change IsOrbitPartition (GensData.denote N gs) _ _ at hpost
  rw [hden] at hpost
  refine ⟨hpre, hpost, B.orbits gs d _ hgs hG₀ hpre, fun hsing => ?_⟩
  have hlt : n + j < N := by
    by_contra hge
    have hnil : basePts (n + j) N = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [length_basePts]
      omega
    revert hsing hpost
    generalize X.O.run GroupOp.orbits ((N, gs, d), WinData.ofPoints N (basePts (n + j) N)) = os
    intro hpost hsing
    rcases os with _ | ⟨o, _ | ⟨o', rest⟩⟩
    · simp [isSingle] at hsing
    · have hp := hpost.1
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil, WinData.ofPoints_fst,
        hnil] at hp
      exact (hpost.2 o List.mem_cons_self).1 (List.Perm.eq_nil hp)
    · simp [isSingle] at hsing
  have hspre : GroupPre DV GroupOp.stabilizer ((N, gs, d), n + j) := ⟨hval, hlt⟩
  refine ⟨hspre, B.stabilizer gs d _ hgs hG₀ hspre, ?_⟩
  have hspost := hO GroupOp.stabilizer _ (Or.inr rfl) hspre
  have hout := B.stabOut gs d (n + j) hG₀ hspre
  rcases hres : X.O.run GroupOp.stabilizer ((N, gs, d), n + j) with ⟨n', ks, e⟩
  rw [hres] at hspost hout
  obtain ⟨hn', hkv, hkden⟩ := hspost
  refine ⟨hn', hkv, hout, ?_, by simp; omega⟩
  change GensData.denote N ks = fixFirst G n (j + 1)
  rw [hkden hlt, hden, pointStab_fixFirst]

/-- **A step of the loop** keeps the invariant. -/
theorem RunsWithin.degBody (hO : MeetsContractOn DV degreeOps X.O)
    (hPre : ∀ op x, degreeOps op → GroupPre DV op x → X.Pre op x)
    {N s n : ℕ} {G₀ G : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    (hGG₀ : G ≤ G₀) (hinv : IsInvariant G (baseSet n N)) {st : ℕ × Bool × GroupData D.denote}
    (hst : DegInv DV N s G n st) :
    RunsWithin X body (Toolkit.degBody n st) (degStep X.O n st) (degRound N B.Borb B.Bstab) ∧
      DegInv DV N s G n (degStep X.O n st) := by
  rcases st with ⟨j, done, N', gs, d⟩
  cases done
  · have hdeg : N' = N := hst.deg
    subst hdeg
    obtain ⟨hpre, -, hcorb, hsing⟩ := degRound_facts hO B hGG₀ hinv hst
    have hround := RunsWithin.roundProg (X := X) (body := body) (n := n) (cnt := j)
      (N := N') (gs := gs) (d := d) (hPre _ _ (Or.inl rfl) hpre)
      (fun h => hPre _ _ (Or.inr rfl) (hsing h).1) (Cs := B.Bstab) (fun h => (hsing h).2.1)
    refine ⟨?_, ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        apply RunsWithin.ite_false
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact hround
      case hc =>
        simp only [Prim.cost, degRound]
        omega
    · unfold degStep
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs with h
      · exact (hsing h).2.2
      · exact ⟨hst.deg, hst.valid, hst.gens, hst.den, hst.le⟩
  · refine ⟨?_, ?_⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        refine (RunsWithin.ite_true (RunsWithin.ret _)).of_eq ?_
        simp [degStep]
      case hc =>
        simp only [Prim.cost, degRound]
        omega
    · simpa [degStep] using hst

/-- The loop's meaning, after `k` steps. -/
theorem degFold (hO : MeetsContractOn DV degreeOps X.O) {N s n : ℕ}
    {G₀ G : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hGG₀ : G ≤ G₀)
    (hinv : IsInvariant G (baseSet n N)) {H : GroupData D.denote}
    (hH : DegInv DV N s G n (0, false, H)) (k : ℕ) :
    DegInv DV N s G n ((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)) ∧
      (((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).2.1 = false →
        ((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).1 = k) ∧
      (((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).2.1 = true →
        ((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).1 < k) ∧
      (∀ i < ((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).1,
        TransAt G n i) ∧
      (((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).2.1 = true →
        ¬ TransAt G n ((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).1 ∨
          n + ((List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H)).1 = N) := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil]
    exact ⟨hH, by simp, by simp, by simp, by simp⟩
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (fun st _ => degStep X.O n st) (0, false, H) = st at ih ⊢
    obtain ⟨hinvst, hnd, hd, htr, hstop⟩ := ih
    rcases st with ⟨j, done, N', gs, d⟩
    cases done
    · have hj : j = k := hnd rfl
      subst hj
      have hdeg : N' = N := hinvst.deg
      subst hdeg
      obtain ⟨-, hpart, -, hsing⟩ := degRound_facts hO B hGG₀ hinv hinvst
      unfold degStep
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs with h
      · refine ⟨(hsing h).2.2, fun _ => rfl, fun h' => by simp at h', fun i hi => ?_,
          fun h' => by simp at h'⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact htr i hi
        · subst hi
          exact transAt_of_single rfl hpart h
      · refine ⟨⟨hinvst.deg, hinvst.valid, hinvst.gens, hinvst.den, hinvst.le⟩,
          fun h' => by simp at h', fun _ => by simp, htr, fun _ => ?_⟩
        exact not_transAt_of_not_single rfl hinvst.le hpart (by simpa using h)
    · have hst : degStep X.O n (j, true, N', gs, d) = (j, true, N', gs, d) := by simp [degStep]
      rw [hst]
      exact ⟨hinvst, fun h => by simp at h, fun _ => by have := hd rfl; omega, htr, hstop⟩

end LoopSpecs

/-! ### The degree and the giant test -/

section Degree

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The cost of the degree program.** -/
theorem RunsWithin.degreeProg (hO : MeetsContractOn DV degreeOps X.O)
    (hPre : ∀ op x, degreeOps op → GroupPre DV op x → X.Pre op x)
    {N s n cap : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hG : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) :
    RunsWithin X body (Toolkit.degreeProg n cap (N, gs, d)) (degreeModel X.O n cap (N, gs, d))
      (degreeCost N cap B.Borb B.Bstab) := by
  have h0 : DegInv DV N s (GensData.denote N gs) n (0, false, (N, gs, d)) :=
    ⟨rfl, hG, hs, (fixFirst_zero _ n).symm, by simpa using hn⟩
  have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := .nat) (b' := dstate D)
    (f := fun st _ => Toolkit.degBody n st) (F := fun st _ => degStep X.O n st)
    (I := DegInv DV N s (GensData.denote N gs) n) (c := degRound N B.Borb B.Bstab)
    (List.range cap) (0, false, (N, gs, d))
    (fun st hst _ _ => RunsWithin.degBody hO hPre B hG₀ hinv hst) h0).1
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_range, degreeCost]
    omega

/-- **The meaning of the degree program**: its result `r ≤ cap` is a degree of transitivity of
the base action, and it is the degree of transitivity when `r < cap`. -/
theorem degreeModel_spec (hO : MeetsContractOn DV degreeOps X.O) {N s n cap : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) {gs : GensData}
    {d : D.denote} (hG : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) (hcap : cap ≤ N - n) :
    degreeModel X.O n cap (N, gs, d) ≤ cap ∧
      IsMultiplyPretransitive (baseHom (GensData.denote N gs) n hinv).range (Fin (N - n))
        (degreeModel X.O n cap (N, gs, d)) ∧
      (degreeModel X.O n cap (N, gs, d) < cap →
        ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n hinv).range (Fin (N - n))
          (degreeModel X.O n cap (N, gs, d) + 1)) := by
  have h0 : DegInv DV N s (GensData.denote N gs) n (0, false, (N, gs, d)) :=
    ⟨rfl, hG, hs, (fixFirst_zero _ n).symm, by simpa using hn⟩
  obtain ⟨-, hnd, hd, htr, hstop⟩ := degFold hO B hG₀ hinv h0 cap
  unfold degreeModel
  generalize (List.range cap).foldl (fun st _ => degStep X.O n st) (0, false, (N, gs, d)) = st
    at hnd hd htr hstop ⊢
  have hle : st.1 ≤ cap := by
    cases h : st.2.1
    · exact (hnd h).le
    · exact (hd h).le
  refine ⟨hle, ?_, fun hlt => ?_⟩
  · exact isMultiplyPretransitive_of_stabTrans _ (by omega) fun i hi =>
      (sameOrbit_iff_stabTrans hinv i).1 (htr i hi)
  · have hdone : st.2.1 = true := by
      cases h : st.2.1
      · have := hnd h
        omega
      · rfl
    rcases hstop hdone with hnt | heq
    · intro hmt
      exact hnt ((sameOrbit_iff_stabTrans hinv _).2 (stabTrans_of_isMultiplyPretransitive _ hmt))
    · omega

/-- **The cost of the giant test.** -/
theorem RunsWithin.giantProg (hO : MeetsContractOn DV degreeOps X.O)
    (hPre : ∀ op x, degreeOps op → GroupPre DV op x → X.Pre op x)
    {N s n : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hG : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) :
    RunsWithin X body (Toolkit.giantProg n (N, gs, d)) (giantModel X.O n (N, gs, d))
      (degreeCost N (N - n - 2) B.Borb B.Bstab + 5) := by
  have hdeg := RunsWithin.degreeProg (X := X) (body := body) (cap := N - n - 2) hO hPre B hG hs
    hG₀ hinv hn
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hdeg
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost]
    omega

/-- **The giant test is exact**: it answers whether `Alt(base) ≤ ψ(G)`. -/
theorem giantModel_iff (hO : MeetsContractOn DV degreeOps X.O) {N s n : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) {gs : GensData}
    {d : D.denote} (hG : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) :
    giantModel X.O n (N, gs, d) = true ↔
      alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hinv).range := by
  obtain ⟨hle, hmt, hnot⟩ := degreeModel_spec (cap := N - n - 2) hO B hG hs hG₀ hinv hn
    (by omega)
  rw [GraphIso.Recursion.alt_le_iff, Fintype.card_fin]
  unfold giantModel
  simp only [beq_iff_eq]
  constructor
  · intro h
    rw [h] at hmt
    exact hmt
  · intro h
    by_contra hne
    have hlt : degreeModel X.O n (N - n - 2) (N, gs, d) < N - n - 2 := by
      change degreeModel X.O n (N - n - 2) (N, gs, d) ≠ N - n - 2 at hne
      omega
    apply hnot hlt
    exact MulAction.isMultiplyPretransitive_of_le (n := N - n - 2) (by omega)
      (by simp)

end Degree

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_degreeProg {n₁ c₁ : var₁ .nat} {n₂ c₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hc : ⟨.nat, c₁, c₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (degreeProg n₁ c₁ G₁) (degreeProg n₂ c₂ G₂) := by
  unfold degreeProg degBody roundProg stabStepProg stopProg rangeFromProg singletonProg mkWindow
    mapList
  prog_wf

theorem wf_giantProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (giantProg n₁ G₁) (giantProg n₂ G₂) := by
  unfold giantProg degreeProg degBody roundProg stabStepProg stopProg rangeFromProg
    singletonProg mkWindow mapList
  prog_wf

end Wf

end GraphIso.Toolkit
