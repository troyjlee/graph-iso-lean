module

public import GraphIso.Toolkit.Reduce
public import GraphIso.SoJProg.DLTest

/-!
# Tuple transporters

Stage 14e (`PLAN-14.md` §9 item 6): a generic tuple transporter through the backend. For a
group `H` (backend group data at degree `N`) and two lists of points `ps`, `qs` of equal
length, `tupleTransProg H ps qs` returns an element `h ∈ H` with `h ps[i] = qs[i]` for every
`i`, or `none` if there is none.

The program keeps an element `g ∈ H` mapping the points processed so far to their targets and
the pointwise stabilizer `K` of those points; the solutions so far form the coset `g K`. At
the point `p = ps[i]` with target `q = qs[i]`, the solutions are `g k` with `k ∈ K` and
`k p = g⁻¹ q`: if `g⁻¹ q` lies in the `K`-orbit of `p` (the backend's `orbitTransversal`), the
transversal element `r` with `r p = g⁻¹ q` gives `g r`, and `K` passes to the stabilizer of `p`
(the backend's `stabilizer`); otherwise there is no solution.

* `tupleTransProg`, `tupleTransModel`: the program and its value.
* `RunsWithin.tupleTransProg`: the value is `some h` with `h ∈ H` mapping `ps` to `qs` exactly
  when such an element exists, at cost `tupleTransCost`, with the backend charges bounded by
  `BackendBounds` (as for `iterStabProg` and `pointStabsProg`).
* `wf_tupleTransProg`.
-/

@[expose] public section

namespace GraphIso.CertProg

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Solver GraphIso.Toolkit

/-! ### The program -/

section Programs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The state: an element and the current group, or `none` once there is no solution. -/
abbrev ttState (D : Ty) : Ty := .option (.prod Ty.perm (Ty.group D))

/-- The transversal entry of the point `t`. -/
def ttFindProg (tr : var (.list (.prod .nat Ty.perm))) (t : var .nat) :
    Prog (groupSig D) rec var (.option (.prod .nat Ty.perm)) :=
  SoJProg.findProg tr fun vr => .bind (.op1 .fst vr) fun v => .op2 .natEq v t

/-- One step: the point `ps[i]` and its target `qs[i]`. -/
def ttStep (pa qa : var (.array .nat)) (st : var (ttState D)) (i : var .nat) :
    Prog (groupSig D) rec var (ttState D) :=
  .caseOption st (.op0 .none) fun gK =>
  .bind (.op1 .fst gK) fun g => .bind (.op1 .snd gK) fun K =>
  .bind (.op2 .arrayGet pa i) fun p => .bind (.op2 .arrayGet qa i) fun q =>
  .bind (.op1 .snd g) fun gi => .bind (.op2 .arrayGet gi q) fun t =>
  .bind (.op2 .pair K p) fun Kp =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbitTransversal Kp) fun tr =>
  .bind (ttFindProg tr t) fun f =>
  .caseOption f (.op0 .none) fun vr =>
  .bind (.op1 .snd vr) fun r =>
  .bind (Prog.call (S := groupSig D) GroupOp.stabilizer Kp) fun K' =>
  .bind (permMul g r) fun g' =>
  .bind (.op2 .pair g' K') fun gK' => .op1 .some gK'

/-- **The tuple transporter**: an element of `H` mapping `ps` to `qs` pointwise, if any. -/
def tupleTransProg (H : var (Ty.group D)) (ps qs : var (.list .nat)) :
    Prog (groupSig D) rec var (.option Ty.perm) :=
  .bind (.op1 .fst H) fun N => .bind (permOne N) fun e =>
  .bind (.op2 .pair e H) fun eH => .bind (.op1 .some eH) fun st₀ =>
  .bind (.op1 .arrayOfList ps) fun pa => .bind (.op1 .arrayOfList qs) fun qa =>
  .bind (.op1 .length ps) fun k => .bind (.op1 .range k) fun is =>
  .bind (.foldList is st₀ fun st i => ttStep pa qa st i) fun res =>
  .caseOption res (.op0 .none) fun gK => .bind (.op1 .fst gK) fun g => .op1 .some g

end Programs

/-! ### The value -/

section Model

variable {D : Ty}

/-- One step on data. -/
def ttStepD (O : Oracle (groupSig D)) (ps qs : List ℕ)
    (st : Option (PermData × GroupData D.denote)) (i : ℕ) :
    Option (PermData × GroupData D.denote) :=
  match st with
  | none => none
  | some (g, K) =>
    match (O.run GroupOp.orbitTransversal (K, ps.getD i 0)).find?
        (fun vr => vr.1 == get g.2 (qs.getD i 0)) with
    | none => none
    | some vr => some (g.mul vr.2, O.run GroupOp.stabilizer (K, ps.getD i 0))

/-- The value of `tupleTransProg`. -/
def tupleTransModel (O : Oracle (groupSig D)) (H : GroupData D.denote) (ps qs : List ℕ) :
    Option PermData :=
  ((List.range ps.length).foldl (ttStepD O ps qs) (some (PermData.one H.1, H))).map Prod.fst

/-- The cost of one step: degree `N`, transversal and stabilizer charges `Bt`, `Bs`. -/
def ttStepCost (N Bt Bs : ℕ) : ℕ := Bt + Bs + 18 * N + 40

/-- The cost of `tupleTransProg` on `k` points. -/
def tupleTransCost (N k Bt Bs : ℕ) : ℕ := 2 * N + 4 * k + k * (ttStepCost N Bt Bs + 1) + 20

end Model

/-! ### Correctness -/

section Spec

variable {N : ℕ}

/-- `h` maps the `j`-th point of `ps` to the `j`-th point of `qs`, for every `j < i`. -/
def MapsPrefix (h : Perm (Fin N)) (ps qs : List ℕ) (i : ℕ) : Prop :=
  ∀ j < i, ∀ hp : ps.getD j 0 < N, (h ⟨ps.getD j 0, hp⟩).val = qs.getD j 0

/-- The first `i` points of `ps`. -/
def prefixSet (N : ℕ) (ps : List ℕ) (i : ℕ) : Set (Fin N) := {v | ∃ j < i, v.val = ps.getD j 0}

theorem tt_mapsPrefix_mono {h : Perm (Fin N)} {ps qs : List ℕ} {i i' : ℕ} (hi : i' ≤ i)
    (hh : MapsPrefix h ps qs i) : MapsPrefix h ps qs i' :=
  fun j hj hp => hh j (lt_of_lt_of_le hj hi) hp

theorem tt_prefixSet_succ (ps : List ℕ) (i : ℕ) (hp : ps.getD i 0 < N) :
    prefixSet N ps (i + 1) = prefixSet N ps i ∪ {⟨ps.getD i 0, hp⟩} := by
  ext v
  simp only [prefixSet, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, hv⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact Or.inl ⟨j, hj, hv⟩
    · exact Or.inr (Fin.ext hv)
  · rintro (⟨j, hj, hv⟩ | rfl)
    · exact ⟨j, Nat.lt_succ_of_lt hj, hv⟩
    · exact ⟨i, Nat.lt_succ_self i, rfl⟩

theorem tt_pointwiseStab_succ (H : Subgroup (Perm (Fin N))) (ps : List ℕ) (i : ℕ)
    (hp : ps.getD i 0 < N) :
    pointwiseStab (pointwiseStab H (prefixSet N ps i)) {⟨ps.getD i 0, hp⟩} =
      pointwiseStab H (prefixSet N ps (i + 1)) := by
  ext g
  simp only [mem_pointwiseStab, tt_prefixSet_succ ps i hp, Set.mem_union,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨hg, h₁⟩, h₂⟩
    refine ⟨hg, fun u hu => ?_⟩
    rcases hu with hu | hu
    · exact h₁ u hu
    · exact h₂ u hu
  · rintro ⟨hg, h⟩
    exact ⟨⟨hg, fun u hu => h u (Or.inl hu)⟩, fun u hu => h u (Or.inr hu)⟩

end Spec

section Invariant

variable {D : Ty} (DV : ℕ → GensData → D.denote → Prop)

/-- The invariant after `i` points: either no element of `H` maps the first `i` points of
`ps` to those of `qs`, or the state holds such an element `g` and the pointwise stabilizer of
those points (so the solutions are `g K`). -/
def TTInv (N s : ℕ) (H : Subgroup (Perm (Fin N))) (ps qs : List ℕ) (i : ℕ) :
    Option (PermData × GroupData D.denote) → Prop
  | none => ¬ ∃ h ∈ H, MapsPrefix h ps qs i
  | some (g, (N', ks, e)) => N' = N ∧ GroupValid DV N ks e ∧ ks.length ≤ s ∧ g.Valid N ∧
      PermData.denote N g ∈ H ∧ MapsPrefix (PermData.denote N g) ps qs i ∧
      GensData.denote N ks = pointwiseStab H (prefixSet N ps i)

end Invariant

section Steps

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem tt_get_toArray (l : List ℕ) (i : ℕ) : get l.toArray i = l.getD i 0 := by
  simp [get, List.getD_eq_getElem?_getD]

/-- The transversal entry search. -/
theorem RunsWithin.ttFindProg (tr : List (ℕ × PermData)) (tg : ℕ) :
    RunsWithin X body (CertProg.ttFindProg tr tg) (tr.find? fun vr => vr.1 == tg)
      (tr.length * 6 + 1) := by
  unfold CertProg.ttFindProg
  exact SoJProg.RunsWithin.findProg (t := .prod .nat Ty.perm) tr
    (p := fun vr => .bind (.op1 .fst vr) fun v => .op2 .natEq v tg)
    (P := fun vr => vr.1 == tg) (c := 2) fun vr _ =>
      RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
        (by simp [Prim.cost])

/-- A transversal has at most `N` entries. -/
theorem tt_length_tr {n : ℕ} {G : Subgroup (Perm (Fin n))} {u : ℕ} {tr : List (ℕ × PermData)}
    (hnd : (tr.map Prod.fst).Nodup) (hfst : ∀ j, j ∈ tr.map Prod.fst ↔ SameOrbit G u j) :
    tr.length ≤ n := by
  have hsub : (tr.map Prod.fst).toFinset ⊆ Finset.range n := by
    intro j hj
    rw [List.mem_toFinset] at hj
    obtain ⟨_, hj', _⟩ := (hfst j).1 hj
    exact Finset.mem_range.2 hj'
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range, List.length_map] at this
  exact this

/-- **One step**, on the state `none`. -/
theorem tt_step_none {N s : ℕ} {H : Subgroup (Perm (Fin N))} {ps qs : List ℕ} {i : ℕ}
    (hinv : TTInv DV N s H ps qs i none) (Bt Bs : ℕ) :
    RunsWithin X body (ttStep (D := D) ps.toArray qs.toArray none i)
        (ttStepD X.O ps qs none i) (ttStepCost N Bt Bs) ∧
      TTInv DV N s H ps qs (i + 1) (ttStepD X.O ps qs none i) := by
  refine ⟨?_, fun ⟨h, hh, hm⟩ => hinv ⟨h, hh, tt_mapsPrefix_mono (Nat.le_succ i) hm⟩⟩
  refine (RunsWithin.caseOption_none (RunsWithin.prim_le rfl le_rfl)).mono ?_
  simp only [Prim.cost, ttStepCost]
  omega

/-- The step's value on a state `some`, by cases on the transversal search. -/
theorem tt_stepD_some (O : Oracle (groupSig D)) (ps qs : List ℕ) (g : PermData)
    (K : GroupData D.denote) (i : ℕ) :
    ttStepD O ps qs (some (g, K)) i =
      ((O.run GroupOp.orbitTransversal (K, ps.getD i 0)).find?
        (fun vr => vr.1 == get g.2 (qs.getD i 0))).map
          fun vr => (g.mul vr.2, O.run GroupOp.stabilizer (K, ps.getD i 0)) := by
  simp only [ttStepD]
  cases List.find? (fun vr => vr.1 == get g.2 (qs.getD i 0))
    (O.run GroupOp.orbitTransversal (K, ps.getD i 0)) <;> rfl

/-- **One step**, on a state `some`. -/
theorem tt_step_some (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {N s : ℕ}
    {G₀ H : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hH : H ≤ G₀)
    {ps qs : List ℕ} (hps : ∀ u ∈ ps, u < N) (hqs : ∀ u ∈ qs, u < N)
    (hlen : qs.length = ps.length) {i : ℕ} (hi : i < ps.length) (g : PermData)
    (K : GroupData D.denote) (hinv : TTInv DV N s H ps qs i (some (g, K))) :
    RunsWithin X body (ttStep (D := D) ps.toArray qs.toArray (some (g, K)) i)
        (ttStepD X.O ps qs (some (g, K)) i) (ttStepCost N B.Btr B.Bstab) ∧
      TTInv DV N s H ps qs (i + 1) (ttStepD X.O ps qs (some (g, K)) i) := by
  obtain ⟨N', ks, e⟩ := K
  obtain ⟨hN', hv, hks, hg, hgH, hmap, hden⟩ := hinv
  subst N'
  set p := ps.getD i 0 with hp_def
  set q := qs.getD i 0 with hq_def
  have hpN : p < N := hps p (by rw [hp_def, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have hqN : q < N := hqs q (by
    rw [hq_def, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hKle : GensData.denote N ks ≤ G₀ := by
    rw [hden]
    exact (pointwiseStab_le _ _).trans hH
  have hpre : GroupPre DV .orbitTransversal ((N, ks, e), p) := ⟨hv, hpN⟩
  have hpreS : GroupPre DV .stabilizer ((N, ks, e), p) := ⟨hv, hpN⟩
  obtain ⟨hnd, hfst, htr⟩ := hO .orbitTransversal _ (Or.inr rfl) hpre
  have hSpost := hO .stabilizer _ (Or.inl rfl) hpreS
  have hBt := B.transversal ks e p hks hKle hpre
  have hBs := B.stabilizer ks e p hks hKle hpreS
  have hout := B.stabOut ks e p hKle hpreS
  obtain ⟨tr, htr_def⟩ : ∃ tr : List (ℕ × PermData),
      X.O.run GroupOp.orbitTransversal ((N, ks, e), p) = tr := ⟨_, rfl⟩
  rw [htr_def] at hnd hfst htr hBt
  have htrlen := tt_length_tr hnd hfst
  -- the target `g⁻¹ q`
  set t := get g.2 q with ht_def
  have ht : ((PermData.denote N g)⁻¹ ⟨q, hqN⟩).val = t := PermData.val_denote_inv_apply hg _
  have hval : ttStepD X.O ps qs (some (g, (N, ks, e))) i =
      (tr.find? fun vr => vr.1 == t).map
        fun vr => (g.mul vr.2, X.O.run GroupOp.stabilizer ((N, ks, e), p)) := by
    rw [tt_stepD_some, htr_def]
  have hpa : Prim.eval (Prim.arrayGet (a := .nat)) (Args.cons ps.toArray (Args.cons i Args.nil)) =
      p := tt_get_toArray ps i
  have hqa : Prim.eval (Prim.arrayGet (a := .nat)) (Args.cons qs.toArray (Args.cons i Args.nil)) =
      q := tt_get_toArray qs i
  rcases hf : tr.find? (fun vr => vr.1 == t) with _ | vr
  · -- `g⁻¹ q` is not in the orbit: no solution
    have hf2 : tr.find? (fun x : ℕ × PermData => x.1 == Array.getD g.2 q Ty.nat.default) =
        none := hf
    refine ⟨?_, ?_⟩
    · rw [hval, hf]
      apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim_le hpa le_rfl)
        run_step (RunsWithin.prim_le hqa le_rfl)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step ((RunsWithin.call (hPre _ _ (Or.inr rfl) hpre)).of_eq htr_def)
        run_step (RunsWithin.ttFindProg tr _)
        simp only [Prim.eval]
        rw [hf2]
        exact RunsWithin.caseOption_none (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost, ttStepCost]
        rw [htr_def]
        omega
    · rw [hval, hf]
      rintro ⟨h, hh, hm⟩
      -- `k = g⁻¹ h` fixes the first `i` points and maps `p` to `t`
      set k := (PermData.denote N g)⁻¹ * h with hk_def
      have hkK : k ∈ GensData.denote N ks := by
        rw [hden, mem_pointwiseStab]
        refine ⟨mul_mem (inv_mem hgH) hh, fun u hu => ?_⟩
        obtain ⟨j, hj, hu⟩ := hu
        have hpj : ps.getD j 0 < N := hu ▸ u.2
        have e₁ := hm j (Nat.lt_succ_of_lt hj) hpj
        have e₂ := hmap j hj hpj
        have hu' : u = ⟨ps.getD j 0, hpj⟩ := Fin.ext hu
        rw [hu', Perm.mul_apply, Perm.inv_eq_iff_eq]
        exact Fin.ext (by rw [e₁, e₂])
      have hkp : (k ⟨p, hpN⟩).val = t := by
        rw [← ht, Perm.mul_apply]
        congr 2
        exact Fin.ext (hm i (Nat.lt_succ_self i) hpN)
      have hso : SameOrbit (GensData.denote N ks) p t :=
        ⟨hpN, hkp ▸ (k ⟨p, hpN⟩).2, k, hkK, Fin.ext hkp⟩
      obtain ⟨vr', hvr', hvr'1⟩ := List.mem_map.1 ((hfst t).2 hso)
      have := List.find?_eq_none.1 hf vr' hvr'
      simp [hvr'1] at this
  · -- the transversal element `r` with `r p = g⁻¹ q`
    have hf2 : tr.find? (fun x : ℕ × PermData => x.1 == Array.getD g.2 q Ty.nat.default) =
        some vr := hf
    have hvr := List.mem_of_find?_eq_some hf
    have hvr1 : vr.1 = t := by simpa using List.find?_some hf
    obtain ⟨hrv, hrK, hrp⟩ := htr vr hvr
    rcases hS : X.O.run GroupOp.stabilizer ((N, ks, e), p) with ⟨N'', ks', e'⟩
    rw [hS] at hSpost hBs hout
    obtain ⟨hN'', hv', hden'⟩ := hSpost
    change N'' = N at hN''
    subst N''
    have hden'' : GensData.denote N ks' = pointStab (GensData.denote N ks) ⟨p, hpN⟩ :=
      hden' hpN
    refine ⟨?_, ?_⟩
    · rw [hval, hf, Option.map_some, hS]
      apply RunsWithin.mono
      case h =>
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim_le hpa le_rfl)
        run_step (RunsWithin.prim_le hqa le_rfl)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step ((RunsWithin.call (hPre _ _ (Or.inr rfl) hpre)).of_eq htr_def)
        run_step (RunsWithin.ttFindProg tr _)
        simp only [Prim.eval]
        rw [hf2]
        run_with RunsWithin.caseOption_some _
        run_step (RunsWithin.prim _ _)
        run_step ((RunsWithin.call (hPre _ _ (Or.inl rfl) hpreS)).of_eq hS)
        run_step (RunsWithin.permMul hg hrv)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le rfl le_rfl
      case hc =>
        simp only [Prim.cost, ttStepCost]
        rw [hS, htr_def]
        omega
    · rw [hval, hf, Option.map_some, hS]
      have hrK' : PermData.denote N vr.2 ∈ GensData.denote N ks := hrK
      have hrH : PermData.denote N vr.2 ∈ H := by
        rw [hden] at hrK'
        exact hrK'.1
      refine ⟨rfl, hv', hout, hg.mul hrv, ?_, ?_, ?_⟩
      · rw [PermData.denote_mul hg hrv]
        exact mul_mem hgH hrH
      · intro j hj hpj
        rw [PermData.denote_mul hg hrv, Perm.mul_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · have hfix : PermData.denote N vr.2 ⟨ps.getD j 0, hpj⟩ = ⟨ps.getD j 0, hpj⟩ := by
            rw [hden, mem_pointwiseStab] at hrK'
            exact hrK'.2 _ ⟨j, hj, rfl⟩
          rw [hfix]
          exact hmap j hj hpj
        · have hrp' : PermData.denote N vr.2 ⟨ps.getD j 0, hpj⟩ =
              (PermData.denote N g)⁻¹ ⟨q, hqN⟩ := by
            apply Fin.ext
            rw [PermData.val_denote_apply hrv, ht, ← hvr1]
            exact hrp
          rw [hrp', ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]
      · show GensData.denote N ks' = _
        rw [hden'', ← tt_pointwiseStab_succ H ps i hpN, ← hden]
        ext x
        simp only [mem_pointStab, mem_pointwiseStab, Set.mem_singleton_iff, forall_eq]
        exact Iff.rfl

end Steps

section Fold

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The fold over the points `i, …, i + len - 1`.** -/
theorem tt_fold (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {N s : ℕ}
    {G₀ H : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀) (hH : H ≤ G₀)
    {ps qs : List ℕ} (hps : ∀ u ∈ ps, u < N) (hqs : ∀ u ∈ qs, u < N)
    (hlen : qs.length = ps.length) :
    ∀ (len i : ℕ) (st : Option (PermData × GroupData D.denote)), i + len ≤ ps.length →
      TTInv DV N s H ps qs i st →
      RunsWithin X body (Prog.foldList (a := .nat) (b := ttState D) (List.range' i len) st
          fun st i => ttStep (D := D) ps.toArray qs.toArray st i)
        ((List.range' i len).foldl (ttStepD X.O ps qs) st)
        (len * (ttStepCost N B.Btr B.Bstab + 1)) ∧
      TTInv DV N s H ps qs (i + len) ((List.range' i len).foldl (ttStepD X.O ps qs) st) := by
  intro len
  induction len with
  | zero =>
    intro i st _ hinv
    exact ⟨(RunsWithin.foldList_nil (X := X) (body := body)).mono (Nat.zero_le _), hinv⟩
  | succ len ih =>
    intro i st hle hinv
    have hi : i < ps.length := by omega
    have hstep : RunsWithin X body (ttStep (D := D) ps.toArray qs.toArray st i)
          (ttStepD X.O ps qs st i) (ttStepCost N B.Btr B.Bstab) ∧
        TTInv DV N s H ps qs (i + 1) (ttStepD X.O ps qs st i) := by
      rcases st with _ | ⟨g, K⟩
      · exact tt_step_none hinv _ _
      · exact tt_step_some hO hPre B hH hps hqs hlen hi g K hinv
    obtain ⟨hrun, hinv'⟩ := hstep
    obtain ⟨hrest, hinvF⟩ := ih (i + 1) _ (by omega) hinv'
    refine ⟨?_, ?_⟩
    · rw [List.range'_succ, List.foldl_cons]
      refine (RunsWithin.foldList_cons hrun hrest).mono ?_
      rw [Nat.succ_mul]
      omega
    · rw [List.range'_succ, List.foldl_cons, show i + (len + 1) = i + 1 + len by omega]
      exact hinvF

/-- The data maps the tuple: `h ps[i] = qs[i]` for every `i`. -/
abbrev MapsTuple {N : ℕ} (h : Perm (Fin N)) (ps qs : List ℕ) : Prop :=
  MapsPrefix h ps qs ps.length

/-- **The tuple transporter.** For `H = ⟨gs⟩` valid at degree `N` and lists `ps`, `qs` of
points below `N` of equal length, the result is `some h` exactly when some element of `H`
maps `ps[i]` to `qs[i]` for every `i`, and then `h` is valid and is such an element. -/
theorem RunsWithin.tupleTransProg (hO : MeetsContractOn DV stabOps X.O)
    (hPre : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x) {N : ℕ} {gs : GensData}
    {d : D.denote} (hGv : GroupValid DV N gs d) {s : ℕ} {G₀ : Subgroup (Perm (Fin N))}
    (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s) (hG₀ : GensData.denote N gs ≤ G₀)
    {ps qs : List ℕ} (hps : ∀ u ∈ ps, u < N) (hqs : ∀ u ∈ qs, u < N)
    (hlen : qs.length = ps.length) :
    RunsWithin X body (CertProg.tupleTransProg (N, gs, d) ps qs)
        (tupleTransModel X.O (N, gs, d) ps qs)
        (tupleTransCost N ps.length B.Btr B.Bstab) ∧
      ((tupleTransModel X.O (N, gs, d) ps qs).isSome = true ↔
        ∃ h ∈ GensData.denote N gs, MapsTuple h ps qs) ∧
      ∀ g, tupleTransModel X.O (N, gs, d) ps qs = some g →
        g.Valid N ∧ PermData.denote N g ∈ GensData.denote N gs ∧
          MapsTuple (PermData.denote N g) ps qs := by
  set H := GensData.denote N gs with hH_def
  have hinv₀ : TTInv DV N s H ps qs 0 (some (PermData.one N, (N, gs, d))) := by
    refine ⟨rfl, hGv, hs, PermData.valid_one N, ?_, fun j hj => absurd hj (Nat.not_lt_zero j),
      ?_⟩
    · rw [PermData.denote_one]
      exact one_mem H
    · ext x
      simp only [mem_pointwiseStab, prefixSet, Set.mem_ofPred_eq, Nat.not_lt_zero, false_and,
        exists_false, false_imp_iff, implies_true, and_true]
      exact Iff.rfl
  obtain ⟨hfold, hinvF⟩ := tt_fold hO hPre B hG₀ hps hqs hlen ps.length 0 _ (by omega) hinv₀
  rw [Nat.zero_add] at hinvF
  have hrange : List.range ps.length = List.range' 0 ps.length := List.range_eq_range'
  have hmodel : tupleTransModel X.O (N, gs, d) ps qs =
      ((List.range' 0 ps.length).foldl (ttStepD X.O ps qs)
        (some (PermData.one N, (N, gs, d)))).map Prod.fst := by
    rw [tupleTransModel, hrange]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmodel]
    have hpre : ∀ {r : (Ty.option Ty.perm).denote} {c : ℕ},
        RunsWithin X body (Prog.caseOption (a := .prod Ty.perm (Ty.group D))
          ((List.range' 0 ps.length).foldl (ttStepD X.O ps qs)
          (some (PermData.one N, (N, gs, d)))) (Prog.op0 Prim.none) fun gK =>
            .bind (.op1 .fst gK) fun g => .op1 .some g) r c →
        RunsWithin X body (CertProg.tupleTransProg (N, gs, d) ps qs) r
          (c + 2 * N + 4 * ps.length + ps.length * (ttStepCost N B.Btr B.Bstab + 1) + 15) := by
      intro r c hk
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.permOne _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        simp only [Prim.eval]
        rw [hrange]
        run_step hfold
        exact hk
      case hc =>
        simp only [Prim.cost, Prim.eval, Args.head]
        rw [hlen]
        omega
    rcases hres : (List.range' 0 ps.length).foldl (ttStepD X.O ps qs)
        (some (PermData.one N, (N, gs, d))) with _ | ⟨g, K⟩
    · refine (hpre (c := 2) (by
        rw [hres]
        exact RunsWithin.caseOption_none (RunsWithin.prim_le rfl le_rfl))).mono ?_
      simp only [tupleTransCost]
      omega
    · refine (hpre (c := 3) (by
        rw [hres]
        exact (RunsWithin.caseOption_some (RunsWithin.bind_le (c := 2) (RunsWithin.prim _ _)
          (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost]))).mono (by omega))).mono ?_
      simp only [tupleTransCost]
      omega
  · rw [hmodel]
    rcases hres : (List.range' 0 ps.length).foldl (ttStepD X.O ps qs)
        (some (PermData.one N, (N, gs, d))) with _ | ⟨g, K⟩
    · rw [hres] at hinvF
      simp only [Option.map_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      exact hinvF
    · rw [hres] at hinvF
      obtain ⟨N', ks, e⟩ := K
      obtain ⟨-, -, -, -, hgH, hmap, -⟩ := hinvF
      simp only [Option.map_some, Option.isSome_some, true_iff]
      exact ⟨_, hgH, hmap⟩
  · intro g' hg'
    rw [hmodel] at hg'
    rcases hres : (List.range' 0 ps.length).foldl (ttStepD X.O ps qs)
        (some (PermData.one N, (N, gs, d))) with _ | ⟨g, K⟩
    · rw [hres] at hg'
      simp at hg'
    · rw [hres] at hg' hinvF
      obtain ⟨N', ks, e⟩ := K
      obtain ⟨-, -, -, hgv, hgH, hmap, -⟩ := hinvF
      simp only [Option.map_some, Option.some.injEq] at hg'
      subst hg'
      exact ⟨hgv, hgH, hmap⟩

end Fold

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_ttFindProg {tr₁ : var₁ (.list (.prod .nat Ty.perm))}
    {tr₂ : var₂ (.list (.prod .nat Ty.perm))} {t₁ : var₁ .nat} {t₂ : var₂ .nat}
    (htr : ⟨.list (.prod .nat Ty.perm), tr₁, tr₂⟩ ∈ Γ) (ht : ⟨.nat, t₁, t₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (ttFindProg (D := D) tr₁ t₁) (ttFindProg (D := D) tr₂ t₂) := by
  unfold ttFindProg
  refine SoJProg.wf_findProg htr fun Γ' hΓ' x₁ x₂ hx => ?_
  prog_wf
  exact hΓ' ht

theorem wf_ttStep {pa₁ qa₁ : var₁ (.array .nat)} {pa₂ qa₂ : var₂ (.array .nat)}
    {st₁ : var₁ (ttState D)} {st₂ : var₂ (ttState D)} {i₁ : var₁ .nat} {i₂ : var₂ .nat}
    (hpa : ⟨.array .nat, pa₁, pa₂⟩ ∈ Γ) (hqa : ⟨.array .nat, qa₁, qa₂⟩ ∈ Γ)
    (hst : ⟨ttState D, st₁, st₂⟩ ∈ Γ) (hi : ⟨.nat, i₁, i₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (ttStep pa₁ qa₁ st₁ i₁) (ttStep pa₂ qa₂ st₂ i₂) := by
  unfold ttStep
  prog_wf

theorem wf_tupleTransProg {H₁ : var₁ (Ty.group D)} {H₂ : var₂ (Ty.group D)}
    {ps₁ qs₁ : var₁ (.list .nat)} {ps₂ qs₂ : var₂ (.list .nat)}
    (hH : ⟨Ty.group D, H₁, H₂⟩ ∈ Γ) (hps : ⟨.list .nat, ps₁, ps₂⟩ ∈ Γ)
    (hqs : ⟨.list .nat, qs₁, qs₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (tupleTransProg H₁ ps₁ qs₁) (tupleTransProg H₂ ps₂ qs₂) := by
  unfold tupleTransProg
  prog_wf

end Wf

end GraphIso.CertProg
