module

public import GraphIso.Main.Frame
public import GraphIso.Reductions.SequentialProg
public import GraphIso.Toolkit.Labels

/-!
# The dynamic chain rule

Stage 14j-2, item 3 (`PLAN-14.md` §14.2, a design correction made during the stage). The chain
rule `seqProg` processes a *fixed* list of orbits: each later orbit is solved inside the coset
returned so far, whose group (an automorphism group of the earlier orbits) need not be
transitive on it. A hinted child must be transitive on its window (`PLAN-14.md` §2.1), so the
hinted steps use **`dynSeqProg`** instead:

* the state is the answer so far and the remaining points;
* while the answer is a coset `τ • H` and points remain, the step computes the orbits of the
  *current* group `H` on the remaining points (`orbits`), takes the first one `O`, solves it
  inside `τ • H` by the parameter `handle`, and removes `O` from the remaining points;
* the loop runs at most `|pts|` times (`foldList` over `List.range |pts|`); every step removes
  a nonempty orbit, so the points are exhausted unless an answer is `none`.

`RunsWithin.dynSeqProg`: if `handle` is correct (with a ghost value `g`, its children, and a
predicate `Q`) on every orbit of every valid coset whose group lies in the starting group
`G₀`, the result is correct for the whole window, at the cost of the handled steps plus
`dynSeqCost`. The processed orbits are disjoint parts of the window, so their sizes sum to at
most `|pts|`. Every processed orbit is an orbit of a subgroup of `G₀` (the hypothesis the
handles need). The `orbits` charges are hypotheses on groups inside `G₀` with at most `sIn`
generators (bounded inputs).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Toolkit

/-! ### The program -/

section Progs

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- The state of the dynamic chain: the answer so far and the remaining points. -/
abbrev dynTy (D : Ty) : Ty := .prod (Ty.answer D) (.list .nat)

/-- **One step of the dynamic chain**: on a coset with points left, solve the first orbit of
the current group on the remaining points and remove it. -/
def dynStep (handle : var Ty.strs → var (Ty.coset D) → var (.list .nat) →
      Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (st : var (dynTy D)) : Prog (groupSig D) rec var (dynTy D) :=
  .bind (.op1 .fst st) fun acc => .bind (.op1 .snd st) fun rem =>
  .caseOption acc (.ret st) fun c =>
  .caseList rem (.ret st) fun _ _ =>
  .bind (.op1 .snd c) fun G => .bind (.op1 .fst G) fun N =>
  .bind (mkWindow N rem) fun w => .bind (.op2 .pair G w) fun Gw =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits Gw) fun os =>
  .caseList os (.ret st) fun O _ =>
  .bind (handle xy c O) fun a =>
  .bind (markProg N O) fun mk =>
  .bind (Toolkit.filterList rem fun j => .bind (.op2 .arrayGet mk j) fun b => .op1 .not b)
    fun rem' =>
  .op2 .pair a rem'

/-- **The dynamic chain rule** on the points `pts`, from the coset `c`. -/
def dynSeqProg (handle : var Ty.strs → var (Ty.coset D) → var (.list .nat) →
      Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (c : var (Ty.coset D)) (pts : var (.list .nat)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .some c) fun a₀ => .bind (.op2 .pair a₀ pts) fun st₀ =>
  .bind (.op1 .length pts) fun k => .bind (.op1 .range k) fun fuel =>
  .bind (.foldList fuel st₀ fun st _ => dynStep handle xy st) fun st =>
  .op1 .fst st

end Progs

/-! ### Costs -/

/-- The cost of one step of the dynamic chain beyond its handled orbit, at degree `N` with at
most `p` points, and the `orbits` charge `Bo` (including the loop's own unit). -/
def dynStepCost (N p Bo : ℕ) : ℕ := Bo + 4 * N + 17 * p + 32

/-- The cost of `dynSeqProg` beyond the handled orbits: `p` steps at most. -/
def dynSeqCost (N p Bo : ℕ) : ℕ := p * dynStepCost N p Bo + 2 * p + 8

/-! ### Facts about the remaining points -/

section Facts

theorem dyn_filter_mask {N : ℕ} {O rem : List ℕ} (hlt : ∀ j ∈ rem, j < N) :
    rem.filter (fun j => !getB (markArr N O) j) = rem.filter (fun j => !decide (j ∈ O)) := by
  apply List.filter_congr
  intro j hj
  have := getB_markArr N O j
  by_cases h : j ∈ O
  · have : getB (markArr N O) j = true := this.2 ⟨hlt j hj, h⟩
    simp [this, h]
  · have : getB (markArr N O) j = false := by
      cases e : getB (markArr N O) j
      · rfl
      · exact absurd (this.1 e).2 h
    simp [this, h]

theorem dyn_ptsSet_append (N : ℕ) (l₁ l₂ : List ℕ) :
    ptsSet N (l₁ ++ l₂) = ptsSet N l₁ ∪ ptsSet N l₂ := by
  ext u
  simp [ptsSet]

theorem dyn_ptsSet_filter (N : ℕ) (rem O : List ℕ) :
    ptsSet N (rem.filter fun j => !decide (j ∈ O)) = ptsSet N rem \ ptsSet N O := by
  ext u
  simp [ptsSet]

/-- Removing a sublist of a duplicate-free list: the rest and the sublist make up the list. -/
theorem dyn_perm_filter {rem O : List ℕ} (hnd : rem.Nodup) (hO : O.Nodup)
    (hsub : ∀ i ∈ O, i ∈ rem) :
    (O ++ rem.filter fun j => !decide (j ∈ O)).Perm rem := by
  have h1 : (rem.filter fun j => decide (j ∈ O)).Perm O := by
    refine (List.perm_ext_iff_of_nodup (hnd.filter _) hO).2 fun i => ?_
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub i h, h⟩⟩
  have h2 := List.filter_append_perm (fun j => decide (j ∈ O)) rem
  refine ((h1.symm.append_right _).trans ?_)
  convert h2 using 2

end Facts

/-! ### The specification -/

section Spec

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The hypothesis on the handle**: on every valid coset `τ • H` of degree `N` whose group lies
in `G₀` and has at most `sIn` generators, and every duplicate-free nonempty `H`-orbit `O` of
points of `pts`, the handle returns a correct answer for the window `O` with at most `sIn`
generators, within `Ch O g` for a ghost value `g` (the children of the step) with `Q O g`. -/
def DynHandle (X : Ctx (groupSig D)) (body : a.denote → Prog (groupSig D) (a, b) Ty.denote b)
    (DV : ℕ → GensData → D.denote → Prop)
    (handle : StrData × StrData → CosetData D → List ℕ →
      Prog (groupSig D) (a, b) Ty.denote (Ty.answer D))
    (xy : StrData × StrData) (N : ℕ) (G₀ : Subgroup (Perm (Fin N))) (pts : List ℕ) (sIn : ℕ)
    {γ : Type} (Ch : List ℕ → γ → ℕ) (Q : List ℕ → γ → Prop) : Prop :=
  ∀ (τ : PermData) (Hd : GroupData D.denote) (O : List ℕ), τ.Valid N → Hd.1 = N →
    GroupValid DV N Hd.2.1 Hd.2.2 → Hd.2.1.length ≤ sIn → GensData.denote N Hd.2.1 ≤ G₀ →
    O.Nodup → O ≠ [] → (∀ i ∈ O, i ∈ pts) →
    (∀ i ∈ O, ∀ j, j ∈ O ↔ SameOrbit (GensData.denote N Hd.2.1) i j) →
    ∃ (ans : AnswerData D) (g : γ), RunsWithin X body (handle xy (τ, Hd) O) ans (Ch O g) ∧
      AnsOK DV N (ptsSet N O) (PermData.denote N τ) (GensData.denote N Hd.2.1)
        (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧ Q O g

/-- **The invariant of the dynamic chain** after `k` steps, with the answer `acc`, the remaining
points `rem` and the processed points `processed`. -/
structure DynInv (DV : ℕ → GensData → D.denote → Prop) (N : ℕ) (xy : StrData × StrData)
    (σd : PermData) (G₀ : Subgroup (Perm (Fin N))) (pts : List ℕ) (sIn k : ℕ)
    (acc : AnswerData D) (rem processed : List ℕ) : Prop where
  perm : (processed ++ rem).Perm pts
  ok : AnsOK DV N (ptsSet N processed) (PermData.denote N σd) G₀ (xy.1.denote N)
    (xy.2.denote N) acc
  grp : ∀ c : CosetData D, acc = some c → c.2.gens.length ≤ sIn ∧
    GensData.denote N c.2.gens ≤ G₀ ∧ IsInvariant (GensData.denote N c.2.gens) (ptsSet N rem)
  prog : ∀ c : CosetData D, acc = some c → rem = [] ∨ rem.length + k ≤ pts.length

/-- A list orbit is invariant. -/
theorem dyn_orbit_inv {N : ℕ} {H : Subgroup (Perm (Fin N))} {O : List ℕ}
    (hO : ∀ i ∈ O, ∀ j, j ∈ O ↔ SameOrbit H i j) : IsInvariant H (ptsSet N O) := by
  intro g hg u hu
  exact (hO u.val hu _).2 ⟨u.2, (g u).2, g, hg, rfl⟩

/-- `caseList` on a list known to be a cons. -/
theorem dyn_caseList_cons {a' t : Ty} {l : (Ty.list a').denote} {x : a'.denote}
    {xs : List a'.denote} {p : Prog (groupSig D) (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog (groupSig D) (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (hl : l = x :: xs) (h : RunsWithin X body (q x xs) r k) :
    RunsWithin X body (.caseList l p q) r (1 + k) := by
  subst hl
  exact RunsWithin.caseList_cons h

variable {handle : StrData × StrData → CosetData D → List ℕ →
    Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
  {xy : StrData × StrData} {N : ℕ} {σd : PermData} {G₀ : Subgroup (Perm (Fin N))}
  {pts : List ℕ} {sIn : ℕ} {γ : Type} {Ch : List ℕ → γ → ℕ} {Q : List ℕ → γ → Prop} {Bo : ℕ}

/-- **One step of the dynamic chain** preserves the invariant, at the cost of the handled orbit
(if any) plus `dynStepCost` (minus the loop's unit). -/
theorem dyn_one (hO : MeetsContractOn DV (· = .orbits) X.O)
    (hPre : ∀ x, GroupPre DV .orbits x → X.Pre .orbits x) (hpts : pts.Nodup)
    (hlt : ∀ i ∈ pts, i < N) (hH : DynHandle X body DV handle xy N G₀ pts sIn Ch Q)
    (hBo : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 = N → Hd.2.1.length ≤ sIn →
      GensData.denote N Hd.2.1 ≤ G₀ → GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo)
    {k : ℕ} {acc : AnswerData D} {rem processed : List ℕ}
    (hI : DynInv DV N xy σd G₀ pts sIn k acc rem processed) :
    ∃ (st : AnswerData D × List ℕ) (new : List (List ℕ × γ)),
      RunsWithin X body (dynStep handle xy (acc, rem)) st
        ((new.map fun s => Ch s.1 s.2).sum + (dynStepCost N pts.length Bo - 1)) ∧
      DynInv DV N xy σd G₀ pts sIn (k + 1) st.1 st.2
        (processed ++ (new.map Prod.fst).flatten) ∧
      ∀ s ∈ new, Q s.1 s.2 := by
  have hremlen : rem.length ≤ pts.length := by
    have := hI.perm.length_eq
    simp only [List.length_append] at this
    omega
  rcases acc with _ | ⟨τ, Hd⟩
  · -- the answer is already `none`
    refine ⟨(none, rem), [], ?_, ?_, by simp⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.caseOption_none (RunsWithin.ret _)
      case hc =>
        simp only [Prim.cost, dynStepCost, List.map_nil, List.sum_nil]
        omega
    · simpa using (⟨hI.perm, hI.ok, (fun c h => by cases h), (fun c h => by cases h)⟩ :
        DynInv DV N xy σd G₀ pts sIn (k + 1) none rem processed)
  rcases rem with _ | ⟨r, rs⟩
  · -- no points left
    refine ⟨(some (τ, Hd), []), [], ?_, ?_, by simp⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.caseOption_some (RunsWithin.caseList_nil (RunsWithin.ret _))
      case hc =>
        simp only [Prim.cost, dynStepCost, List.map_nil, List.sum_nil]
        omega
    · simpa using (⟨hI.perm, hI.ok, hI.grp, fun _ _ => Or.inl rfl⟩ :
        DynInv DV N xy σd G₀ pts sIn (k + 1) (some (τ, Hd)) [] processed)
  -- a step on the first orbit of the current group
  set rem := r :: rs with hremdef
  obtain ⟨hτ, hdeg, hGv, hiso⟩ := id hI.ok
  obtain ⟨Nd, gs, d⟩ := Hd
  change Nd = N at hdeg
  subst hdeg
  obtain ⟨hsIn, hle, hinv⟩ := hI.grp _ rfl
  change gs.length ≤ sIn at hsIn
  change GensData.denote Nd gs ≤ G₀ at hle
  change IsInvariant (GensData.denote Nd gs) (ptsSet Nd rem) at hinv
  have hnd : (processed ++ rem).Nodup := hI.perm.nodup_iff.2 hpts
  have hremnd : rem.Nodup := (List.nodup_append.1 hnd).2.1
  have hrempts : ∀ i ∈ rem, i ∈ pts := fun i hi =>
    hI.perm.mem_iff.1 (List.mem_append_right _ hi)
  have hremlt : ∀ i ∈ rem, i < Nd := fun i hi => hlt i (hrempts i hi)
  have hwv : (WinData.ofPoints Nd rem).Valid Nd := WinData.valid_ofPoints hremnd hremlt
  have hpre : GroupPre DV .orbits ((Nd, gs, d), WinData.ofPoints Nd rem) := ⟨hGv, hwv, hinv⟩
  have hos := hO .orbits _ rfl hpre
  change IsOrbitPartition (GensData.denote Nd gs) (WinData.ofPoints Nd rem)
    (X.O.run GroupOp.orbits ((Nd, gs, d), WinData.ofPoints Nd rem)) at hos
  set os : List (List ℕ) := X.O.run GroupOp.orbits ((Nd, gs, d), WinData.ofPoints Nd rem)
    with hosdef
  obtain ⟨O, os', hcons⟩ : ∃ O os', os = O :: os' := by
    rcases hO' : os with _ | ⟨O, os'⟩
    · have := hos.1.length_eq
      rw [hO'] at this
      simp [WinData.ofPoints, hremdef] at this
    · exact ⟨O, os', rfl⟩
  have hOmem : O ∈ os := by rw [hcons]; exact List.mem_cons_self
  obtain ⟨hOne, hOorb⟩ := hos.2 O hOmem
  have hflnd : os.flatten.Nodup := hos.1.nodup_iff.2 hremnd
  have hOnd : O.Nodup := (List.nodup_flatten.1 hflnd).1 O hOmem
  have hOrem : ∀ i ∈ O, i ∈ rem := fun i hi =>
    hos.1.mem_iff.1 (List.mem_flatten.2 ⟨O, hOmem, hi⟩)
  have hOpts : ∀ i ∈ O, i ∈ pts := fun i hi => hrempts i (hOrem i hi)
  obtain ⟨ans, g, hrun, hok, hgen, hQ⟩ :=
    hH τ (Nd, gs, d) O hτ rfl hGv hsIn hle hOnd hOne hOpts hOorb
  have hOinv : IsInvariant (GensData.denote Nd gs) (ptsSet Nd O) := dyn_orbit_inv hOorb
  set rem' := rem.filter fun j => !decide (j ∈ O) with hrem'
  have hperm' := dyn_perm_filter hremnd hOnd hOrem
  refine ⟨(ans, rem'), [(O, g)], ?_, ?_, by simpa using hQ⟩
  · have hfilt := Toolkit.RunsWithin.filterList (X := X) (body := body) (a' := .nat) (xs := rem)
      (p := fun j => .bind (.op2 .arrayGet (markArr Nd O) j) fun b => .op1 .not b)
      (P := fun j => !getB (markArr Nd O) j) (c := 2) fun j _ =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.prim_le rfl le_rfl)
          (by simp [Prim.cost])
    rw [dyn_filter_mask hremlt] at hfilt
    have hOlen : O.length ≤ rem.length := by
      have := hperm'.length_eq
      simp only [List.length_append] at this
      omega
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      apply RunsWithin.caseOption_some
      apply RunsWithin.caseList_cons
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.mkWindow _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (x := ((Nd, gs, d), WinData.ofPoints Nd rem)) (hPre _ hpre))
      apply dyn_caseList_cons hcons
      run_step hrun
      run_step (RunsWithin.markProg _ _)
      run_step hfilt
      exact RunsWithin.prim _ _
    case hc =>
      have hB := hBo (Nd, gs, d) (WinData.ofPoints Nd rem) rfl hsIn hle hpre
      simp only [Prim.cost, dynStepCost, markCost, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      simp only [Prim.eval] at *
      omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      rw [List.append_assoc]
      exact (hperm'.append_left processed).trans hI.perm
    · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      rw [dyn_ptsSet_append]
      exact AnsOK.union_some hI.ok hok
    · intro c hc
      change ans = some c at hc
      subst hc
      have e := AnsOK.eq_aut hOinv hok
      refine ⟨hgen c rfl, ?_, ?_⟩
      · rw [e]
        exact (aut_le hOinv _).trans hle
      · rw [e, hrem', dyn_ptsSet_filter]
        exact (hinv.diff hOinv).aut hOinv _
    · intro c _
      right
      change rem'.length + (k + 1) ≤ pts.length
      have h1 := hperm'.length_eq
      have h2 := hI.prog _ rfl
      have hpos : 0 < O.length := List.length_pos_of_ne_nil hOne
      simp only [List.length_append] at h1
      rw [← hrem'] at h1
      rcases h2 with h2 | h2
      · exact absurd h2 (by simp [hremdef])
      · omega

/-- **The loop** of the dynamic chain: from any state satisfying the invariant after `k` steps,
the remaining `|fs|` steps keep the invariant, at the cost of the handled orbits plus
`dynStepCost` per step. -/
theorem dyn_fold (hO : MeetsContractOn DV (· = .orbits) X.O)
    (hPre : ∀ x, GroupPre DV .orbits x → X.Pre .orbits x) (hpts : pts.Nodup)
    (hlt : ∀ i ∈ pts, i < N) (hH : DynHandle X body DV handle xy N G₀ pts sIn Ch Q)
    (hBo : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 = N → Hd.2.1.length ≤ sIn →
      GensData.denote N Hd.2.1 ≤ G₀ → GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo) :
    ∀ (fs : List ℕ) (k : ℕ) (acc : AnswerData D) (rem processed : List ℕ),
      DynInv DV N xy σd G₀ pts sIn k acc rem processed →
      ∃ (st : AnswerData D × List ℕ) (steps : List (List ℕ × γ)),
        RunsWithin X body (Prog.foldList (a := .nat) (b := dynTy D) fs (acc, rem)
            fun st _ => dynStep handle xy st) st
          ((steps.map fun s => Ch s.1 s.2).sum + fs.length * dynStepCost N pts.length Bo) ∧
        DynInv DV N xy σd G₀ pts sIn (k + fs.length) st.1 st.2
          (processed ++ (steps.map Prod.fst).flatten) ∧
        ∀ s ∈ steps, Q s.1 s.2
  | [], k, acc, rem, processed, hI =>
    ⟨(acc, rem), [], by simpa using RunsWithin.foldList_nil, by simpa using hI, by simp⟩
  | _ :: fs, k, acc, rem, processed, hI => by
    obtain ⟨st₁, new, hr₁, hI₁, hQ₁⟩ := dyn_one hO hPre hpts hlt hH hBo hI
    obtain ⟨st, steps, hr, hI', hQ'⟩ :=
      dyn_fold hO hPre hpts hlt hH hBo fs (k + 1) st₁.1 st₁.2 _ hI₁
    refine ⟨st, new ++ steps, ?_, ?_, ?_⟩
    · refine (RunsWithin.foldList_cons (f := fun st _ => dynStep handle xy st) hr₁ hr).mono ?_
      have h1 : 1 ≤ dynStepCost N pts.length Bo := by simp only [dynStepCost]; omega
      simp only [List.map_append, List.sum_append, List.length_cons, Nat.succ_mul]
      omega
    · have e : k + (fs.length + 1) = k + 1 + fs.length := by omega
      simpa [List.length_cons, e, List.map_append, List.flatten_append, List.append_assoc]
        using hI'
    · intro s hs
      rcases List.mem_append.1 hs with hs | hs
      · exact hQ₁ s hs
      · exact hQ' s hs

/-- **The dynamic chain rule.** From the coset `σ • G₀` (`G₀ = ⟨gs⟩`, at most `sIn`
generators) on the `G₀`-invariant points `pts`, with a handle correct on every orbit of every
valid coset inside `G₀` (`DynHandle`), the result is a correct answer for the window `pts`
with at most `sIn` generators. The cost is that of the handled orbits (`steps`, each with its
ghost value) plus `dynSeqCost`. The handled orbits are disjoint parts of `pts`: their sizes
sum to at most `|pts|`. -/
theorem RunsWithin.dynSeqProg (hO : MeetsContractOn DV (· = .orbits) X.O)
    (hPre : ∀ x, GroupPre DV .orbits x → X.Pre .orbits x) {gs : GensData} {d : D.denote}
    (hσ : σd.Valid N) (hGv : GroupValid DV N gs d) (hs : gs.length ≤ sIn) (hpts : pts.Nodup)
    (hlt : ∀ i ∈ pts, i < N) (hinv : IsInvariant (GensData.denote N gs) (ptsSet N pts))
    (hH : DynHandle X body DV handle xy N (GensData.denote N gs) pts sIn Ch Q)
    (hBo : ∀ (Hd : GroupData D.denote) (w : WinData), Hd.1 = N → Hd.2.1.length ≤ sIn →
      GensData.denote N Hd.2.1 ≤ GensData.denote N gs → GroupPre DV .orbits (Hd, w) →
      X.B.call GroupOp.orbits (Hd, w) (X.O.run GroupOp.orbits (Hd, w)) ≤ Bo) :
    ∃ (ans : AnswerData D) (steps : List (List ℕ × γ)),
      RunsWithin X body (Main.dynSeqProg handle xy (σd, (N, gs, d)) pts) ans
        ((steps.map fun s => Ch s.1 s.2).sum + dynSeqCost N pts.length Bo) ∧
      AnsOK DV N (ptsSet N pts) (PermData.denote N σd) (GensData.denote N gs)
        (xy.1.denote N) (xy.2.denote N) ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      (steps.map fun s => s.1.length).sum ≤ pts.length ∧
      ∀ s ∈ steps, Q s.1 s.2 := by
  have hempty : ptsSet N ([] : List ℕ) = ∅ := by
    ext u
    simp [ptsSet]
  have hI₀ : DynInv DV N xy σd (GensData.denote N gs) pts sIn 0 (some (σd, (N, gs, d))) pts
      [] := by
    refine ⟨by simp, ?_, ?_, ?_⟩
    · rw [hempty]
      exact AnsOK.empty_window (D := D) (Gd := (N, gs, d)) (x := xy.1.denote N)
        (y := xy.2.denote N) hσ rfl hGv
    · intro c hc
      cases hc
      exact ⟨hs, le_rfl, hinv⟩
    · intro c _
      right
      omega
  obtain ⟨st, steps, hr, hI, hQ⟩ := dyn_fold hO hPre hpts hlt hH hBo (List.range pts.length) 0
    _ pts [] hI₀
  rw [List.length_range, Nat.zero_add, List.nil_append] at *
  have hsum : (steps.map fun s => s.1.length).sum = (steps.map Prod.fst).flatten.length := by
    rw [List.length_flatten, List.map_map]
    rfl
  have hlen := hI.perm.length_eq
  simp only [List.length_append] at hlen
  refine ⟨st.1, steps, ?_, ?_, ?_, by omega, hQ⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hr
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head, dynSeqCost]
      omega
  · rcases hst : st.1 with _ | c
    · have hok := hI.ok
      rw [hst] at hok
      have hsub : ptsSet N (steps.map Prod.fst).flatten ∪ ptsSet N pts = ptsSet N pts := by
        refine Set.union_eq_right.2 fun u hu => ?_
        exact hI.perm.mem_iff.1 (List.mem_append_left _ hu)
      rw [← hsub]
      exact AnsOK.union_none hok
    · have hrem : st.2 = [] := by
        rcases hI.prog c hst with h | h
        · exact h
        · exact List.eq_nil_of_length_eq_zero (by omega)
      have hok := hI.ok
      rw [hst] at hok
      have hp := hI.perm
      rw [hrem, List.append_nil] at hp
      have e : ptsSet N (steps.map Prod.fst).flatten = ptsSet N pts := by
        ext u
        exact hp.mem_iff
      rwa [e] at hok
  · intro c hc
    exact (hI.grp c hc).1

end Spec

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_dynSeqProg
    {h₁ : var₁ Ty.strs → var₁ (Ty.coset D) → var₁ (.list .nat) →
      Prog (groupSig D) rec var₁ (Ty.answer D)}
    {h₂ : var₂ Ty.strs → var₂ (Ty.coset D) → var₂ (.list .nat) →
      Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hh : ∀ Γ' : WfCtx var₁ var₂, Γ ⊆ Γ' → ∀ x₁ x₂ c₁ c₂ o₁ o₂,
      ⟨Ty.strs, x₁, x₂⟩ ∈ Γ' → ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ' → ⟨.list .nat, o₁, o₂⟩ ∈ Γ' →
      Prog.Wf r Γ' (h₁ x₁ c₁ o₁) (h₂ x₂ c₂ o₂))
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {c₁ : var₁ (Ty.coset D)}
    {c₂ : var₂ (Ty.coset D)} {p₁ : var₁ (.list .nat)} {p₂ : var₂ (.list .nat)}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hc : ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ)
    (hp : ⟨.list .nat, p₁, p₂⟩ ∈ Γ) :
    Prog.Wf r Γ (dynSeqProg h₁ xy₁ c₁ p₁) (dynSeqProg h₂ xy₂ c₂ p₂) := by
  unfold dynSeqProg dynStep mkWindow markProg Toolkit.filterList mapList
  prog_wf
  all_goals
    exact hh _ (fun y hy => by simp [hy]) _ _ _ _ _ _
      (by repeat (first | exact List.mem_cons_self | exact hxy | apply List.mem_cons_of_mem))
      (by repeat (first | exact List.mem_cons_self | exact hc | apply List.mem_cons_of_mem))
      (by repeat (first | exact List.mem_cons_self | exact hp | apply List.mem_cons_of_mem))

end Wf

end GraphIso.Main
