module

public import GraphIso.Reductions.Data

/-!
# Sequential processing of windows, as a program

`seqProg sub xy c os` processes the point lists `os` (for example the orbits of the current
group on a window) one after the other. It starts from the input coset `c`; at each step it
builds the window of the next point list and calls `sub` on it **inside the coset returned by
the previous step**. Once a step returns `none`, the remaining steps return `none` at constant
cost.

`RunsWithin.seqProg`: if every window is invariant under the input group and `sub` is correct
on each window inside any valid coset, then the result is a correct answer for the union of
the windows, at cost at most

  `1 + Σ_{o ∈ os} (C o + 2 n + 5 |o| + 13)`,

where `C o` bounds the sub-call on the window of `o`; `2 n + 5 |o| + 7` of each term builds the
window and the rest is bookkeeping. `seqInputs_of_isOrbitPartition` supplies the hypotheses
from an exact orbit partition, as returned by the `orbits` operation.
-/

@[expose] public section

namespace GraphIso.Programs

open Equiv Cost

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type} {D : Ty}

/-- One sequential step: if the current answer is a coset, solve the next window inside it. -/
def seqStep (sub : var (Ty.inst D) → Prog S rec var (Ty.answer D)) (xy : var Ty.strs)
    (acc : var (Ty.answer D)) (pts : var (.list .nat)) : Prog S rec var (Ty.answer D) :=
  .caseOption acc (.op0 .none) fun c =>
    .bind (.op1 .snd c) fun g =>
    .bind (.op1 .fst g) fun n =>
    .bind (mkWindow n pts) fun w =>
    .bind (.op2 .pair w c) fun wc =>
    .bind (.op2 .pair xy wc) fun I =>
    sub I

/-- Process the windows of `os` sequentially, starting from the coset `c`. -/
def seqProg (sub : var (Ty.inst D) → Prog S rec var (Ty.answer D)) (xy : var Ty.strs)
    (c : var (Ty.coset D)) (os : var (.list (.list .nat))) : Prog S rec var (Ty.answer D) :=
  .bind (.op1 .some c) fun init => .foldList os init fun acc pts => seqStep sub xy acc pts

section Specs

variable {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop} {sub : InstData D → Prog S (a, b) Ty.denote (Ty.answer D)}
  {xy : StrData × StrData} {n : ℕ} {os : List (List ℕ)} {Cw : List ℕ → ℕ} {s : ℕ}

/-- The sub-solver hypothesis of the sequential reduction: correct on the window of each
`o ∈ os`, inside any valid coset of degree `n` whose group lies in `G` and has at most `sIn`
generators (the cosets that actually arise do). -/
abbrev SeqSub (X : Ctx S) (body : a.denote → Prog S (a, b) Ty.denote b)
    (DV : ℕ → GensData → D.denote → Prop) (sub : InstData D → Prog S (a, b) Ty.denote (Ty.answer D))
    (xy : StrData × StrData) (n : ℕ) (os : List (List ℕ)) (Cw : List ℕ → ℕ) (s sIn : ℕ)
    (G : Subgroup (Perm (Fin n))) : Prop :=
  SubSolves X body DV sub
    (fun I => I.1 = xy ∧ I.Valid DV ∧ I.degree = n ∧ (∃ o ∈ os, I.2.1 = WinData.ofPoints n o) ∧
      I.2.2.2.gens.length ≤ sIn ∧ GensData.denote n I.2.2.2.gens ≤ G)
    (fun I => Cw I.2.1.1) s

/-- The per-window cost bound of the sequential reduction. -/
def seqCost (n : ℕ) (Cw : List ℕ → ℕ) (o : List ℕ) : ℕ := Cw o + 2 * n + 5 * o.length + 13

private theorem seq_fold {G : Subgroup (Perm (Fin n))} {σ : Perm (Fin n)} {s₀ : ℕ}
    (hos : ∀ o ∈ os, o.Nodup ∧ (∀ i ∈ o, i < n) ∧ IsInvariant G (ptsSet n o))
    (hsub : SeqSub X body DV sub xy n os Cw s (max s s₀) G) :
    ∀ (os' : List (List ℕ)), (∀ o ∈ os', o ∈ os) → ∀ (acc : AnswerData D) (Wd : Set (Fin n)),
      IsInvariant G Wd → AnsOK DV n Wd σ G (xy.1.denote n) (xy.2.denote n) acc →
      (∀ c : CosetData D, acc = some c → c.2.gens.length ≤ max s s₀) →
      ∃ ans : AnswerData D,
        RunsWithin X body (Prog.foldList (a := .list .nat) (b := Ty.answer D) os' acc
          fun acc pts => seqStep sub xy acc pts) ans ((os'.map (seqCost n Cw)).sum) ∧
        AnsOK DV n (Wd ∪ seqUnion (os'.map (ptsSet n))) σ G (xy.1.denote n) (xy.2.denote n) ans ∧
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ max s s₀
  | [], _, acc, Wd, _, hacc, hgens => ⟨acc, RunsWithin.foldList_nil, by simpa using hacc, hgens⟩
  | o :: os', hsubl, acc, Wd, hWd, hacc, hgens => by
    have ho := hos o (hsubl o List.mem_cons_self)
    have hrest : ∀ o' ∈ os', o' ∈ os := fun o' h => hsubl o' (List.mem_cons_of_mem _ h)
    have hWd' : IsInvariant G (Wd ∪ ptsSet n o) := hWd.union ho.2.2
    have hset : Wd ∪ seqUnion ((o :: os').map (ptsSet n)) =
        (Wd ∪ ptsSet n o) ∪ seqUnion (os'.map (ptsSet n)) := by
      simp [Set.union_assoc]
    rw [hset, List.map_cons, List.sum_cons]
    rcases acc with _ | ⟨τ, m, gs, d⟩
    · -- a previous step failed
      obtain ⟨ans, hr, hok, hg⟩ := seq_fold hos hsub os' hrest none (Wd ∪ ptsSet n o) hWd'
        (AnsOK.union_none hacc) (fun c h => by cases h)
      refine ⟨ans, ((RunsWithin.foldList_cons (RunsWithin.caseOption_none (RunsWithin.prim _ _))
        hr).mono ?_), hok, hg⟩
      simp [Prim.cost, seqCost]
    · -- solve the window of `o` inside the current coset
      obtain ⟨hτ, hm, hGv, _⟩ := id hacc
      change m = n at hm
      subst m
      have e := AnsOK.eq_aut hWd hacc
      simp only [GroupData.gens] at e
      have hinvH : IsInvariant (GensData.denote n gs) (ptsSet n o) := by
        rw [e]
        exact ho.2.2.aut hWd _
      have hP : (xy, WinData.ofPoints n o, τ, n, gs, d).1 = xy ∧
          InstData.Valid (D := D) (xy, WinData.ofPoints n o, τ, n, gs, d) DV ∧
          InstData.degree (D := D) (xy, WinData.ofPoints n o, τ, n, gs, d) = n ∧
          (∃ o' ∈ os, (WinData.ofPoints n o) = WinData.ofPoints n o') ∧
          gs.length ≤ max s s₀ ∧ GensData.denote n gs ≤ G :=
        ⟨rfl, ⟨WinData.valid_ofPoints ho.1 ho.2.1, hτ, hGv, hinvH⟩, rfl,
          ⟨o, hsubl o List.mem_cons_self, rfl⟩, hgens _ rfl, e ▸ aut_le hWd _⟩
      obtain ⟨ansO, hrO, hokO, hgO⟩ := hsub _ hP
      obtain ⟨ans, hr, hok, hg⟩ := seq_fold hos hsub os' hrest ansO (Wd ∪ ptsSet n o) hWd'
        (AnsOK.union_some hacc hokO) (fun c h => (hgO c h).trans (le_max_left _ _))
      refine ⟨ans, ?_, hok, hg⟩
      have hstep : RunsWithin X body (seqStep sub xy (some (τ, n, gs, d)) o) ansO
          (1 + (1 + (1 + ((2 * n + 5 * o.length + 7) + (1 + (1 + Cw o)))))) := by
        refine RunsWithin.caseOption_some ?_
        refine RunsWithin.bind (RunsWithin.prim _ _) ?_
        refine RunsWithin.bind (RunsWithin.prim _ _) ?_
        refine RunsWithin.bind (RunsWithin.mkWindow _ _) ?_
        refine RunsWithin.bind (RunsWithin.prim _ _) ?_
        refine RunsWithin.bind (RunsWithin.prim _ _) ?_
        exact hrO
      refine (RunsWithin.foldList_cons (f := fun acc pts => seqStep sub xy acc pts) hstep hr).mono
        ?_
      simp only [seqCost]
      omega

/-- **Sequential reduction.** -/
theorem RunsWithin.seqProg {σd : PermData} {Gd : GroupData D.denote} (hn : Gd.degree = n)
    (hσ : σd.Valid n) (hGv : GroupValid DV n Gd.gens Gd.data)
    (hos : ∀ o ∈ os, o.Nodup ∧ (∀ i ∈ o, i < n) ∧
      IsInvariant (GensData.denote n Gd.gens) (ptsSet n o))
    (hsub : SeqSub X body DV sub xy n os Cw s (max s Gd.gens.length) (GensData.denote n Gd.gens)) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Programs.seqProg sub xy (σd, Gd) os) ans
        (1 + (os.map (seqCost n Cw)).sum) ∧
      AnsOK DV n (seqUnion (os.map (ptsSet n))) (PermData.denote n σd)
        (GensData.denote n Gd.gens) (xy.1.denote n) (xy.2.denote n) ans ∧
      ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ max s Gd.gens.length := by
  obtain ⟨ans, hr, hok, hg⟩ := seq_fold (s₀ := Gd.gens.length) (σ := PermData.denote n σd) hos
    hsub os (fun _ h => h) (some (σd, Gd)) ∅ (isInvariant_empty _)
    (AnsOK.empty_window hσ hn hGv) (fun c h => by cases h; exact le_max_right _ _)
  exact ⟨ans, RunsWithin.bind (RunsWithin.prim _ _) hr, by simpa using hok, hg⟩

end Specs

/-- An exact orbit partition of a window supplies the hypotheses of the sequential
reduction, and its windows cover the window. -/
theorem seqInputs_of_isOrbitPartition {n : ℕ} {G : Subgroup (Perm (Fin n))} {w : WinData}
    (hw : w.Valid n) {os : List (List ℕ)} (hos : IsOrbitPartition G w os) :
    (∀ o ∈ os, o.Nodup ∧ (∀ i ∈ o, i < n) ∧ IsInvariant G (ptsSet n o)) ∧
      seqUnion (os.map (ptsSet n)) = w.denote n := by
  obtain ⟨hperm, hblocks⟩ := hos
  have hnd : os.flatten.Nodup := hperm.nodup_iff.2 hw.nodup
  have hmem : ∀ i, i ∈ os.flatten ↔ i ∈ w.1 := fun i => hperm.mem_iff
  refine ⟨fun o ho => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (List.nodup_flatten.1 hnd).1 o ho
  · intro i hi
    exact hw.lt i ((hmem i).1 (List.mem_flatten.2 ⟨o, ho, hi⟩))
  · rintro g hg u hu
    have hu' : u.val ∈ o := hu
    have := ((hblocks o ho).2 u.val hu' (g u).val).2
      ⟨u.2, (g u).2, g, hg, rfl⟩
    exact this
  · ext u
    simp only [mem_seqUnion, List.mem_map, ptsSet]
    constructor
    · rintro ⟨_, ⟨o, ho, rfl⟩, hu⟩
      exact (hmem u.val).1 (List.mem_flatten.2 ⟨o, ho, hu⟩)
    · intro hu
      obtain ⟨o, ho, hu⟩ := List.mem_flatten.1 ((hmem u.val).2 hu)
      exact ⟨_, ⟨o, ho, rfl⟩, hu⟩

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_seqProg {sub₁ : var₁ (Ty.inst D) → Prog S rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog S rec var₂ (Ty.answer D)} (hsub : WfFun r Γ sub₁ sub₂)
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {c₁ : var₁ (Ty.coset D)} {c₂ : var₂ (Ty.coset D)}
    {os₁ : var₁ (.list (.list .nat))} {os₂ : var₂ (.list (.list .nat))}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hc : ⟨Ty.coset D, c₁, c₂⟩ ∈ Γ)
    (hos : ⟨.list (.list .nat), os₁, os₂⟩ ∈ Γ) :
    Prog.Wf r Γ (seqProg sub₁ xy₁ c₁ os₁) (seqProg sub₂ xy₂ c₂ os₂) := by
  unfold seqProg seqStep mkWindow mapList
  prog_wf
  all_goals exact hsub _ (fun y hy => by simp [hy]) _ _ (by simp)

end Wf

end GraphIso.Programs
