module

public import GraphIso.Sims.Orbits
public import Mathlib.Data.Finite.Perm

/-!
# Coset representatives by a search over cosets

For `K ≤ G = ⟨gs⟩`, `cosetRepsModel n gs ks` searches the left cosets of `K = ⟨ks⟩`: from the
identity, it multiplies each found representative `r` on the left by each generator, and
keeps `g r` unless `r'⁻¹ g r ∈ K` for a found `r'`, which is decided by sifting in the
complete table of `K` (`coveredB_iff`).

At the end the union of the found cosets is closed under left multiplication by the
generators, hence by `G` (`mul_mem_of_closed`, a finiteness argument), so the cosets cover `G`;
they are pairwise distinct by construction. So the representatives form a left transversal
(`cosetRepsModel_spec`). Distinct cosets inside `G` number at most `[G : K] = |G| / |K|`
(`length_le_index`), which bounds the iterations.
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv

/-! ### Closure of a union of cosets -/

/-- In a finite group, a set closed under left multiplication by the elements of `S` is closed
under left multiplication by the subgroup they generate. -/
theorem mul_mem_of_closed {M : Type*} [Group M] [Finite M] {S C : Set M}
    (h : ∀ s ∈ S, ∀ c ∈ C, s * c ∈ C) : ∀ x ∈ Subgroup.closure S, ∀ c ∈ C, x * c ∈ C := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one => intro c hc; rwa [one_mul]
  | mul x y _ _ ihx ihy => intro c hc; rw [mul_assoc]; exact ihx _ (ihy c hc)
  | inv x _ ih =>
    intro c hc
    have himg := image_eq_of_mapsTo_of_finite (Set.toFinite C) (g := Equiv.mulLeft x) ih
    rw [← himg] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    simpa using hc'

/-! ### The search -/

/-- Is `x` in the left coset `r' K` of a found representative `r'`? -/
def coveredB (n : ℕ) (TK : Table) (reps : List PermData) (x : PermData) : Bool :=
  reps.any fun r' => (sift n (frontBase n (emptyWin n)) TK 0 (r'.inv.mul x)).1 == n

/-- Visit `g r`: keep it unless its coset was found. -/
def repsVisit (n : ℕ) (TK : Table) (r : PermData) (acc : List PermData × List PermData)
    (g : PermData) : List PermData × List PermData :=
  if coveredB n TK acc.1 (g.mul r) then acc else (g.mul r :: acc.1, g.mul r :: acc.2)

/-- One iteration: pop a representative and visit its generator images. -/
def repsStep (n : ℕ) (TK : Table) (gs : GensData) (st : List PermData × List PermData) :
    Option (List PermData × List PermData) :=
  match st.2 with
  | [] => none
  | r :: rest => some (gs.foldl (repsVisit n TK r) (st.1, rest))

/-- Left coset representatives of `⟨ks⟩` in `⟨gs⟩`. -/
def cosetRepsModel (n : ℕ) (gs ks : GensData) : List PermData :=
  (iter (repsStep n (tableFor n (emptyWin n) ks).1 gs) (n.factorial + 1)
    ([PermData.one n], [PermData.one n])).1

section Search

variable {n : ℕ} {gs ks : GensData}

theorem coveredB_iff (hks : GensData.AllValid n ks) {reps : List PermData}
    (hreps : ∀ r ∈ reps, r.Valid n) {x : PermData} (hx : x.Valid n) :
    coveredB n (tableFor n (emptyWin n) ks).1 reps x = true ↔
      ∃ r' ∈ reps, (r'.denote n)⁻¹ * x.denote n ∈ GensData.denote n ks := by
  have hC := complete_tableFor (emptyWin_valid n) hks
  simp only [coveredB, List.any_eq_true, beq_iff_eq]
  refine exists_congr fun r' => and_congr_right fun hr' => ?_
  have hv := (hreps r' hr').inv.mul hx
  rw [sift_eq_iff hC.wf hv (Nat.zero_le n) (fun i hi => absurd hi (by omega)), hC.gamma_iff,
    PermData.denote_mul (hreps r' hr').inv hx, PermData.denote_inv (hreps r' hr')]
  simp

/-- The invariant of the coset search, without the closure condition. -/
structure RBInv (n : ℕ) (G K : Subgroup (Perm (Fin n))) (st : List PermData × List PermData) :
    Prop where
  valid : ∀ r ∈ st.1, r.Valid n ∧ r.denote n ∈ G
  distinct : st.1.Pairwise fun a b => (a.denote n)⁻¹ * b.denote n ∉ K
  queue_sub : ∀ r ∈ st.2, r ∈ st.1
  queue_nodup : st.2.Nodup

/-- The invariant: representatives not queued have every generator image's coset found. -/
structure RInv (n : ℕ) (gs ks : GensData) (st : List PermData × List PermData) : Prop
    extends RBInv n (GensData.denote n gs) (GensData.denote n ks) st where
  closed : ∀ r ∈ st.1, r ∉ st.2 → ∀ g ∈ gs,
    ∃ r' ∈ st.1, (r'.denote n)⁻¹ * (g.denote n * r.denote n) ∈ GensData.denote n ks
  one : PermData.one n ∈ st.1

/-- Pairwise distinct cosets of `K` inside `G` number at most `|G| / |K|`. -/
theorem length_le_index {G K : Subgroup (Perm (Fin n))} {reps : List PermData}
    (hv : ∀ r ∈ reps, r.Valid n ∧ r.denote n ∈ G)
    (hd : reps.Pairwise fun a b => (a.denote n)⁻¹ * b.denote n ∉ K) (hK : K ≤ G) :
    reps.length ≤ Nat.card G / Nat.card K := by
  rw [Nat.le_div_iff_mul_le Nat.card_pos]
  let f : Fin reps.length × K → G := fun p =>
    ⟨(reps.get p.1).denote n * p.2, mul_mem (hv _ (List.get_mem _ _)).2 (hK p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, κ⟩ ⟨j, κ'⟩ h
    simp only [f, Subtype.mk.injEq] at h
    have hij : ((reps.get i).denote n)⁻¹ * (reps.get j).denote n ∈ K := by
      have e : ((reps.get i).denote n)⁻¹ * (reps.get j).denote n =
          (κ : Perm (Fin n)) * (κ' : Perm (Fin n))⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
      rw [e]
      exact mul_mem κ.2 (inv_mem κ'.2)
    have hij' : i = j := by
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · exact List.pairwise_iff_getElem.1 hd i j i.2 j.2 hlt hij
      · have := List.pairwise_iff_getElem.1 hd j i j.2 i.2 hlt
        refine this ?_
        have := inv_mem hij
        simpa using this
    subst hij'
    have : κ = κ' := Subtype.ext (mul_left_cancel h)
    rw [this]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at this

/-- The potential of the coset search, for an index bound `I`. -/
def rpot (I : ℕ) (st : List PermData × List PermData) : ℕ := st.2.length + (I - st.1.length)

variable {G K : Subgroup (Perm (Fin n))}

theorem repsVisit_spec (hks : GensData.AllValid n ks) {r g : PermData} (hr : r.Valid n)
    (hrG : r.denote n ∈ G) (hg : g.Valid n) (hgG : g.denote n ∈ G)
    {acc : List PermData × List PermData}
    (hacc : RBInv n G (GensData.denote n ks) acc) :
    RBInv n G (GensData.denote n ks) (repsVisit n (tableFor n (emptyWin n) ks).1 r acc g) ∧
      (∃ r' ∈ (repsVisit n (tableFor n (emptyWin n) ks).1 r acc g).1,
        (r'.denote n)⁻¹ * (g.denote n * r.denote n) ∈ GensData.denote n ks) ∧
      ∃ new : List PermData,
        (repsVisit n (tableFor n (emptyWin n) ks).1 r acc g).1 = new ++ acc.1 ∧
        (repsVisit n (tableFor n (emptyWin n) ks).1 r acc g).2 = new ++ acc.2 := by
  have hx : (g.mul r).Valid n := hg.mul hr
  have hden : (g.mul r).denote n = g.denote n * r.denote n := PermData.denote_mul hg hr
  have hcov := coveredB_iff hks (fun r' hr' => (hacc.valid r' hr').1) hx
  unfold repsVisit
  by_cases hc : coveredB n (tableFor n (emptyWin n) ks).1 acc.1 (g.mul r) = true
  · simp only [hc, ↓reduceIte]
    obtain ⟨r', hr', hK⟩ := hcov.1 hc
    exact ⟨hacc, ⟨r', hr', hden ▸ hK⟩, [], rfl, rfl⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    have hnot : ∀ r' ∈ acc.1, (r'.denote n)⁻¹ * (g.mul r).denote n ∉ GensData.denote n ks :=
      fun r' hr' hK => hc (hcov.2 ⟨r', hr', hK⟩)
    have hnotin : g.mul r ∉ acc.1 := fun h => hnot _ h (by rw [inv_mul_cancel]; exact one_mem _)
    refine ⟨⟨fun r' hr' => ?_, List.pairwise_cons.2 ⟨fun a ha hK => hnot a ha ?_, hacc.distinct⟩,
      fun r' hr' => ?_, List.nodup_cons.2 ⟨fun h => hnotin (hacc.queue_sub _ h),
        hacc.queue_nodup⟩⟩, ⟨g.mul r, List.mem_cons_self, ?_⟩, [g.mul r], rfl, rfl⟩
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact ⟨hx, hden ▸ mul_mem hgG hrG⟩
      · exact hacc.valid r' hr'
    · simpa using inv_mem hK
    · rcases List.mem_cons.1 hr' with rfl | hr'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hacc.queue_sub r' hr')
    · rw [← hden, inv_mul_cancel]
      exact one_mem _

theorem reps_fold (hks : GensData.AllValid n ks) {r : PermData} (hr : r.Valid n)
    (hrG : r.denote n ∈ G) :
    ∀ (l : List PermData), (∀ g ∈ l, g.Valid n ∧ g.denote n ∈ G) →
      ∀ acc, RBInv n G (GensData.denote n ks) acc →
      RBInv n G (GensData.denote n ks)
          (l.foldl (repsVisit n (tableFor n (emptyWin n) ks).1 r) acc) ∧
        (∀ g ∈ l, ∃ r' ∈ (l.foldl (repsVisit n (tableFor n (emptyWin n) ks).1 r) acc).1,
          (r'.denote n)⁻¹ * (g.denote n * r.denote n) ∈ GensData.denote n ks) ∧
        ∃ new : List PermData,
          (l.foldl (repsVisit n (tableFor n (emptyWin n) ks).1 r) acc).1 = new ++ acc.1 ∧
          (l.foldl (repsVisit n (tableFor n (emptyWin n) ks).1 r) acc).2 = new ++ acc.2
  | [], _, acc, hacc => ⟨hacc, fun _ h => absurd h List.not_mem_nil, [], rfl, rfl⟩
  | g :: l, hl, acc, hacc => by
    obtain ⟨hg, hgG⟩ := hl g List.mem_cons_self
    obtain ⟨h₁, hcov, new₁, hr₁, hq₁⟩ := repsVisit_spec hks hr hrG hg hgG hacc
    obtain ⟨h₂, hcovs, new₂, hr₂, hq₂⟩ :=
      reps_fold hks hr hrG l (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) _ h₁
    rw [List.foldl_cons]
    refine ⟨h₂, fun g' hg' => ?_, new₂ ++ new₁, by rw [hr₂, hr₁, List.append_assoc],
      by rw [hq₂, hq₁, List.append_assoc]⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · obtain ⟨r', hr', hK⟩ := hcov
      exact ⟨r', by rw [hr₂]; exact List.mem_append_right _ hr', hK⟩
    · exact hcovs g' hg'

theorem repsStep_spec (hgs : GensData.AllValid n gs) (hks : GensData.AllValid n ks)
    (hK : GensData.denote n ks ≤ GensData.denote n gs) {st : List PermData × List PermData}
    (hI : RInv n gs ks st) {r : PermData} {rest : List PermData} (hq : st.2 = r :: rest) :
    ∃ st', repsStep n (tableFor n (emptyWin n) ks).1 gs st = some st' ∧ RInv n gs ks st' ∧
      rpot (Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks)) st' + 1 ≤
        rpot (Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks)) st := by
  obtain ⟨reps, queue⟩ := st
  simp only at hq
  subst hq
  have hrr := hI.queue_sub r List.mem_cons_self
  obtain ⟨hrv, hrG⟩ := hI.valid r hrr
  have h₀ : RBInv n (GensData.denote n gs) (GensData.denote n ks) (reps, rest) :=
    ⟨hI.valid, hI.distinct, fun q hq => hI.queue_sub q (List.mem_cons_of_mem _ hq),
      (List.nodup_cons.1 hI.queue_nodup).2⟩
  obtain ⟨h₁, hcov, new, hr', hq'⟩ := reps_fold hks hrv hrG gs
    (fun g hg => ⟨hgs g hg, GensData.mem_denote_of_mem hg⟩) _ h₀
  refine ⟨_, rfl, ⟨h₁, fun q hq hqn g hg => ?_, ?_⟩, ?_⟩
  · simp only [hr'] at hq ⊢
    simp only [hq'] at hqn
    rcases List.mem_append.1 hq with hq | hq
    · exact absurd (List.mem_append_left _ hq) hqn
    · by_cases hqr : q = r
      · subst hqr
        obtain ⟨r'', hr'', hK'⟩ := hcov g hg
        rw [hr'] at hr''
        exact ⟨r'', hr'', hK'⟩
      · have hnot : q ∉ r :: rest := by
          rw [List.mem_cons, not_or]
          exact ⟨hqr, fun h => hqn (List.mem_append_right _ h)⟩
        obtain ⟨r'', hr'', hK'⟩ := hI.closed q hq hnot g hg
        exact ⟨r'', List.mem_append_right _ hr'', hK'⟩
  · simp only [hr']
    exact List.mem_append_right _ hI.one
  · have hlen := length_le_index h₁.valid h₁.distinct hK
    simp only [rpot, hr', hq', List.length_append, List.length_cons] at hlen ⊢
    omega

theorem iter_repsStep (hgs : GensData.AllValid n gs) (hks : GensData.AllValid n ks)
    (hK : GensData.denote n ks ≤ GensData.denote n gs) :
    ∀ (m : ℕ) (st : List PermData × List PermData), RInv n gs ks st →
      rpot (Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks)) st < m →
      RInv n gs ks (iter (repsStep n (tableFor n (emptyWin n) ks).1 gs) m st) ∧
        (iter (repsStep n (tableFor n (emptyWin n) ks).1 gs) m st).2 = []
  | 0, _, _, hm => absurd hm (Nat.not_lt_zero _)
  | m + 1, st, hI, hm => by
    rcases hq : st.2 with _ | ⟨r, rest⟩
    · have hstep : repsStep n (tableFor n (emptyWin n) ks).1 gs st = none := by
        simp [repsStep, hq]
      simp only [iter, hstep]
      exact ⟨hI, hq⟩
    · obtain ⟨st', hstep, hI', hpot⟩ := repsStep_spec hgs hks hK hI hq
      simp only [iter, hstep]
      exact iter_repsStep hgs hks hK m st' hI' (by omega)

theorem card_le_factorial (G : Subgroup (Perm (Fin n))) : Nat.card G ≤ n.factorial := by
  have := Subgroup.card_le_of_le (le_top : G ≤ ⊤)
  rwa [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin] at this

/-- **The search returns a left transversal of `K` in `G`.** -/
theorem cosetRepsModel_spec (hgs : GensData.AllValid n gs) (hks : GensData.AllValid n ks)
    (hK : GensData.denote n ks ≤ GensData.denote n gs) :
    (∀ r ∈ cosetRepsModel n gs ks, r.Valid n) ∧
      IsLeftTransversal (GensData.denote n gs) (GensData.denote n ks)
        (fun i : Fin (cosetRepsModel n gs ks).length =>
          PermData.denote n ((cosetRepsModel n gs ks).get i)) := by
  set I := Nat.card (GensData.denote n gs) / Nat.card (GensData.denote n ks)
  have hI₀ : RInv n gs ks ([PermData.one n], [PermData.one n]) := by
    refine ⟨⟨fun r hr => ?_, List.pairwise_singleton _ _, fun r hr => hr,
      List.nodup_singleton _⟩, fun r hr hrq => absurd (by simpa using hr) (by simpa using hrq),
      List.mem_singleton_self _⟩
    rw [List.mem_singleton.1 hr]
    exact ⟨PermData.valid_one n, by rw [PermData.denote_one]; exact one_mem _⟩
  have hpot : rpot I ([PermData.one n], [PermData.one n]) < n.factorial + 1 := by
    have h₁ : I ≤ Nat.card (GensData.denote n gs) := Nat.div_le_self _ _
    have h₂ := card_le_factorial (GensData.denote n gs)
    have h₃ := Nat.factorial_pos n
    simp only [rpot, List.length_singleton]
    omega
  obtain ⟨hI, hq⟩ := iter_repsStep hgs hks hK _ _ hI₀ hpot
  have hrs : cosetRepsModel n gs ks = (iter (repsStep n (tableFor n (emptyWin n) ks).1 gs)
      (n.factorial + 1) ([PermData.one n], [PermData.one n])).1 := rfl
  rw [hrs]
  generalize iter (repsStep n (tableFor n (emptyWin n) ks).1 gs) (n.factorial + 1)
    ([PermData.one n], [PermData.one n]) = st at hI hq
  refine ⟨fun r hr => (hI.valid r hr).1, ⟨⟨fun i => (hI.valid _ (List.get_mem _ _)).2, ?_⟩, ?_⟩⟩
  · -- the found cosets cover `G`
    intro x hx
    let C : Set (Perm (Fin n)) :=
      {c | ∃ r ∈ st.1, (r.denote n)⁻¹ * c ∈ GensData.denote n ks}
    have hC : ∀ s ∈ GensData.denoteSet n gs, ∀ c ∈ C, s * c ∈ C := by
      rintro _ ⟨g, hg, rfl⟩ c ⟨r, hr, hrc⟩
      obtain ⟨r', hr', hK'⟩ := hI.closed r hr (by rw [hq]; exact List.not_mem_nil) g hg
      refine ⟨r', hr', ?_⟩
      have e : (r'.denote n)⁻¹ * (g.denote n * c) =
          ((r'.denote n)⁻¹ * (g.denote n * r.denote n)) * ((r.denote n)⁻¹ * c) := by group
      rw [e]
      exact mul_mem hK' hrc
    have h1 : (1 : Perm (Fin n)) ∈ C :=
      ⟨PermData.one n, hI.one, by rw [PermData.denote_one, inv_one, one_mul]; exact one_mem _⟩
    obtain ⟨r, hr, hrx⟩ := mul_one x ▸ mul_mem_of_closed hC x hx 1 h1
    obtain ⟨i, rfl⟩ := List.get_of_mem hr
    exact ⟨i, hrx⟩
  · -- distinct cosets
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact List.pairwise_iff_getElem.1 hI.distinct i j i.2 j.2 hlt hij
    · refine List.pairwise_iff_getElem.1 hI.distinct j i j.2 i.2 hlt ?_
      simpa using inv_mem hij

end Search

end GraphIso.Sims
