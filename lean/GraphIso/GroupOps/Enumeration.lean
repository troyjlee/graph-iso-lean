module

public import GraphIso.Solver.Cost
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Set.Card

/-!
# The reference backend: enumeration (functional models)

The backend data of a group is the list of **all** its elements (`Ty.gens`). The data
invariant `refDV n gs el` says that `el` lists every element of `⟨gs⟩` exactly once, as valid
data.

Functional models of the four operations the solver uses:

* `generate`: `enumerate n gs`, a search from the identity closing under left multiplication
  by the generators and their inverses, with duplicate detection by scanning. The output
  group is given by all its elements, both as generators and as data.
* `stabilizer`: filter the elements fixing the point.
* `orbitTransversal`: one element for each image of the point.
* `orbits`: the orbits of the listed window points, by images under all elements.

`refOracle_meets` proves that these meet the exact contracts. The search is complete:
processed elements have all their generator and inverse successors recorded
(`ClosureInv.closed`), and each iteration processes exactly one new element, so `n!`
iterations suffice (`enumerate_spec`).
-/

@[expose] public section

namespace GraphIso.Enum

open Equiv Cost

/-! ### Membership by scanning -/

/-- Is `h` in the list, by forward-array comparison? -/
def memB (h : PermData) (l : List PermData) : Bool := l.any fun e => PermData.beq e h

theorem memB_iff {n : ℕ} {h : PermData} {l : List PermData} (hh : h.Valid n)
    (hl : GensData.AllValid n l) : memB h l = true ↔ h ∈ l := by
  simp only [memB, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hbeq⟩
    have := PermData.denote_injOn (hl e he) hh ((PermData.beq_iff (hl e he) hh).1 hbeq)
    exact this ▸ he
  · intro hmem
    exact ⟨h, hmem, (PermData.beq_iff hh hh).2 rfl⟩

/-! ### Counting valid elements of a subgroup -/

theorem length_le_card {n : ℕ} {G : Subgroup (Perm (Fin n))} {l : List PermData}
    (hv : GensData.AllValid n l) (hnd : l.Nodup) (hG : ∀ e ∈ l, PermData.denote n e ∈ G) :
    l.length ≤ Nat.card G := by
  have hinj : ∀ a ∈ l, ∀ b ∈ l, PermData.denote n a = PermData.denote n b → a = b :=
    fun a ha b hb h => PermData.denote_injOn (hv a ha) (hv b hb) h
  have hnd' : (l.map (PermData.denote n)).Nodup := hnd.map_on hinj
  have hsub : ((l.map (PermData.denote n)).toFinset : Set (Perm (Fin n))) ⊆ G := by
    intro π hπ
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hπ)
    exact hG e he
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', List.length_map,
    ← Nat.card_coe_set_eq] at this
  exact this

/-! ### Closure of a set under left multiplication -/

/-- A set containing `1` and closed under left multiplication by the generators and their
inverses contains the generated subgroup. -/
theorem closure_subset_of_closed {n : ℕ} {S F : Set (Perm (Fin n))} (h1 : 1 ∈ F)
    (hmul : ∀ π ∈ F, ∀ g ∈ S, g * π ∈ F ∧ g⁻¹ * π ∈ F) :
    (Subgroup.closure S : Set (Perm (Fin n))) ⊆ F := by
  intro π hπ
  have hπ' : π ∈ (Subgroup.closure S).toSubmonoid := hπ
  rw [Subgroup.closure_toSubmonoid] at hπ'
  suffices ∀ ρ ∈ F, π * ρ ∈ F by simpa using this 1 h1
  clear hπ
  induction hπ' using Submonoid.closure_induction with
  | mem x hx =>
    intro ρ hρ
    rcases hx with hx | hx
    · exact (hmul ρ hρ x hx).1
    · simpa using (hmul ρ hρ x⁻¹ hx).2
  | one => intro ρ hρ; simpa using hρ
  | mul x y _ _ hx hy =>
    intro ρ hρ
    rw [mul_assoc]
    exact hx _ (hy ρ hρ)

/-! ### The search -/

/-- Record `h` if it is new: in the found list and on the stack. -/
def insertNew (acc : List PermData × List PermData) (h : PermData) :
    List PermData × List PermData :=
  if memB h acc.1 then acc else (h :: acc.1, h :: acc.2)

/-- Process the popped element `f`: record `g * f` and `g⁻¹ * f` for every generator `g`. -/
def expand (gs : GensData) (acc : List PermData × List PermData) (f : PermData) :
    List PermData × List PermData :=
  gs.foldl (fun acc g => insertNew (insertNew acc (g.mul f)) (g.inv.mul f)) acc

/-- One iteration: pop an element and process it; `none` when the stack is empty. -/
def closureStep (gs : GensData) (st : List PermData × List PermData) :
    Option (List PermData × List PermData) :=
  match st.2 with
  | [] => none
  | f :: rest => some (expand gs (st.1, rest) f)

/-- Iterate the search with fuel. -/
def closureIter (gs : GensData) : ℕ → List PermData × List PermData → List PermData × List PermData
  | 0, st => st
  | k + 1, st =>
    match closureStep gs st with
    | none => st
    | some st' => closureIter gs k st'

/-- All elements of `⟨gs⟩`, starting from the identity of degree `n`. -/
def enumerate (n : ℕ) (gs : GensData) : List PermData :=
  (closureIter gs n.factorial ([PermData.one n], [PermData.one n])).1

section Search

variable {n : ℕ} {gs : GensData}

/-- The invariant of the search for the subgroup `⟨gs⟩`. -/
structure ClosureInv (n : ℕ) (gs : GensData) (st : List PermData × List PermData) : Prop where
  valid : GensData.AllValid n st.1
  nodup : st.1.Nodup
  mem : ∀ e ∈ st.1, PermData.denote n e ∈ GensData.denote n gs
  one : PermData.one n ∈ st.1
  stack_sub : ∀ e ∈ st.2, e ∈ st.1
  stack_nodup : st.2.Nodup
  closed : ∀ f ∈ st.1, f ∉ st.2 → ∀ g ∈ gs, g.mul f ∈ st.1 ∧ g.inv.mul f ∈ st.1

theorem closureInv_init :
    ClosureInv n gs ([PermData.one n], [PermData.one n]) where
  valid := fun e he => by
    rw [List.mem_singleton.1 he]
    exact PermData.valid_one n
  nodup := List.nodup_singleton _
  mem := by simp [PermData.denote_one, one_mem]
  one := List.mem_singleton_self _
  stack_sub := fun e he => he
  stack_nodup := List.nodup_singleton _
  closed := fun f hf hfs => absurd hf hfs

/-- The weaker invariant kept while processing one element. -/
structure PartInv (n : ℕ) (gs : GensData) (st : List PermData × List PermData) : Prop where
  valid : GensData.AllValid n st.1
  nodup : st.1.Nodup
  mem : ∀ e ∈ st.1, PermData.denote n e ∈ GensData.denote n gs
  stack_sub : ∀ e ∈ st.2, e ∈ st.1
  stack_nodup : st.2.Nodup

/-- `new` extends `old` by recording new elements, each also pushed on the stack. -/
structure Extends (old new : List PermData × List PermData) : Prop where
  found_sub : ∀ e ∈ old.1, e ∈ new.1
  stack_sub : ∀ e ∈ old.2, e ∈ new.2
  new_on_stack : ∀ e ∈ new.1, e ∈ old.1 ∨ e ∈ new.2
  stack_new : ∀ e ∈ new.2, e ∈ old.2 ∨ e ∉ old.1
  diff : new.1.length - new.2.length = old.1.length - old.2.length

theorem Extends.refl (st : List PermData × List PermData) : Extends st st :=
  ⟨fun _ h => h, fun _ h => h, fun _ h => Or.inl h, fun _ h => Or.inl h, rfl⟩

theorem Extends.trans {a b c : List PermData × List PermData} (h₁ : Extends a b)
    (h₂ : Extends b c) : Extends a c where
  found_sub e he := h₂.found_sub e (h₁.found_sub e he)
  stack_sub e he := h₂.stack_sub e (h₁.stack_sub e he)
  new_on_stack e he := by
    rcases h₂.new_on_stack e he with hb | hc
    · rcases h₁.new_on_stack e hb with ha | hb2
      · exact Or.inl ha
      · exact Or.inr (h₂.stack_sub e hb2)
    · exact Or.inr hc
  stack_new e he := by
    rcases h₂.stack_new e he with hb | hb
    · exact h₁.stack_new e hb
    · exact Or.inr fun ha => hb (h₁.found_sub e ha)
  diff := h₂.diff.trans h₁.diff

theorem PartInv.insertNew {st : List PermData × List PermData} (h : PartInv n gs st)
    {x : PermData} (hx : x.Valid n) (hxG : PermData.denote n x ∈ GensData.denote n gs) :
    PartInv n gs (Enum.insertNew st x) ∧ Extends st (Enum.insertNew st x) ∧
      x ∈ (Enum.insertNew st x).1 := by
  unfold Enum.insertNew
  cases hm : memB x st.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnot : x ∉ st.1 := fun hmem => by
      rw [(memB_iff hx h.valid).2 hmem] at hm
      cases hm
    refine ⟨⟨h.valid.cons hx, List.nodup_cons.2 ⟨hnot, h.nodup⟩, ?_, ?_, ?_⟩,
      ⟨fun e he => List.mem_cons_of_mem _ he, fun e he => List.mem_cons_of_mem _ he, ?_, ?_, ?_⟩,
      List.mem_cons_self⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hxG
      · exact h.mem e he
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h.stack_sub e he)
    · exact List.nodup_cons.2 ⟨fun hs => hnot (h.stack_sub x hs), h.stack_nodup⟩
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Or.inr List.mem_cons_self
      · exact Or.inl he
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Or.inr hnot
      · exact Or.inl he
    · simp only [List.length_cons]
      omega
  · simp only [↓reduceIte]
    exact ⟨h, Extends.refl st, (memB_iff hx h.valid).1 hm⟩

/-- Processing one popped element `f` over a list of generators. -/
theorem PartInv.expand (hgs : GensData.AllValid n gs) {f : PermData} (hf : f.Valid n)
    (hfG : PermData.denote n f ∈ GensData.denote n gs) :
    ∀ (gs' : GensData), (∀ g ∈ gs', g ∈ gs) → ∀ st, PartInv n gs st →
      PartInv n gs (Enum.expand gs' st f) ∧ Extends st (Enum.expand gs' st f) ∧
        ∀ g ∈ gs', g.mul f ∈ (Enum.expand gs' st f).1 ∧ g.inv.mul f ∈ (Enum.expand gs' st f).1
  | [], _, st, h => ⟨h, Extends.refl st, fun _ hg => absurd hg List.not_mem_nil⟩
  | g :: gs', hsub, st, h => by
    have hg := hgs g (hsub g List.mem_cons_self)
    have hgG : PermData.denote n g ∈ GensData.denote n gs :=
      GensData.mem_denote_of_mem (hsub g List.mem_cons_self)
    have h₁ := h.insertNew (hg.mul hf) (by
      rw [PermData.denote_mul hg hf]; exact mul_mem hgG hfG)
    have h₂ := h₁.1.insertNew (hg.inv.mul hf) (by
      rw [PermData.denote_mul hg.inv hf, PermData.denote_inv hg]
      exact mul_mem (inv_mem hgG) hfG)
    have ih := PartInv.expand hgs hf hfG gs' (fun g' hg' => hsub g' (List.mem_cons_of_mem _ hg'))
      _ h₂.1
    have hstep : Enum.expand (g :: gs') st f =
        Enum.expand gs' (Enum.insertNew (Enum.insertNew st (g.mul f)) (g.inv.mul f)) f := rfl
    rw [hstep]
    refine ⟨ih.1, (h₁.2.1.trans h₂.2.1).trans ih.2.1, fun g' hg' => ?_⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact ⟨ih.2.1.found_sub _ (h₂.2.1.found_sub _ h₁.2.2), ih.2.1.found_sub _ h₂.2.2⟩
    · exact ih.2.2 g' hg'

theorem ClosureInv.partInv {st : List PermData × List PermData} {f : PermData}
    {rest : List PermData} (h : ClosureInv n gs st) (hst : st.2 = f :: rest) :
    PartInv n gs (st.1, rest) where
  valid := h.valid
  nodup := h.nodup
  mem := h.mem
  stack_sub e he := h.stack_sub e (by rw [hst]; exact List.mem_cons_of_mem _ he)
  stack_nodup := by have := h.stack_nodup; rw [hst] at this; exact (List.nodup_cons.1 this).2

theorem length_le_of_subset_nodup {l₁ l₂ : List PermData} (h₁ : l₁.Nodup)
    (hsub : ∀ e ∈ l₁, e ∈ l₂) : l₁.length ≤ l₂.length :=
  (h₁.subperm hsub).length_le

/-- One iteration preserves the invariant and processes exactly one element. -/
theorem ClosureInv.step (hgs : GensData.AllValid n gs) {st : List PermData × List PermData}
    {f : PermData} {rest : List PermData} (h : ClosureInv n gs st) (hst : st.2 = f :: rest) :
    ClosureInv n gs (Enum.expand gs (st.1, rest) f) ∧
      (Enum.expand gs (st.1, rest) f).1.length - (Enum.expand gs (st.1, rest) f).2.length =
        st.1.length - st.2.length + 1 := by
  have hfmem : f ∈ st.1 := h.stack_sub f (by rw [hst]; exact List.mem_cons_self)
  have hp := h.partInv hst
  obtain ⟨hr, hext, hsucc⟩ := hp.expand hgs (h.valid f hfmem) (h.mem f hfmem) gs (fun _ h => h) _
  set r := Enum.expand gs (st.1, rest) f
  have hlen : st.2.length ≤ st.1.length := length_le_of_subset_nodup h.stack_nodup h.stack_sub
  refine ⟨⟨hr.valid, hr.nodup, hr.mem, hext.found_sub _ h.one, hr.stack_sub, hr.stack_nodup,
    ?_⟩, ?_⟩
  · intro x hx hxs g hg
    rcases hext.new_on_stack x hx with hxold | hxs'
    · by_cases hxf : x = f
      · subst hxf
        exact hsucc g hg
      · have hnot : x ∉ st.2 := by
          rw [hst]
          rintro (_ | ⟨_, hrest⟩)
          · exact hxf rfl
          · exact hxs (hext.stack_sub x hrest)
        have := h.closed x hxold hnot g hg
        exact ⟨hext.found_sub _ this.1, hext.found_sub _ this.2⟩
    · exact absurd hxs' hxs
  · rw [hext.diff]
    rw [hst] at hlen ⊢
    simp only [List.length_cons] at hlen ⊢
    omega

/-- With enough fuel the search empties its stack. -/
theorem closureIter_spec (hgs : GensData.AllValid n gs) :
    ∀ (fuel : ℕ) (st : List PermData × List PermData), ClosureInv n gs st →
      Nat.card (GensData.denote n gs) ≤ st.1.length - st.2.length + fuel →
      ClosureInv n gs (closureIter gs fuel st) ∧ (closureIter gs fuel st).2 = []
  | 0, st, h, hfuel => by
    refine ⟨h, ?_⟩
    have h1 := length_le_card h.valid h.nodup h.mem
    have h2 := length_le_of_subset_nodup h.stack_nodup h.stack_sub
    simp only [closureIter]
    exact List.eq_nil_of_length_eq_zero (by omega)
  | fuel + 1, st, h, hfuel => by
    rcases hst : st.2 with _ | ⟨f, rest⟩
    · have : closureIter gs (fuel + 1) st = st := by
        simp only [closureIter, closureStep, hst]
      rw [this]
      exact ⟨h, hst⟩
    · have hstep := h.step hgs hst
      have : closureIter gs (fuel + 1) st =
          closureIter gs fuel (Enum.expand gs (st.1, rest) f) := by
        simp only [closureIter, closureStep, hst]
      rw [this]
      exact closureIter_spec hgs fuel _ hstep.1 (by rw [hstep.2]; omega)

end Search

/-- The data invariant of the reference backend: `el` lists every element of `⟨gs⟩` exactly
once, as valid data. -/
def refDV (n : ℕ) (gs : GensData) (el : List PermData) : Prop :=
  GensData.AllValid n el ∧ el.Nodup ∧
    ∀ π, π ∈ GensData.denote n gs ↔ ∃ e ∈ el, PermData.denote n e = π

/-- **The search is exact**: it lists every element of `⟨gs⟩` exactly once. -/
theorem enumerate_spec {n : ℕ} {gs : GensData} (hgs : GensData.AllValid n gs) :
    refDV n gs (enumerate n gs) ∧ (enumerate n gs).length = Nat.card (GensData.denote n gs) := by
  have hcard : Nat.card (GensData.denote n gs) ≤ n.factorial := by
    have := Subgroup.card_le_of_le (le_top : GensData.denote n gs ≤ ⊤)
    rwa [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n),
      Fintype.card_fin] at this
  obtain ⟨hinv, hempty⟩ := closureIter_spec hgs n.factorial _ closureInv_init (by simpa using hcard)
  set r := closureIter gs n.factorial ([PermData.one n], [PermData.one n])
  have hall : ∀ π, π ∈ GensData.denote n gs ↔ ∃ e ∈ r.1, PermData.denote n e = π := by
    intro π
    constructor
    · intro hπ
      have hsub := closure_subset_of_closed (S := GensData.denoteSet n gs)
        (F := {π | ∃ e ∈ r.1, PermData.denote n e = π})
        ⟨PermData.one n, hinv.one, PermData.denote_one n⟩ (by
          rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
          have hc := hinv.closed f hf (by rw [hempty]; exact List.not_mem_nil) g hg
          have hgv := hgs g hg
          have hfv := hinv.valid f hf
          refine ⟨⟨_, hc.1, PermData.denote_mul hgv hfv⟩, ⟨_, hc.2, ?_⟩⟩
          rw [PermData.denote_mul hgv.inv hfv, PermData.denote_inv hgv])
      exact hsub hπ
    · rintro ⟨e, he, rfl⟩
      exact hinv.mem e he
  refine ⟨⟨hinv.valid, hinv.nodup, hall⟩, le_antisymm (length_le_card hinv.valid hinv.nodup
    hinv.mem) ?_⟩
  -- every element of the group is listed, so the group is no larger than the list
  have hsub : (GensData.denote n gs : Set (Perm (Fin n))) ⊆
      ((r.1.map (PermData.denote n)).toFinset : Set (Perm (Fin n))) := by
    intro π hπ
    obtain ⟨e, he, rfl⟩ := (hall π).1 hπ
    exact List.mem_toFinset.2 (List.mem_map_of_mem he)
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at this
  exact this.trans ((List.toFinset_card_le _).trans (by rw [List.length_map]; rfl))



/-- A group listed by its elements, as generators and data. -/
theorem refDV_self {n : ℕ} {gs : GensData} {el : List PermData} (h : refDV n gs el) :
    refDV n el el ∧ GensData.denote n el = GensData.denote n gs := by
  have hset : GensData.denoteSet n el = (GensData.denote n gs : Set (Perm (Fin n))) := by
    ext π
    exact ((h.2.2 π).trans (by simp [GensData.denoteSet])).symm
  have hden : GensData.denote n el = GensData.denote n gs := by
    rw [GensData.denote, hset, Subgroup.closure_eq]
  exact ⟨⟨h.1, h.2.1, fun π => by rw [hden]; exact h.2.2 π⟩, hden⟩

/-! ### Orbits as relations on positions -/

section SameOrbit

variable {n : ℕ} {G : Subgroup (Perm (Fin n))}

/-- With the elements listed, `SameOrbit` is reachability by a listed element. -/
theorem sameOrbit_iff {gs : GensData} {el : List PermData} (h : refDV n gs el) {u : ℕ}
    (hu : u < n) (j : ℕ) :
    SameOrbit (GensData.denote n gs) u j ↔ ∃ e ∈ el, get e.1 u = j := by
  constructor
  · rintro ⟨_, hj, g, hg, hgu⟩
    obtain ⟨e, he, rfl⟩ := (h.2.2 g).1 hg
    refine ⟨e, he, ?_⟩
    rw [← PermData.val_denote_apply (h.1 e he) ⟨u, hu⟩, hgu]
  · rintro ⟨e, he, rfl⟩
    have hv := h.1 e he
    exact ⟨hu, hv.fwd_lt u hu, PermData.denote n e, (h.2.2 _).2 ⟨e, he, rfl⟩,
      Fin.ext (PermData.val_denote_apply hv ⟨u, hu⟩)⟩

end SameOrbit

/-! ### Images without repetition -/

/-- Fold the images `f e` of the listed elements into `acc`, skipping repetitions. -/
def imgDedup (f : PermData → ℕ) (el : List PermData) (acc : List ℕ) : List ℕ :=
  el.foldl (fun l e => if l.contains (f e) then l else f e :: l) acc

theorem imgDedup_spec (f : PermData → ℕ) :
    ∀ (el : List PermData) (acc : List ℕ), acc.Nodup →
      (imgDedup f el acc).Nodup ∧ ∀ j, j ∈ imgDedup f el acc ↔ j ∈ acc ∨ ∃ e ∈ el, f e = j
  | [], acc, h => ⟨h, fun j => by simp [imgDedup]⟩
  | e :: el, acc, h => by
    have hstep : imgDedup f (e :: el) acc =
        imgDedup f el (if acc.contains (f e) then acc else f e :: acc) := rfl
    by_cases hc : acc.contains (f e) = true
    · have hs' : imgDedup f (e :: el) acc = imgDedup f el acc := by
        simp only [hstep, hc, ↓reduceIte]
      rw [hs']
      obtain ⟨h₁, h₂⟩ := imgDedup_spec f el acc h
      refine ⟨h₁, fun j => (h₂ j).trans ?_⟩
      have hfe : f e ∈ acc := by simpa using hc
      constructor
      · rintro (hj | ⟨e', he', rfl⟩)
        · exact Or.inl hj
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', rfl⟩
      · rintro (hj | ⟨e', he', rfl⟩)
        · exact Or.inl hj
        · rcases List.mem_cons.1 he' with rfl | he'
          · exact Or.inl hfe
          · exact Or.inr ⟨e', he', rfl⟩
    · have hs' : imgDedup f (e :: el) acc = imgDedup f el (f e :: acc) := by
        simp only [hstep, hc, Bool.false_eq_true, ↓reduceIte]
      rw [hs']
      have hfe : f e ∉ acc := by simpa using hc
      obtain ⟨h₁, h₂⟩ := imgDedup_spec f el (f e :: acc) (List.nodup_cons.2 ⟨hfe, h⟩)
      refine ⟨h₁, fun j => (h₂ j).trans ?_⟩
      simp only [List.mem_cons]
      constructor
      · rintro ((rfl | hj) | ⟨e', he', rfl⟩)
        · exact Or.inr ⟨e, Or.inl rfl, rfl⟩
        · exact Or.inl hj
        · exact Or.inr ⟨e', Or.inr he', rfl⟩
      · rintro (hj | ⟨e', he', rfl⟩)
        · exact Or.inl (Or.inr hj)
        · rcases he' with rfl | he'
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr ⟨e', he', rfl⟩

/-! ### Stabilizers -/

/-- The listed elements fixing `u`. -/
def stabElems (el : List PermData) (u : ℕ) : List PermData := el.filter fun e => get e.1 u == u

theorem stabElems_spec {n : ℕ} {gs : GensData} {el : List PermData} (h : refDV n gs el)
    {u : ℕ} (hu : u < n) :
    refDV n (stabElems el u) (stabElems el u) ∧
      GensData.denote n (stabElems el u) = pointStab (GensData.denote n gs) ⟨u, hu⟩ := by
  have hmem : ∀ e, e ∈ stabElems el u ↔ e ∈ el ∧ get e.1 u = u := by
    intro e; simp [stabElems]
  have hfix : ∀ e ∈ el, (get e.1 u = u ↔ PermData.denote n e ⟨u, hu⟩ = ⟨u, hu⟩) := by
    intro e he
    rw [Fin.ext_iff, PermData.val_denote_apply (h.1 e he)]
  have hiff : ∀ π, π ∈ pointStab (GensData.denote n gs) ⟨u, hu⟩ ↔
      ∃ e ∈ stabElems el u, PermData.denote n e = π := by
    intro π
    rw [mem_pointStab]
    constructor
    · rintro ⟨hπ, hπu⟩
      obtain ⟨e, he, rfl⟩ := (h.2.2 π).1 hπ
      exact ⟨e, (hmem e).2 ⟨he, (hfix e he).2 hπu⟩, rfl⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨he, heu⟩ := (hmem e).1 he
      exact ⟨(h.2.2 _).2 ⟨e, he, rfl⟩, (hfix e he).1 heu⟩
  have hvalid : GensData.AllValid n (stabElems el u) := fun e he => h.1 e ((hmem e).1 he).1
  have hden : GensData.denote n (stabElems el u) = pointStab (GensData.denote n gs) ⟨u, hu⟩ := by
    apply le_antisymm
    · rw [GensData.denote_le_iff]
      intro e he
      exact (hiff _).2 ⟨e, he, rfl⟩
    · intro π hπ
      obtain ⟨e, he, rfl⟩ := (hiff π).1 hπ
      exact GensData.mem_denote_of_mem he
  refine ⟨⟨hvalid, h.2.1.filter _, fun π => ?_⟩, hden⟩
  rw [hden]
  exact hiff π

/-! ### Subgroups by filtering -/

/-- Filtering the element list of `G` by a test that decides membership in `H ≤ G` lists `H`. -/
theorem refDV_filter {n : ℕ} {gs : GensData} {el : List PermData} (h : refDV n gs el)
    (p : PermData → Bool) {H : Subgroup (Perm (Fin n))} (hHG : H ≤ GensData.denote n gs)
    (hp : ∀ e ∈ el, p e = true ↔ PermData.denote n e ∈ H) :
    refDV n (el.filter p) (el.filter p) ∧ GensData.denote n (el.filter p) = H := by
  have hmem : ∀ e, e ∈ el.filter p ↔ e ∈ el ∧ p e = true := fun e => by simp
  have hiff : ∀ π, π ∈ H ↔ ∃ e ∈ el.filter p, PermData.denote n e = π := by
    intro π
    constructor
    · intro hπ
      obtain ⟨e, he, rfl⟩ := (h.2.2 π).1 (hHG hπ)
      exact ⟨e, (hmem e).2 ⟨he, (hp e he).2 hπ⟩, rfl⟩
    · rintro ⟨e, he, rfl⟩
      obtain ⟨he, hpe⟩ := (hmem e).1 he
      exact (hp e he).1 hpe
  have hvalid : GensData.AllValid n (el.filter p) := fun e he => h.1 e ((hmem e).1 he).1
  have hden : GensData.denote n (el.filter p) = H := by
    apply le_antisymm
    · rw [GensData.denote_le_iff]
      intro e he
      exact (hiff _).2 ⟨e, he, rfl⟩
    · intro π hπ
      obtain ⟨e, he, rfl⟩ := (hiff π).1 hπ
      exact GensData.mem_denote_of_mem he
  refine ⟨⟨hvalid, h.2.1.filter _, fun π => ?_⟩, hden⟩
  rw [hden]
  exact hiff π

/-! ### Pointwise stabilizers -/

/-- The listed elements fixing every listed point. -/
def kerElems (el : List PermData) (pts : List ℕ) : List PermData :=
  el.filter fun e => pts.all fun u => get e.1 u == u

theorem kerElems_spec {n : ℕ} {gs : GensData} {el : List PermData} (h : refDV n gs el)
    {w : WinData} (hw : w.Valid n) :
    refDV n (kerElems el w.1) (kerElems el w.1) ∧
      GensData.denote n (kerElems el w.1) =
        pointwiseStab (GensData.denote n gs) (w.denote n) := by
  refine refDV_filter h _ (pointwiseStab_le _ _) fun e he => ?_
  have hev := h.1 e he
  have hG : PermData.denote n e ∈ GensData.denote n gs := (h.2.2 _).2 ⟨e, he, rfl⟩
  simp only [List.all_eq_true, beq_iff_eq, mem_pointwiseStab, hG, true_and]
  constructor
  · intro hfix u hu
    exact Fin.ext ((PermData.val_denote_apply hev u).trans (hfix u hu))
  · intro hfix u hu
    have := congrArg Fin.val (hfix ⟨u, hw.lt u hu⟩ hu)
    rwa [PermData.val_denote_apply hev] at this

/-! ### Lifts -/

/-- Does `g` map the `j`-th window point to the `π' j`-th, for every `j`? -/
def mapsB (w : WinData) (g π' : PermData) : Bool :=
  (List.range w.1.length).all fun j =>
    get g.1 (get w.1.toArray j) == get w.1.toArray (get π'.1 j)

theorem mapsB_iff (w : WinData) (g π' : PermData) : mapsB w g π' = true ↔ MapsWindowBy w g π' := by
  simp only [mapsB, List.all_eq_true, List.mem_range, beq_iff_eq, get_toArray,
    MapsWindowBy]

/-- The first listed element restricting to `π'`, or the identity of degree `n`. -/
def liftModel (n : ℕ) (el : List PermData) (w : WinData) (π' : PermData) : PermData :=
  (el.find? fun e => mapsB w e π').getD (PermData.one n)

theorem liftModel_spec {n : ℕ} {gs : GensData} {el : List PermData} (h : refDV n gs el)
    {w : WinData} {π' : PermData}
    (hex : ∃ r, PermData.Valid n r ∧ PermData.denote n r ∈ GensData.denote n gs ∧
      MapsWindowBy w r π') :
    PermData.Valid n (liftModel n el w π') ∧
      PermData.denote n (liftModel n el w π') ∈ GensData.denote n gs ∧
      MapsWindowBy w (liftModel n el w π') π' := by
  obtain ⟨r, hr, hrG, hrm⟩ := hex
  obtain ⟨e, he, hre⟩ := (h.2.2 _).1 hrG
  have heq : e = r := PermData.denote_injOn (h.1 e he) hr hre
  subst heq
  have hfound : (el.find? fun e => mapsB w e π').isSome := by
    rw [List.find?_isSome]
    exact ⟨e, he, (mapsB_iff w e π').2 hrm⟩
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 hfound
  have hfm := List.mem_of_find?_eq_some hf
  have hfp := List.find?_some hf
  simp only [liftModel, hf, Option.getD_some]
  exact ⟨h.1 f hfm, (h.2.2 _).2 ⟨f, hfm, rfl⟩, (mapsB_iff w f π').1 hfp⟩

/-! ### Coset representatives -/

/-- Does `g` lie in the left `K`-coset of a kept representative? (`kl` lists `K`.) -/
def coveredB (kl acc : List PermData) (g : PermData) : Bool :=
  acc.any fun r => memB (r.inv.mul g) kl

/-- One step of the greedy search: keep `g` unless it is covered. -/
def repsStep (kl : List PermData) (acc : List PermData) (g : PermData) : List PermData :=
  if coveredB kl acc g then acc else g :: acc

/-- Greedy left coset representatives of `K` (listed by `kl`) in `G` (listed by `el`). -/
def repsModel (el kl : List PermData) : List PermData := el.foldl (repsStep kl) []

section Reps

variable {n : ℕ} {ks : GensData} {kl : List PermData}

theorem coveredB_iff (hkl : refDV n ks kl) {acc : List PermData} (hacc : GensData.AllValid n acc)
    {g : PermData} (hg : g.Valid n) :
    coveredB kl acc g = true ↔
      ∃ r ∈ acc, (PermData.denote n r)⁻¹ * PermData.denote n g ∈ GensData.denote n ks := by
  simp only [coveredB, List.any_eq_true]
  refine exists_congr fun r => and_congr_right fun hr => ?_
  have hv : (r.inv.mul g).Valid n := (hacc r hr).inv.mul hg
  rw [memB_iff hv hkl.1, ← PermData.denote_inv (hacc r hr),
    ← PermData.denote_mul (hacc r hr).inv hg]
  constructor
  · intro h
    exact (hkl.2.2 _).2 ⟨_, h, rfl⟩
  · intro h
    obtain ⟨e, he, hed⟩ := (hkl.2.2 _).1 h
    exact PermData.denote_injOn (hkl.1 e he) hv hed ▸ he

/-- The pairwise condition of a transversal, in list order. -/
def RepsApart (n : ℕ) (K : Subgroup (Perm (Fin n))) (a b : PermData) : Prop :=
  (PermData.denote n b)⁻¹ * PermData.denote n a ∉ K

/-- One step keeps the invariant: kept elements are listed and pairwise apart. -/
theorem repsStep_inv {el : List PermData} (hel : GensData.AllValid n el) (hkl : refDV n ks kl)
    {acc : List PermData} (hacc : ∀ r ∈ acc, r ∈ el)
    (hpw : acc.Pairwise (RepsApart n (GensData.denote n ks))) {g : PermData} (hg : g ∈ el) :
    (∀ r ∈ repsStep kl acc g, r ∈ el) ∧
      (repsStep kl acc g).Pairwise (RepsApart n (GensData.denote n ks)) := by
  have haccv : GensData.AllValid n acc := fun r hr => hel r (hacc r hr)
  unfold repsStep
  by_cases hc : coveredB kl acc g = true
  · simp only [hc, ↓reduceIte]
    exact ⟨hacc, hpw⟩
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun r hr => ?_, List.Pairwise.cons (fun r hr hin => hc ?_) hpw⟩
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact hg
      · exact hacc r hr
    · exact (coveredB_iff hkl haccv (hel g hg)).2 ⟨r, hr, hin⟩

/-- Kept elements are pairwise apart, hence distinct. -/
theorem nodup_of_repsApart {K : Subgroup (Perm (Fin n))} {l : List PermData}
    (h : l.Pairwise (RepsApart n K)) : l.Nodup :=
  h.imp fun {a b} hab heq => hab (by rw [heq, inv_mul_cancel]; exact K.one_mem)

theorem repsFold_spec {el : List PermData} (hel : GensData.AllValid n el) (hkl : refDV n ks kl) :
    ∀ (l acc : List PermData), (∀ g ∈ l, g ∈ el) → (∀ r ∈ acc, r ∈ el) →
      acc.Pairwise (RepsApart n (GensData.denote n ks)) →
      (∀ r ∈ l.foldl (repsStep kl) acc, r ∈ el) ∧
      (l.foldl (repsStep kl) acc).Pairwise (RepsApart n (GensData.denote n ks)) ∧
      (∀ r ∈ acc, r ∈ l.foldl (repsStep kl) acc) ∧
      ∀ g ∈ l, ∃ r ∈ l.foldl (repsStep kl) acc,
        (PermData.denote n r)⁻¹ * PermData.denote n g ∈ GensData.denote n ks
  | [], acc, _, hacc, hpw => ⟨hacc, hpw, fun _ h => h, fun _ h => absurd h (by simp)⟩
  | g :: l, acc, hl, hacc, hpw => by
    have hgel : g ∈ el := hl g List.mem_cons_self
    have haccv : GensData.AllValid n acc := fun r hr => hel r (hacc r hr)
    have hstep : (∀ r ∈ repsStep kl acc g, r ∈ el) ∧
        (repsStep kl acc g).Pairwise (RepsApart n (GensData.denote n ks)) ∧
        (∀ r ∈ acc, r ∈ repsStep kl acc g) ∧
        ∃ r ∈ repsStep kl acc g,
          (PermData.denote n r)⁻¹ * PermData.denote n g ∈ GensData.denote n ks := by
      unfold repsStep
      by_cases hc : coveredB kl acc g = true
      · simp only [hc, ↓reduceIte]
        exact ⟨hacc, hpw, fun _ h => h, (coveredB_iff hkl haccv (hel g hgel)).1 hc⟩
      · simp only [hc, Bool.false_eq_true, ↓reduceIte]
        refine ⟨fun r hr => ?_, ?_, fun r hr => List.mem_cons_of_mem _ hr,
          ⟨g, List.mem_cons_self, by simp⟩⟩
        · rcases List.mem_cons.1 hr with rfl | hr
          · exact hgel
          · exact hacc r hr
        · refine List.Pairwise.cons (fun r hr hin => hc ?_) hpw
          exact (coveredB_iff hkl haccv (hel g hgel)).2 ⟨r, hr, hin⟩
    obtain ⟨h₁, h₂, h₃, r₀, hr₀, hr₀g⟩ := hstep
    obtain ⟨i₁, i₂, i₃, i₄⟩ := repsFold_spec hel hkl l (repsStep kl acc g)
      (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')) h₁ h₂
    refine ⟨i₁, i₂, fun r hr => i₃ r (h₃ r hr), fun g' hg' => ?_⟩
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact ⟨r₀, i₃ r₀ hr₀, hr₀g⟩
    · exact i₄ g' hg'

/-- **The greedy representatives form a left transversal.** -/
theorem repsModel_spec {gs : GensData} {el : List PermData} (h : refDV n gs el)
    (hkl : refDV n ks kl) :
    (∀ r ∈ repsModel el kl, PermData.Valid n r) ∧
      IsLeftTransversal (GensData.denote n gs) (GensData.denote n ks)
        (fun i : Fin (repsModel el kl).length => PermData.denote n ((repsModel el kl).get i)) := by
  obtain ⟨h₁, h₂, -, h₄⟩ := repsFold_spec h.1 hkl el [] (fun _ h => h)
    (fun _ h => absurd h (by simp))
    List.Pairwise.nil
  have hmemG : ∀ r ∈ repsModel el kl, PermData.denote n r ∈ GensData.denote n gs :=
    fun r hr => (h.2.2 _).2 ⟨r, h₁ r hr, rfl⟩
  refine ⟨fun r hr => h.1 r (h₁ r hr), ⟨⟨fun i => hmemG _ (List.get_mem _ _), fun g hg => ?_⟩,
    fun i j hij => ?_⟩⟩
  · obtain ⟨e, he, rfl⟩ := (h.2.2 g).1 hg
    obtain ⟨r, hr, hrg⟩ := h₄ e he
    obtain ⟨i, rfl⟩ := List.get_of_mem hr
    exact ⟨i, hrg⟩
  · by_contra hne
    have hpw := List.pairwise_iff_getElem.1 h₂
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · apply hpw i j i.2 j.2 hlt
      have := inv_mem hij
      rw [mul_inv_rev, inv_inv] at this
      exact this
    · exact hpw j i j.2 i.2 hlt hij

end Reps

/-! ### Orbit transversals -/

/-- One pair `(e u, e)` for each image of `u` under a listed element. -/
def transModel (el : List PermData) (u : ℕ) : List (ℕ × PermData) :=
  el.foldl (fun acc e =>
    if (acc.map Prod.fst).contains (get e.1 u) then acc else (get e.1 u, e) :: acc) []

theorem transModel_fold (u : ℕ) :
    ∀ (el : List PermData) (acc : List (ℕ × PermData)), (acc.map Prod.fst).Nodup →
      let r := el.foldl (fun acc e =>
        if (acc.map Prod.fst).contains (get e.1 u) then acc else (get e.1 u, e) :: acc) acc
      (r.map Prod.fst).Nodup ∧ (∀ j, j ∈ r.map Prod.fst ↔ j ∈ acc.map Prod.fst ∨
        ∃ e ∈ el, get e.1 u = j) ∧ ∀ p ∈ r, p ∈ acc ∨ (p.2 ∈ el ∧ get p.2.1 u = p.1)
  | [], acc, h => ⟨h, fun j => by simp, fun p hp => Or.inl hp⟩
  | e :: el, acc, h => by
    intro r
    by_cases hc : (acc.map Prod.fst).contains (get e.1 u) = true
    · have hr : r = el.foldl (fun acc e => if (acc.map Prod.fst).contains (get e.1 u) then acc
          else (get e.1 u, e) :: acc) acc := by simp only [r, List.foldl_cons, hc, ↓reduceIte]
      obtain ⟨h₁, h₂, h₃⟩ := transModel_fold u el acc h
      rw [hr]
      have hfe : get e.1 u ∈ acc.map Prod.fst := by simpa using hc
      refine ⟨h₁, fun j => (h₂ j).trans ?_, fun p hp => (h₃ p hp).imp id fun h' =>
        ⟨List.mem_cons_of_mem _ h'.1, h'.2⟩⟩
      constructor
      · rintro (hj | ⟨e', he', rfl⟩)
        · exact Or.inl hj
        · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', rfl⟩
      · rintro (hj | ⟨e', he', rfl⟩)
        · exact Or.inl hj
        · rcases List.mem_cons.1 he' with rfl | he'
          · exact Or.inl hfe
          · exact Or.inr ⟨e', he', rfl⟩
    · have hr : r = el.foldl (fun acc e => if (acc.map Prod.fst).contains (get e.1 u) then acc
          else (get e.1 u, e) :: acc) ((get e.1 u, e) :: acc) := by
        simp only [r, List.foldl_cons, hc, Bool.false_eq_true, ↓reduceIte]
      have hfe : get e.1 u ∉ acc.map Prod.fst := by simpa using hc
      obtain ⟨h₁, h₂, h₃⟩ := transModel_fold u el ((get e.1 u, e) :: acc)
        (by simpa using List.nodup_cons.2 ⟨hfe, h⟩)
      rw [hr]
      refine ⟨h₁, fun j => (h₂ j).trans ?_, fun p hp => ?_⟩
      · simp only [List.map_cons, List.mem_cons]
        constructor
        · rintro ((rfl | hj) | ⟨e', he', rfl⟩)
          · exact Or.inr ⟨e, Or.inl rfl, rfl⟩
          · exact Or.inl hj
          · exact Or.inr ⟨e', Or.inr he', rfl⟩
        · rintro (hj | ⟨e', he', rfl⟩)
          · exact Or.inl (Or.inr hj)
          · rcases he' with rfl | he'
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr ⟨e', he', rfl⟩
      · rcases h₃ p hp with hp | hp
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact Or.inr ⟨List.mem_cons_self, rfl⟩
          · exact Or.inl hp
        · exact Or.inr ⟨List.mem_cons_of_mem _ hp.1, hp.2⟩

theorem transModel_spec {n : ℕ} {gs : GensData} {el : List PermData} (h : refDV n gs el)
    {u : ℕ} (hu : u < n) :
    ((transModel el u).map Prod.fst).Nodup ∧
      (∀ j, j ∈ (transModel el u).map Prod.fst ↔ SameOrbit (GensData.denote n gs) u j) ∧
      ∀ vr ∈ transModel el u, PermData.Valid n vr.2 ∧
        PermData.denote n vr.2 ∈ GensData.denote n gs ∧ get vr.2.1 u = vr.1 := by
  obtain ⟨h₁, h₂, h₃⟩ := transModel_fold u el [] List.nodup_nil
  refine ⟨h₁, fun j => (h₂ j).trans ?_, fun vr hvr => ?_⟩
  · rw [sameOrbit_iff h hu]
    simp
  · rcases h₃ vr hvr with hvr | ⟨hel, hget⟩
    · exact absurd hvr List.not_mem_nil
    · exact ⟨h.1 _ hel, (h.2.2 _).2 ⟨_, hel, rfl⟩, hget⟩

/-! ### Orbit partitions -/

/-- The orbit of `u`, without repetition. -/
def orbitPts (el : List PermData) (u : ℕ) : List ℕ := imgDedup (fun e => get e.1 u) el []

/-- The orbits of the listed points, in the order they are first met. -/
def orbitsModel (el : List PermData) (pts : List ℕ) : List (List ℕ) :=
  (pts.foldl (fun (acc : List ℕ × List (List ℕ)) u =>
    if acc.1.contains u then acc else (orbitPts el u ++ acc.1, orbitPts el u :: acc.2))
    ([], [])).2

section Orbits

variable {n : ℕ} {gs : GensData} {el : List PermData}

theorem orbitPts_spec (h : refDV n gs el) {u : ℕ} (hu : u < n) :
    (orbitPts el u).Nodup ∧ ∀ j, j ∈ orbitPts el u ↔ SameOrbit (GensData.denote n gs) u j := by
  obtain ⟨h₁, h₂⟩ := imgDedup_spec (fun e => get e.1 u) el [] List.nodup_nil
  refine ⟨h₁, fun j => (h₂ j).trans ?_⟩
  rw [sameOrbit_iff h hu]
  simp

/-- The invariant of the orbit fold. -/
structure OrbitsInv (n : ℕ) (gs : GensData) (w : WinData) (acc : List ℕ × List (List ℕ)) :
    Prop where
  flat : acc.1 = acc.2.flatten
  nodup : acc.1.Nodup
  sub : ∀ j ∈ acc.1, j ∈ w.1
  blocks : ∀ o ∈ acc.2, o ≠ [] ∧ ∀ i ∈ o, ∀ j, j ∈ o ↔ SameOrbit (GensData.denote n gs) i j

theorem orbits_fold (h : refDV n gs el) {w : WinData} (hw : w.Valid n)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∀ (pts : List ℕ), (∀ u ∈ pts, u ∈ w.1) → ∀ acc, OrbitsInv n gs w acc →
      let r := pts.foldl (fun (acc : List ℕ × List (List ℕ)) u =>
        if acc.1.contains u then acc else (orbitPts el u ++ acc.1, orbitPts el u :: acc.2)) acc
      OrbitsInv n gs w r ∧ (∀ u ∈ pts, u ∈ r.1) ∧ ∀ j ∈ acc.1, j ∈ r.1
  | [], _, acc, hacc => ⟨hacc, fun _ hu => absurd hu List.not_mem_nil, fun _ hj => hj⟩
  | u :: pts, hpts, acc, hacc => by
    intro r
    have huw := hpts u List.mem_cons_self
    have hun : u < n := hw.lt u huw
    have hrest : ∀ v ∈ pts, v ∈ w.1 := fun v hv => hpts v (List.mem_cons_of_mem _ hv)
    by_cases hc : acc.1.contains u = true
    · have hr : r = pts.foldl (fun (acc : List ℕ × List (List ℕ)) u =>
          if acc.1.contains u then acc else (orbitPts el u ++ acc.1, orbitPts el u :: acc.2))
          acc := by simp only [r, List.foldl_cons, hc, ↓reduceIte]
      rw [hr]
      obtain ⟨h₁, h₂, h₃⟩ := orbits_fold h hw hinv pts hrest acc hacc
      refine ⟨h₁, fun v hv => ?_, h₃⟩
      rcases List.mem_cons.1 hv with rfl | hv
      · exact h₃ _ (by simpa using hc)
      · exact h₂ v hv
    · have hr : r = pts.foldl (fun (acc : List ℕ × List (List ℕ)) u =>
          if acc.1.contains u then acc else (orbitPts el u ++ acc.1, orbitPts el u :: acc.2))
          (orbitPts el u ++ acc.1, orbitPts el u :: acc.2) := by
        simp only [r, List.foldl_cons, hc, Bool.false_eq_true, ↓reduceIte]
      rw [hr]
      have hnotu : u ∉ acc.1 := by simpa using hc
      obtain ⟨hond, horb⟩ := orbitPts_spec h hun
      -- the new orbit is disjoint from the covered points
      have hdisj : ∀ j ∈ orbitPts el u, j ∉ acc.1 := by
        intro j hj hjc
        rw [hacc.flat] at hjc
        obtain ⟨o, ho, hjo⟩ := List.mem_flatten.1 hjc
        have hb := (hacc.blocks o ho).2 j hjo
        have : u ∈ o := (hb u).2 (SameOrbit.symm ((horb j).1 hj))
        exact hnotu (hacc.flat ▸ List.mem_flatten.2 ⟨o, ho, this⟩)
      have hacc' : OrbitsInv n gs w (orbitPts el u ++ acc.1, orbitPts el u :: acc.2) := by
        refine ⟨by simp [hacc.flat], List.nodup_append.2 ⟨hond, hacc.nodup, ?_⟩, ?_, ?_⟩
        · intro a ha b hb hab
          subst hab
          exact hdisj a ha hb
        · intro j hj
          rcases List.mem_append.1 hj with hj | hj
          · exact SameOrbit.mem_of_invariant hinv ((horb j).1 hj) huw
          · exact hacc.sub j hj
        · intro o ho
          rcases List.mem_cons.1 ho with rfl | ho
          · refine ⟨List.ne_nil_of_mem ((horb u).2 (sameOrbit_refl hun)), fun i hi j => ?_⟩
            rw [horb j]
            have hui := (horb i).1 hi
            exact ⟨fun hj => SameOrbit.trans (SameOrbit.symm hui) hj,
              fun hj => SameOrbit.trans hui hj⟩
          · exact hacc.blocks o ho
      obtain ⟨h₁, h₂, h₃⟩ := orbits_fold h hw hinv pts hrest _ hacc'
      refine ⟨h₁, fun v hv => ?_, fun j hj => h₃ j (List.mem_append_right _ hj)⟩
      rcases List.mem_cons.1 hv with rfl | hv
      · exact h₃ _ (List.mem_append_left _ ((horb _).2 (sameOrbit_refl hun)))
      · exact h₂ v hv

/-- One step of the orbit fold keeps the invariant. -/
theorem orbits_step (h : refDV n gs el) {w : WinData} (hw : w.Valid n)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) {acc : List ℕ × List (List ℕ)}
    (hacc : OrbitsInv n gs w acc) {u : ℕ} (hu : u ∈ w.1) :
    OrbitsInv n gs w (if acc.1.contains u then acc
      else (orbitPts el u ++ acc.1, orbitPts el u :: acc.2)) := by
  have h₁ := (orbits_fold h hw hinv [u] (fun v hv => by
    rw [List.mem_singleton.1 hv]; exact hu) acc hacc).1
  simpa using h₁

theorem orbitsModel_spec (h : refDV n gs el) {w : WinData} (hw : w.Valid n)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    IsOrbitPartition (GensData.denote n gs) w (orbitsModel el w.1) := by
  obtain ⟨hI, hall, -⟩ := orbits_fold h hw hinv w.1 (fun _ h => h) ([], [])
    ⟨rfl, List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  refine ⟨?_, hI.blocks⟩
  rw [orbitsModel, ← hI.flat]
  exact (List.perm_ext_iff_of_nodup hI.nodup hw.nodup).2 fun j => ⟨hI.sub j, hall j⟩

end Orbits

/-! ### The reference oracle -/

/-- The functional models of the reference backend. Operations the solver does not call
return default values. -/
def refOracle : Oracle (groupSig Ty.gens) := ⟨fun op x =>
  match op, x with
  | .generate, (n, gs) => (n, enumerate n gs, enumerate n gs)
  | .stabilizer, ((n, _, el), u) => (n, stabElems el u, stabElems el u)
  | .orbitTransversal, ((_, _, el), u) => transModel el u
  | .orbits, ((_, _, el), w) => orbitsModel el w.1
  | .kernel, ((n, _, el), w) => (n, kerElems el w.1, kerElems el w.1)
  | .lift, ((n, _, el), w, π') => liftModel n el w π'
  | .cosetReps, ((_, _, el), (_, _, kl)) => repsModel el kl
  | _, _ => Ty.default _⟩

/-- **The reference oracle meets the contracts of the operations the solver uses.** -/
theorem refOracle_meets : MeetsContractOn refDV Solver.solverOps refOracle := by
  rintro op x (rfl | rfl | rfl | rfl) hpre
  · obtain ⟨⟨n, gs, el⟩, w⟩ := x
    obtain ⟨⟨_, hdv⟩, hw, hinv⟩ := hpre
    exact orbitsModel_spec hdv hw hinv
  · obtain ⟨⟨n, gs, el⟩, u⟩ := x
    obtain ⟨⟨_, hdv⟩, hu⟩ := hpre
    obtain ⟨h₁, h₂⟩ := stabElems_spec hdv hu
    exact ⟨rfl, ⟨h₁.1, h₁⟩, fun hu' => h₂⟩
  · obtain ⟨⟨n, gs, el⟩, u⟩ := x
    obtain ⟨⟨_, hdv⟩, hu⟩ := hpre
    exact transModel_spec hdv hu
  · obtain ⟨n, gs⟩ := x
    obtain ⟨hdv, -⟩ := enumerate_spec hpre
    obtain ⟨h₁, h₂⟩ := refDV_self hdv
    exact ⟨rfl, ⟨h₁.1, h₁⟩, h₂⟩

/-- The operations of the restriction and block reductions, besides `generate`. -/
theorem refOracle_meets_kernel_lift :
    MeetsContractOn refDV (fun op => op = .kernel ∨ op = .lift ∨ op = .cosetReps) refOracle := by
  rintro op x (rfl | rfl | rfl) hpre
  · obtain ⟨⟨n, gs, el⟩, w⟩ := x
    obtain ⟨⟨_, hdv⟩, hw, -⟩ := hpre
    obtain ⟨h₁, h₂⟩ := kerElems_spec hdv hw
    exact ⟨rfl, ⟨h₁.1, h₁⟩, h₂⟩
  · obtain ⟨⟨n, gs, el⟩, w, π'⟩ := x
    obtain ⟨⟨_, hdv⟩, -, -, -, hex⟩ := hpre
    exact liftModel_spec hdv hex
  · obtain ⟨⟨n, gs, el⟩, ⟨n', ks, kl⟩⟩ := x
    obtain ⟨⟨_, hdv⟩, ⟨_, hkl⟩, rfl, -⟩ := hpre
    exact repsModel_spec hdv hkl

end GraphIso.Enum
