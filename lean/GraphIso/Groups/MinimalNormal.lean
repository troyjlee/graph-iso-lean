module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Order.SupIndep
public import Mathlib.Tactic.Group

/-!
# Nonabelian minimal normal subgroups

Relative to a subgroup `Y` of a finite group `X` (`Y = ⊤` for the usual notions):

* `NNormal N T`: `T` is a subgroup of `N` normalized by `N`.
* `IsMinNormal Y N`: `N` is a minimal normal subgroup of `Y`; every nontrivial `Y` has one
  (`exists_isMinNormal`).
* `exists_simple_factors`: a nonabelian minimal normal subgroup `N` of `Y` is the product of a
  finite set `F` of subgroups, the conjugates under `Y` of a minimal subgroup `T ≤ N` normalized
  by `N`. They are normalized by `N`, nonabelian simple, pairwise commuting and independent,
  their supremum is `N`, and conjugation by `Y` permutes them transitively.

The proof: two distinct conjugates of `T` meet trivially (their intersection is normalized by
`N` and lies in `T`'s conjugate), hence commute; `T` is nonabelian, otherwise `N` would be; the
intersection of a conjugate with the supremum of the others is normalized by `N`, and cannot be
the conjugate itself, which would then be abelian; a normal subgroup of a conjugate `A` is
normalized by `A` and centralized by the others, hence normalized by `N`.
-/

@[expose] public section

namespace GraphIso.Groups

variable {X : Type*} [Group X]

/-- The conjugate of `A` by `g`. -/
abbrev cj (g : X) (A : Subgroup X) : Subgroup X := A.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : X} {A : Subgroup X} : x ∈ cj g A ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [mul_assoc]⟩

theorem cj_mul (g h : X) (A : Subgroup X) : cj g (cj h A) = cj (g * h) A := by
  ext x
  simp only [mem_cj, mul_inv_rev]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem cj_one (A : Subgroup X) : cj 1 A = A := by
  ext x
  simp

theorem card_cj (g : X) (A : Subgroup X) : Nat.card (cj g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

/-- `T` is a subgroup of `N` normalized by `N`. -/
def NNormal (N T : Subgroup X) : Prop := T ≤ N ∧ ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T

theorem nnormal_self (N : Subgroup X) : NNormal N N :=
  ⟨le_rfl, fun _ hn _ ht => N.mul_mem (N.mul_mem hn ht) (N.inv_mem hn)⟩

theorem nnormal_top_iff {N : Subgroup X} : NNormal ⊤ N ↔ N.Normal :=
  ⟨fun h => ⟨fun t ht g => h.2 g trivial t ht⟩, fun h => ⟨le_top, fun g _ t ht =>
    h.conj_mem t ht g⟩⟩

theorem NNormal.cj_eq {Y T : Subgroup X} (hT : NNormal Y T) {g : X} (hg : g ∈ Y) :
    cj g T = T := by
  ext x
  rw [mem_cj]
  constructor
  · intro h
    have := hT.2 g hg _ h
    simpa [mul_assoc] using this
  · intro h
    have := hT.2 g⁻¹ (Y.inv_mem hg) x h
    simpa using this

theorem NNormal.cj {Y N T : Subgroup X} (hN : NNormal Y N) (hT : NNormal N T) {g : X}
    (hg : g ∈ Y) : NNormal N (cj g T) := by
  refine ⟨fun x hx => ?_, fun n hn t ht => ?_⟩
  · have := hN.2 g hg _ (hT.1 (mem_cj.1 hx))
    simpa [mul_assoc] using this
  · rw [mem_cj] at ht ⊢
    have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.2 g⁻¹ (Y.inv_mem hg) n hn
    have := hT.2 _ hn' _ ht
    simpa [mul_assoc] using this

theorem NNormal.inf {N A B : Subgroup X} (hA : NNormal N A) (hB : NNormal N B) :
    NNormal N (A ⊓ B) :=
  ⟨inf_le_left.trans hA.1, fun n hn t ht => ⟨hA.2 n hn t ht.1, hB.2 n hn t ht.2⟩⟩

theorem nnormal_iSup {N : Subgroup X} {ι : Type*} {A : ι → Subgroup X}
    (hA : ∀ i, NNormal N (A i)) : NNormal N (⨆ i, A i) := by
  refine ⟨iSup_le fun i => (hA i).1, fun n hn t ht => ?_⟩
  have : ⨆ i, A i ≤ cj n⁻¹ (⨆ i, A i) := by
    refine iSup_le fun i x hx => mem_cj.2 ?_
    simp only [inv_inv]
    exact Subgroup.mem_iSup_of_mem i ((hA i).2 n hn x hx)
  have := mem_cj.1 (this ht)
  simpa using this

theorem nnormal_iSup₂ {N : Subgroup X} {ι : Type*} {p : ι → Prop} {A : ι → Subgroup X}
    (hA : ∀ i, p i → NNormal N (A i)) : NNormal N (⨆ (i) (_ : p i), A i) := by
  refine ⟨iSup₂_le fun i hi => (hA i hi).1, fun n hn t ht => ?_⟩
  have : ⨆ (i) (_ : p i), A i ≤ cj n⁻¹ (⨆ (i) (_ : p i), A i) := by
    refine iSup₂_le fun i hi x hx => mem_cj.2 ?_
    simp only [inv_inv]
    exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi ((hA i hi).2 n hn x hx))
  have := mem_cj.1 (this ht)
  simpa using this

/-- `N` is a minimal normal subgroup of `Y`. -/
def IsMinNormal (Y N : Subgroup X) : Prop :=
  NNormal Y N ∧ N ≠ ⊥ ∧ ∀ M : Subgroup X, NNormal Y M → M ≤ N → M = ⊥ ∨ M = N

theorem exists_isMinNormal [Finite X] {Y : Subgroup X} (hY : Y ≠ ⊥) :
    ∃ N : Subgroup X, IsMinNormal Y N := by
  classical
  have hex : ∃ m, ∃ N : Subgroup X, NNormal Y N ∧ N ≠ ⊥ ∧ Nat.card N = m :=
    ⟨_, Y, nnormal_self Y, hY, rfl⟩
  obtain ⟨N, hN, hNb, hNc⟩ := Nat.find_spec hex
  refine ⟨N, hN, hNb, fun M hM hMN => ?_⟩
  by_cases hMb : M = ⊥
  · exact Or.inl hMb
  · right
    have := Nat.find_min' hex ⟨M, hM, hMb, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hMN (by omega)

/-! ### The factors -/

/-- **Nonabelian minimal normal subgroups are products of simple groups.** -/
theorem exists_simple_factors [Finite X] {Y N : Subgroup X} (hN : IsMinNormal Y N)
    (hna : ∃ x ∈ N, ∃ y ∈ N, x * y ≠ y * x) :
    ∃ F : Finset (Subgroup X),
      (∀ A ∈ F, NNormal N A) ∧
      (∀ A ∈ F, IsSimpleGroup A) ∧
      (∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) ∧
      iSupIndep (fun A : F => (A : Subgroup X)) ∧
      (⨆ A : F, (A : Subgroup X)) = N ∧
      (∀ g ∈ Y, ∀ A ∈ F, cj g A ∈ F) ∧
      (∀ A ∈ F, ∀ B ∈ F, ∃ g ∈ Y, cj g A = B) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨hNn, hNb, hNmin⟩ := hN
  -- a minimal nontrivial subgroup normalized by `N`
  have hex : ∃ m, ∃ T : Subgroup X, NNormal N T ∧ T ≠ ⊥ ∧ Nat.card T = m :=
    ⟨_, N, nnormal_self N, hNb, rfl⟩
  obtain ⟨T, hT, hTb, hTc⟩ := Nat.find_spec hex
  have hmin : ∀ U : Subgroup X, NNormal N U → U ≠ ⊥ → Nat.card T ≤ Nat.card U := fun U hU hUb =>
    hTc ▸ Nat.find_min' hex ⟨U, hU, hUb, rfl⟩
  let F : Finset (Subgroup X) := (Finset.univ.filter (· ∈ Y)).image fun g => cj g T
  have hmemF : ∀ A, A ∈ F ↔ ∃ g ∈ Y, cj g T = A := fun A => by simp [F]
  have hFn : ∀ A ∈ F, NNormal N A := fun A hA => by
    obtain ⟨g, hg, rfl⟩ := (hmemF A).1 hA
    exact hNn.cj hT hg
  have hFc : ∀ A ∈ F, Nat.card A = Nat.card T := fun A hA => by
    obtain ⟨g, -, rfl⟩ := (hmemF A).1 hA
    exact card_cj g T
  have hFb : ∀ A ∈ F, A ≠ ⊥ := fun A hA h => by
    have := hFc A hA
    rw [h, Subgroup.card_bot] at this
    exact hTb (Subgroup.eq_bot_of_card_eq T this.symm)
  -- minimality of each member
  have hFmin : ∀ A ∈ F, ∀ U, NNormal N U → U ≤ A → U = ⊥ ∨ U = A := fun A hA U hU hUA => by
    by_cases hUb : U = ⊥
    · exact Or.inl hUb
    · right
      exact Subgroup.eq_of_le_of_card_ge hUA (by rw [hFc A hA]; exact hmin U hU hUb)
  -- distinct members meet trivially and commute
  have hdisj : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → A ⊓ B = ⊥ := fun A hA B hB hAB => by
    rcases hFmin A hA (A ⊓ B) ((hFn A hA).inf (hFn B hB)) inf_le_left with h | h
    · exact h
    · exfalso
      have hle : A ≤ B := h ▸ inf_le_right
      exact hAB (Subgroup.eq_of_le_of_card_ge hle (by rw [hFc A hA, hFc B hB]))
  have hcomm : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := by
    intro A hA B hB hAB x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ A := by
      have := (hFn A hA).2 y ((hFn B hB).1 hy) x⁻¹ (A.inv_mem hx)
      have := A.mul_mem hx this
      simpa [mul_assoc] using this
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ B :=
      B.mul_mem ((hFn B hB).2 x ((hFn A hA).1 hx) y hy) (B.inv_mem hy)
    have : x * y * x⁻¹ * y⁻¹ ∈ A ⊓ B := ⟨h1, h2⟩
    rw [hdisj A hA B hB hAB, Subgroup.mem_bot] at this
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [this, one_mul]
  -- conjugation permutes the members, and the supremum is normal
  have hcjF : ∀ g ∈ Y, ∀ A ∈ F, cj g A ∈ F := fun g hg A hA => by
    obtain ⟨h, hh, rfl⟩ := (hmemF A).1 hA
    exact (hmemF _).2 ⟨g * h, Y.mul_mem hg hh, (cj_mul g h T).symm⟩
  have hTF : T ∈ F := (hmemF T).2 ⟨1, Y.one_mem, cj_one T⟩
  let S : Subgroup X := ⨆ A : F, (A : Subgroup X)
  have hSN : S ≤ N := iSup_le fun A => (hFn A A.2).1
  have hSn : NNormal Y S := by
    refine ⟨hSN.trans hNn.1, fun g hg x hx => ?_⟩
    have hle : S ≤ cj g⁻¹ S := by
      refine iSup_le fun A y hy => mem_cj.2 ?_
      have hm : cj g A ∈ F := hcjF g hg A A.2
      have : g * y * g⁻¹ ∈ cj g A := mem_cj.2 (by simpa [mul_assoc] using hy)
      simpa using Subgroup.mem_iSup_of_mem (⟨_, hm⟩ : F) this
    have := mem_cj.1 (hle hx)
    simpa using this
  have hSb : S ≠ ⊥ := fun h => hTb (le_bot_iff.1 (h ▸ le_iSup (fun A : F => (A : Subgroup X))
    ⟨T, hTF⟩))
  have hSeq : S = N := (hNmin S hSn hSN).resolve_left hSb
  -- transitivity
  have htrans : ∀ A ∈ F, ∀ B ∈ F, ∃ g ∈ Y, cj g A = B := by
    intro A hA B hB
    obtain ⟨a, ha, rfl⟩ := (hmemF A).1 hA
    obtain ⟨b, hb, rfl⟩ := (hmemF B).1 hB
    exact ⟨b * a⁻¹, Y.mul_mem hb (Y.inv_mem ha), by rw [cj_mul, inv_mul_cancel_right]⟩
  -- the members are nonabelian
  have hFna : ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := by
    intro A hA
    by_contra hA'
    push Not at hA'
    have hall : ∀ B ∈ F, ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
      intro B hB x hx y hy
      obtain ⟨g, -, rfl⟩ := htrans A hA B hB
      have := hA' _ (mem_cj.1 hx) _ (mem_cj.1 hy)
      calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
        _ = y * x := by group
    have hcen : S ≤ Subgroup.centralizer S := by
      refine iSup_le fun A => ?_
      rw [Subgroup.le_centralizer_iff]
      refine iSup_le fun B => fun y hy => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      by_cases hAB : (A : Subgroup X) = B
      · exact hall A A.2 x hx y (hAB ▸ hy)
      · exact hcomm A A.2 B B.2 hAB x hx y hy
    obtain ⟨x, hx, y, hy, hxy⟩ := hna
    rw [← hSeq] at hx hy
    exact hxy (Subgroup.mem_centralizer_iff.1 (hcen hy) x hx)
  -- independence
  have hind : iSupIndep (fun A : F => (A : Subgroup X)) := by
    rw [iSupIndep_def]
    intro A
    let P : Subgroup X := ⨆ (B : F) (_ : B ≠ A), (B : Subgroup X)
    have hPn : NNormal N P := nnormal_iSup₂ fun B _ => hFn B B.2
    rw [disjoint_iff]
    rcases hFmin A A.2 ((A : Subgroup X) ⊓ P) ((hFn A A.2).inf hPn) inf_le_left with h | h
    · exact h
    · exfalso
      have hAP : (A : Subgroup X) ≤ P := h ▸ inf_le_right
      have hPc : P ≤ Subgroup.centralizer (A : Subgroup X) := by
        refine iSup_le fun B => iSup_le fun hBA => fun y hy => ?_
        refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
        exact hcomm A A.2 B B.2 (fun e => hBA (Subtype.ext e.symm)) x hx y hy
      obtain ⟨x, hx, y, hy, hxy⟩ := hFna A A.2
      exact hxy (Subgroup.mem_centralizer_iff.1 (hPc (hAP hy)) x hx)
  -- each member is simple
  have hFs : ∀ A ∈ F, IsSimpleGroup A := by
    intro A hA
    have hnt : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 (hFb A hA)
    refine ⟨fun B hB => ?_⟩
    let B' : Subgroup X := B.map A.subtype
    have hB'A : B' ≤ A := Subgroup.map_subtype_le B
    let P : Subgroup X := ⨆ (C : F) (_ : (C : Subgroup X) ≠ A), (C : Subgroup X)
    have hNsup : N ≤ A ⊔ P := by
      rw [← hSeq]
      refine iSup_le fun C => ?_
      by_cases hC : (C : Subgroup X) = A
      · rw [hC]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le C hC le_rfl)
    have hAnorm : A ≤ Subgroup.normalizer (B' : Set X) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹, hB.conj_mem y hy ⟨a, ha⟩, by simp⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨⟨a, ha⟩⁻¹ * y * ⟨a, ha⟩, ?_, ?_⟩
        · have := hB.conj_mem y hy ⟨a, ha⟩⁻¹
          simpa using this
        · simp only [Subgroup.coe_subtype] at hyx ⊢
          simp [hyx, mul_assoc]
    have hPnorm : P ≤ Subgroup.normalizer (B' : Set X) := by
      refine iSup_le fun C => iSup_le fun hCA => fun c hc => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcx : ∀ y ∈ B', c * y * c⁻¹ = y := fun y hy => by
        rw [hcomm C C.2 A hA hCA c hc y (hB'A hy), mul_inv_cancel_right]
      constructor
      · intro hx
        rwa [hcx x hx]
      · intro hx
        have hxA : x ∈ A := by
          have := (hFn A hA).2 c⁻¹ ((hFn C C.2).1 (C.1.inv_mem hc)) _ (hB'A hx)
          simpa [mul_assoc] using this
        have : c * x * c⁻¹ = x := by
          rw [hcomm C C.2 A hA hCA c hc x hxA, mul_inv_cancel_right]
        rwa [this] at hx
    have hB'N : NNormal N B' := by
      refine ⟨hB'A.trans (hFn A hA).1, fun n hn t ht => ?_⟩
      have := (sup_le hAnorm hPnorm) (hNsup hn)
      exact (Subgroup.mem_normalizer_iff.1 this t).1 ht
    rcases hFmin A hA B' hB'N hB'A with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      have : (y : X) ∈ B' := ⟨y, hy, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).2 (Subtype.ext this)
    · right
      rw [eq_top_iff]
      intro y _
      have : (y : X) ∈ B' := by rw [h]; exact y.2
      obtain ⟨z, hz, hzy⟩ := this
      rwa [← Subtype.ext hzy]
  exact ⟨F, hFn, hFs, hFna, hcomm, hind, hSeq, hcjF, htrans⟩



end GraphIso.Groups
