module

public import GraphIso.Sims.SiftProg
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.Linarith

/-!
# The orbit of a structure under permutation generators

Stage 14d, item 6 (`PLAN-14.md` §8), first half: a generic orbit enumeration, used for leaf
stabilizers (macro-step M4) and later for Align.

The setting: a structure type `τ`, permutation data acting on structures (`act`), an equality
test (`eqb`), and a decoding `dec` into a type on which `Perm (Fin k)` acts, with
`dec (act σ x) = σ • dec x` and `eqb x y = true ↔ dec x = dec y`. The generators `gd` generate
`H = GensData.denote k gd`.

* `orbitD act eqb k gd x₀`: the breadth-first closure from `x₀`. It returns the list `orb` of
  the structures found (starting with `x₀`, distinct after decoding) and, for every generator
  `i`, its index map on `orb`: the position of `gd[i] • orb[j]` in `orb`.
* `orbitD_spec`: `orb` decodes to the orbit of `dec x₀` under `H`, without repetition, and the
  index maps are correct; `orbitD_length_eq`: its length is the orbit's cardinality.
* `orbitProg actP eqP gd x₀`: the program, a `.loop` (no `.recur`), with membership tested by
  `eqP` against `orb`. `RunsWithin.orbitProg`: it returns `orbitD …` at cost at most
  `orbitCost r g cAct cEq`, for `r` the orbit size, `g` generators, and per-call costs
  `cAct` and `cEq` of the action and the equality test. `wf_orbitProg`: it is well-formed when
  `actP` and `eqP` are (`oc_WfFun2`).

The data hypotheses are bundled in `OrbitHyp`, relative to an invariant `J` of the structures
that the action preserves; the program costs are hypotheses on structures satisfying `J`.
-/

@[expose] public section

namespace GraphIso.SoJTree

open Equiv Cost Programs GraphIso.Sims

/-! ### The data model -/

section Model

variable {τ : Ty} (act : PermData → τ.denote → τ.denote) (eqb : τ.denote → τ.denote → Bool)

/-- One step of the search for `y`: the position, and the index found so far. -/
def oc_findStep (y : τ.denote) (acc : ℕ × Option ℕ) (z : τ.denote) : ℕ × Option ℕ :=
  (acc.1 + 1, match acc.2 with
    | some i => some i
    | none => if eqb y z then some acc.1 else none)

/-- The index of the first element of `orb` equal to `y` under `eqb`, if any. -/
def oc_find (y : τ.denote) (orb : List τ.denote) : Option ℕ :=
  (orb.foldl (oc_findStep eqb y) (0, none)).2

/-- The image of `x` under one generator: appended to the structures and the queue if it is
new; its index is recorded (in reverse order). -/
def oc_genStep (x : τ.denote) (acc : List τ.denote × (List τ.denote × List ℕ)) (σ : PermData) :
    List τ.denote × (List τ.denote × List ℕ) :=
  match oc_find eqb (act σ x) acc.1 with
  | some i => (acc.1, acc.2.1, i :: acc.2.2)
  | none => (acc.1 ++ [act σ x], acc.2.1 ++ [act σ x], acc.1.length :: acc.2.2)

/-- One iteration of the closure: process the head of the queue under every generator. The
state is the structures found, the queue, and the index rows of the processed structures (in
reverse order). -/
def oc_step (gd : List PermData) (st : List τ.denote × (List τ.denote × List (Array ℕ))) :
    Option (List τ.denote × (List τ.denote × List (Array ℕ))) :=
  match st.2.1 with
  | [] => none
  | x :: rest =>
    let r := gd.foldl (oc_genStep act eqb x) (st.1, rest, [])
    some (r.1, r.2.1, r.2.2.reverse.toArray :: st.2.2)

/-- The initial state. -/
def oc_init (x₀ : τ.denote) : List τ.denote × (List τ.denote × List (Array ℕ)) :=
  ([x₀], [x₀], [])

/-- The index maps from the rows: entry `j` of map `i` is entry `i` of row `j`. -/
def oc_imgs (g : ℕ) (rows : List (Array ℕ)) : List (List ℕ) :=
  (List.range g).map fun i => rows.map fun row => get row i

/-- **The orbit closure on data.** The fuel `k! + 1` exceeds the number of iterations, since
the orbit has at most `k!` elements. -/
def orbitD (k : ℕ) (gd : List PermData) (x₀ : τ.denote) : List τ.denote × List (List ℕ) :=
  let st := iter (oc_step act eqb gd) (k.factorial + 1) (oc_init x₀)
  (st.1, oc_imgs gd.length st.2.2.reverse)

end Model

/-! ### The programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type} {τ : Ty}

/-- Accumulators of the generator fold: structures, queue, indices (reversed). -/
abbrev oc_accTy (τ : Ty) : Ty := .prod (.list τ) (.prod (.list τ) (.list .nat))

/-- States of the closure loop: structures, queue, rows (reversed). -/
abbrev oc_stateTy (τ : Ty) : Ty := .prod (.list τ) (.prod (.list τ) (.list (.array .nat)))

/-- One step of the search for `y` (`oc_findStep`). -/
def oc_findBody (eqP : var τ → var τ → Prog S rec var .bool) (y : var τ)
    (acc : var (.prod .nat (.option .nat))) (z : var τ) :
    Prog S rec var (.prod .nat (.option .nat)) :=
  .bind (eqP y z) fun e => .bind (.op1 .fst acc) fun i => .bind (.op1 .snd acc) fun o =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' =>
  .caseOption o
    (.ite e (.bind (.op1 .some i) fun si => .op2 .pair i' si) (.op2 .pair i' o))
    fun _ => .op2 .pair i' o

/-- The index of `y` in `orb`, if any (`oc_find`). -/
def oc_findProg (eqP : var τ → var τ → Prog S rec var .bool) (y : var τ) (orb : var (.list τ)) :
    Prog S rec var (.option .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.none (a := .nat))) fun nn =>
  .bind (.op2 .pair z nn) fun acc₀ =>
  .bind (.foldList orb acc₀ fun acc w => oc_findBody eqP y acc w) fun fin => .op1 .snd fin

/-- The image of `x` under one generator (`oc_genStep`). -/
def oc_genBody (actP : var Ty.perm → var τ → Prog S rec var τ)
    (eqP : var τ → var τ → Prog S rec var .bool) (x : var τ) (acc : var (oc_accTy τ))
    (σ : var Ty.perm) : Prog S rec var (oc_accTy τ) :=
  .bind (actP σ x) fun y => .bind (.op1 .fst acc) fun orb => .bind (.op1 .snd acc) fun qr =>
  .bind (.op1 .fst qr) fun q => .bind (.op1 .snd qr) fun row =>
  .bind (oc_findProg eqP y orb) fun fo =>
  .caseOption fo
    (.bind (.op1 .length orb) fun len => .bind (.op0 (.nil (a := τ))) fun nl =>
      .bind (.op2 .cons y nl) fun ys => .bind (.op2 .append orb ys) fun orb' =>
      .bind (.op2 .append q ys) fun q' => .bind (.op2 .cons len row) fun row' =>
      .bind (.op2 .pair q' row') fun qr' => .op2 .pair orb' qr')
    fun i => .bind (.op2 .cons i row) fun row' => .bind (.op2 .pair q row') fun qr' =>
      .op2 .pair orb qr'

/-- One iteration of the closure loop (`oc_step`). -/
def oc_stepBody (actP : var Ty.perm → var τ → Prog S rec var τ)
    (eqP : var τ → var τ → Prog S rec var .bool) (gd : var Ty.gens) (st : var (oc_stateTy τ)) :
    Prog S rec var (.option (oc_stateTy τ)) :=
  .bind (.op1 .fst st) fun orb => .bind (.op1 .snd st) fun qr =>
  .bind (.op1 .fst qr) fun q => .bind (.op1 .snd qr) fun rows =>
  .caseList q (.op0 .none) fun x rest =>
    .bind (.op0 (.nil (a := .nat))) fun nl => .bind (.op2 .pair rest nl) fun qr₀ =>
    .bind (.op2 .pair orb qr₀) fun acc₀ =>
    .bind (.foldList gd acc₀ fun acc σ => oc_genBody actP eqP x acc σ) fun fin =>
    .bind (.op1 .fst fin) fun orb' => .bind (.op1 .snd fin) fun qr' =>
    .bind (.op1 .fst qr') fun q' => .bind (.op1 .snd qr') fun rr =>
    .bind (.op1 .reverse rr) fun row => .bind (.op1 .arrayOfList row) fun ra =>
    .bind (.op2 .cons ra rows) fun rows' => .bind (.op2 .pair q' rows') fun qr'' =>
    .bind (.op2 .pair orb' qr'') fun st' => .op1 .some st'

/-- **The orbit of `x₀` under the generators `gd`** (`orbitD`): the structures found and, for
every generator, its index map. -/
def orbitProg (actP : var Ty.perm → var τ → Prog S rec var τ)
    (eqP : var τ → var τ → Prog S rec var .bool) (gd : var Ty.gens) (x₀ : var τ) :
    Prog S rec var (.prod (.list τ) (.list (.list .nat))) :=
  .bind (.op0 (.nil (a := τ))) fun nl => .bind (.op2 .cons x₀ nl) fun l =>
  .bind (.op0 (.nil (a := .array .nat))) fun nr => .bind (.op2 .pair l nr) fun qr =>
  .bind (.op2 .pair l qr) fun st₀ =>
  .bind (.loop st₀ fun st => oc_stepBody actP eqP gd st) fun fin =>
  .bind (.op1 .fst fin) fun orb => .bind (.op1 .snd fin) fun qr' =>
  .bind (.op1 .snd qr') fun rr => .bind (.op1 .reverse rr) fun rows =>
  .bind (.op1 .length gd) fun g => .bind (.op1 .range g) fun is =>
  .bind (mapList is fun i => mapList rows fun row => .op2 .arrayGet row i) fun imgs =>
  .op2 .pair orb imgs

end Prog

/-! ### Correctness of the data model -/

section Find

variable {τ : Ty} {eqb : τ.denote → τ.denote → Bool}

theorem oc_foldl_find_some (y : τ.denote) :
    ∀ (l : List τ.denote) (n i : ℕ), (l.foldl (oc_findStep eqb y) (n, some i)).2 = some i
  | [], _, _ => rfl
  | _ :: l, n, i => oc_foldl_find_some y l (n + 1) i

theorem oc_foldl_find_none (y : τ.denote) :
    ∀ (l : List τ.denote) (n : ℕ), (l.foldl (oc_findStep eqb y) (n, none)).2 = none →
      ∀ z ∈ l, eqb y z = false
  | [], _, _ => by simp
  | z :: l, n, h => by
    rw [List.foldl_cons] at h
    by_cases hz : eqb y z = true
    · simp only [oc_findStep, hz, ite_true] at h
      rw [oc_foldl_find_some] at h
      exact absurd h (Option.some_ne_none _)
    · simp only [oc_findStep, hz] at h
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · simpa using hz
      · exact oc_foldl_find_none y l (n + 1) h w hw

theorem oc_foldl_find_some_spec (y : τ.denote) :
    ∀ (l : List τ.denote) (n i : ℕ), (l.foldl (oc_findStep eqb y) (n, none)).2 = some i →
      n ≤ i ∧ i < n + l.length ∧ eqb y (l.getD (i - n) default) = true
  | [], _, _, h => by simp at h
  | z :: l, n, i, h => by
    rw [List.foldl_cons] at h
    by_cases hz : eqb y z = true
    · simp only [oc_findStep, hz, ite_true] at h
      rw [oc_foldl_find_some] at h
      cases h
      simp [hz]
    · simp only [oc_findStep, hz] at h
      obtain ⟨h₁, h₂, h₃⟩ := oc_foldl_find_some_spec y l (n + 1) i h
      refine ⟨by omega, by simp only [List.length_cons]; omega, ?_⟩
      rw [show i - n = (i - (n + 1)) + 1 by omega]
      simpa using h₃

theorem oc_find_none {y : τ.denote} {orb : List τ.denote} (h : oc_find eqb y orb = none) :
    ∀ z ∈ orb, eqb y z = false :=
  oc_foldl_find_none y orb 0 h

theorem oc_find_some {y : τ.denote} {orb : List τ.denote} {i : ℕ}
    (h : oc_find eqb y orb = some i) : i < orb.length ∧ eqb y (orb.getD i default) = true := by
  obtain ⟨-, h₂, h₃⟩ := oc_foldl_find_some_spec y orb 0 i h
  exact ⟨by omega, by simpa using h₃⟩

end Find

section Spec

variable {τ : Ty} {act : PermData → τ.denote → τ.denote} {eqb : τ.denote → τ.denote → Bool}
  {k : ℕ} {O : Type*} [MulAction (Perm (Fin k)) O] {dec : τ.denote → O} {J : τ.denote → Prop}
  {gd : List PermData}

/-- A list of structures with distinct decodings, in the orbit of `y₀`, satisfying `J`. -/
def oc_Good (k : ℕ) {O : Type*} [MulAction (Perm (Fin k)) O] (dec : τ.denote → O)
    (J : τ.denote → Prop) (gd : List PermData) (y₀ : O) (orb : List τ.denote) : Prop :=
  (orb.map dec).Nodup ∧ ∀ z ∈ orb, dec z ∈ MulAction.orbit (GensData.denote k gd) y₀ ∧ J z

theorem oc_card_orbit_le (y₀ : O) :
    Nat.card (MulAction.orbit (GensData.denote k gd) y₀) ≤ k.factorial := by
  refine (Finite.card_range_le _).trans ((Subgroup.card_le_card_group _).trans ?_)
  rw [Nat.card_perm, Nat.card_fin]

theorem oc_good_length_le {y₀ : O} {orb : List τ.denote} (h : oc_Good k dec J gd y₀ orb) :
    orb.length ≤ Nat.card (MulAction.orbit (GensData.denote k gd) y₀) := by
  classical
  have hsub : (((orb.map dec).toFinset : Finset O) : Set O) ⊆
      MulAction.orbit (GensData.denote k gd) y₀ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
    exact (h.2 z hz).1
  have := Set.ncard_le_ncard hsub (Set.finite_range _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup h.1, List.length_map,
    ← Nat.card_coe_set_eq] at this
  exact this

theorem oc_smul_mem_orbit {y₀ y : O} {σ : PermData} (hσ : σ ∈ gd)
    (hy : y ∈ MulAction.orbit (GensData.denote k gd) y₀) :
    PermData.denote k σ • y ∈ MulAction.orbit (GensData.denote k gd) y₀ :=
  MulAction.mem_orbit_of_mem_orbit
    (⟨PermData.denote k σ, Subgroup.subset_closure ⟨σ, hσ, rfl⟩⟩ : GensData.denote k gd) hy

/-- The data hypotheses: the action is decoded, stays in `J`, and the test decides equality. -/
structure OrbitHyp (act : PermData → τ.denote → τ.denote) (eqb : τ.denote → τ.denote → Bool)
    (k : ℕ) {O : Type*} [MulAction (Perm (Fin k)) O] (dec : τ.denote → O) (J : τ.denote → Prop)
    (gd : List PermData) : Prop where
  dec_act : ∀ σ ∈ gd, ∀ x, J x → dec (act σ x) = PermData.denote k σ • dec x
  J_act : ∀ σ ∈ gd, ∀ x, J x → J (act σ x)
  eqb_iff : ∀ x y, J x → J y → (eqb x y = true ↔ dec x = dec y)

theorem oc_genStep_spec (hH : OrbitHyp act eqb k dec J gd) {y₀ : O} {x : τ.denote} (hx : J x)
    (hxo : dec x ∈ MulAction.orbit (GensData.denote k gd) y₀) {σ : PermData} (hσ : σ ∈ gd)
    {acc : List τ.denote × (List τ.denote × List ℕ)} (hacc : oc_Good k dec J gd y₀ acc.1) :
    ∃ news : List τ.denote, (oc_genStep act eqb x acc σ).1 = acc.1 ++ news ∧
      (oc_genStep act eqb x acc σ).2.1 = acc.2.1 ++ news ∧
      ∃ e, (oc_genStep act eqb x acc σ).2.2 = e :: acc.2.2 ∧
        e < (oc_genStep act eqb x acc σ).1.length ∧
        dec ((oc_genStep act eqb x acc σ).1.getD e default) = PermData.denote k σ • dec x ∧
        oc_Good k dec J gd y₀ (oc_genStep act eqb x acc σ).1 := by
  have hJy := hH.J_act σ hσ x hx
  have hdy := hH.dec_act σ hσ x hx
  rcases hf : oc_find eqb (act σ x) acc.1 with _ | i
  · have hne := oc_find_none hf
    simp only [oc_genStep, hf]
    refine ⟨[act σ x], rfl, rfl, acc.1.length, rfl, by simp, ?_, ?_⟩
    · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      exact hdy
    · refine ⟨?_, fun z hz => ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hacc.1, List.nodup_singleton _, ?_⟩
        intro a ha b hb
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 ha
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
        subst hb
        intro e
        have := (hH.eqb_iff _ _ hJy (hacc.2 z hz).2).2 e.symm
        rw [hne z hz] at this
        exact Bool.false_ne_true this
      · rcases List.mem_append.1 hz with hz | hz
        · exact hacc.2 z hz
        · rw [List.mem_singleton.1 hz, hdy]
          exact ⟨oc_smul_mem_orbit hσ hxo, hJy⟩
  · obtain ⟨hi, he⟩ := oc_find_some hf
    simp only [oc_genStep, hf]
    refine ⟨[], by simp, by simp, i, rfl, hi, ?_, hacc⟩
    have hmem : acc.1.getD i default ∈ acc.1 := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    rw [← hdy]
    exact ((hH.eqb_iff _ _ hJy (hacc.2 _ hmem).2).1 he).symm

theorem oc_genFold_spec (hH : OrbitHyp act eqb k dec J gd) {y₀ : O} {x : τ.denote} (hx : J x)
    (hxo : dec x ∈ MulAction.orbit (GensData.denote k gd) y₀) :
    ∀ (ls : List PermData) (acc : List τ.denote × (List τ.denote × List ℕ)),
      (∀ σ ∈ ls, σ ∈ gd) → oc_Good k dec J gd y₀ acc.1 →
      ∃ (news : List τ.denote) (es : List ℕ),
        (ls.foldl (oc_genStep act eqb x) acc).1 = acc.1 ++ news ∧
        (ls.foldl (oc_genStep act eqb x) acc).2.1 = acc.2.1 ++ news ∧
        (ls.foldl (oc_genStep act eqb x) acc).2.2 = es.reverse ++ acc.2.2 ∧
        es.length = ls.length ∧
        (∀ i < ls.length, es.getD i 0 < (ls.foldl (oc_genStep act eqb x) acc).1.length ∧
          dec ((ls.foldl (oc_genStep act eqb x) acc).1.getD (es.getD i 0) default) =
            PermData.denote k (ls.getD i default) • dec x) ∧
        oc_Good k dec J gd y₀ (ls.foldl (oc_genStep act eqb x) acc).1
  | [], acc, _, hacc => ⟨[], [], by simp, by simp, by simp, rfl, by simp, hacc⟩
  | σ :: ls, acc, hls, hacc => by
    obtain ⟨n₁, h₁, h₁', e, he, helt, hed, hg⟩ :=
      oc_genStep_spec hH hx hxo (hls σ List.mem_cons_self) hacc
    obtain ⟨n₂, es, h₂, h₂', h₂'', hlen, hes, hg'⟩ :=
      oc_genFold_spec hH hx hxo ls (oc_genStep act eqb x acc σ)
        (fun τ' h => hls τ' (List.mem_cons_of_mem _ h)) hg
    simp only [List.foldl_cons]
    refine ⟨n₁ ++ n₂, e :: es, by rw [h₂, h₁, List.append_assoc],
      by rw [h₂', h₁', List.append_assoc], by rw [h₂'', he]; simp, by simp [hlen], ?_, hg'⟩
    intro i hi
    rcases i with _ | i
    · simp only [List.getD_cons_zero, List.getD_cons_zero]
      rw [h₂]
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_append _ _ _ _ helt]
      exact hed
    · simp only [List.getD_cons_succ]
      exact hes i (by simp only [List.length_cons] at hi; omega)

/-- A set closed under the generators is closed under the group they generate. -/
theorem oc_closure_closed {S : Finset O} {gens : Set (Perm (Fin k))}
    (hS : ∀ g ∈ gens, ∀ y ∈ S, g • y ∈ S) :
    ∀ h ∈ Subgroup.closure gens, ∀ y ∈ S, h • y ∈ S := by
  classical
  have hinv : ∀ h : Perm (Fin k), (∀ y ∈ S, h • y ∈ S) → ∀ y ∈ S, h⁻¹ • y ∈ S := by
    intro h hh y hy
    have hsub : S.image (h • ·) ⊆ S := Finset.image_subset_iff.2 hh
    have hcard : (S.image (h • ·)).card = S.card :=
      Finset.card_image_of_injective _ (MulAction.injective h)
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard])
    rw [← heq] at hy
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
    simpa using hy'
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem g hg => exact hS g hg
  | one => simp
  | mul x y _ _ hx hy => intro z hz; rw [mul_smul]; exact hx _ (hy z hz)
  | inv x _ hx => exact hinv x hx

/-- **The invariant of the closure loop**: the structures found are good and start with `x₀`;
the queue is a suffix of them, after the processed ones; and the row of every processed
structure holds, for every generator, the index of its image. -/
structure oc_Inv (k : ℕ) {O : Type*} [MulAction (Perm (Fin k)) O] (dec : τ.denote → O)
    (J : τ.denote → Prop) (gd : List PermData) (x₀ : τ.denote)
    (st : List τ.denote × (List τ.denote × List (Array ℕ))) : Prop where
  good : oc_Good k dec J gd (dec x₀) st.1
  head : st.1[0]? = some x₀
  split : ∃ P, st.1 = P ++ st.2.1 ∧ P.length = st.2.2.length
  rows : ∀ j < st.2.2.length, ∀ i < gd.length,
    get (st.2.2.reverse.getD j #[]) i < st.1.length ∧
    dec (st.1.getD (get (st.2.2.reverse.getD j #[]) i) default) =
      PermData.denote k (gd.getD i default) • dec (st.1.getD j default)

theorem oc_init_inv {x₀ : τ.denote} (hx₀ : J x₀) : oc_Inv k dec J gd x₀ (oc_init x₀) := by
  refine ⟨⟨by simp [oc_init], fun z hz => ?_⟩, rfl, ⟨[], by simp [oc_init], rfl⟩,
    fun j hj => ?_⟩
  · rw [List.mem_singleton.1 hz]
    exact ⟨MulAction.mem_orbit_self _, hx₀⟩
  · simp [oc_init] at hj

theorem oc_step_nil {st : List τ.denote × (List τ.denote × List (Array ℕ))} (h : st.2.1 = []) :
    oc_step act eqb gd st = none := by
  simp [oc_step, h]

theorem oc_step_spec (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote}
    {st : List τ.denote × (List τ.denote × List (Array ℕ))} (hI : oc_Inv k dec J gd x₀ st)
    {x : τ.denote} {rest : List τ.denote} (hq : st.2.1 = x :: rest) :
    ∃ st' news, oc_step act eqb gd st = some st' ∧ st'.1 = st.1 ++ news ∧
      st'.2.1 = rest ++ news ∧ oc_Inv k dec J gd x₀ st' := by
  obtain ⟨P, hP, hPl⟩ := hI.split
  rw [hq] at hP
  have hxm : x ∈ st.1 := by rw [hP]; simp
  obtain ⟨hxo, hx⟩ := hI.good.2 x hxm
  obtain ⟨news, es, h₁, h₂, h₃, hlen, hes, hg⟩ :=
    oc_genFold_spec hH hx hxo gd (st.1, rest, []) (fun _ h => h) hI.good
  simp only at h₁ h₂ h₃
  simp only [List.append_nil] at h₃
  refine ⟨_, news, by simp only [oc_step, hq]; rfl, h₁, h₂, ?_⟩
  rw [h₃, List.reverse_reverse]
  have hxs : x :: rest = st.2.1 := hq.symm
  refine ⟨hg, ?_, ⟨P ++ [x], ?_, ?_⟩, ?_⟩
  · rw [h₁, List.getElem?_append_left (by rw [hP]; simp)]
    exact hI.head
  · rw [h₁, h₂, hP]
    simp
  · simp [hPl]
  · intro j hj i hi
    have hlt : st.1.length ≤ (List.foldl (oc_genStep act eqb x) (st.1, rest, []) gd).1.length := by
      rw [h₁]; simp
    rw [List.reverse_cons]
    simp only [List.length_cons] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by simpa using hj)]
      obtain ⟨hr₁, hr₂⟩ := hI.rows j hj i hi
      have hjP : j < st.1.length := by rw [hP]; simp; omega
      refine ⟨hr₁.trans_le hlt, ?_⟩
      rw [h₁, List.getD_append _ _ _ _ hr₁, List.getD_append _ _ _ _ hjP]
      exact hr₂
    · rw [List.getD_append_right _ _ _ _ (by simp), List.length_reverse, Nat.sub_self,
        List.getD_cons_zero, GraphIso.get_toArray]
      obtain ⟨he₁, he₂⟩ := hes i hi
      refine ⟨he₁, ?_⟩
      rw [he₂]
      congr 1
      rw [h₁, hP, ← hPl, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      simp

theorem oc_iter_inv (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} :
    ∀ (m : ℕ) (st : List τ.denote × (List τ.denote × List (Array ℕ))),
      oc_Inv k dec J gd x₀ st → oc_Inv k dec J gd x₀ (iter (oc_step act eqb gd) m st)
  | 0, _, hI => hI
  | m + 1, st, hI => by
    rcases hq : st.2.1 with _ | ⟨x, rest⟩
    · simp only [iter, oc_step_nil hq]
      exact hI
    · obtain ⟨st', news, hs, -, -, hI'⟩ := oc_step_spec hH hI hq
      simp only [iter, hs]
      exact oc_iter_inv hH m st' hI'

theorem oc_iter_done (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} :
    ∀ (m : ℕ) (st : List τ.denote × (List τ.denote × List (Array ℕ))),
      oc_Inv k dec J gd x₀ st →
      st.2.1.length + (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) -
        st.1.length) < m →
      oc_step act eqb gd (iter (oc_step act eqb gd) m st) = none
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, st, hI, h => by
    rcases hq : st.2.1 with _ | ⟨x, rest⟩
    · simp [iter, oc_step_nil hq]
    · obtain ⟨st', news, hs, h₁, h₂, hI'⟩ := oc_step_spec hH hI hq
      simp only [iter, hs]
      refine oc_iter_done hH m st' hI' ?_
      have hR := oc_good_length_le hI'.good
      rw [hq] at h
      rw [h₁] at hR
      rw [h₁, h₂]
      simp only [List.length_append, List.length_cons] at h hR ⊢
      omega

theorem oc_final_spec {x₀ : τ.denote} {st : List τ.denote × (List τ.denote × List (Array ℕ))}
    (hI : oc_Inv k dec J gd x₀ st) (hq : st.2.1 = []) :
    st.1[0]? = some x₀ ∧ (st.1.map dec).Nodup ∧
      (∀ y, (∃ z ∈ st.1, dec z = y) ↔ y ∈ MulAction.orbit (GensData.denote k gd) (dec x₀)) ∧
      (∀ z ∈ st.1, J z) ∧ (oc_imgs gd.length st.2.2.reverse).length = gd.length ∧
      ∀ i < gd.length, ((oc_imgs gd.length st.2.2.reverse).getD i []).length = st.1.length ∧
        ∀ j < st.1.length, ((oc_imgs gd.length st.2.2.reverse).getD i []).getD j 0 <
          st.1.length ∧
          dec (st.1.getD (((oc_imgs gd.length st.2.2.reverse).getD i []).getD j 0) default) =
            PermData.denote k (gd.getD i default) • dec (st.1.getD j default) := by
  classical
  obtain ⟨P, hP, hPl⟩ := hI.split
  rw [hq, List.append_nil] at hP
  have hlen : st.1.length = st.2.2.length := by rw [hP, hPl]
  have himg : ∀ i < gd.length, (oc_imgs gd.length st.2.2.reverse).getD i [] =
      st.2.2.reverse.map fun row => get row i := by
    intro i hi
    rw [List.getD_eq_getElem _ _ (by simpa [oc_imgs] using hi)]
    simp [oc_imgs]
  have hentry : ∀ i < gd.length, ∀ j < st.1.length,
      ((oc_imgs gd.length st.2.2.reverse).getD i []).getD j 0 =
        get (st.2.2.reverse.getD j #[]) i := by
    intro i hi j hj
    have hj' : j < st.2.2.reverse.length := by rw [List.length_reverse, ← hlen]; exact hj
    rw [himg i hi, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map,
      List.getD_eq_getElem _ _ hj']
  refine ⟨hI.head, hI.good.1, fun y => ⟨?_, ?_⟩, fun z hz => (hI.good.2 z hz).2, by
    simp [oc_imgs], fun i hi => ⟨by rw [himg i hi, List.length_map, List.length_reverse, hlen],
    fun j hj => ?_⟩⟩
  · rintro ⟨z, hz, rfl⟩
    exact (hI.good.2 z hz).1
  · intro hy
    set S : Finset O := (st.1.map dec).toFinset
    have hS : ∀ g ∈ GensData.denoteSet k gd, ∀ y ∈ S, g • y ∈ S := by
      rintro g ⟨σ, hσ, rfl⟩ y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hz
      have hi : gd.idxOf σ < gd.length := List.idxOf_lt_length_iff.2 hσ
      have hσi : gd.getD (gd.idxOf σ) default = σ := by
        rw [List.getD_eq_getElem _ _ hi, List.getElem_idxOf]
      obtain ⟨hr₁, hr₂⟩ := hI.rows j (by rw [← hlen]; exact hj) _ hi
      rw [hσi, List.getD_eq_getElem _ _ hj] at hr₂
      rw [← hr₂]
      refine List.mem_toFinset.2 (List.mem_map.2 ⟨_, ?_, rfl⟩)
      rw [List.getD_eq_getElem _ _ hr₁]
      exact List.getElem_mem hr₁
    have hx₀S : dec x₀ ∈ S := by
      refine List.mem_toFinset.2 (List.mem_map.2 ⟨x₀, ?_, rfl⟩)
      exact List.mem_of_getElem? hI.head
    obtain ⟨h, rfl⟩ := MulAction.mem_orbit_iff.1 hy
    have := oc_closure_closed hS (h : Perm (Fin k)) h.2 _ hx₀S
    obtain ⟨z, hz, he⟩ := List.mem_map.1 (List.mem_toFinset.1 this)
    exact ⟨z, hz, he.trans (Subgroup.smul_def h _).symm⟩
  · rw [hentry i hi j hj]
    exact hI.rows j (by rw [← hlen]; exact hj) i hi

/-- From the initial state, the loop stops within `|orbit| + 1` iterations. -/
theorem oc_init_done (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} (hx₀ : J x₀) :
    oc_step act eqb gd (iter (oc_step act eqb gd)
      (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) + 1) (oc_init x₀)) = none := by
  have hR := oc_good_length_le (oc_init_inv (gd := gd) (k := k) (dec := dec) hx₀).good
  refine oc_iter_done hH _ _ (oc_init_inv hx₀) ?_
  simp only [oc_init, List.length_singleton] at hR ⊢
  omega

theorem oc_iter_eq (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} (hx₀ : J x₀) {m : ℕ}
    (hm : Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) + 1 ≤ m) :
    iter (oc_step act eqb gd) m (oc_init x₀) = iter (oc_step act eqb gd)
      (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) + 1) (oc_init x₀) :=
  iter_eq_of_fix _ _ (oc_init_done hH hx₀) m hm

/-- The final state of the closure loop. -/
theorem oc_final_state (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} (hx₀ : J x₀) :
    let st := iter (oc_step act eqb gd)
      (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) + 1) (oc_init x₀)
    oc_Inv k dec J gd x₀ st ∧ st.2.1 = [] := by
  intro st
  have hI : oc_Inv k dec J gd x₀ st := oc_iter_inv hH _ _ (oc_init_inv hx₀)
  refine ⟨hI, ?_⟩
  rcases hq : st.2.1 with _ | ⟨x, rest⟩
  · rfl
  · obtain ⟨st', -, hs, -⟩ := oc_step_spec hH hI hq
    have := oc_init_done hH (gd := gd) hx₀
    rw [hs] at this
    exact absurd this (Option.some_ne_none _)

theorem orbitD_eq_iter (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} (hx₀ : J x₀) :
    orbitD act eqb k gd x₀ =
      ((iter (oc_step act eqb gd)
        (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) + 1) (oc_init x₀)).1,
       oc_imgs gd.length (iter (oc_step act eqb gd)
        (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) + 1)
          (oc_init x₀)).2.2.reverse) := by
  unfold orbitD
  rw [oc_iter_eq hH hx₀ (Nat.add_le_add_right (oc_card_orbit_le _) 1)]

/-- **The orbit closure is correct.** Writing `(orb, imgs) = orbitD act eqb k gd x₀` and
`r = |orb|`: `orb` starts with `x₀`; it decodes, without repetition, to the orbit of `dec x₀`
under `H = GensData.denote k gd`; its elements satisfy `J`; and for every generator `i` and
`j < r`, `imgs[i][j] < r` is the index of `gd[i] • orb[j]`. -/
theorem orbitD_spec (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} (hx₀ : J x₀) :
    (orbitD act eqb k gd x₀).1[0]? = some x₀ ∧ ((orbitD act eqb k gd x₀).1.map dec).Nodup ∧
      (∀ y, (∃ z ∈ (orbitD act eqb k gd x₀).1, dec z = y) ↔
        y ∈ MulAction.orbit (GensData.denote k gd) (dec x₀)) ∧
      (∀ z ∈ (orbitD act eqb k gd x₀).1, J z) ∧ (orbitD act eqb k gd x₀).2.length = gd.length ∧
      ∀ i < gd.length,
        ((orbitD act eqb k gd x₀).2.getD i []).length = (orbitD act eqb k gd x₀).1.length ∧
        ∀ j < (orbitD act eqb k gd x₀).1.length,
          ((orbitD act eqb k gd x₀).2.getD i []).getD j 0 < (orbitD act eqb k gd x₀).1.length ∧
          dec ((orbitD act eqb k gd x₀).1.getD (((orbitD act eqb k gd x₀).2.getD i []).getD j 0)
            default) = PermData.denote k (gd.getD i default) •
              dec ((orbitD act eqb k gd x₀).1.getD j default) := by
  rw [orbitD_eq_iter hH hx₀]
  obtain ⟨hI, hq⟩ := oc_final_state hH hx₀
  exact oc_final_spec hI hq

/-- **The orbit closure has the orbit's cardinality.** -/
theorem orbitD_length_eq (hH : OrbitHyp act eqb k dec J gd) {x₀ : τ.denote} (hx₀ : J x₀) :
    (orbitD act eqb k gd x₀).1.length =
      Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) := by
  classical
  obtain ⟨-, hnd, hiff, -⟩ := orbitD_spec hH hx₀
  have hset : (((orbitD act eqb k gd x₀).1.map dec).toFinset : Set O) =
      MulAction.orbit (GensData.denote k gd) (dec x₀) := by
    ext y
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_map]
    exact hiff y
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd,
    List.length_map]

end Spec

/-! ### Costs -/

section ProgSpec

/-- The cost bound of one iteration: `R` structures at most, `g` generators. -/
def oc_iterCost (R g cAct cEq : ℕ) : ℕ := g * (cAct + R * (cEq + 13) + 20) + 18

/-- **The cost bound of the orbit closure**: `r` structures in the orbit, `g` generators, and
per-call costs `cAct` and `cEq` of the action and the equality test. -/
def orbitCost (r g cAct cEq : ℕ) : ℕ :=
  (r + 1) * (g * (cAct + r * (cEq + 13) + 20) + 19) + g * (4 * r + 7) + r + 14

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}
  {τ : Ty} {act : PermData → τ.denote → τ.denote} {eqb : τ.denote → τ.denote → Bool}
  {k : ℕ} {O : Type*} [MulAction (Perm (Fin k)) O] {dec : τ.denote → O} {J : τ.denote → Prop}
  {gd : List PermData} {actP : PermData → τ.denote → Prog S (a, b) Ty.denote τ}
  {eqP : τ.denote → τ.denote → Prog S (a, b) Ty.denote .bool} {cAct cEq : ℕ}

theorem oc_caseOption_eq_none {a' t : Ty} {o : (Ty.option a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {c : ℕ} (ho : o = none) (h : RunsWithin X body p r c) :
    RunsWithin X body (.caseOption o p q) r (1 + c) := by
  subst ho
  exact RunsWithin.caseOption_none h

theorem oc_caseOption_eq_some {a' t : Ty} {o : (Ty.option a').denote} {v : a'.denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {c : ℕ} (ho : o = some v) (h : RunsWithin X body (q v) r c) :
    RunsWithin X body (.caseOption o p q) r (1 + c) := by
  subst ho
  exact RunsWithin.caseOption_some h

theorem oc_caseList_eq_nil {a' t : Ty} {l : (Ty.list a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t}
    {r : t.denote} {c : ℕ} (hl : l = []) (h : RunsWithin X body p r c) :
    RunsWithin X body (.caseList l p q) r (1 + c) := by
  subst hl
  exact RunsWithin.caseList_nil h

theorem oc_caseList_eq_cons {a' t : Ty} {l : (Ty.list a').denote} {x : a'.denote}
    {xs : List a'.denote} {p : Prog S (a, b) Ty.denote t}
    {q : a'.denote → List a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote} {c : ℕ}
    (hl : l = x :: xs) (h : RunsWithin X body (q x xs) r c) :
    RunsWithin X body (.caseList l p q) r (1 + c) := by
  subst hl
  exact RunsWithin.caseList_cons h

theorem RunsWithin.oc_findBody {y z : τ.denote}
    (he : RunsWithin X body (eqP y z) (eqb y z) cEq) (acc : ℕ × Option ℕ) :
    RunsWithin X body (SoJTree.oc_findBody eqP y acc z) (oc_findStep eqb y acc z) (cEq + 8) := by
  obtain ⟨i, o⟩ := acc
  rcases o with _ | j
  · by_cases hb : eqb y z = true
    · apply RunsWithin.mono
      case h =>
        run_step he
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with oc_caseOption_eq_none rfl _
        run_with RunsWithin.ite_pos hb _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, oc_findStep, hb]) le_rfl
      case hc => simp only [Prim.cost]; omega
    · apply RunsWithin.mono
      case h =>
        run_step he
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with oc_caseOption_eq_none rfl _
        run_with RunsWithin.ite_neg (Bool.eq_false_iff.2 hb) _
        exact RunsWithin.prim_le (by simp [Prim.eval, oc_findStep, hb]) le_rfl
      case hc => simp only [Prim.cost]; omega
  · apply RunsWithin.mono
    case h =>
      run_step he
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with oc_caseOption_eq_some rfl _
      exact RunsWithin.prim_le (by simp [Prim.eval, oc_findStep]) le_rfl
    case hc => simp only [Prim.cost]; omega

theorem RunsWithin.oc_findProg {y : τ.denote} {orb : List τ.denote}
    (he : ∀ z ∈ orb, RunsWithin X body (eqP y z) (eqb y z) cEq) :
    RunsWithin X body (SoJTree.oc_findProg eqP y orb) (oc_find eqb y orb)
      (orb.length * (cEq + 9) + 4) := by
  have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := τ)
    (b' := .prod .nat (.option .nat)) (f := fun acc w => SoJTree.oc_findBody eqP y acc w)
    (F := oc_findStep eqb y) (I := fun _ => True) (c := cEq + 8) orb (0, none)
    (fun acc _ z hz => ⟨RunsWithin.oc_findBody (he z hz) acc, trivial⟩) trivial).1
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, show cEq + 8 + 1 = cEq + 9 by omega]
    omega

theorem RunsWithin.oc_genBody {x : τ.denote} {σ : PermData}
    (ha : RunsWithin X body (actP σ x) (act σ x) cAct)
    {acc : List τ.denote × (List τ.denote × List ℕ)}
    (he : ∀ z ∈ acc.1, RunsWithin X body (eqP (act σ x) z) (eqb (act σ x) z) cEq) :
    RunsWithin X body (SoJTree.oc_genBody actP eqP x acc σ) (oc_genStep act eqb x acc σ)
      (cAct + acc.1.length * (cEq + 12) + acc.2.1.length + 17) := by
  obtain ⟨orb, q, row⟩ := acc
  simp only at he ⊢
  have hfind := RunsWithin.oc_findProg (X := X) (body := body) he
  rcases hf : oc_find eqb (act σ x) orb with _ | i
  · rw [show oc_genStep act eqb x (orb, q, row) σ =
      (orb ++ [act σ x], q ++ [act σ x], orb.length :: row) by simp [oc_genStep, hf]]
    apply RunsWithin.mono
    case h =>
      run_step ha
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfind
      run_with oc_caseOption_eq_none hf _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons]
      nlinarith
  · rw [show oc_genStep act eqb x (orb, q, row) σ = (orb, q, i :: row) by
      simp [oc_genStep, hf]]
    apply RunsWithin.mono
    case h =>
      run_step ha
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfind
      run_with oc_caseOption_eq_some hf _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
    case hc =>
      simp only [Prim.cost]
      nlinarith

theorem RunsWithin.oc_stepBody (hH : OrbitHyp act eqb k dec J gd)
    (hact : ∀ σ ∈ gd, ∀ x, J x → RunsWithin X body (actP σ x) (act σ x) cAct)
    (heq : ∀ x y, J x → J y → RunsWithin X body (eqP x y) (eqb x y) cEq) {x₀ : τ.denote}
    {st : List τ.denote × (List τ.denote × List (Array ℕ))} (hI : oc_Inv k dec J gd x₀ st) :
    RunsWithin X body (SoJTree.oc_stepBody actP eqP gd st) (oc_step act eqb gd st)
      (oc_iterCost (Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀))) gd.length
        cAct cEq) := by
  set R := Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) with hR
  rcases hq : st.2.1 with _ | ⟨x, rest⟩
  · rw [oc_step_nil hq]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with oc_caseList_eq_nil hq _
      exact RunsWithin.prim _ _
    case hc =>
      simp only [Prim.cost, oc_iterCost]
      omega
  · obtain ⟨P, hP, -⟩ := hI.split
    rw [hq] at hP
    have hxm : x ∈ st.1 := by rw [hP]; simp
    obtain ⟨hxo, hx⟩ := hI.good.2 x hxm
    have hrest : rest.length ≤ st.1.length := by rw [hP]; simp; omega
    obtain ⟨news, es, -, -, h₃, hlen, -, -⟩ :=
      oc_genFold_spec hH hx hxo gd (st.1, rest, []) (fun _ h => h) hI.good
    simp only [List.append_nil] at h₃
    have hfold := (RunsWithin.foldList_inv (X := X) (body := body) (a' := Ty.perm)
      (b' := oc_accTy τ) (f := fun acc σ => SoJTree.oc_genBody actP eqP x acc σ)
      (F := oc_genStep act eqb x)
      (I := fun acc => oc_Good k dec J gd (dec x₀) acc.1 ∧ acc.2.1.length ≤ acc.1.length)
      (c := cAct + R * (cEq + 13) + 17) gd (st.1, rest, [])
      (fun acc hacc σ hσ => by
        obtain ⟨news', h₁', h₂', -, -, -, -, hg'⟩ := oc_genStep_spec hH hx hxo hσ hacc.1
        refine ⟨(RunsWithin.oc_genBody (hact σ hσ x hx) fun z hz =>
          heq _ _ (hH.J_act σ hσ x hx) (hacc.1.2 z hz).2).mono ?_, hg', ?_⟩
        · have h₁ := oc_good_length_le hacc.1
          have h₂ := hacc.2
          rw [← hR] at h₁
          have : acc.1.length * (cEq + 12) + acc.2.1.length ≤ R * (cEq + 13) := by
            nlinarith
          omega
        · rw [h₁', h₂', List.length_append, List.length_append]
          omega)
      ⟨hI.good, hrest⟩).1
    rw [show oc_step act eqb gd st = some ((gd.foldl (oc_genStep act eqb x) (st.1, rest, [])).1,
      (gd.foldl (oc_genStep act eqb x) (st.1, rest, [])).2.1,
      (gd.foldl (oc_genStep act eqb x) (st.1, rest, [])).2.2.reverse.toArray :: st.2.2) by
        simp only [oc_step, hq]]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with oc_caseList_eq_cons hq _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, h₃, List.length_reverse, hlen,
        oc_iterCost]
      nlinarith

/-- The potential of the closure loop: the iterations left (the queue, the structures not yet
found, and the last test) times the cost of one iteration. -/
def oc_pot (R g cAct cEq : ℕ) {τ : Ty} (st : List τ.denote × (List τ.denote × List (Array ℕ))) :
    ℕ :=
  (st.2.1.length + (R - st.1.length) + 1) * (oc_iterCost R g cAct cEq + 1)

/-- **The orbit closure costs at most `orbitCost r g cAct cEq`**, for `r` the orbit size and
`g` the number of generators, when the action and the equality test cost at most `cAct` and
`cEq` on structures satisfying `J`. -/
theorem RunsWithin.orbitProg (hH : OrbitHyp act eqb k dec J gd)
    (hact : ∀ σ ∈ gd, ∀ x, J x → RunsWithin X body (actP σ x) (act σ x) cAct)
    (heq : ∀ x y, J x → J y → RunsWithin X body (eqP x y) (eqb x y) cEq) {x₀ : τ.denote}
    (hx₀ : J x₀) :
    RunsWithin X body (SoJTree.orbitProg actP eqP gd x₀) (orbitD act eqb k gd x₀)
      (orbitCost (orbitD act eqb k gd x₀).1.length gd.length cAct cEq) := by
  set R := Nat.card (MulAction.orbit (GensData.denote k gd) (dec x₀)) with hR
  set iC := oc_iterCost R gd.length cAct cEq with hiC
  have hR1 : 1 ≤ R := by
    have := oc_good_length_le (oc_init_inv (gd := gd) (k := k) (dec := dec) hx₀).good
    simp only [oc_init, List.length_singleton] at this
    exact this
  have hloop := RunsWithin.loop_pot (X := X) (body := body)
    (f := SoJTree.oc_stepBody actP eqP gd) (F := oc_step act eqb gd)
    (I := oc_Inv k dec J gd x₀) (Φ := oc_pot R gd.length cAct cEq)
    (fun st hst => ⟨iC, RunsWithin.oc_stepBody hH hact heq hst, fun _ => by
        simp only [oc_pot]
        rw [← hiC]
        nlinarith, fun st' hF => by
        rcases hq : st.2.1 with _ | ⟨x, rest⟩
        · rw [oc_step_nil hq] at hF
          simp at hF
        · obtain ⟨st'', news, hs, h₁, h₂, hI'⟩ := oc_step_spec hH hst hq
          rw [hs] at hF
          cases hF
          refine ⟨hI', ?_⟩
          have hle := oc_good_length_le hI'.good
          rw [← hR, h₁] at hle
          simp only [oc_pot, h₁, h₂, hq, List.length_append, List.length_cons] at hle ⊢
          rw [← hiC]
          have e : rest.length + news.length + (R - (st.1.length + news.length)) + 1 + 1 =
              rest.length + 1 + (R - st.1.length) + 1 := by omega
          rw [← e]
          ring_nf
          omega⟩)
    (oc_pot R gd.length cAct cEq (oc_init x₀) + 1) (oc_init x₀) (oc_init_inv hx₀)
    (Nat.lt_succ_self _)
  have hpot₀ : oc_pot R gd.length cAct cEq (oc_init x₀) = (R + 1) * (iC + 1) := by
    simp only [oc_pot, oc_init, List.length_singleton]
    rw [← hiC]
    congr 1
    omega
  rw [oc_iter_eq hH hx₀ (by rw [hpot₀]; nlinarith)] at hloop
  have hlen : (orbitD act eqb k gd x₀).1.length = R := orbitD_length_eq hH hx₀
  rw [orbitD_eq_iter hH hx₀] at hlen ⊢
  obtain ⟨hI, hq⟩ := oc_final_state hH hx₀
  set st := iter (oc_step act eqb gd) (R + 1) (oc_init x₀) with hst
  obtain ⟨P, hP, hPl⟩ := hI.split
  rw [hq, List.append_nil] at hP
  have hrows : st.2.2.reverse.length = R := by
    rw [List.length_reverse, ← hPl, ← hP, hlen]
  have houter := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .list .nat) (xs := List.range gd.length)
    (f := fun i => mapList (a' := .array .nat) (b' := .nat) st.2.2.reverse fun row =>
      .op2 .arrayGet row i)
    (F := fun i => st.2.2.reverse.map fun row => get row i) (c := R * 4 + 2)
    (fun i _ => (RunsWithin.mapList_le (X := X) (body := body) (a' := .array .nat) (b' := .nat)
      (xs := st.2.2.reverse) (f := fun row => .op2 .arrayGet row i) (F := fun row => get row i)
      (c := 1) fun row _ => RunsWithin.prim_le rfl le_rfl).mono (by rw [hrows]))
  simp only [hlen]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hloop
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step houter
    exact RunsWithin.prim_le (by simp [Prim.eval, oc_imgs]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, hpot₀, hiC,
      oc_iterCost, orbitCost, List.length_reverse] at hrows ⊢
    rw [hrows]
    ring_nf
    omega

end ProgSpec

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool} {τ : Ty}
  {actP₁ : var₁ Ty.perm → var₁ τ → Prog S rec var₁ τ}
  {actP₂ : var₂ Ty.perm → var₂ τ → Prog S rec var₂ τ}
  {eqP₁ : var₁ τ → var₁ τ → Prog S rec var₁ .bool} {eqP₂ : var₂ τ → var₂ τ → Prog S rec var₂ .bool}

/-- Well-formedness of a binary element program, in every extension of the context. -/
def oc_WfFun2 {a₁ a₂ t : Ty} (r : Bool) (Γ : WfCtx var₁ var₂)
    (f₁ : var₁ a₁ → var₁ a₂ → Prog S rec var₁ t) (f₂ : var₂ a₁ → var₂ a₂ → Prog S rec var₂ t) :
    Prop :=
  ∀ Γ' : WfCtx var₁ var₂, Γ ⊆ Γ' → ∀ x₁ x₂ y₁ y₂, ⟨a₁, x₁, x₂⟩ ∈ Γ' → ⟨a₂, y₁, y₂⟩ ∈ Γ' →
    Prog.Wf r Γ' (f₁ x₁ y₁) (f₂ x₂ y₂)

theorem oc_WfFun2.mono {a₁ a₂ t : Ty} {Γ Γ' : WfCtx var₁ var₂}
    {f₁ : var₁ a₁ → var₁ a₂ → Prog S rec var₁ t} {f₂ : var₂ a₁ → var₂ a₂ → Prog S rec var₂ t}
    (h : oc_WfFun2 r Γ f₁ f₂) (hΓ : Γ ⊆ Γ') : oc_WfFun2 r Γ' f₁ f₂ :=
  fun Γ'' h' => h Γ'' (List.Subset.trans hΓ h')

theorem wf_oc_findBody {Γ : WfCtx var₁ var₂} (hE : oc_WfFun2 r Γ eqP₁ eqP₂) {y₁ : var₁ τ}
    {y₂ : var₂ τ} {acc₁ : var₁ (.prod .nat (.option .nat))}
    {acc₂ : var₂ (.prod .nat (.option .nat))} {z₁ : var₁ τ} {z₂ : var₂ τ}
    (hy : ⟨τ, y₁, y₂⟩ ∈ Γ) (hacc : ⟨_, acc₁, acc₂⟩ ∈ Γ) (hz : ⟨τ, z₁, z₂⟩ ∈ Γ) :
    Prog.Wf r Γ (oc_findBody eqP₁ y₁ acc₁ z₁) (oc_findBody eqP₂ y₂ acc₂ z₂) := by
  unfold oc_findBody
  refine .bind (hE Γ (fun _ h => h) _ _ _ _ hy hz) fun _ _ => ?_
  prog_wf

theorem wf_oc_findProg {Γ : WfCtx var₁ var₂} (hE : oc_WfFun2 r Γ eqP₁ eqP₂) {y₁ : var₁ τ}
    {y₂ : var₂ τ} {orb₁ : var₁ (.list τ)} {orb₂ : var₂ (.list τ)} (hy : ⟨τ, y₁, y₂⟩ ∈ Γ)
    (horb : ⟨.list τ, orb₁, orb₂⟩ ∈ Γ) :
    Prog.Wf r Γ (oc_findProg eqP₁ y₁ orb₁) (oc_findProg eqP₂ y₂ orb₂) := by
  unfold oc_findProg
  refine .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.foldList (by simp [horb]) (by simp) fun _ _ _ _ =>
      wf_oc_findBody (hE.mono fun _ h => by simp [h]) (by simp [hy]) (by simp) (by simp))
      fun _ _ => .prim _ (.cons (by simp) .nil)

theorem wf_oc_genBody {Γ : WfCtx var₁ var₂} (hA : oc_WfFun2 r Γ actP₁ actP₂)
    (hE : oc_WfFun2 r Γ eqP₁ eqP₂) {x₁ : var₁ τ} {x₂ : var₂ τ} {acc₁ : var₁ (oc_accTy τ)}
    {acc₂ : var₂ (oc_accTy τ)} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm} (hx : ⟨τ, x₁, x₂⟩ ∈ Γ)
    (hacc : ⟨_, acc₁, acc₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ) :
    Prog.Wf r Γ (oc_genBody actP₁ eqP₁ x₁ acc₁ σ₁) (oc_genBody actP₂ eqP₂ x₂ acc₂ σ₂) := by
  unfold oc_genBody
  refine .bind (hA Γ (fun _ h => h) _ _ _ _ hσ hx) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hacc]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hacc]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_oc_findProg (hE.mono fun _ h => by simp [h]) (by simp) (by simp)) fun _ _ => ?_
  prog_wf

theorem wf_oc_stepBody {Γ : WfCtx var₁ var₂} (hA : oc_WfFun2 r Γ actP₁ actP₂)
    (hE : oc_WfFun2 r Γ eqP₁ eqP₂) {gd₁ : var₁ Ty.gens} {gd₂ : var₂ Ty.gens}
    {st₁ : var₁ (oc_stateTy τ)} {st₂ : var₂ (oc_stateTy τ)} (hgd : ⟨Ty.gens, gd₁, gd₂⟩ ∈ Γ)
    (hst : ⟨_, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf r Γ (oc_stepBody actP₁ eqP₁ gd₁ st₁) (oc_stepBody actP₂ eqP₂ gd₂ st₂) := by
  unfold oc_stepBody
  refine .bind (.prim _ (.cons hst .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hst]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .caseList (by simp) (.prim _ .nil) fun _ _ _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil)))
      fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.foldList (by simp [hgd]) (by simp) fun _ _ _ _ =>
      wf_oc_genBody (hA.mono fun _ h => by simp [h]) (hE.mono fun _ h => by simp [h])
        (by simp) (by simp) (by simp)) fun _ _ => ?_
  prog_wf

/-- **The orbit closure is well-formed** when the action and the equality test are. -/
theorem wf_orbitProg {Γ : WfCtx var₁ var₂} (hA : oc_WfFun2 r Γ actP₁ actP₂)
    (hE : oc_WfFun2 r Γ eqP₁ eqP₂) {gd₁ : var₁ Ty.gens} {gd₂ : var₂ Ty.gens} {x₁ : var₁ τ}
    {x₂ : var₂ τ} (hgd : ⟨Ty.gens, gd₁, gd₂⟩ ∈ Γ) (hx : ⟨τ, x₁, x₂⟩ ∈ Γ) :
    Prog.Wf r Γ (orbitProg actP₁ eqP₁ gd₁ x₁) (orbitProg actP₂ eqP₂ gd₂ x₂) := by
  unfold orbitProg
  refine .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hx]) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil)))
      fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.loop (by simp) fun _ _ =>
      wf_oc_stepBody (hA.mono fun _ h => by simp [h]) (hE.mono fun _ h => by simp [h])
        (by simp [hgd]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hgd]) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ hΓ' _ _ hi => wf_mapList (hΓ' (by simp))
      fun _ hΓ'' _ _ hrow => .prim _ (.cons hrow (.cons (hΓ'' hi) .nil)))
      fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.SoJTree
