module

public import GraphIsoChecks.Reference
public import GraphIso.Solver.ReferenceCompose
import all Init.Data.Array.Basic
import all Init.Data.List.Sort.Basic
import all Init.Data.Nat.Bitwise.Basic
import all Mathlib.Data.List.Sort

/-!
# Phase 5 checks: restriction, lifting and block systems

Concrete runs, evaluated by the kernel, of the two phase-5 reductions with the reference
backend, the recursive solver as sub-solver, and their answers compared with brute force over
`Perm (Fin 4)`.

* **Restriction** of `G = ⟨(0 1), (2 3)⟩` to the window `{0, 1}`: the restricted group has degree
  2 and the restriction is not faithful, with kernel `⟨(2 3)⟩`. The lifted answer
  contains the kernel, and only with it does it list every solution.
* **Block system** `{0, 1}, {2, 3}` for the dihedral group `G = ⟨(0 1), (0 2)(1 3)⟩` of order
  8: the block kernel computed by the induced action at degree 6 is `⟨(0 1), (2 3)⟩`, of index
  2, and the reduction branches over its two cosets.
-/

@[expose] public section

namespace GraphIsoChecks.Restriction

open Equiv GraphIso GraphIso.Cost GraphIso.Programs GraphIso.Solver GraphIso.Reference
  GraphIso.Enum GraphIsoChecks.Reference

/-- Brute force: the permutations of `Fin n` in `σ • ⟨gs⟩` matching `x` and `y` on `W`. -/
def BruteIso (n : ℕ) (w : WinData) (σd : PermData) (gs : GensData) (x y : StrData)
    (g : Perm (Fin n)) : Prop :=
  (∃ e ∈ enumerate n gs, PermData.denote n σd * PermData.denote n e = g) ∧
    ∀ u : Fin n, u.val ∈ w.1 → x.denote n u = y.denote n (g u)

instance (n : ℕ) (w : WinData) (σd : PermData) (gs : GensData) (x y : StrData) :
    DecidablePred (BruteIso n w σd gs x y) := fun _ => by unfold BruteIso; infer_instance

/-- Run a reduction with the reference backend, the solver as sub-solver. -/
def runWith (p : Prog (groupSig Ty.gens) (Rec Ty.gens) Ty.denote (Ty.answer Ty.gens)) :
    Option (AnswerData Ty.gens × ℕ) :=
  (eval Ctx.empty.O (referenceSolver.proc Ty.denote) 1000000 (p.subst refImpl)).map
    fun r => (r.1, Trace.localCost r.2)

/-- A restriction run evaluated by the kernel is the run of `restrict_reference`: its answer
is correct and its cost is within `restrictReferenceCost`. -/
theorem runRestrict_spec {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} {ans : AnswerData Ty.gens} {c : ℕ} (hw : WinData.validB n w = true)
    (hσ : PermData.validB n σd = true) (hgs : GensData.allValidB n gs = true)
    (hinv : GensData.invariantB gs w = true)
    (h : runWith (restrictProg (fun J => .recur J) (xy, w, σd, n, gs, enumerate n gs)) =
      some (ans, c)) :
    Answer.IsCorrect (AnswerData.denote n ans) (w.denote n) (σd.denote n) (gs.denote n)
        (xy.1.denote n) (xy.2.denote n) ∧
      c ≤ restrictReferenceCost n w.1.length (Nat.card (GensData.denote n gs)) gs.length := by
  have hw' := WinData.validB_iff.1 hw
  have hgs' := GensData.allValidB_iff.1 hgs
  obtain ⟨ans', tr, hr, hc, hok⟩ := restrict_reference (xy := xy) hw'
    (PermData.validB_iff.1 hσ) hgs' ((GensData.invariantB_iff hgs' hw').1 hinv)
  unfold runWith at h
  rcases he : eval Ctx.empty.O (referenceSolver.proc Ty.denote) 1000000
    ((restrictProg (fun J => .recur J) (xy, w, σd, n, gs, enumerate n gs)).subst refImpl) with
    _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hok.isCorrect, hc⟩

/-- A block-reduction run evaluated by the kernel is the run of `blockReduce_reference`. That
`G` permutes the blocks is checked on the elements of `G`. -/
theorem runBlocks_spec {n : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData}
    {gs : GensData} {bs : List (List ℕ)} {ans : AnswerData Ty.gens} {c : ℕ}
    (hw : WinData.validB n w = true) (hσ : PermData.validB n σd = true)
    (hgs : GensData.allValidB n gs = true) (hinv : GensData.invariantB gs w = true)
    (hbs : IsBlockList w bs)
    (hG : ∀ e ∈ enumerate n gs, ∀ b ∈ bs, ∃ b' ∈ bs, ∀ u : Fin n, u.val ∈ b →
      (PermData.denote n e u).val ∈ b')
    (h : runWith (blockReduceProg (fun J => .recur J) xy w σd (n, gs, enumerate n gs) bs) =
      some (ans, c)) :
    Answer.IsCorrect (AnswerData.denote n ans) (w.denote n) (σd.denote n) (gs.denote n)
        (xy.1.denote n) (xy.2.denote n) ∧
      c ≤ blockReferenceCost n w.1.length bs.length (Nat.card (GensData.denote n gs)) gs.length
        (Nat.card (GensData.denote n gs) / Nat.card (blockKernel (GensData.denote n gs) bs)) := by
  have hw' := WinData.validB_iff.1 hw
  have hgs' := GensData.allValidB_iff.1 hgs
  have hG' : PermutesBlocks (GensData.denote n gs) bs := by
    intro g hg b hb
    obtain ⟨e, he, rfl⟩ := ((enumerate_spec hgs').1.2.2 g).1 hg
    exact hG e he b hb
  obtain ⟨ans', tr, hr, hc, hok⟩ := blockReduce_reference (xy := xy) hw'
    (PermData.validB_iff.1 hσ) hgs' ((GensData.invariantB_iff hgs' hw').1 hinv) hbs hG'
  unfold runWith at h
  rcases he : eval Ctx.empty.O (referenceSolver.proc Ty.denote) 1000000
    ((blockReduceProg (fun J => .recur J) xy w σd (n, gs, enumerate n gs) bs).subst refImpl) with
    _ | ⟨a, tr'⟩
  · rw [he] at h
    cases h
  · rw [he] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨rfl, rfl⟩ := Runs.unique ⟨_, he⟩ hr
    exact ⟨hok.isCorrect, hc⟩

/-- A successful answer of degree 4 whose group data is its generator list. -/
def ans4 (τ : PermData) (gs : GensData) : AnswerData Ty.gens := some (τ, (4, gs, gs))

def p01 : PermData := PermData.ofPerm (swap (0 : Fin 4) 1)
def p23 : PermData := PermData.ofPerm (swap (2 : Fin 4) 3)
def p0213 : PermData := PermData.ofPerm (swap (0 : Fin 4) 2 * swap 1 3)
def id4 : PermData := PermData.one 4

/-! ### Restriction with a non-faithful action -/

def k4 : GensData := [p01, p23]
def w01 : WinData := WinData.ofPoints 4 [0, 1]
def instR : InstData Ty.gens :=
  ((#[0, 1, 5, 6], #[1, 0, 7, 8]), w01, id4, 4, k4, enumerate 4 k4)

/-- The answer: representative `(0 1)(2 3)`, group generated by the kernel element `(2 3)`
and the identity. -/
theorem runR : runWith (restrictProg (fun J => .recur J) instR) =
    some (ans4 (PermData.ofPerm (swap (0 : Fin 4) 1 * swap 2 3)) [p23, id4], 3283) := by
  decide +kernel

-- The solutions are exactly the coset of the answer, by brute force.
example : ∀ g, g ∈ Answer.denote (AnswerData.denote 4
      (ans4 (PermData.ofPerm (swap (0 : Fin 4) 1 * swap 2 3)) [p23, id4])) ↔
    BruteIso 4 w01 id4 k4 #[0, 1, 5, 6] #[1, 0, 7, 8] g := by
  intro g
  rw [ans4, mem_denote_some (by decide)]
  revert g
  decide

example := runRestrict_spec (by decide) (by decide) (by decide) (by decide) runR

theorem card_k4 : Nat.card (GensData.denote 4 k4) = 4 := by
  rw [← (enumerate_spec (GensData.allValidB_iff.1 (by decide))).2]
  decide

-- The bound of `restrict_reference` for this instance.
example : restrictReferenceCost 4 w01.1.length (Nat.card (GensData.denote 4 k4)) k4.length =
    245677 := by
  rw [card_k4]
  decide

-- There are two solutions, `(0 1)` and `(0 1)(2 3)`, differing by the kernel element.
example : ∀ g, BruteIso 4 w01 id4 k4 #[0, 1, 5, 6] #[1, 0, 7, 8] g ↔
    g = swap 0 1 ∨ g = swap 0 1 * swap 2 3 := by
  decide

-- The kernel of the restriction is nontrivial, so the lifted group needs it.
example : swap (2 : Fin 4) 3 ∈ pointwiseStab (GensData.denote 4 k4) (w01.denote 4) := by
  refine ⟨?_, fun u hu => ?_⟩
  · have := GensData.mem_denote_of_mem (n := 4) (g := p23) (gs := k4) (by decide)
    simpa [p23] using this
  · rw [WinData.mem_denote] at hu
    revert u
    decide

/-! ### The block-system reduction -/

def d4 : GensData := [p01, p0213]
def blocks : List (List ℕ) := [[0, 1], [2, 3]]
def wAll : WinData := WinData.ofPoints 4 [0, 1, 2, 3]
def instB : InstData Ty.gens :=
  ((#[0, 1, 0, 0], #[0, 0, 1, 0]), wAll, id4, 4, d4, enumerate 4 d4)

example : (enumerate 4 d4).length = 8 := by decide

/-- The block kernel, listed by its elements: `(0 1)`, `(2 3)`, `(0 1)(2 3)` and the identity. -/
def kerList : GensData :=
  [p01, p23, PermData.ofPerm (swap (0 : Fin 4) 1 * swap 2 3), id4]

theorem runK : (eval Ctx.empty.O (referenceSolver.proc Ty.denote) 100000
    ((blockKernelProg (D := Ty.gens) (var := Ty.denote) (rec := Rec Ty.gens) 4 d4 blocks).subst
      refImpl)).map (fun r => (r.1, Trace.localCost r.2)) =
    some ((4, kerList, kerList), 18279) := by
  decide +kernel

-- The computed kernel is the block kernel, by brute force: the elements of `G` mapping each
-- block into itself.
example : ∀ g : Perm (Fin 4), (∃ e ∈ kerList, PermData.denote 4 e = g) ↔
    (∃ e ∈ enumerate 4 d4, PermData.denote 4 e = g) ∧
      ∀ b ∈ blocks, ∀ u : Fin 4, u.val ∈ b → (g u).val ∈ b := by
  decide

theorem runBlocks : runWith (blockReduceProg (fun J => .recur J) instB.1 instB.2.1 instB.2.2.1
      instB.2.2.2 blocks) =
    some (ans4 (PermData.ofPerm (swap (0 : Fin 4) 3 * swap 1 2)) [p23, id4], 26133) := by
  decide +kernel

example : ∀ g, g ∈ Answer.denote (AnswerData.denote 4
      (ans4 (PermData.ofPerm (swap (0 : Fin 4) 3 * swap 1 2)) [p23, id4])) ↔
    BruteIso 4 wAll id4 d4 #[0, 1, 0, 0] #[0, 0, 1, 0] g := by
  intro g
  rw [ans4, mem_denote_some (by decide)]
  revert g
  decide

example := runBlocks_spec (by decide) (by decide) (by decide) (by decide)
  ⟨by decide, by decide⟩ (by decide) runBlocks

-- Two branches: the index of the block kernel.
example : (repsModel (enumerate 4 d4) kerList).length = 2 := by decide

theorem card_d4 : Nat.card (GensData.denote 4 d4) = 8 := by
  rw [← (enumerate_spec (GensData.allValidB_iff.1 (by decide))).2]
  decide

/-- The block kernel has order 4, by counting the permutations of `Fin 4` in `G` that map each
block into itself. -/
theorem card_blockKernel_d4 : Nat.card (blockKernel (GensData.denote 4 d4) blocks) = 4 := by
  have hv : GensData.AllValid 4 d4 := GensData.allValidB_iff.1 (by decide)
  have h : ∀ g, g ∈ blockKernel (GensData.denote 4 d4) blocks ↔
      (∃ e ∈ enumerate 4 d4, PermData.denote 4 e = g) ∧
        ∀ b ∈ blocks, ∀ u : Fin 4, u.val ∈ b → (g u).val ∈ b := fun g => by
    rw [mem_blockKernel, (enumerate_spec hv).1.2.2 g]
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  decide

-- The bound of `blockReduce_reference` for this instance: `R = 8 / 4 = 2` branches.
example : blockReferenceCost 4 wAll.1.length blocks.length (Nat.card (GensData.denote 4 d4))
    d4.length (Nat.card (GensData.denote 4 d4) /
      Nat.card (blockKernel (GensData.denote 4 d4) blocks)) = 30233029 := by
  rw [card_blockKernel_d4, card_d4]
  decide

end GraphIsoChecks.Restriction
