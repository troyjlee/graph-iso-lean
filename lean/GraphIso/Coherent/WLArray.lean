module

public import GraphIso.Coherent.Tuples
public import GraphIso.Sims.SiftProg

/-!
# The Weisfeiler–Leman refinement on arrays

The functional models of the programs of `GraphIso/Coherent/WLProg.lean`: a colouring is an
array indexed by codes, and a round reads the precomputed information on every tuple
(`infoL`). The round on arrays computes the round of `GraphIso/Coherent/WL.lean` exactly:

* `sigA col (infoAt k m (enc x)) = sig (toFun col) x` (`sigA_infoAt`), and likewise for round 0;
* the sorted list of the distinct signatures is `sigList` (`sigListA_eq`);
* `stepA` on the array of a state is the array of `wlStep` (`stepA_repSt`), and `initA` is the
  array of `wlInit` (`initA_eq`);
* hence `wlA k m col`, the iteration on arrays, is the array of `wl k m (toFun col)` together
  with its colour list (`wlA_eq`).
-/

@[expose] public section

namespace GraphIso.Coherent

open Finset Function

variable {k m : ℕ}

/-! ### Signatures -/

/-- The round-0 signature from the information on a tuple. -/
def sig0A (col : Array ℕ) (e : Info) : List (List ℕ) := [[get col e.1], e.2.1]

/-- The signature from the information on a tuple. -/
def sigA (col : Array ℕ) (e : Info) : List (List ℕ) :=
  [get col e.1] :: e.2.2.2.map (get col) ::
    (e.2.2.1.map fun v => v.map (get col)).insertionSort (· ≤ ·)

theorem sig0A_infoAt (col : Array ℕ) (x : Tup k m) :
    sig0A col (infoAt k m (enc x)) = sig0 (toFun col) x := by
  rw [infoAt_enc]
  rfl

theorem sigA_infoAt (col : Array ℕ) (x : Tup k m) :
    sigA col (infoAt k m (enc x)) = sig (toFun col) x := by
  rw [infoAt_enc]
  simp only [sigA, sig, toFun, List.map_map, Function.comp_def]
  rfl

/-- The signatures of all tuples in the order of their codes. -/
theorem map_infoL (f : Info → List (List ℕ)) (s : Tup k m → List (List ℕ))
    (hf : ∀ x, f (infoAt k m (enc x)) = s x) :
    (infoL k m).map f = (List.finRange (m ^ k)).map fun t => s (finFunctionFinEquiv.symm t) := by
  rw [infoL_eq, List.map_map]
  exact List.map_congr_left fun t _ => hf _

theorem toFinset_map_finRange (s : Tup k m → List (List ℕ)) :
    ((List.finRange (m ^ k)).map fun t => s (finFunctionFinEquiv.symm t)).toFinset =
      univ.image s := by
  ext a
  simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and, mem_image, mem_univ]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨finFunctionFinEquiv x, by simp⟩

/-! ### Rounds -/

/-- A round on arrays from the list of signatures: rank them, or `none` if no class splits. -/
def roundA (sigs : List (List (List ℕ))) (n : ℕ) (orig : List ℕ) :
    Option (Array ℕ × ℕ × List ℕ) :=
  if (sigs.toFinset.sort (· ≤ ·)).length = n then none
  else some ((sigs.map fun s => (sigs.toFinset.sort (· ≤ ·)).idxOf s).toArray,
    (sigs.toFinset.sort (· ≤ ·)).length,
    (sigs.toFinset.sort (· ≤ ·)).map fun s => orig.getD (sigColour s) 0)

variable (k m) in
/-- One round on arrays. -/
def stepA (st : Array ℕ × ℕ × List ℕ) : Option (Array ℕ × ℕ × List ℕ) :=
  roundA ((infoL k m).map (sigA st.1)) st.2.1 st.2.2

variable (k m) in
/-- Round 0 on arrays. -/
def initA (col : Array ℕ) : Array ℕ × ℕ × List ℕ :=
  let sigs := (infoL k m).map (sig0A col)
  let S := sigs.toFinset.sort (· ≤ ·)
  ((sigs.map fun s => S.idxOf s).toArray, S.length, S.map sigColour)

/-- A state of the refinement as arrays. -/
def repSt (st : WLState k m) : Array ℕ × ℕ × List ℕ := (arrOf k m st.1, st.2.1, st.2.2)

theorem arrOf_rank (s : Tup k m → List (List ℕ)) :
    (((List.finRange (m ^ k)).map fun t => s (finFunctionFinEquiv.symm t)).map fun a =>
      (sigList s).idxOf a).toArray = arrOf k m (rank s) := by
  simp only [arrOf, rank, List.map_map]
  rfl

/-- **A round on arrays is the round of the model.** -/
theorem stepA_repSt (st : WLState k m) : stepA k m (repSt st) = (wlStep st).map repSt := by
  have hs := map_infoL (k := k) (m := m) (sigA (arrOf k m st.1)) (sig st.1)
    fun x => by rw [sigA_infoAt, toFun_arrOf]
  have hS : (((infoL k m).map (sigA (arrOf k m st.1))).toFinset.sort (· ≤ ·)) =
      sigList (sig st.1) := by
    rw [hs, toFinset_map_finRange]
    rfl
  simp only [stepA, repSt, roundA, hS, wlStep]
  split
  · rfl
  · simp only [Option.map_some]
    rw [hs, arrOf_rank]
    rfl

/-- **Round 0 on arrays is round 0 of the model.** -/
theorem initA_eq (col : Array ℕ) :
    initA k m col = repSt (wlInit (k := k) (m := m) (toFun col)) := by
  have hs := map_infoL (k := k) (m := m) (sig0A col) (sig0 (toFun col))
    fun x => sig0A_infoAt col x
  have hS : (((infoL k m).map (sig0A col)).toFinset.sort (· ≤ ·)) =
      sigList (sig0 (toFun (k := k) (m := m) col)) := by
    rw [hs, toFinset_map_finRange]
    rfl
  simp only [initA, hS, repSt, wlInit]
  rw [hs, arrOf_rank]

theorem wlIter_eq_iter : ∀ (j : ℕ) (st : WLState k m), wlIter j st = Sims.iter wlStep j st
  | 0, _ => rfl
  | j + 1, st => by
    simp only [wlIter, Sims.iter]
    cases wlStep st with
    | none => rfl
    | some st' => exact wlIter_eq_iter j st'

theorem iter_stepA : ∀ (j : ℕ) (st : WLState k m),
    Sims.iter (stepA k m) j (repSt st) = repSt (wlIter j st)
  | 0, _ => rfl
  | j + 1, st => by
    simp only [Sims.iter, wlIter, stepA_repSt]
    cases wlStep st with
    | none => rfl
    | some st' => exact iter_stepA j st'

variable (k m) in
/-- **The refinement on arrays**: the stable colouring and the colour list. -/
def wlA (col : Array ℕ) : Array ℕ × List ℕ :=
  ((Sims.iter (stepA k m) (m ^ k + 1) (initA k m col)).1,
    (Sims.iter (stepA k m) (m ^ k + 1) (initA k m col)).2.2)

/-- **The refinement on arrays computes the model.** -/
theorem wlA_eq (col : Array ℕ) :
    wlA k m col = (arrOf k m (wl k m (toFun col)).1, (wl k m (toFun col)).2) := by
  rw [wlA, initA_eq, iter_stepA]
  rfl

/-- More rounds change nothing. -/
theorem iter_stepA_of_le (col : Array ℕ) {j : ℕ} (hj : m ^ k + 1 ≤ j) :
    Sims.iter (stepA k m) j (initA k m col) =
      Sims.iter (stepA k m) (m ^ k + 1) (initA k m col) := by
  rw [initA_eq, iter_stepA, iter_stepA, wlIter_eq_iter, wlIter_eq_iter,
    Sims.iter_eq_of_fix (m ^ k + 1) _ (by rw [← wlIter_eq_iter]; exact wlStep_wlIter _) j hj]

end GraphIso.Coherent
