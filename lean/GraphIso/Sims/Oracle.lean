module

public import GraphIso.Sims.Cosets

/-!
# The Schreier–Sims backend: oracle and contracts

The backend keeps no data (`D = Ty.unit`, invariant `ssDV` trivially true): every operation
that needs a stabilizer chain builds the complete table it needs from the group's generators.
`ssOracle` collects the functional models of the eight operations, and `ssOracle_meets`
proves that it meets every contract of `GraphIso/GroupOps/Interface.lean`, including `mem`.
Output groups have at most `n²` generators (`ssOracle_gens_le`).
-/

@[expose] public section

namespace GraphIso.Sims

open Equiv Cost

/-- The backend data invariant: there is no data. -/
def ssDV (_ : ℕ) (_ : GensData) (_ : Unit) : Prop := True

/-- The Schreier–Sims oracle. -/
def ssOracle : Oracle (groupSig Ty.unit) := ⟨fun op x =>
  match op, x with
  | .generate, (n, gs) => (n, generateModel n gs, ())
  | .mem, ((n, gs, _), π) => memModel n gs π
  | .orbits, ((n, gs, _), w) => orbitsModel n gs w
  | .stabilizer, ((n, gs, _), u) => (n, stabModel n gs u, ())
  | .orbitTransversal, ((n, gs, _), u) => orbitBFS n gs u
  | .cosetReps, ((n, gs, _), (_, ks, _)) => cosetRepsModel n gs ks
  | .kernel, ((n, gs, _), w) => (n, kernelModel n gs w, ())
  | .lift, ((n, gs, _), w, π') => liftModel n gs w π'⟩

/-- **The Schreier–Sims oracle meets every contract.** -/
theorem ssOracle_meets : MeetsContract ssDV ssOracle := by
  rintro op x hpre
  cases op with
  | generate =>
    obtain ⟨n, gs⟩ := x
    obtain ⟨h₁, h₂, -⟩ := generateModel_spec (n := n) hpre
    exact ⟨rfl, ⟨h₁, trivial⟩, h₂⟩
  | mem =>
    obtain ⟨⟨n, gs, _⟩, π⟩ := x
    obtain ⟨⟨hgs, -⟩, hπ⟩ := hpre
    exact memModel_iff hgs hπ
  | orbits =>
    obtain ⟨⟨n, gs, _⟩, w⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, hinv⟩ := hpre
    exact orbitsModel_spec hgs hw hinv
  | stabilizer =>
    obtain ⟨⟨n, gs, _⟩, u⟩ := x
    obtain ⟨⟨hgs, -⟩, hu⟩ := hpre
    obtain ⟨h₁, h₂, -⟩ := stabModel_spec hgs hu
    exact ⟨rfl, ⟨h₁, trivial⟩, fun _ => h₂⟩
  | orbitTransversal =>
    obtain ⟨⟨n, gs, _⟩, u⟩ := x
    obtain ⟨⟨hgs, -⟩, hu⟩ := hpre
    exact orbitBFS_spec hu hgs
  | cosetReps =>
    obtain ⟨⟨n, gs, _⟩, ⟨n', ks, _⟩⟩ := x
    obtain ⟨⟨hgs, -⟩, ⟨hks, -⟩, hn, hK⟩ := hpre
    change n' = n at hn
    subst hn
    exact cosetRepsModel_spec hgs hks hK
  | kernel =>
    obtain ⟨⟨n, gs, _⟩, w⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -⟩ := hpre
    obtain ⟨h₁, h₂, -⟩ := kernelModel_spec hgs hw
    exact ⟨rfl, ⟨h₁, trivial⟩, h₂⟩
  | lift =>
    obtain ⟨⟨n, gs, _⟩, w, π'⟩ := x
    obtain ⟨⟨hgs, -⟩, hw, -, -, r, hr, hrG, hmap⟩ := hpre
    exact liftModel_spec hgs hw hr hrG hmap

/-- Output groups have at most `n²` generators. -/
theorem ssOracle_gens_le {n : ℕ} {gs : GensData} (hgs : GensData.AllValid n gs) :
    (ssOracle.run .generate (n, gs)).2.1.length ≤ n * n ∧
      ∀ u < n, (ssOracle.run .stabilizer ((n, gs, ()), u)).2.1.length ≤ n * n := by
  refine ⟨(generateModel_spec hgs).2.2, fun u hu => (stabModel_spec hgs hu).2.2⟩

end GraphIso.Sims
