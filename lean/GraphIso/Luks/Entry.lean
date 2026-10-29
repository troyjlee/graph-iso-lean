module

public import GraphIso.Luks.Correctness
public import GraphIso.Solver.Checked

/-!
# The entry points with Luks's strategy

The entry programs `solveEntry` and `solveChecked` (`GraphIso/Solver/Entry.lean`,
`GraphIso/Solver/Checked.lean`) end with a recursive call, so they run unchanged inside the
procedure `luksBody`: the initial `generate` builds the group's backend data, and the
recursion is Luks's strategy.

* `luksEntry_spec`: against a backend meeting the contracts of `luksOps`, with bounds
  `LuksBounds X DV n s R ⟨gs⟩`, `PrimBounded ⟨gs⟩ c` and `n ^ c ≤ R`, the entry returns a
  correct answer at cost at most `11 + (charge of the initial generate) + luksBound Q c |W|`.
* `luks_backend_refinement`: the same after substituting implementations.
* `luksChecked_spec`: the validating entry, on every input.
-/

@[expose] public section

namespace GraphIso.Luks

open Equiv Pointwise Cost Programs Solver

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **The public entry with Luks's strategy, against an abstract backend.** -/
theorem luksEntry_spec (hO : MeetsContractOn DV luksOps X.O)
    (hPre : ∀ op x, luksOps op → GroupPre DV op x → X.Pre op x) {n s R c : ℕ}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData}
    (B : LuksBounds X DV n s R (GensData.denote n gs))
    (hprim : PrimBounded (GensData.denote n gs) c) (hR : n ^ c ≤ R) (hw : w.Valid n)
    (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ ans : AnswerData D,
      RunsWithin X (luksBody D Ty.denote) (solveEntry D Ty.denote (xy, w, σd, n, gs)) ans
        (11 + X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) +
          luksBound (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c w.1.length) ∧
      AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans ∧
      ∀ c' : CosetData D, ans = some c' → c'.2.gens.length ≤ s := by
  have hpreG : GroupPre DV .generate (n, gs) := hgs
  have hpost := hO .generate (n, gs) (Or.inr (Or.inl rfl)) hpreG
  have hsG := B.genOut gs hgs le_rfl
  rcases hG : X.O.run GroupOp.generate (n, gs) with ⟨n', gs', d⟩
  rw [hG] at hpost hsG
  obtain ⟨hn', hGv, hden⟩ := hpost
  change n' = n at hn'
  subst n'
  change GensData.denote n gs' = GensData.denote n gs at hden
  have hv : InstData.Valid (D := D) (xy, w, σd, n, gs', d) DV :=
    ⟨hw, hσ, hGv, by change IsInvariant (GensData.denote n gs') _; rw [hden]; exact hinv⟩
  obtain ⟨ans, hr, hok, hg⟩ := luks_spec hO hPre B hprim hR _ xy w σd gs' d hv hsG
    (by rw [hden]) rfl
  refine ⟨ans, ?_, ?_, hg⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.call (X := X) (op := GroupOp.generate) (x := (n, gs))
        (hPre _ _ (Or.inr (Or.inl rfl)) hpreG))
      rw [hG]
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.recur hr
    case hc =>
      simp only [Prim.cost, hG]
      omega
  · change AnsOK DV n (w.denote n) (σd.denote n) (GensData.denote n gs') _ _ ans at hok
    rw [hden] at hok
    exact hok

/-- **Backend substitution with Luks's strategy.** -/
theorem luks_backend_refinement {S' : Signature} (hO : MeetsContractOn DV luksOps X.O)
    (hPre : ∀ op x, luksOps op → GroupPre DV op x → X.Pre op x) {I : WfImpl (groupSig D) S'}
    {O' : Oracle S'} {B' : CostSchedule S'} (himpl : Implements X.O X.B X.Pre I.impl O' B')
    {n s R c : ℕ} {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData}
    (B : LuksBounds X DV n s R (GensData.denote n gs))
    (hprim : PrimBounded (GensData.denote n gs) c) (hR : n ^ c ≤ R) (hw : w.Valid n)
    (hσ : σd.Valid n) (hgs : GensData.AllValid n gs)
    (hinv : IsInvariant (GensData.denote n gs) (w.denote n)) :
    ∃ (ans : AnswerData D) (tr : Trace S'),
      Runs O' ((WfProc.subst ⟨luksBody D, luksBody_wf⟩ I).proc Ty.denote)
        ((solveEntry D Ty.denote (xy, w, σd, n, gs)).subst I.impl) ans tr ∧
      Trace.cost B' tr ≤
        11 + X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) +
          luksBound (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c w.1.length ∧
      AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans := by
  obtain ⟨ans, ⟨tr, hr, hc, hpre⟩, hok, -⟩ := luksEntry_spec hO hPre B hprim hR hw hσ hgs hinv
  obtain ⟨tr', hr', hc'⟩ := Runs.subst himpl hr hpre
  exact ⟨ans, tr', hr', hc'.trans hc, hok⟩

/-- **The validating entry with Luks's strategy, against an abstract backend.** -/
theorem luksChecked_spec (hO : MeetsContractOn DV luksOps X.O)
    (hPre : ∀ op x, luksOps op → GroupPre DV op x → X.Pre op x) {q n s R c : ℕ}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {gs : GensData}
    (B : LuksBounds X DV n s R (GensData.denote n gs))
    (hprim : PrimBounded (GensData.denote n gs) c) (hR : n ^ c ≤ R) :
    ∃ r : Option (AnswerData D),
      RunsWithin X (luksBody D Ty.denote)
        (solveChecked D Ty.denote (q, xy, w, σd, n, gs)) r
        (validCost n w.1.length gs.length + 4 +
          if inputValidB q (xy, w, σd, n, gs) then
            11 + X.B.call .generate (n, gs) (X.O.run .generate (n, gs)) +
              luksBound (luksQ n s B.Borb B.Bge B.Bke B.Bgt B.sKe B.Bcr B.Bgen) c w.1.length
          else 0) ∧
      (r = none ↔ ¬ InputValid q (xy, w, σd, n, gs)) ∧
      ∀ ans : AnswerData D, r = some ans →
        AnsOK DV n (w.denote n) (σd.denote n) (gs.denote n) (xy.1.denote n) (xy.2.denote n) ans ∧
          ∀ c' : CosetData D, ans = some c' → c'.2.gens.length ≤ s := by
  have hv := RunsWithin.inputValidProg (X := X) (body := luksBody D Ty.denote) q n xy w σd gs
  cases hb : inputValidB q (xy, w, σd, n, gs) with
  | false =>
    refine ⟨none, ?_, ⟨fun _ hi => absurd (inputValidB_iff.2 hi) (by rw [hb]; simp),
      fun _ => rfl⟩, fun _ h => absurd h (by simp)⟩
    rw [hb] at hv
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hv
      exact RunsWithin.ite_false (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost]
      omega
  | true =>
    obtain ⟨-, -, hw, hσ, hgs, hinv⟩ := inputValidB_iff.1 hb
    obtain ⟨ans, hr, hok, hg⟩ := luksEntry_spec hO hPre B hprim hR hw hσ hgs hinv
    refine ⟨some ans, ?_, ⟨fun h => absurd h (by simp), fun h => absurd (inputValidB_iff.1 hb) h⟩,
      fun a ha => ?_⟩
    · rw [hb] at hv
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step hv
        apply RunsWithin.ite_true
        run_step hr
        exact RunsWithin.prim _ _
      case hc =>
        simp only [Prim.cost, ↓reduceIte]
        omega
    · cases ha
      exact ⟨hok, hg⟩

end GraphIso.Luks
