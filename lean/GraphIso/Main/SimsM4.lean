module

public import GraphIso.Main.SimsRD

/-!
# M4 with the Schreier–Sims backend

Stage 14j-5c, items 1–3 (`PLAN-14.md` §14.8), for M4: `RunsWithin.m4StepProg_ss` and
`RunsWithin.m4StepProg_ns_ss`, the specs `RunsWithin.m4StepProg` and `RunsWithin.m4StepProg_ns`
at `ssCtx` with every backend hypothesis proved.

* **The leaf stabilizer** (`M4Charges`) is computed by orbit–stabilizer on the leaf's orbit of
  `r` structures, at degree `N + r` (`ss_leafStab_sizes`): the extended generators are valid
  (`os_allValid_extGens`), so its sizes are at most `(N + r)²`, and `r ≤ msCount (m − j)` since
  the leaves form a tree invariant under `H` (`ss_m4_pre`, from `ms_leaves_of`).
* **Reduce-and-derive** on the stabilizer `K`: `RDBounds` is `rd_ss_boundsS`, and the per-orbit
  `RDOrbit` is `rd_orbit_free_ssU` for a partition leaf or `rd_orbit_cj_ssU` for a Johnson leaf.
  The latter needs the Johnson facts of `m4_cj_facts`, hence the case condition `2j ≤ m`, which
  the dispatcher tests (stage 14j-5d).
* **The work** `m4WorkSS` is the monotone envelope (`envSup`) of the spec's cost at these charges,
  in the string positions `n`, the base size `m`, the individualization depth `j`, the window `p`,
  the sub-solver bound `s`, the label array's size `Ls`, `sIn` and `Lg`. The depth `j` stays an
  argument: under `TransitivityBound` it is small (`m4_deg_le_T`), which stage 14j-6 uses.
* **The union cells bounded by the labels** (stage 14j-6b-1, `PLAN-14.md` §14.11 items 4–5):
  `RunsWithin.m4StepProg_ns_ssU` proves the step without stuck orbits for any bounds `uB` (the
  factor) and `uD` (the derived hints' Johnson fallback, `ssBdJU`, `ss_m4_hDU`) on the union
  labels, at the cost at the instance's sizes. `RunsWithin.m4StepProg_ns_ss` takes `uB ≥ m` and
  `uD = m`; `RunsWithin.m4StepProg_nsL_ss` takes both at `labLen L · λ(m)` (`ss_union_le_lab`),
  with the work `m4WorkNsLSS`: no factorial of `m` in the factor or the work.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Cost MulAction GraphIso GraphIso.Programs GraphIso.Toolkit GraphIso.Recursion
  Sims Solver GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree GraphIso.Case2b GraphIso.Align

/-! ### The leaf stabilizer -/

section LeafStab

/-- **The sizes of the leaf stabilizer with Schreier–Sims**: the orbit has `r ≥ 1` leaves, the
extended group and the stabilizer of its point `N` at most `(N + r)²` generators, the transversal
at most `N + r` pairs, and the stabilizer of the leaf at most `N²` generators (by
`RunsWithin.orbitStabProg` for the invariant `ssBnd 0`). -/
theorem ss_leafStab_sizes {N n' : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) (o : OutD) :
    0 < msR n' N gs o ∧
      (osGroup ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1.length ≤
        (N + msR n' N gs o) * (N + msR n' N gs o) ∧
      (osStab ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1.length ≤
        (N + msR n' N gs o) * (N + msR n' N gs o) ∧
      (osTrans ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).length ≤ N + msR n' N gs o ∧
      (orbitStabModel ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).1.2.1.length ≤
        N * N := by
  obtain ⟨hr, hlen, ρ, himg, -⟩ := ls_orbit_facts hgs (ms_win_valid n' N) (ms_win_inv hinv) o
  have hv := os_allValid_extGens hgs himg
  have hv1 : GensData.AllValid (N + msR n' N gs o)
      (osGroup ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1 :=
    (generateModel_spec hv).1
  have hlt : N < N + msR n' N gs o := by
    have : 0 < msR n' N gs o := hr
    omega
  obtain ⟨-, -, hval, -⟩ := RunsWithin.orbitStabProg (X := ssCtxB 0) (DV := ssBnd 0)
    (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    (fun op x _ hx => ssOracle_meets_bnd 0 op x hx) (fun _ _ _ h => h) hgs hr ρ himg hlen
    le_rfl le_rfl le_rfl le_rfl
  refine ⟨hr, (generateModel_spec hv).2.2, (stabModel_spec hv1 hlt).2.2,
    orbitBFS_length_le hlt hv1, ?_⟩
  have h := hval.2
  change _ ≤ max 0 (N * N) at h
  exact h.trans (max_le (Nat.zero_le _) le_rfl)

theorem os_extGens_length (N r : ℕ) (gs : GensData) (imgs : List (List ℕ)) :
    (os_extGens N r gs imgs).length = gs.length := by
  simp [os_extGens]

/-- **The charges of the leaf stabilizer with Schreier–Sims**, for a group of at most `S`
generators whose leaf orbit has at most `R` structures. -/
theorem ss_m4Charges {N n' S R : ℕ} {gs : GensData} (hgs : GensData.AllValid N gs)
    (hl : gs.length ≤ S) (hinv : IsInvariant (GensData.denote N gs) (baseSet n' N)) {o : OutD}
    (hR : msR n' N gs o ≤ R) :
    M4Charges ssCtx n' N gs o ((N + R) * (N + R)) (N + R) (genCost (N + R) S + 2)
      (stabCost (N + R) ((N + R) * (N + R)) + 5) (transCost (N + R) ((N + R) * (N + R)) + 5)
      (genCost N ((N + R) * (N + R)) + 2) := by
  obtain ⟨-, hg, hs, ht, -⟩ := ss_leafStab_sizes hgs hinv o
  have e : (N + msR n' N gs o) * (N + msR n' N gs o) ≤ (N + R) * (N + R) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine ⟨ssB_generate_le (by omega) (by rw [os_extGens_length]; exact hl) _, ?_, ?_,
    ssB_generate_le le_rfl ((List.length_map _).trans_le (hs.trans e)) _, hs.trans e,
    ht.trans (by omega)⟩
  · change stabCost (N + msR n' N gs o)
      (osGroup ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1.length + 5 ≤ _
    unfold stabCost
    gcongr
    all_goals first | omega | exact Sims.buildCost_mono₂ (by omega) (hg.trans e)
  · change transCost (N + msR n' N gs o)
      (osGroup ssCtx.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1.length + 5 ≤ _
    unfold transCost
    gcongr
    all_goals omega

end LeafStab


/-! ### The individualized group and its leaf -/

section Pre

/-- **M4's individualized group with Schreier–Sims**, under M4's case conditions, for an
instance of at most `S ≥ N²` generators: valid with at most `S` generators (by the invariant
`ssBnd S`), its base `[n + j, N)` invariant, and the first leaf's orbit of at most
`msCount (m − j)` structures (the leaves form an `H`-invariant tree, `ms_leaves_of`). -/
theorem ss_m4_pre {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ}
    {gs : GensData} {n₀ n : ℕ} {L : LabelData} {S : ℕ}
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hgs : gs.length ≤ S) (hS : N * N ≤ S) :
    GensData.AllValid N (m4PS ssCtx.O n (N, gs, ())).1.2.1 ∧
      (m4PS ssCtx.O n (N, gs, ())).1.2.1.length ≤ S ∧
      IsInvariant (GensData.denote N (m4PS ssCtx.O n (N, gs, ())).1.2.1)
        (baseSet (n + m4J ssCtx.O n (N, gs, ())) N) ∧
      msR (n + m4J ssCtx.O n (N, gs, ())) N (m4PS ssCtx.O n (N, gs, ())).1.2.1
          (msLeaf ssCtx.O (n + m4J ssCtx.O n (N, gs, ())) (m4PS ssCtx.O n (N, gs, ())).1) ≤
        msCount (N - n - m4J ssCtx.O n (N, gs, ())) := by
  have hO : MeetsContractOn (ssBnd S) rdOps (ssCtxB S).O :=
    fun op x _ hx => ssOracle_meets_bnd S op x hx
  have hOdeg : MeetsContractOn (ssBnd S) degreeOps (ssCtxB S).O :=
    fun op x h hx => hO op x (m4_degOps h) hx
  have hOs : MeetsContractOn (ssBnd S) stabOps (ssCtxB S).O :=
    fun op x h hx => hO op x (m4_stabOps h) hx
  have hOm : MeetsContractOn (ssBnd S) m4StructOps (ssCtxB S).O :=
    fun op x h hx => hO op x (m4_structOps h) hx
  have hn : n ≤ N := hI.le
  have hinv : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hG : GroupValid (D := Ty.unit) (ssBnd S) N gs () :=
    ⟨hI.valid.group.1, show gs.length ≤ max S (N * N) from le_max_of_le_left hgs⟩
  have B := ssBoundsB S N S ⊤ hS
  obtain ⟨-, hdm, htrH, h2H⟩ := indiv_of_degree hOdeg B hG hgs le_top hinv hn
    (cap := N - n - 2) (by omega) htr hng
  have hjd : m4J ssCtx.O n (N, gs, ()) + 1 ≤ N - n := by
    have : m4Deg ssCtx.O n (N, gs, ()) + 1 ≤ N - n := hdm
    unfold m4J
    omega
  have hS' : ∀ u ∈ (List.range (m4J ssCtx.O n (N, gs, ()))).map (n + ·), n ≤ u ∧ u < N := by
    intro u hu
    simp only [List.mem_map, List.mem_range] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    omega
  obtain ⟨-, hpsN₀, hpsv₀, hpsden, -⟩ := Toolkit.RunsWithin.pointStabsProg
    (a := Ty.unit) (b := Ty.unit)
    (body := fun x => (Prog.ret x : Prog (groupSig Ty.unit) (Ty.unit, Ty.unit) Ty.denote Ty.unit))
    hOs (fun _ _ _ h => h) hG hinv hS' B hgs le_top
  have hpsN : (m4PS ssCtx.O n (N, gs, ())).1.1 = N := hpsN₀
  have hpsv : GroupValid (D := Ty.unit) (ssBnd S) N (m4PS ssCtx.O n (N, gs, ())).1.2.1
      (m4PS ssCtx.O n (N, gs, ())).1.2.2 := hpsv₀
  have hHden : GensData.denote N (m4PS ssCtx.O n (N, gs, ())).1.2.1 =
      fixFirst (GensData.denote N gs) n (m4J ssCtx.O n (N, gs, ())) := by
    show GensData.denote N (pointStabsModel (ssCtxB S).O (N, gs, ())
      ((List.range (m4J ssCtx.O n (N, gs, ()))).map (n + ·))).1.2.1 = _
    rw [hpsden, range_map_eq_range', pointwiseStab_range']
  have hinvH : IsInvariant (GensData.denote N (m4PS ssCtx.O n (N, gs, ())).1.2.1)
      (baseSet (n + m4J ssCtx.O n (N, gs, ())) N) := by
    rw [hHden]
    exact fixFirst_base_inv hinv _
  obtain ⟨htrH', h2H'⟩ := m4_trans_congr hHden.symm (fixFirst_base_inv hinv _) hinvH
  have hn' : n + m4J ssCtx.O n (N, gs, ()) < N := by omega
  have hk4' : 4 ≤ N - (n + m4J ssCtx.O n (N, gs, ())) := by omega
  have hP1 : (m4PS ssCtx.O n (N, gs, ())).1 =
      (N, (m4PS ssCtx.O n (N, gs, ())).1.2.1, (m4PS ssCtx.O n (N, gs, ())).1.2.2) :=
    Prod.ext hpsN rfl
  refine ⟨hpsv.1, hpsv.2.trans (max_le le_rfl hS), hinvH, ?_⟩
  obtain ⟨hne, hall⟩ := ms_leaves_of hOm hpsv hinvH hn' (htrH' htrH) (h2H' h2H) hk4'
  rw [hP1]
  rcases hL : msLeaves ssCtx.O (n + m4J ssCtx.O n (N, gs, ()))
    (N, (m4PS ssCtx.O n (N, gs, ())).1.2.1, (m4PS ssCtx.O n (N, gs, ())).1.2.2) with
    _ | ⟨o, rest⟩
  · exact absurd hL hne
  have ho : o ∈ msLeaves (ssCtxB S).O (n + m4J ssCtx.O n (N, gs, ()))
      (N, (m4PS ssCtx.O n (N, gs, ())).1.2.1, (m4PS ssCtx.O n (N, gs, ())).1.2.2) := by
    change o ∈ msLeaves ssCtx.O _ _
    rw [hL]
    exact List.mem_cons_self
  obtain ⟨-, -, -, horb, -⟩ := hall o ho
  have hleaf : msLeaf ssCtx.O (n + m4J ssCtx.O n (N, gs, ()))
      (N, (m4PS ssCtx.O n (N, gs, ())).1.2.1, (m4PS ssCtx.O n (N, gs, ())).1.2.2) = o := by
    simp [msLeaf, hL]
  rw [hleaf]
  have hk : msK (n + m4J ssCtx.O n (N, gs, ())) N = N - n - m4J ssCtx.O n (N, gs, ()) := by
    rw [msK_eq]
    omega
  unfold msR
  rw [leafOrbit_length_eq hpsv.1 (ms_win_valid _ N) (ms_win_inv hinvH) o, ← hk]
  exact horb

end Pre


/-! ### The work -/

section Work

/-- `RDOrbit` at a larger work bound. -/
theorem RDOrbit.mono {D : Ty} {X : Ctx (groupSig D)} {a b : Ty}
    {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
    {DV : ℕ → GensData → D.denote → Prop} {n N : ℕ} {w : WinData} {L : LabelData}
    {st : ℕ × CJData} {sIn Bd Bd' : ℕ} {gs : GensData} {d : D.denote} {O : List ℕ}
    (h : RDOrbit X body DV n N w L st sIn Bd gs d O) (hb : Bd ≤ Bd') :
    RDOrbit X body DV n N w L st sIn Bd' gs d O :=
  ⟨h.run.mono hb, h.out, h.deg, h.gens⟩

/-- The work of one orbit of reduce-and-derive in M4 with Schreier–Sims, for factor `F` and
stuck work `W6`: the derived hint (`ssBdF + ssBdJ`, covering both kinds of structure) and the
charges of `rd_ss_boundsS`. -/
def m4WhSS (n m p s Ls sIn Lg F W6 : ℕ) : ℕ :=
  rdOrbitWork (n + m) n p s sIn F (ssBdF n (n + m) p sIn + ssBdJ n (n + m) p Ls sIn)
    (Sims.liftCost (n + m) sIn n + 7) (genCost (n + m) Lg + 2)
    (orbitsCost (n + m) sIn (n + m) + 5) W6

/-- The stuck work of reduce-and-derive with Schreier–Sims (`rd6Cost` at `rd_ss_boundsS`). -/
def m4W6SS (n m p s sIn Lg : ℕ) : ℕ :=
  rd6Cost (n + m) n p s sIn (kerCost (n + m) sIn (n + m) + 5) (orbitsCost (n + m) sIn (n + m) + 5)
    (repsCost (n + m) sIn ((n + m) * (n + m)) m.factorial + 7) (genCost (n + m) Lg + 2)

/-- **M4's cost with Schreier–Sims**, for per-orbit work `Wh`: `m4StepCost` at the backend bounds
`ssBoundsS (n + m) sIn` and the leaf stabilizer's charges of `ss_m4Charges` with
`R = msCount (m − j)`. -/
def m4CostSS (n m j p sIn Lg Wh : ℕ) : ℕ :=
  m4StepCost (n + m) m j sIn (orbitsCost (n + m) sIn (n + m) + 5) (stabCost (n + m) sIn + 5)
    (transCost (n + m) sIn + 5)
    ((n + m + msCount (m - j)) * (n + m + msCount (m - j))) (n + m + msCount (m - j))
    (genCost (n + m + msCount (m - j)) sIn + 2)
    (stabCost (n + m + msCount (m - j)) ((n + m + msCount (m - j)) * (n + m + msCount (m - j))) +
      5)
    (transCost (n + m + msCount (m - j))
      ((n + m + msCount (m - j)) * (n + m + msCount (m - j))) + 5)
    (genCost (n + m) ((n + m + msCount (m - j)) * (n + m + msCount (m - j))) + 2) p sIn Wh
    (orbitsCost (n + m) sIn (n + m) + 5) (genCost (n + m) Lg + 2)

/-- **The work of M4 with Schreier–Sims** (general factor): the monotone envelope of `m4CostSS`
with the per-orbit work `m4WhSS` at factor `m!` and stuck work `m4W6SS`, in the string positions
`n`, the base size `m`, the individualization depth `j`, the window `p`, the sub-solver bound
`s`, the label array's size `Ls`, `sIn` and `Lg`. -/
def m4WorkSS (n m j p s Ls sIn Lg : ℕ) : ℕ :=
  envSup [n, m, j, p, s, Ls, sIn, Lg] fun xs =>
    m4CostSS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 6 0) (xs.getD 7 0)
      (m4WhSS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 3 0) (xs.getD 4 0) (xs.getD 5 0) (xs.getD 6 0)
        (xs.getD 7 0) (xs.getD 1 0).factorial
        (m4W6SS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 3 0) (xs.getD 4 0) (xs.getD 6 0)
          (xs.getD 7 0)))

/-- **The work of M4 with Schreier–Sims without stuck orbits**: as `m4WorkSS`, with factor
`max m uB!` and no stuck work. -/
def m4WorkNsSS (n m j p s Ls sIn Lg uB : ℕ) : ℕ :=
  envSup [n, m, j, p, s, Ls, sIn, Lg, uB] fun xs =>
    m4CostSS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 6 0) (xs.getD 7 0)
      (m4WhSS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 3 0) (xs.getD 4 0) (xs.getD 5 0) (xs.getD 6 0)
        (xs.getD 7 0) (max (xs.getD 1 0) (xs.getD 8 0).factorial) 0)

/-- **`m4WhSS` at a union-cell bound `u` for the derived hint's work** (stage 14j-6b-1):
`ssBdJU … u` in place of `ssBdJ`. `m4WhSS` is the case `u = m`. -/
def m4WhUSS (n m p s Ls sIn Lg F W6 u : ℕ) : ℕ :=
  rdOrbitWork (n + m) n p s sIn F (ssBdF n (n + m) p sIn + ssBdJU n (n + m) p Ls sIn u)
    (Sims.liftCost (n + m) sIn n + 7) (genCost (n + m) Lg + 2)
    (orbitsCost (n + m) sIn (n + m) + 5) W6

theorem m4WhSS_eq (n m p s Ls sIn Lg F W6 : ℕ) :
    m4WhSS n m p s Ls sIn Lg F W6 = m4WhUSS n m p s Ls sIn Lg F W6 m := by
  unfold m4WhSS m4WhUSS
  rw [ssBdJ_eq, Nat.add_sub_cancel_left]

/-- **The work of M4 with Schreier–Sims without stuck orbits, with the union cells bounded by
`uB`** (stage 14j-6b-1): as `m4WorkNsSS`, with the derived hint's Johnson fallback also at `uB`
(`m4WhUSS`), so no factorial of `m` when `uB` is the labels' bound. -/
def m4WorkNsLSS (n m j p s Ls sIn Lg uB : ℕ) : ℕ :=
  envSup [n, m, j, p, s, Ls, sIn, Lg, uB] fun xs =>
    m4CostSS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 2 0) (xs.getD 3 0) (xs.getD 6 0) (xs.getD 7 0)
      (m4WhUSS (xs.getD 0 0) (xs.getD 1 0) (xs.getD 3 0) (xs.getD 4 0) (xs.getD 5 0) (xs.getD 6 0)
        (xs.getD 7 0) (max (xs.getD 1 0) (xs.getD 8 0).factorial) 0 (xs.getD 8 0))

theorem m4WorkNsLSS_mono {n n' m m' j j' p p' s s' Ls Ls' sIn sIn' Lg Lg' uB uB' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hj : j ≤ j') (hp : p ≤ p') (hs : s ≤ s') (hL : Ls ≤ Ls')
    (hI : sIn ≤ sIn') (hg : Lg ≤ Lg') (hu : uB ≤ uB') :
    m4WorkNsLSS n m j p s Ls sIn Lg uB ≤ m4WorkNsLSS n' m' j' p' s' Ls' sIn' Lg' uB' :=
  envSup_mono (.cons hn (.cons hm (.cons hj (.cons hp (.cons hs (.cons hL (.cons hI
    (.cons hg (.cons hu .nil))))))))) _

theorem m4WorkSS_mono {n n' m m' j j' p p' s s' Ls Ls' sIn sIn' Lg Lg' : ℕ} (hn : n ≤ n')
    (hm : m ≤ m') (hj : j ≤ j') (hp : p ≤ p') (hs : s ≤ s') (hL : Ls ≤ Ls') (hI : sIn ≤ sIn')
    (hg : Lg ≤ Lg') : m4WorkSS n m j p s Ls sIn Lg ≤ m4WorkSS n' m' j' p' s' Ls' sIn' Lg' :=
  envSup_mono (.cons hn (.cons hm (.cons hj (.cons hp (.cons hs (.cons hL (.cons hI
    (.cons hg .nil)))))))) _

theorem m4WorkNsSS_mono {n n' m m' j j' p p' s s' Ls Ls' sIn sIn' Lg Lg' uB uB' : ℕ}
    (hn : n ≤ n') (hm : m ≤ m') (hj : j ≤ j') (hp : p ≤ p') (hs : s ≤ s') (hL : Ls ≤ Ls')
    (hI : sIn ≤ sIn') (hg : Lg ≤ Lg') (hu : uB ≤ uB') :
    m4WorkNsSS n m j p s Ls sIn Lg uB ≤ m4WorkNsSS n' m' j' p' s' Ls' sIn' Lg' uB' :=
  envSup_mono (.cons hn (.cons hm (.cons hj (.cons hp (.cons hs (.cons hL (.cons hI
    (.cons hg (.cons hu .nil))))))))) _

end Work


/-! ### The corollaries -/

section Step

variable {a b : Ty} {body : a.denote → Prog (groupSig Ty.unit) (a, b) Ty.denote b}
  {sub : HInstData Ty.unit → Prog (groupSig Ty.unit) (a, b) Ty.denote (Ty.answer Ty.unit)}
  {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData} {n₀ n : ℕ}
  {L : LabelData}

/-- The per-orbit hypothesis of reduce-and-derive in M4, for Schreier–Sims, at a union-cell bound
`uD` for the derived hint's work (stage 14j-6b-1): as `ss_m4_hD`, with `ssBdJU … uD`
(`rd_orbit_cj_ssUB`). -/
theorem ss_m4_hDU {gsH gsK : GensData} {o : OutD} {sIn : ℕ} (hN : N * N ≤ sIn)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hHle : GensData.denote N gsH ≤ GensData.denote N gs) {j : ℕ}
    (hinvH : IsInvariant (GensData.denote N gsH) (baseSet (n + j) N))
    (hKden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin (msK (n + j) N))) (decodeOut (msK (n + j) N) o)).comap
        (msPsi (GensData.denote N gsH) (n + j) hinvH)).map (GensData.denote N gsH).subtype)
    (hKG : GensData.denote N gsK ≤ GensData.denote N gs) (hjN : n + j ≤ N)
    (hout : M4Out (msK (n + j) N) o) (hlkj : o.1 = 2 → LkJ (msK (n + j) N) o)
    (hS : 2 * j ≤ N - n) {uD : ℕ}
    (huD : ∀ {t : ℕ} {jd : Align.JData}, JValid (N - n) jd → IsJohnson univ t (jdec (N - n) jd) →
      ∀ O : List ℕ, O.Nodup → O ≠ [] →
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0)
          []).length ≤ uD) :
    ∀ gs' d' O, RDSet ssDV n N gs w L gsK sIn gs' d' O →
      RDOrbit ssCtx body ssDV n N w L (m4StD (N - n) j o) sIn
        (ssBdF n N w.1.length sIn + ssBdJU n N w.1.length L.size sIn uD) gs' d' O := by
  have hKb : IsInvariant (GensData.denote N gsK) (baseSet n N) :=
    fun x hx u hu => hinv x (hKG hx) u hu
  rcases hout with ⟨p₀, ho', -⟩ | ⟨J, ho', hJ, htrim, hdisj⟩
  · have hst1 : (m4StD (N - n) j o).1 ≠ 2 := by
      show (extD (N - n) (m4L (N - n) j) o).1 ≠ 2
      rw [m4_extD_one (m4_tag_inl ho')]
      decide
    exact fun gs' d' O hset =>
      (rd_orbit_free_ssU hst1 hN gs' d' O hset).mono (Nat.le_add_right _ _)
  · obtain ⟨h2, hJv, hJ', hKcj, -⟩ := m4_cj_facts hinv hHle hinvH hKden hKb hjN ho' hJ htrim
      hdisj (hlkj (m4_tag_inr ho')) hS
    exact fun gs' d' O hset =>
      (rd_orbit_cj_ssUB h2 hKb hJv hJ' hKcj hN (fun O hO hne => huD hJv hJ' O hO hne) gs' d' O
        hset).mono (Nat.le_add_left _ _)

/-- The per-orbit hypothesis of reduce-and-derive in M4, for Schreier–Sims, from the facts that
`m4_core` supplies: a partition leaf gives a state without a Johnson structure; a Johnson leaf
gives a valid coloured Johnson structure preserved by `K` (`m4_cj_facts`, which needs `2j ≤ m`). -/
theorem ss_m4_hD {gsH gsK : GensData} {o : OutD} {sIn : ℕ} (hN : N * N ≤ sIn)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hHle : GensData.denote N gsH ≤ GensData.denote N gs) {j : ℕ}
    (hinvH : IsInvariant (GensData.denote N gsH) (baseSet (n + j) N))
    (hKden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin (msK (n + j) N))) (decodeOut (msK (n + j) N) o)).comap
        (msPsi (GensData.denote N gsH) (n + j) hinvH)).map (GensData.denote N gsH).subtype)
    (hKG : GensData.denote N gsK ≤ GensData.denote N gs) (hjN : n + j ≤ N)
    (hout : M4Out (msK (n + j) N) o) (hlkj : o.1 = 2 → LkJ (msK (n + j) N) o)
    (hS : 2 * j ≤ N - n) :
    ∀ gs' d' O, RDSet ssDV n N gs w L gsK sIn gs' d' O →
      RDOrbit ssCtx body ssDV n N w L (m4StD (N - n) j o) sIn
        (ssBdF n N w.1.length sIn + ssBdJ n N w.1.length L.size sIn) gs' d' O :=
  ss_m4_hDU hN hinv hHle hinvH hKden hKG hjN hout hlkj hS fun hJv _ _ hO hne =>
    (ss_union_le hO hne).trans (ss_cells_le hJv)

/-- **M4 with Schreier–Sims, general factor** (`RunsWithin.m4StepProg` at `ssCtx`). For a valid
hinted instance whose base action is transitive and not a giant, with `4 + j ≤ m` and `2j ≤ m`
(`j = m4J`, the Johnson facts of a Johnson leaf), at most `sIn ≥ N²` generators, a sub-solver
with the spec's predicate and `s ≤ sIn`, and `Lg` large enough for `generate`'s inputs
(`hLg`, `hLR`): the spec's conclusion with the work `m4WorkSS n m j |W| s |L| sIn Lg`. No charge,
generator-count, `BackendBounds`, `RDBounds` or `RDOrbit` hypothesis. -/
theorem RunsWithin.m4StepProg_ss
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    {C : ℕ → Option ℕ → ℕ} {s sIn Lg : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hgs : gs.length ≤ sIn) (hN : N * N ≤ sIn) (hs : s ≤ sIn)
    (hLg : (N - n).factorial * (sIn + 1) ≤ Lg)
    (hLR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (sIn + 1) ≤ Lg) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length s L.size sIn Lg) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length ((m4Reps ssCtx.O n (N, gs, ())).length * (N - n).factorial)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps ssCtx.O n (N, gs, ())).length ≤ m4R (N - n) (m4J ssCtx.O n (N, gs, ())) := by
  have hO : MeetsContractOn ssDV rdOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, rdOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hn : n ≤ N := hI.le
  have hinv : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  obtain ⟨hHv, hHl, hinvH0, hr⟩ := ss_m4_pre hI htr hng hk4 hgs hN
  have hKs := ss_m4K_gens_le hI htr hng hk4 hgs hN
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := m4_core hO hPre hI htr hng hk4
    (ssBoundsS N sIn ⊤ hN) hgs le_top (ss_m4Charges hHv hHl hinvH0 hr)
    (C := C) (sIn := sIn) (F := (N - n).factorial)
    fun gsH gsK dK o hinvH hHden hK ho hKv hKden hKG hrs hcov hR hout hlkj => by
      have hKs' : gsK.length ≤ sIn := by rw [hK] at hKs; exact hKs
      have hLr : (m4Reps ssCtx.O n (N, gs, ())).length * (sIn + 1) ≤ Lg :=
        (Nat.mul_le_mul_right _ hR).trans hLR
      have hHle : GensData.denote N gsH ≤ GensData.denote N gs := by
        rw [hHden]
        exact fixFirst_le _ _ _
      have hjN : n + m4J ssCtx.O n (N, gs, ()) ≤ N := by omega
      exact RunsWithin.rdProg_general hO hPre hI hsub (rd_ss_boundsS n N sIn Lg hN) hs hLg hKv
        hKG hKs' hrs hcov hLr
        (ss_m4_hD hN hinv hHle hinvH hKden hKG hjN hout hlkj hS)
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left ?_ _), hok, hg, hch, hR⟩
  have e : n + (N - n) = N := by omega
  refine le_of_eq_of_le ?_ (le_envSup (forall₂_le_refl _) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ, m4CostSS, m4WhSS, m4W6SS, e]
  rfl


/-- **M4 with Schreier–Sims, without stuck orbits, for any union-cell bounds**
(`RunsWithin.m4StepProg_ns` at `ssCtx`; stage 14j-6b-1). Under the hypotheses of
`RunsWithin.m4StepProg_ss` and the numeric conditions of `RunsWithin.m4StepProg_ns`, with `uB` and
`uD` bounding the union labels of every valid Johnson structure (`huF`, `huD`): the spec's
conclusion, with factor `|reps| · max m uB!` and the cost at the instance's sizes, the derived
hint's Johnson fallback charged at `uD` (`m4WhUSS`). -/
theorem RunsWithin.m4StepProg_ns_ssU
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hpart : 4 * max ((N - n - m4J ssCtx.O n (N, gs, ()) + 3) / 2) (m4J ssCtx.O n (N, gs, ())) ≤
      3 * (N - n))
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n) (hm5 : 5 ≤ N - n)
    {C : ℕ → Option ℕ → ℕ} {s sIn Lg uB uD : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hgs : gs.length ≤ sIn) (hN : N * N ≤ sIn) (hs : s ≤ sIn)
    (huF : ∀ {t : ℕ} {jd : Align.JData}, JValid (N - n) jd → IsJohnson univ t (jdec (N - n) jd) →
      ∀ O : List ℕ, O.Nodup → O ≠ [] →
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0)
          []).length ≤ uB)
    (huD : ∀ {t : ℕ} {jd : Align.JData}, JValid (N - n) jd → IsJohnson univ t (jdec (N - n) jd) →
      ∀ O : List ℕ, O.Nodup → O ≠ [] →
        ((labJUD jd.2.1.length (markArr (N - n) jd.1) jd.2.2.2 L O).getD (O.headD 0)
          []).length ≤ uD)
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hLR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (sIn + 1) ≤ Lg) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4CostSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length sIn Lg
            (m4WhUSS n (N - n) w.1.length s L.size sIn Lg (max (N - n) uB.factorial) 0 uD)) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length ((m4Reps ssCtx.O n (N, gs, ())).length * max (N - n) uB.factorial)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps ssCtx.O n (N, gs, ())).length ≤ m4R (N - n) (m4J ssCtx.O n (N, gs, ())) := by
  have hO : MeetsContractOn ssDV rdOps ssCtx.O := fun op x _ hx => ssOracle_meets op x hx
  have hPre : ∀ op x, rdOps op → GroupPre ssDV op x → ssCtx.Pre op x := fun _ _ _ h => h
  have hn : n ≤ N := hI.le
  have hinv : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  obtain ⟨hHv, hHl, hinvH0, hr⟩ := ss_m4_pre hI htr hng hk4 hgs hN
  have hKs := ss_m4K_gens_le hI htr hng hk4 hgs hN
  have hB := rd_ss_boundsS n N sIn Lg hN
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := m4_core hO hPre hI htr hng hk4
    (ssBoundsS N sIn ⊤ hN) hgs le_top (ss_m4Charges hHv hHl hinvH0 hr)
    (C := C) (sIn := sIn) (F := max (N - n) uB.factorial)
    (Wh := rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial)
      (ssBdF n N w.1.length sIn + ssBdJU n N w.1.length L.size sIn uD) (Sims.liftCost N sIn n + 7)
      (genCost N Lg + 2) (orbitsCost N sIn N + 5) 0)
    fun gsH gsK dK o hinvH hHden hK ho hKv hKden hKG hrs hcov hR hout hlkj => by
      have hKs' : gsK.length ≤ sIn := by rw [hK] at hKs; exact hKs
      have hLr : (m4Reps ssCtx.O n (N, gs, ())).length * (sIn + 1) ≤ Lg :=
        (Nat.mul_le_mul_right _ hR).trans hLR
      have hHle : GensData.denote N gsH ≤ GensData.denote N gs := by
        rw [hHden]
        exact fixFirst_le _ _ _
      have hjN : n + m4J ssCtx.O n (N, gs, ()) ≤ N := by omega
      have hD := ss_m4_hDU (body := body) (w := w) (L := L) hN hinv hHle hinvH hKden hKG hjN hout
        hlkj hS huD
      have hKb : IsInvariant (GensData.denote N gsK) (baseSet n N) :=
        fun x hx u hu => hinv x (hKG hx) u hu
      have hk' : msK (n + m4J ssCtx.O n (N, gs, ())) N = N - n - m4J ssCtx.O n (N, gs, ()) := by
        rw [msK_eq]
        omega
      rcases hout with ⟨p₀, ho', hp₀⟩ | ⟨J, ho', hJ, htrim, hdisj⟩
      · obtain ⟨hpv, hpK⟩ := m4_part_facts hinv hHle hinvH hKden hKb hjN ho' hp₀
        have hst1 : (m4StD (N - n) (m4J ssCtx.O n (N, gs, ())) o).1 ≠ 2 := by
          show (extD (N - n) (m4L (N - n) (m4J ssCtx.O n (N, gs, ()))) o).1 ≠ 2
          rw [m4_extD_one (m4_tag_inl ho')]
          decide
        have ht : 4 * max ((msK (n + m4J ssCtx.O n (N, gs, ())) N + 3) / 2)
            (m4J ssCtx.O n (N, gs, ())) ≤ 3 * (N - n) := by
          rw [hk']
          exact hpart
        have hLg' : (N - n) * (sIn + 1) ≤ Lg :=
          (Nat.mul_le_mul_right _ (le_max_left _ _)).trans hLg
        obtain ⟨ans, ch, hrun, hok, hg, hcl⟩ := RunsWithin.rdProg_part_ns hO hPre hI hsub hB hs
          hLg' hKv hKG hKs' hrs hcov hLr hD hst1 hKb hpv hpK ht (by omega)
        refine ⟨ans, ch, hrun.mono ?_, hok, hg, ⟨hcl.sum_le.trans ?_, hcl.pred, hcl.pos⟩⟩
        · exact Nat.add_le_add_left (rdCost_mono_wh (rdOrbitWork_mono (le_max_left _ _))) _
        · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_max_left _ _))
      · obtain ⟨h2, hJv, hJ', hKcj, hq⟩ := m4_cj_facts hinv hHle hinvH hKden hKb hjN ho' hJ
          htrim hdisj (hlkj (m4_tag_inr ho')) hS
        exact RunsWithin.rdProg_cj_ns hO hPre hI hsub hB hs hLg hKv hKG hKs' hrs hcov hLr hD h2
          hKb hJv hJ' hKcj hq hm5 fun _ _ _ hset => huF hJv hJ' _ hset.1.nodup hset.1.ne
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left (le_of_eq ?_) _), hok, hg, hch, hR⟩
  have e : n + (N - n) = N := by omega
  simp only [m4CostSS, m4WhUSS, e]
  rfl


/-- **M4 with Schreier–Sims, without stuck orbits** (`RunsWithin.m4StepProg_ns` at `ssCtx`).
Under the hypotheses of `RunsWithin.m4StepProg_ss` and the numeric conditions of
`RunsWithin.m4StepProg_ns`, with a union-cell bound `uB ≥ m`: the union labels are cell indices,
and a valid Johnson structure has at most `m` cells (`ss_union_le`, `ss_cells_le`). The conclusion
is the spec's, with factor `|reps| · max m uB!` and the work `m4WorkNsSS`. -/
theorem RunsWithin.m4StepProg_ns_ss
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hpart : 4 * max ((N - n - m4J ssCtx.O n (N, gs, ()) + 3) / 2) (m4J ssCtx.O n (N, gs, ())) ≤
      3 * (N - n))
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n) (hm5 : 5 ≤ N - n)
    {C : ℕ → Option ℕ → ℕ} {s sIn Lg uB : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hgs : gs.length ≤ sIn) (hN : N * N ≤ sIn) (hs : s ≤ sIn) (huB : N - n ≤ uB)
    (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hLR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (sIn + 1) ≤ Lg) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkNsSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length s L.size sIn Lg uB) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length ((m4Reps ssCtx.O n (N, gs, ())).length * max (N - n) uB.factorial)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps ssCtx.O n (N, gs, ())).length ≤ m4R (N - n) (m4J ssCtx.O n (N, gs, ())) := by
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := RunsWithin.m4StepProg_ns_ssU hI htr hng hk4 hpart hS
    hm5 hsub hgs hN hs (uD := N - n)
    (fun hJv _ _ hO hne => ((ss_union_le hO hne).trans (ss_cells_le hJv)).trans huB)
    (fun hJv _ _ hO hne => (ss_union_le hO hne).trans (ss_cells_le hJv)) hLg hLR
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left ?_ _), hok, hg, hch, hR⟩
  refine le_of_eq_of_le ?_ (le_envSup (forall₂_le_refl _) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ, m4WhSS_eq]

/-- **M4 with Schreier–Sims, without stuck orbits, with the union cells bounded by the labels**
(stage 14j-6b-1, `PLAN-14.md` §14.11 item 5). As `RunsWithin.m4StepProg_ns_ss`, at
`uB = labLen L · λ(m)` (`ss_union_le_lab`), with no lower bound on `uB`: the factor is
`|reps| · max m (labLen L · λ(m))!`, and the work `m4WorkNsLSS` charges the derived hints'
Johnson fallback at the same bound, so neither has a factorial of `m`. -/
theorem RunsWithin.m4StepProg_nsL_ss
    (hI : HInstValid ssDV (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg ssCtx.O n (N, gs, ()) < N - n - 2) (hk4 : 4 + m4J ssCtx.O n (N, gs, ()) ≤ N - n)
    (hpart : 4 * max ((N - n - m4J ssCtx.O n (N, gs, ()) + 3) / 2) (m4J ssCtx.O n (N, gs, ())) ≤
      3 * (N - n))
    (hS : 2 * m4J ssCtx.O n (N, gs, ()) ≤ N - n) (hm5 : 5 ≤ N - n)
    {C : ℕ → Option ℕ → ℕ} {s sIn Lg : ℕ}
    (hsub : HSubSolves ssCtx body ssDV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    (hgs : gs.length ≤ sIn) (hN : N * N ≤ sIn) (hs : s ≤ sIn)
    (hLg : max (N - n) (labLen L * lam (N - n)).factorial * (sIn + 1) ≤ Lg)
    (hLR : m4R (N - n) (m4J ssCtx.O n (N, gs, ())) * (sIn + 1) ≤ Lg) :
    ∃ (ans : AnswerData Ty.unit) (ch : List (ℕ × Option ℕ)),
      RunsWithin ssCtx body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, ()), n₀, n, some L) : HInstData Ty.unit)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4WorkNsLSS n (N - n) (m4J ssCtx.O n (N, gs, ())) w.1.length s L.size sIn Lg
            (labLen L * lam (N - n))) ∧
      InstData.OK (D := Ty.unit) (xy, w, σd, N, gs, ()) ssDV ans ∧
      (∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length
        ((m4Reps ssCtx.O n (N, gs, ())).length * max (N - n) (labLen L * lam (N - n)).factorial)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps ssCtx.O n (N, gs, ())).length ≤ m4R (N - n) (m4J ssCtx.O n (N, gs, ())) := by
  obtain ⟨ans, ch, hrun, hok, hg, hch, hR⟩ := RunsWithin.m4StepProg_ns_ssU hI htr hng hk4 hpart hS
    hm5 hsub hgs hN hs (fun hJv hJ _ hO _ => ss_union_le_lab hJv hJ hO _)
    (fun hJv hJ _ hO _ => ss_union_le_lab hJv hJ hO _) hLg hLR
  refine ⟨ans, ch, hrun.mono (Nat.add_le_add_left ?_ _), hok, hg, hch, hR⟩
  refine le_of_eq_of_le ?_ (le_envSup (forall₂_le_refl _) _)
  simp only [List.getD_cons_zero, List.getD_cons_succ]

end Step

/-! ### Parameter choices -/

section Params

/-- The bound on `generate`'s inputs for M4 on base size `m` with `j` individualized points. -/
def ssLgM4 (m j sIn : ℕ) : ℕ := (m.factorial + m4R m j) * (sIn + 1)

/-- The bound on `generate`'s inputs for M4 without stuck orbits, with union-cell bound `uB`. -/
def ssLgM4Ns (m j uB sIn : ℕ) : ℕ := (max m uB.factorial + m4R m j) * (sIn + 1)

/-- **M4's parameters**: `sIn = ssSIn N s |gs|` and `Lg = ssLgM4 (N − n) j sIn` meet `hgs`, `hN`,
`hs`, `hLg` and `hLR` of `RunsWithin.m4StepProg_ss` (with `j = m4J …`). The other hypotheses
are the case's conditions (`htr`, `hng`, `hk4`, `2j ≤ m`), which the dispatcher tests. -/
theorem m4_params (N n j s g : ℕ) :
    g ≤ ssSIn N s g ∧ N * N ≤ ssSIn N s g ∧ s ≤ ssSIn N s g ∧
      (N - n).factorial * (ssSIn N s g + 1) ≤ ssLgM4 (N - n) j (ssSIn N s g) ∧
      m4R (N - n) j * (ssSIn N s g + 1) ≤ ssLgM4 (N - n) j (ssSIn N s g) := by
  obtain ⟨h1, h2, h3⟩ := ssSIn_spec N s g
  refine ⟨h3, h1, h2, Nat.mul_le_mul_right _ (Nat.le_add_right _ _),
    Nat.mul_le_mul_right _ (Nat.le_add_left _ _)⟩

/-- **M4's parameters without stuck orbits**: as `m4_params`, with `uB = N − n` and
`Lg = ssLgM4Ns (N − n) j (N − n) sIn` (`huB`, `hLg`, `hLR` of `RunsWithin.m4StepProg_ns_ss`). -/
theorem m4ns_params (N n j s g : ℕ) :
    g ≤ ssSIn N s g ∧ N * N ≤ ssSIn N s g ∧ s ≤ ssSIn N s g ∧ N - n ≤ N - n ∧
      max (N - n) (N - n).factorial * (ssSIn N s g + 1) ≤
        ssLgM4Ns (N - n) j (N - n) (ssSIn N s g) ∧
      m4R (N - n) j * (ssSIn N s g + 1) ≤ ssLgM4Ns (N - n) j (N - n) (ssSIn N s g) := by
  obtain ⟨h1, h2, h3⟩ := ssSIn_spec N s g
  refine ⟨h3, h1, h2, le_rfl, Nat.mul_le_mul_right _ (Nat.le_add_right _ _),
    Nat.mul_le_mul_right _ (Nat.le_add_left _ _)⟩

end Params

end GraphIso.Main
