module

public import GraphIso.Main.M4Bridge
public import GraphIso.Main.M4Struct
public import GraphIso.Main.RD

/-!
# M4 as a step

Stage 14j-3, item 5 (`PLAN-14.md` §14.3). Macro-step M4 for a hinted instance
`I = (σ • G, W, L)` of degree `N`, string positions `[0, n)` and base `[n, N)` (`m = N − n`),
whose base action is transitive and not a giant. `m4StepProg sub I`:

1. the computed degree of transitivity `dg = degreeModel … (m − 2)` (`degreeProg`; the case
   condition, not a giant, is `dg < m − 2`, as `giantModel_iff` reads it), and `j = dg − 1`;
2. individualization: `H = fixFirst G n j`, the pointwise stabilizer of the first `j` base
   positions, with at most `m^j` coset representatives (`pointStabsProg`);
3. the structure of M4 on the remaining base `[n + j, N)` and its stabilizer `K ≤ H`, with at
   most `msCount (m − j)` coset representatives (`m4StructProg`, stage 14j-3 item 4);
4. the composed cover of `G` by `K` (`prodRepsLProg`, `isLeftCover_prodRepsD`);
5. the leaf extended to the whole base (stage 14h's `extD` along the base indices
   `L = [j, m)`), and the structure `st` handed to reduce-and-derive: the tag of the leaf, its
   Johnson data, and the colouring `indColsD m j` (`1` on the individualized points, `0` on the
   rest; it equals `restColsD m L`, `indColsD_eq`);
6. reduce-and-derive (`rdProg`).

There is no alignment: everything depends on `G` alone. Specs:

* `m4_run`: the run of the program from the runs of its parts (any values), the structural
  lemma that keeps the main proofs small.
* `RunsWithin.m4StepProg` (general factor): an answer correct for the instance, the run within
  the children's cost plus `m4StepCost`, the generator bound, `StepChild |W| m` children with
  factor `|reps| · m!`, and `|reps| ≤ m^j · msCount (m − j)`.
* `RunsWithin.m4StepProg_ns` (no stuck orbit): under the numeric conditions
  `4 · max ((m − j + 3)/2) j ≤ 3m` (a partition leaf, extended with the individualized points as
  one class), `2j ≤ m` and `m ≥ 5` (a Johnson leaf, coloured `{individualized, rest}`), with
  `uB` bounding the union cells as in `rdProg_cj_ns`: the extended structure is valid and
  preserved by `K` (`m4_part_facts`, `m4_cj_facts`, through `m4_K_rel`), reduce-and-derive
  meets no stuck orbit, and the factor is `|reps| · max m uB!`.
* `m4_core`: the composition, for any run of reduce-and-derive on the computed structure.
* `m4_deg_le`: the computed degree is at most the true degree of transitivity of the base
  action (any `d` with `¬ (d + 1)`-transitive bounds it); `m4_deg_le_T`: under
  `TransitivityBound T` and a base action not containing the alternating group, it is at most
  `T m`; `m4_numeric`: `2j + 6 ≤ m` gives all the numeric conditions.
* `m4_ps_gens_le`: the individualized group has at most `s` generators for a backend whose
  stabilizers have at most `s` (`BackendBounds.stabOut`).
* `m4Charges_exact`: the leaf stabilizer's charges are on specific inputs, so they hold with
  their own values.
* `wf_m4StepProg`: well-formedness.

The charges: `BackendBounds` for the degree, the individualization and the orbital
configuration; `M4Charges` for the leaf stabilizer on its specific inputs; `RDBounds` and the
per-orbit `RDOrbit` (on the orbits that can occur) for reduce-and-derive, as in `RD.lean`, with
the generator count of `K` (`hKs`) a hypothesis on the computed group and the generation bound
`hLR` numeric (`m4R m j · (sIn + 1) ≤ Lg`).
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Finset Cost MulAction GraphIso GraphIso.Programs GraphIso.Toolkit
  GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree GraphIso.Case2b GraphIso.Align

/-! ### Programs -/

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The colouring of the base indices `[0, m)`: `1` on the first `j` (the individualized
points), `0` on the rest. -/
def indColsProg (m j : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range m) fun xs =>
  .bind (mapList xs fun x => .bind (.op2 .natLt x j) fun b =>
      .ite b (.op0 (.natLit 1)) (.op0 (.natLit 0))) fun l =>
  .op1 .arrayOfList l

/-- The structure handed to reduce-and-derive: the tag of the extended leaf, its Johnson data,
and the colouring of the individualized points. -/
def m4StProg (m j : var .nat) (o : var outTy) : Prog S rec var stTy :=
  .bind (.op1 .fst o) fun tag => .bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun jd =>
  .bind (indColsProg m j) fun cols => .bind (.op2 .pair jd cols) fun cj => .op2 .pair tag cj

/-- **The tail of M4**: from the individualized group `H` and its representatives, the structure
and its stabilizer `K`, the composed cover, the extended structure, and reduce-and-derive. -/
def m4TailProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) (n N j : var .nat) (hr : var (.prod (Ty.group D) (.list Ty.perm))) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst hr) fun H => .bind (.op1 .snd hr) fun reps₁ =>
  .bind (.op2 .add n j) fun n' =>
  .bind (m4StructProg n' H) fun kr =>
  .bind (.op1 .fst kr) fun K => .bind (.op1 .snd kr) fun r₃ =>
  .bind (.op1 .fst r₃) fun reps₂ => .bind (.op1 .snd r₃) fun o =>
  .bind (prodRepsLProg reps₁ reps₂) fun reps =>
  .bind (.op2 .sub N n) fun m => .bind (.op2 .sub m j) fun k =>
  .bind (Toolkit.rangeFromProg j k) fun L =>
  .bind (Case2b.extProg m L o) fun o' =>
  .bind (m4StProg m j o') fun st =>
  rdProg sub I reps K st

/-- **M4 as a step**: the degree of transitivity, the individualization of the first `dg − 1`
base points, and the tail. -/
def m4StepProg (sub : var (hinstTy D) → Prog (groupSig D) rec var (Ty.answer D))
    (I : var (hinstTy D)) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst I) fun J => .bind (.op1 .snd I) fun r₁ =>
  .bind (.op1 .snd r₁) fun r₂ => .bind (.op1 .fst r₂) fun n =>
  .bind (.op1 .snd J) fun wc => .bind (.op1 .snd wc) fun c => .bind (.op1 .snd c) fun G =>
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (.op0 (.natLit 2)) fun two => .bind (.op2 .sub m two) fun cap =>
  .bind (Toolkit.degreeProg n cap G) fun dg =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub dg one) fun j =>
  .bind (Toolkit.rangeFromProg n j) fun S =>
  .bind (Toolkit.pointStabsProg G S) fun hr =>
  m4TailProg sub I n N j hr

end Programs

/-! ### Models and costs -/

section Model

variable {D : Ty}

/-- The colouring `1` on `[0, j)`, `0` on `[j, m)`. -/
def indColsD (m j : ℕ) : Array ℕ := ((List.range m).map fun x => if x < j then 1 else 0).toArray

/-- The base indices `[j, m)`, the image of the remaining base. -/
def m4L (m j : ℕ) : List ℕ := (List.range (m - j)).map (j + ·)

/-- The structure handed to reduce-and-derive, from a leaf `o` on the remaining base. -/
def m4StD (m j : ℕ) (o : OutD) : ℕ × CJData :=
  ((extD m (m4L m j) o).1, ((extD m (m4L m j) o).2.2, indColsD m j))

/-- The computed degree of transitivity (with `cap = m − 2`). -/
def m4Deg (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : ℕ :=
  degreeModel O n (G.1 - n - 2) G

/-- The number of individualized points, `dg − 1`. -/
def m4J (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : ℕ := m4Deg O n G - 1

/-- The individualized group and its representatives. -/
def m4PS (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) :
    GroupData D.denote × List PermData :=
  pointStabsModel O G ((List.range (m4J O n G)).map (n + ·))

/-- The structure, its stabilizer and representatives. -/
def m4Str (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) :
    GroupData D.denote × (List PermData × OutD) :=
  m4StructModel O (n + m4J O n G) (m4PS O n G).1

/-- The stabilizer `K` of the structure. -/
def m4K (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : GroupData D.denote :=
  (m4Str O n G).1

/-- The composed cover of `G` by `K`. -/
def m4Reps (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : List PermData :=
  prodRepsD (m4PS O n G).2 (m4Str O n G).2.1

/-- The structure handed to reduce-and-derive. -/
def m4St (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : ℕ × CJData :=
  m4StD (G.1 - n) (m4J O n G) (m4Str O n G).2.2

/-- The bound on the cover: `m^j · msCount (m − j)`. -/
def m4R (m j : ℕ) : ℕ := m ^ j * msCount (m - j)

/-- **The work of M4** beyond reduce-and-derive's children: degree `N`, `m = N − n`, `j`
individualized points, `s` generators (of `G` and the individualized group), the backend bounds
`Borb`, `Bstab`, `Btr`, the leaf stabilizer's `sS`, `L`, `Bge`, `Bst`, `Btr'`, `Bgt`, and
reduce-and-derive's work `rdCost N p r sIn Wh Bo Bgen` with `r = m4R m j`. -/
def m4StepCost (N m j s Borb Bstab Btr sS L Bge Bst Btr' Bgt p sIn Wh Bo Bgen : ℕ) : ℕ :=
  degreeCost N (m - 2) Borb Bstab + pointStabsCost N m Btr Bstab j +
    m4StructCost N (m - j) s Btr Bstab Borb sS L Bge Bst Btr' Bgt +
    prodRepsLCost N (m ^ j) (msCount (m - j)) +
    extCost m (m - j) (outB (m - j) ((m - j + 3) / 2)) + 5 * j + 5 * (m - j) + 8 * m +
    rdCost N p (m4R m j) sIn Wh Bo Bgen + 60

end Model

/-! ### Small lemmas -/

section Small

theorem indColsD_eq {m j : ℕ} (hj : j ≤ m) : indColsD m j = restColsD m (m4L m j) := by
  unfold indColsD restColsD m4L
  congr 1
  refine List.map_congr_left fun x hx => ?_
  rw [List.mem_range] at hx
  have hmem : x ∈ (List.range (m - j)).map (j + ·) ↔ j ≤ x := by
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨a, -, rfl⟩
      omega
    · intro h
      exact ⟨x - j, by omega, by omega⟩
  have h' : x ∈ (List.range (m - j)).map (j + ·) ↔ ¬ x < j := by rw [hmem]; omega
  by_cases h : x < j
  · simp [h, h']
  · simp [h, h']

theorem m4L_length (m j : ℕ) : (m4L m j).length = m - j := by simp [m4L]

theorem m4L_nodup (m j : ℕ) : (m4L m j).Nodup :=
  (List.nodup_range).map fun a b h => by simpa using h

theorem m4L_lt {m j : ℕ} : ∀ v ∈ m4L m j, v < m := by
  intro v hv
  simp only [m4L, List.mem_map, List.mem_range] at hv
  obtain ⟨a, ha, rfl⟩ := hv
  omega

theorem mem_m4L {m j v : ℕ} : v ∈ m4L m j ↔ j ≤ v ∧ v < m := by
  simp only [m4L, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨v - j, by omega, by omega⟩

theorem range_map_eq_range' (n j : ℕ) : (List.range j).map (n + ·) = List.range' n j :=
  List.range'_eq_map_range.symm

end Small

/-! ### Runs of the pieces -/

section PieceRuns

variable {D : Ty} {S : Signature} {a b : Ty} {X : Ctx S}
  {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.indColsProg (m j : ℕ) :
    RunsWithin X body (Main.indColsProg m j) (indColsD m j) (8 * m + 4) := by
  have hf : ∀ x ∈ List.range m, RunsWithin X body
      (.bind (.op2 .natLt x j) fun b => .ite b (.op0 (.natLit 1)) (.op0 (.natLit 0)))
      (if x < j then 1 else 0) 3 := by
    intro x _
    refine RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.ite (k := 1) ?_)
      (by simp [Prim.cost])
    by_cases h : x < j
    · simp only [Prim.eval, h, decide_true, Bool.cond_true, ite_true]
      exact RunsWithin.prim_le rfl (by simp [Prim.cost])
    · simp only [Prim.eval, h, decide_false, Bool.cond_false, ite_false]
      exact RunsWithin.prim_le rfl (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    unfold Main.indColsProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le hf)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_map]
    omega

theorem RunsWithin.m4StProg (m j : ℕ) (o : OutD) :
    RunsWithin X body (Main.m4StProg m j o) (o.1, (o.2.2, indColsD m j)) (8 * m + 9) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.m4StProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.indColsProg m j)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost]
    omega

end PieceRuns

/-! ### The run of the program from its parts -/

section Run

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}

/-- **The run of M4 from the runs of its parts**, for any values: the degree `dg`, the
individualized group and representatives `ps`, the structure `sm`, and reduce-and-derive. -/
theorem m4_run {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {lab : Option LabelData} {dg cdeg : ℕ}
    (hdeg : RunsWithin X body (Toolkit.degreeProg n (N - n - 2) (N, gs, d)) dg cdeg)
    {ps : GroupData D.denote × List PermData} {cps : ℕ}
    (hps : RunsWithin X body
      (Toolkit.pointStabsProg (N, gs, d) ((List.range (dg - 1)).map (n + ·))) ps cps)
    {sm : GroupData D.denote × (List PermData × OutD)} {csm : ℕ}
    (hsm : RunsWithin X body (Main.m4StructProg (n + (dg - 1)) ps.1) sm csm)
    (hr₁ : ∀ r ∈ ps.2, PermData.Valid N r) (hr₂ : ∀ r ∈ sm.2.1, PermData.Valid N r)
    {ans : AnswerData D} {crd : ℕ}
    (hrd : RunsWithin X body
      (Main.rdProg sub (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D)
        (prodRepsD ps.2 sm.2.1) sm.1 (m4StD (N - n) (dg - 1) sm.2.2)) ans crd) :
    RunsWithin X body (Main.m4StepProg sub (((xy, w, σd, N, gs, d), n₀, n, lab) : HInstData D))
      ans (cdeg + 5 * (dg - 1) + cps + csm + prodRepsLCost N ps.2.length sm.2.1.length +
        5 * (N - n - (dg - 1)) + extCost (N - n) (N - n - (dg - 1)) (outSize sm.2.2) +
        8 * (N - n) + crd + 40) := by
  apply RunsWithin.mono
  case h =>
    unfold Main.m4StepProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hdeg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.rangeFromProg n (dg - 1))
    run_step hps
    unfold Main.m4TailProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hsm
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prodRepsLProg hr₁ hr₂)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.rangeFromProg (dg - 1) (N - n - (dg - 1)))
    run_step (RunsWithin.extProg (N - n) (m4L (N - n) (dg - 1)) sm.2.2)
    run_step (RunsWithin.m4StProg (N - n) (dg - 1) (extD (N - n) (m4L (N - n) (dg - 1)) sm.2.2))
    exact hrd
  case hc =>
    simp only [Prim.cost, Prim.eval, m4L_length]
    omega

end Run

/-! ### Supporting lemmas -/

section Support

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- The group of `pointStabsModel` is the iterated stabilizer. -/
theorem m4_ps_fst (O : Oracle (groupSig D)) :
    ∀ (ps : List ℕ) (acc : GroupData D.denote × List PermData),
      (ps.foldl (psStep O) acc).1 = iterStabModel O acc.1 ps := by
  intro ps
  induction ps with
  | nil => intro acc; rfl
  | cons u ps ih =>
    intro acc
    rw [List.foldl_cons, ih]
    rfl

/-- **The individualized group has at most `s` generators** for a backend whose stabilizers have
at most `s` (`BackendBounds.stabOut`). -/
theorem m4_ps_gens_le (hO : MeetsContractOn DV stabOps X.O) {N s : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s G₀) {gs : GensData}
    {d : D.denote} (hG : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀) {ps : List ℕ} (hps : ∀ u ∈ ps, u < N) :
    (pointStabsModel X.O (N, gs, d) ps).1.2.1.length ≤ s := by
  unfold pointStabsModel
  rw [m4_ps_fst]
  exact Case2b.cp2_iterStab_gens_le hO B ps (N, gs, d) hps rfl hG hs hG₀

/-- Transitivity and non-2-transitivity transfer along an equality of groups. -/
theorem m4_trans_congr {N n' : ℕ} {A B : Subgroup (Perm (Fin N))} (h : A = B)
    (hA : IsInvariant A (baseSet n' N)) (hB : IsInvariant B (baseSet n' N)) :
    ((∀ γ δ : Fin (N - n'), ∃ g : ↥A, baseHom A n' hA g γ = δ) →
      ∀ γ δ : Fin (N - n'), ∃ g : ↥B, baseHom B n' hB g γ = δ) ∧
    (¬ IsMultiplyPretransitive (baseHom A n' hA).range (Fin (N - n')) 2 →
      ¬ IsMultiplyPretransitive (baseHom B n' hB).range (Fin (N - n')) 2) := by
  subst h
  exact ⟨id, id⟩

theorem m4StructCost_mono {N k s s' Btr Bstab Borb sS L Bge Bst Btr' Bgt : ℕ} (h : s ≤ s') :
    m4StructCost N k s Btr Bstab Borb sS L Bge Bst Btr' Bgt ≤
      m4StructCost N k s' Btr Bstab Borb sS L Bge Bst Btr' Bgt := by
  unfold m4StructCost
  have := Nat.pow_le_pow_left
    (show N + k + s + msCount k + outB k ((k + 3) / 2) + 2 ≤
      N + k + s' + msCount k + outB k ((k + 3) / 2) + 2 by omega) 8
  omega

theorem prodRepsLCost_mono {N a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    prodRepsLCost N a b ≤ prodRepsLCost N a' b' := by
  unfold prodRepsLCost
  have h1 : b * (12 * N + 18) + 4 ≤ b' * (12 * N + 18) + 4 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ hb) _
  have h2 := Nat.mul_le_mul ha h1
  omega

theorem extCost_mono {m P L L' : ℕ} (h : L ≤ L') : extCost m P L ≤ extCost m P L' := by
  unfold extCost
  have h1 := Nat.mul_le_mul_left m (show 32 * P + 9 * L + 40 ≤ 32 * P + 9 * L' + 40 by omega)
  have h2 := Nat.mul_le_mul h (show 9 * L + 8 ≤ 9 * L' + 8 by omega)
  omega

theorem rdCost_mono {N p r r' sIn Wh Bo Bgen : ℕ} (h : r ≤ r') :
    rdCost N p r sIn Wh Bo Bgen ≤ rdCost N p r' sIn Wh Bo Bgen := by
  unfold rdCost
  have := Nat.mul_le_mul_right (24 * N + (p * Wh + dynSeqCost N p Bo + 10) + sIn + 45) h
  omega

end Support

/-! ### The core of the spec -/

section Core

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem m4_degOps {op : GroupOp} (h : degreeOps op) : rdOps op := by
  rcases h with h | h <;> simp [rdOps, h]

theorem m4_stabOps {op : GroupOp} (h : stabOps op) : rdOps op := by
  rcases h with h | h <;> simp [rdOps, h]

theorem m4_structOps {op : GroupOp} (h : m4StructOps op) : rdOps op := by
  rcases h with h | h | h | h <;> simp [rdOps, h]

/-- **The core of M4**: from a run of reduce-and-derive on the computed structure (`hRD`, given
the facts about the stabilizer `K = (N, gsK, dK)` and the leaf `o`), the run of the whole step,
with the work `m4StepCost` and the cover bound `|reps| ≤ m^j · msCount (m − j)`. -/
theorem m4_core (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg X.O n (N, gs, d) < N - n - 2) (hk4 : 4 + m4J X.O n (N, gs, d) ≤ N - n)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s₀ G₀)
    (hs₀ : gs.length ≤ s₀) (hG₀ : GensData.denote N gs ≤ G₀) {sS Lt Bge Bst Btr Bgt : ℕ}
    (hB4 : M4Charges X (n + m4J X.O n (N, gs, d)) N (m4PS X.O n (N, gs, d)).1.2.1
      (msLeaf X.O (n + m4J X.O n (N, gs, d)) (m4PS X.O n (N, gs, d)).1) sS Lt Bge Bst Btr Bgt)
    {C : ℕ → Option ℕ → ℕ} {sIn F Wh Bo Bgen : ℕ}
    (hRD : ∀ (gsH gsK : GensData) (dK : D.denote) (o : OutD)
      (hinvH : IsInvariant (GensData.denote N gsH) (baseSet (n + m4J X.O n (N, gs, d)) N)),
      GensData.denote N gsH = fixFirst (GensData.denote N gs) n (m4J X.O n (N, gs, d)) →
      m4K X.O n (N, gs, d) = (N, gsK, dK) → (m4Str X.O n (N, gs, d)).2.2 = o →
      GroupValid DV N gsK dK →
      GensData.denote N gsK =
        ((MulAction.stabilizer (Perm (Fin (msK (n + m4J X.O n (N, gs, d)) N)))
          (decodeOut (msK (n + m4J X.O n (N, gs, d)) N) o)).comap
            (msPsi (GensData.denote N gsH) (n + m4J X.O n (N, gs, d)) hinvH)).map
          (GensData.denote N gsH).subtype →
      GensData.denote N gsK ≤ GensData.denote N gs →
      (∀ r ∈ m4Reps X.O n (N, gs, d), PermData.Valid N r) →
      IsLeftCover (GensData.denote N gs) (GensData.denote N gsK)
        (fun i : Fin (m4Reps X.O n (N, gs, d)).length =>
          PermData.denote N ((m4Reps X.O n (N, gs, d)).get i)) →
      (m4Reps X.O n (N, gs, d)).length ≤ m4R (N - n) (m4J X.O n (N, gs, d)) →
      M4Out (msK (n + m4J X.O n (N, gs, d)) N) o →
      (o.1 = 2 → LkJ (msK (n + m4J X.O n (N, gs, d)) N) o) →
      ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
        RunsWithin X body
          (Main.rdProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D)
            (m4Reps X.O n (N, gs, d)) (N, gsK, dK) (m4StD (N - n) (m4J X.O n (N, gs, d)) o))
          ans ((ch.map fun x => C x.1 x.2).sum +
            rdCost N w.1.length (m4Reps X.O n (N, gs, d)).length sIn Wh Bo Bgen) ∧
        InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
        (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
        ChildList w.1.length ((m4Reps X.O n (N, gs, d)).length * F)
          (StepChild w.1.length (N - n)) ch) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4StepCost N (N - n) (m4J X.O n (N, gs, d)) s₀ B.Borb B.Bstab B.Btr sS Lt Bge Bst Btr
            Bgt w.1.length sIn Wh Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length ((m4Reps X.O n (N, gs, d)).length * F)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps X.O n (N, gs, d)).length ≤ m4R (N - n) (m4J X.O n (N, gs, d)) := by
  have hOdeg : MeetsContractOn DV degreeOps X.O := fun op x h hx => hO op x (m4_degOps h) hx
  have hPdeg : ∀ op x, degreeOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (m4_degOps h) hx
  have hOs : MeetsContractOn DV stabOps X.O := fun op x h hx => hO op x (m4_stabOps h) hx
  have hPs : ∀ op x, stabOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (m4_stabOps h) hx
  have hOm : MeetsContractOn DV m4StructOps X.O := fun op x h hx => hO op x (m4_structOps h) hx
  have hPm : ∀ op x, m4StructOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (m4_structOps h) hx
  have hn : n ≤ N := hI.le
  have hinv : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  have hG : GroupValid DV N gs d := hI.valid.group
  -- the degree and the individualization
  have hdegrun := Toolkit.RunsWithin.degreeProg (body := body) (cap := N - n - 2) hOdeg hPdeg B
    hG hs₀ hG₀ hinv hn
  obtain ⟨hd1, hdm, htrH, h2H⟩ := indiv_of_degree hOdeg B hG hs₀ hG₀ hinv hn (cap := N - n - 2)
    (by omega) htr hng
  have hjd : m4J X.O n (N, gs, d) + 1 ≤ N - n := by
    have : m4Deg X.O n (N, gs, d) + 1 ≤ N - n := hdm
    unfold m4J
    omega
  have hS : ∀ u ∈ (List.range (m4J X.O n (N, gs, d))).map (n + ·), n ≤ u ∧ u < N := by
    intro u hu
    simp only [List.mem_map, List.mem_range] at hu
    obtain ⟨i, hi, rfl⟩ := hu
    omega
  obtain ⟨hpsrun, hpsN₀, hpsv₀, hpsden, hpsrv₀, hpscov₀, hpslen₀⟩ :=
    Toolkit.RunsWithin.pointStabsProg (body := body) hOs hPs hG hinv hS B hs₀ hG₀
  have hpsN : (m4PS X.O n (N, gs, d)).1.1 = N := hpsN₀
  have hpsv : GroupValid DV N (m4PS X.O n (N, gs, d)).1.2.1 (m4PS X.O n (N, gs, d)).1.2.2 :=
    hpsv₀
  have hpsrv : ∀ r ∈ (m4PS X.O n (N, gs, d)).2, PermData.Valid N r := hpsrv₀
  have hpscov : IsLeftCover (GensData.denote N gs)
      (GensData.denote N (m4PS X.O n (N, gs, d)).1.2.1)
      (fun i : Fin (m4PS X.O n (N, gs, d)).2.length =>
        PermData.denote N ((m4PS X.O n (N, gs, d)).2.get i)) := hpscov₀
  have hpslen : (m4PS X.O n (N, gs, d)).2.length ≤
      (N - n) ^ ((List.range (m4J X.O n (N, gs, d))).map (n + ·)).length := hpslen₀
  have hHden : GensData.denote N (m4PS X.O n (N, gs, d)).1.2.1 =
      fixFirst (GensData.denote N gs) n (m4J X.O n (N, gs, d)) := by
    show GensData.denote N (pointStabsModel X.O (N, gs, d)
      ((List.range (m4J X.O n (N, gs, d))).map (n + ·))).1.2.1 = _
    rw [hpsden, range_map_eq_range', pointwiseStab_range']
  have hsH : (m4PS X.O n (N, gs, d)).1.2.1.length ≤ s₀ :=
    m4_ps_gens_le hOs B hG hs₀ hG₀ fun u hu => (hS u hu).2
  have hinvH : IsInvariant (GensData.denote N (m4PS X.O n (N, gs, d)).1.2.1)
      (baseSet (n + m4J X.O n (N, gs, d)) N) := by
    rw [hHden]
    exact fixFirst_base_inv hinv _
  obtain ⟨htrH', h2H'⟩ := m4_trans_congr hHden.symm (fixFirst_base_inv hinv _) hinvH
  have htrH'' := htrH' htrH
  have h2H'' := h2H' h2H
  have hHle : GensData.denote N (m4PS X.O n (N, gs, d)).1.2.1 ≤ GensData.denote N gs := by
    rw [hHden]
    exact fixFirst_le _ _ _
  have hn' : n + m4J X.O n (N, gs, d) < N := by omega
  have hk4' : 4 ≤ N - (n + m4J X.O n (N, gs, d)) := by omega
  -- the structure
  have hP1 : (m4PS X.O n (N, gs, d)).1 =
      (N, (m4PS X.O n (N, gs, d)).1.2.1, (m4PS X.O n (N, gs, d)).1.2.2) := Prod.ext hpsN rfl
  have hB4' : M4Charges X (n + m4J X.O n (N, gs, d)) N (m4PS X.O n (N, gs, d)).1.2.1
      (msLeaf X.O (n + m4J X.O n (N, gs, d))
        (N, (m4PS X.O n (N, gs, d)).1.2.1, (m4PS X.O n (N, gs, d)).1.2.2)) sS Lt Bge Bst Btr
      Bgt := by
    rw [← hP1]
    exact hB4
  have hstr := RunsWithin.m4StructProg (body := body) hOm hPm B hpsv hsH (hHle.trans hG₀) hinvH
    hn' htrH'' h2H'' hk4' hB4'
  obtain ⟨hKN, hKv, hKden, hr₂v, hKcov, hr₂len, -, hout, hlkj, hosz, -⟩ :=
    m4Struct_spec hOm hPm hpsv hinvH hn' htrH'' h2H'' hk4' hB4'
  rw [← hP1] at hstr hKN hKv hKden hr₂v hKcov hr₂len hout hlkj hosz
  have hstrE : m4Str X.O n (N, gs, d) =
      m4StructModel X.O (n + m4J X.O n (N, gs, d)) (m4PS X.O n (N, gs, d)).1 := rfl
  rw [← hstrE] at hKN hKv hKden hr₂v hKcov hr₂len hout hlkj hosz
  have hK1 : (m4Str X.O n (N, gs, d)).1 =
      (N, (m4Str X.O n (N, gs, d)).1.2.1, (m4Str X.O n (N, gs, d)).1.2.2) := Prod.ext hKN rfl
  have hKH : GensData.denote N (m4Str X.O n (N, gs, d)).1.2.1 ≤
      GensData.denote N (m4PS X.O n (N, gs, d)).1.2.1 := by
    have : GensData.denote N (m4Str X.O n (N, gs, d)).1.2.1 = _ := hKden
    rw [this]
    exact Subgroup.map_subtype_le _
  have hr₁v : ∀ r ∈ (m4PS X.O n (N, gs, d)).2, PermData.Valid N r := hpsrv
  have hpsrun' : RunsWithin X body (Toolkit.pointStabsProg (N, gs, d)
      ((List.range (m4Deg X.O n (N, gs, d) - 1)).map (n + ·))) (m4PS X.O n (N, gs, d))
      (pointStabsCost N (N - n) B.Btr B.Bstab
        ((List.range (m4J X.O n (N, gs, d))).map (n + ·)).length) := hpsrun
  have hrsv : ∀ r ∈ m4Reps X.O n (N, gs, d), PermData.Valid N r := prodRepsD_valid hr₁v hr₂v
  have hcov := isLeftCover_prodRepsD hr₁v hr₂v hpscov hKcov hHle
  -- the bounds
  have hlen₁ : (m4PS X.O n (N, gs, d)).2.length ≤ (N - n) ^ m4J X.O n (N, gs, d) := by
    have := hpslen
    simp only [List.length_map, List.length_range] at this
    exact this
  have hk : msK (n + m4J X.O n (N, gs, d)) N = N - n - m4J X.O n (N, gs, d) := by
    rw [msK_eq]
    omega
  have hlen₂ : (m4Str X.O n (N, gs, d)).2.1.length ≤
      msCount (N - n - m4J X.O n (N, gs, d)) := by
    rw [← hk]
    exact hr₂len
  have hR : (m4Reps X.O n (N, gs, d)).length ≤ m4R (N - n) (m4J X.O n (N, gs, d)) := by
    unfold m4Reps m4R
    rw [length_prodRepsD]
    exact Nat.mul_le_mul hlen₁ hlen₂
  obtain ⟨ans, ch, hrd, hok, hg, hcl⟩ := hRD (m4PS X.O n (N, gs, d)).1.2.1
    (m4Str X.O n (N, gs, d)).1.2.1
    (m4Str X.O n (N, gs, d)).1.2.2 (m4Str X.O n (N, gs, d)).2.2 hinvH hHden hK1 rfl hKv hKden
    (hKH.trans hHle) hrsv hcov hR hout hlkj
  have hrd' : RunsWithin X body
      (Main.rdProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D)
        (prodRepsD (m4PS X.O n (N, gs, d)).2 (m4Str X.O n (N, gs, d)).2.1)
        (m4Str X.O n (N, gs, d)).1
        (m4StD (N - n) (m4Deg X.O n (N, gs, d) - 1) (m4Str X.O n (N, gs, d)).2.2)) ans
      ((ch.map fun x => C x.1 x.2).sum +
        rdCost N w.1.length (m4Reps X.O n (N, gs, d)).length sIn Wh Bo Bgen) := by
    rw [hK1]
    exact hrd
  have hrun := m4_run (dg := m4Deg X.O n (N, gs, d)) hdegrun hpsrun' hstr hr₁v hr₂v hrd'
  have hosz' : outSize (m4Str X.O n (N, gs, d)).2.2 ≤
      outB (N - n - m4J X.O n (N, gs, d)) ((N - n - m4J X.O n (N, gs, d) + 3) / 2) := by
    rw [← hk]
    exact hosz
  refine ⟨ans, ch, hrun.mono ?_, hok, hg, hcl, hR⟩
  have e1 : N - (n + m4J X.O n (N, gs, d)) = N - n - m4J X.O n (N, gs, d) := by omega
  have c1 := m4StructCost_mono (N := N) (k := N - n - m4J X.O n (N, gs, d)) (Btr := B.Btr)
    (Bstab := B.Bstab) (Borb := B.Borb) (sS := sS) (L := Lt) (Bge := Bge) (Bst := Bst)
    (Btr' := Btr) (Bgt := Bgt) hsH
  have c2 := prodRepsLCost_mono (N := N) hlen₁ hlen₂
  have c3 := extCost_mono (m := N - n) (P := N - n - m4J X.O n (N, gs, d)) hosz'
  have c4 := rdCost_mono (N := N) (p := w.1.length) (sIn := sIn) (Wh := Wh) (Bo := Bo)
    (Bgen := Bgen) hR
  have hjj : m4Deg X.O n (N, gs, d) - 1 = m4J X.O n (N, gs, d) := rfl
  simp only [List.length_map, List.length_range, e1, hjj] at c1 c2 c3 c4 ⊢
  unfold m4StepCost
  rw [← hstrE]
  omega

end Core

/-! ### M4 with the general factor -/

section General

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **M4 as a step, general factor.** For a valid hinted instance whose base action is transitive
and not a giant (`m4Deg … < m − 2`), with at least four remaining base points
(`4 + j ≤ m`): an answer correct for the instance, the run within the children's cost plus
`m4StepCost`, the generator bound, `StepChild |W| m` children with factor `|reps| · m!`, and
the cover bound `|reps| ≤ m^j · msCount (m − j)` (`m4R`). The charges: `BackendBounds` for the
degree, the individualization and the orbital configuration; `M4Charges` for the leaf
stabilizer; `RDBounds`, the generator count `hKs` of the computed `K`, the numeric `hLR`, and
the per-orbit `RDOrbit` (`hD`) for reduce-and-derive, on the computed `K` and structure. -/
theorem RunsWithin.m4StepProg (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg X.O n (N, gs, d) < N - n - 2) (hk4 : 4 + m4J X.O n (N, gs, d) ≤ N - n)
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    {sIn : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s₀ G₀)
    (hs₀ : gs.length ≤ s₀) (hG₀ : GensData.denote N gs ≤ G₀) {sS Lt Bge Bst Btr Bgt : ℕ}
    (hB4 : M4Charges X (n + m4J X.O n (N, gs, d)) N (m4PS X.O n (N, gs, d)).1.2.1
      (msLeaf X.O (n + m4J X.O n (N, gs, d)) (m4PS X.O n (N, gs, d)).1) sS Lt Bge Bst Btr Bgt)
    {Lg Blift Bgen Bo Bk Bcr Bd : ℕ} (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hs : s ≤ sIn) (hLg : (N - n).factorial * (sIn + 1) ≤ Lg)
    (hKs : (m4K X.O n (N, gs, d)).2.1.length ≤ sIn)
    (hLR : m4R (N - n) (m4J X.O n (N, gs, d)) * (sIn + 1) ≤ Lg)
    (hD : ∀ gs' d' O, RDSet DV n N gs w L (m4K X.O n (N, gs, d)).2.1 sIn gs' d' O →
      RDOrbit X body DV n N w L (m4St X.O n (N, gs, d)) sIn Bd gs' d' O) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4StepCost N (N - n) (m4J X.O n (N, gs, d)) s₀ B.Borb B.Bstab B.Btr sS Lt Bge Bst Btr
            Bgt w.1.length sIn
            (rdOrbitWork N n w.1.length s sIn (N - n).factorial Bd Blift Bgen Bo
              (rd6Cost N n w.1.length s sIn Bk Bo Bcr Bgen)) Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length ((m4Reps X.O n (N, gs, d)).length * (N - n).factorial)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps X.O n (N, gs, d)).length ≤ m4R (N - n) (m4J X.O n (N, gs, d)) := by
  refine m4_core hO hPre hI htr hng hk4 B hs₀ hG₀ hB4
    fun gsH gsK dK o hinvH _ hK ho hKv _ hKG hrs hcov hR _ _ => ?_
  have hKs' : gsK.length ≤ sIn := by
    have := hKs
    rw [hK] at this
    exact this
  have hLr : (m4Reps X.O n (N, gs, d)).length * (sIn + 1) ≤ Lg :=
    (Nat.mul_le_mul_right _ hR).trans hLR
  have hst : m4St X.O n (N, gs, d) = m4StD (N - n) (m4J X.O n (N, gs, d)) o := by
    unfold m4St
    rw [ho]
  have hD' : ∀ gs' d' O, RDSet DV n N gs w L gsK sIn gs' d' O →
      RDOrbit X body DV n N w L (m4StD (N - n) (m4J X.O n (N, gs, d)) o) sIn Bd gs' d' O := by
    intro gs' d' O hset
    have := hD gs' d' O (by rw [hK]; exact hset)
    rw [hst] at this
    exact this
  exact RunsWithin.rdProg_general hO hPre hI hsub hB hs hLg hKv hKG hKs' hrs hcov hLr hD'

end General

/-! ### The extended structure is valid and preserved -/

section StructFacts

/-- The numbering of the remaining base `[n + j, N)` by base indices `[j, m)`. -/
def m4E (n N j : ℕ) : Fin (msK (n + j) N) ↪ Fin (N - n) :=
  shE (m4L (N - n) j) (msK (n + j) N) (by rw [m4L_length, msK_eq]; omega) m4L_lt (m4L_nodup _ _)

theorem m4E_val (n N j : ℕ) (i : Fin (msK (n + j) N)) : (m4E n N j i).val = j + i.val := by
  simp [m4E, shE_val, m4L]

theorem m4_hwb (n j N : ℕ) : ∀ i ∈ (baseWin (n + j) N).1, n ≤ i := fun i hi => by
  have := (mem_basePts.1 hi).1
  omega

/-- The numbering of the window of stage 14d's leaf stabilizer is `m4E`. -/
theorem m4_winE_eq (n N j : ℕ) :
    winE (ms_win_valid (n + j) N) (m4_hwb n j N) = m4E n N j := by
  ext i
  rw [winE_val, m4E_val]
  have hi : i.val < (basePts (n + j) N).length := i.2
  show (basePts (n + j) N)[i.val] - n = j + i.val
  rw [getElem_basePts]
  omega

theorem m4_mem_L (n N j : ℕ) (x : Fin (N - n)) :
    x.val ∈ m4L (N - n) j ↔ ∃ i, m4E n N j i = x :=
  mem_iff_shE _ _ _ _ _ x

theorem m4_tag_inl {k : ℕ} {o : OutD} {p : CPart (Fin k)}
    (h : decodeOut k o = some (.inl p)) : o.1 = 1 := by
  unfold decodeOut at h
  split_ifs at h with h1 h2 <;> simp_all

theorem m4_tag_inr {k : ℕ} {o : OutD} {J : JEmb (Fin k)}
    (h : decodeOut k o = some (.inr J)) : o.1 = 2 := by
  unfold decodeOut at h
  split_ifs at h with h1 h2 <;> simp_all

theorem m4_extD_one {m : ℕ} {L : List ℕ} {o : OutD} (h : o.1 = 1) : (extD m L o).1 = 1 := by
  unfold extD
  simp [h, partD]

variable {N n j : ℕ} {gs gsH gsK : GensData}

/-- **Every element of the leaf stabilizer acts on the remaining base as a permutation fixing
the leaf**, carried by `m4E` to its base action. -/
theorem m4_K_rel (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hHle : GensData.denote N gsH ≤ GensData.denote N gs)
    (hinvH : IsInvariant (GensData.denote N gsH) (baseSet (n + j) N)) {o : OutD}
    (hKden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin (msK (n + j) N))) (decodeOut (msK (n + j) N) o)).comap
        (msPsi (GensData.denote N gsH) (n + j) hinvH)).map (GensData.denote N gsH).subtype)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (g : ↥(GensData.denote N gsK)) :
    ∃ π : Perm (Fin (msK (n + j) N)),
      (∀ i, m4E n N j (π i) = baseHom (GensData.denote N gsK) n hKb g (m4E n N j i)) ∧
        π • decodeOut (msK (n + j) N) o = decodeOut (msK (n + j) N) o := by
  have hg : g.1 ∈ ((MulAction.stabilizer (Perm (Fin (msK (n + j) N)))
      (decodeOut (msK (n + j) N) o)).comap (msPsi (GensData.denote N gsH) (n + j) hinvH)).map
        (GensData.denote N gsH).subtype := by
    rw [← hKden]
    exact g.2
  obtain ⟨h, hh, he⟩ := Subgroup.mem_map.1 hg
  have hinvHn : IsInvariant (GensData.denote N gsH) (baseSet n N) :=
    fun x hx u hu => hinv x (hHle hx) u hu
  refine ⟨msPsi (GensData.denote N gsH) (n + j) hinvH h, fun i => ?_,
    MulAction.mem_stabilizer_iff.1 (Subgroup.mem_comap.1 hh)⟩
  rw [baseHom_congr hKb hinvHn g h he.symm]
  have := baseHom_winE hinvHn (ms_win_valid (n + j) N) (m4_hwb n j N) (ms_win_inv hinvH) h i
  rw [m4_winE_eq] at this
  exact this.symm

/-- **A partition leaf, extended**: a colored `max ((k + 3)/2) j`-partition of the base, preserved
by the leaf stabilizer. -/
theorem m4_part_facts (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hHle : GensData.denote N gsH ≤ GensData.denote N gs)
    (hinvH : IsInvariant (GensData.denote N gsH) (baseSet (n + j) N)) {o : OutD}
    (hKden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin (msK (n + j) N))) (decodeOut (msK (n + j) N) o)).comap
        (msPsi (GensData.denote N gsH) (n + j) hinvH)).map (GensData.denote N gsH).subtype)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hjN : n + j ≤ N)
    {p₀ : CPart (Fin (msK (n + j) N))} (ho : decodeOut (msK (n + j) N) o = some (.inl p₀))
    (hp₀ : IsColPart univ ((msK (n + j) N + 3) / 2) p₀) :
    IsColPart univ (max ((msK (n + j) N + 3) / 2) j) (extPart (m4E n N j) p₀) ∧
      ∀ g : ↥(GensData.denote N gsK),
        baseHom (GensData.denote N gsK) n hKb g • extPart (m4E n N j) p₀ =
          extPart (m4E n N j) p₀ := by
  refine ⟨?_, fun g => ?_⟩
  · have h := extPart_valid (e := m4E n N j) hp₀
    have hc : (univ \ univ.map (m4E n N j)).card = j := by
      rw [card_sdiff_of_subset (subset_univ _), card_map, card_univ, card_univ, Fintype.card_fin,
        Fintype.card_fin, msK_eq]
      omega
    rwa [hc] at h
  · obtain ⟨π, he, hπ⟩ := m4_K_rel hinv hHle hinvH hKden hKb g
    rw [ho, Option.smul_some, Sum.smul_inl] at hπ
    have hπp : π • p₀ = p₀ := Sum.inl_injective (Option.some_injective _ hπ)
    have := extPart_relabel (baseHom (GensData.denote N gsK) n hKb g) π he p₀
    rw [hπp] at this
    exact this.symm

/-- **A Johnson leaf, extended and coloured**: the data are valid Johnson data of the base, the
coloured structure (`1` on the individualized points) is preserved by the leaf stabilizer, and
each colour class off `V₀` has at most `m/2` points when `2j ≤ m`. -/
theorem m4_cj_facts (hinv : IsInvariant (GensData.denote N gs) (baseSet n N))
    (hHle : GensData.denote N gsH ≤ GensData.denote N gs)
    (hinvH : IsInvariant (GensData.denote N gsH) (baseSet (n + j) N)) {o : OutD}
    (hKden : GensData.denote N gsK =
      ((MulAction.stabilizer (Perm (Fin (msK (n + j) N))) (decodeOut (msK (n + j) N) o)).comap
        (msPsi (GensData.denote N gsH) (n + j) hinvH)).map (GensData.denote N gsH).subtype)
    (hKb : IsInvariant (GensData.denote N gsK) (baseSet n N)) (hjN : n + j ≤ N)
    {J : JEmb (Fin (msK (n + j) N))} (ho : decodeOut (msK (n + j) N) o = some (.inr J))
    (hJ : IsJohnson univ ((msK (n + j) N + 3) / 2) J) (htrim : ∀ v, v ∉ J.V0 → J.f v = ∅)
    (hdisj : ∀ A ∈ J.Λ, Disjoint A J.V0) (hlkj : LkJ (msK (n + j) N) o)
    (hS : 2 * j ≤ N - n) :
    (m4StD (N - n) j o).1 = 2 ∧ JValid (N - n) (m4StD (N - n) j o).2.1 ∧
      IsJohnson univ ((msK (n + j) N + 3) / 2) (jdec (N - n) (m4StD (N - n) j o).2.1) ∧
      (∀ g : ↥(GensData.denote N gsK),
        baseHom (GensData.denote N gsK) n hKb g • cjdec (N - n) (m4StD (N - n) j o).2 =
          cjdec (N - n) (m4StD (N - n) j o).2) ∧
      ∀ c, 2 * (univ.filter fun γ => γ ∉ (jdec (N - n) (m4StD (N - n) j o).2.1).V0 ∧
        cjcol (N - n) (m4StD (N - n) j o).2 γ = c).card ≤ N - n := by
  have h2 : o.1 = 2 := m4_tag_inr ho
  have hk : (m4L (N - n) j).length = msK (n + j) N := by rw [m4L_length, msK_eq]; omega
  have hlkj' : LkJ (m4L (N - n) j).length o := by rw [hk]; exact hlkj
  obtain ⟨hext2, hD⟩ := lk_ext (m4L_nodup (N - n) j) m4L_lt h2 hlkj'
  have hjd : jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2 = extJohn (m4E n N j) J := by
    have e1 := decodeOut_extD_shE (m4L (N - n) j) (msK (n + j) N) hk m4L_lt
      (m4L_nodup (N - n) j) o
    rw [ld_decodeOut_two hext2, ho] at e1
    exact Sum.inr_injective (Option.some_injective _ e1)
  have hJ' : IsJohnson univ ((msK (n + j) N + 3) / 2)
      (jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2) := by
    rw [hjd]
    exact extJohn_valid (m4E n N j) hJ
  have htrim' : ∀ v, v ∉ (jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2).V0 →
      (jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2).f v = ∅ := by
    rw [hjd]
    exact extJohn_trim (m4E n N j) htrim
  have hdisj' : ∀ A ∈ (jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2).Λ,
      Disjoint A (jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2).V0 := by
    rw [hjd]
    exact extJohn_disj (m4E n N j) hdisj
  have hcols : indColsD (N - n) j = restColsD (N - n) (m4L (N - n) j) :=
    indColsD_eq (by omega)
  refine ⟨hext2, jvalid_of_isJohnson (lk_jshape hD hJ' htrim' hdisj') hJ', hJ', fun g => ?_,
    fun c => ?_⟩
  · obtain ⟨π, he, hπ⟩ := m4_K_rel hinv hHle hinvH hKden hKb g
    rw [ho, Option.smul_some, Sum.smul_inr] at hπ
    have hπJ : π • J = J := Sum.inr_injective (Option.some_injective _ hπ)
    show _ • cjdec (N - n) ((extD (N - n) (m4L (N - n) j) o).2.2, indColsD (N - n) j) =
      cjdec (N - n) ((extD (N - n) (m4L (N - n) j) o).2.2, indColsD (N - n) j)
    rw [hcols]
    exact cj_ext_stab (m4E n N j) (m4_mem_L n N j) hjd _ π he hπJ
  · show 2 * (univ.filter fun γ => γ ∉ (jdec (N - n) (extD (N - n) (m4L (N - n) j) o).2.2).V0 ∧
      cjcol (N - n) ((extD (N - n) (m4L (N - n) j) o).2.2, indColsD (N - n) j) γ = c).card ≤
        N - n
    rw [hcols]
    refine cj_ext_hq (m4E n N j) (m4_mem_L n N j) hjd hJ (by omega) ?_ c
    rw [msK_eq]
    omega

end StructFacts

/-! ### M4 without stuck orbits -/

section NoStuck

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

theorem rdOrbitWork_mono {N n p s sIn F F' Bd Blift Bgen Bo W6 : ℕ} (h : F ≤ F') :
    rdOrbitWork N n p s sIn F Bd Blift Bgen Bo W6 ≤
      rdOrbitWork N n p s sIn F' Bd Blift Bgen Bo W6 := by
  unfold rdOrbitWork rd5Cost
  have := Nat.mul_le_mul_right (24 * N + p * (2 * N + 17) + 5 * p + sIn + 48) h
  omega

theorem rdCost_mono_wh {N p r sIn Wh Wh' Bo Bgen : ℕ} (h : Wh ≤ Wh') :
    rdCost N p r sIn Wh Bo Bgen ≤ rdCost N p r sIn Wh' Bo Bgen := by
  unfold rdCost
  have h1 := Nat.mul_le_mul_left p h
  have h2 := Nat.mul_le_mul_left r
    (show 24 * N + (p * Wh + dynSeqCost N p Bo + 10) + sIn + 45 ≤
      24 * N + (p * Wh' + dynSeqCost N p Bo + 10) + sIn + 45 by omega)
  omega

/-- **M4 as a step, without stuck orbits.** Under the hypotheses of `RunsWithin.m4StepProg` and
the numeric conditions `4 · max ((m − j + 3)/2) j ≤ 3m` (a partition leaf, extended with the
`j` individualized points as one class), `2j ≤ m` and `m ≥ 5` (a Johnson leaf, coloured
`{individualized, rest}`), with `uB` bounding the union cells of the orbits that can occur:
reduce-and-derive meets no stuck orbit (`rd_ns_part`, `rd_ns_cj`, through `m4_part_facts`,
`m4_cj_facts`), and the factor is `|reps| · max m uB!`. -/
theorem RunsWithin.m4StepProg_ns (hO : MeetsContractOn DV rdOps X.O)
    (hPre : ∀ op x, rdOps op → GroupPre DV op x → X.Pre op x)
    {sub : HInstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {N : ℕ} {gs : GensData}
    {d : D.denote} {n₀ n : ℕ} {L : LabelData}
    (hI : HInstValid DV (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D))
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hI.base_inv g γ = δ)
    (hng : m4Deg X.O n (N, gs, d) < N - n - 2) (hk4 : 4 + m4J X.O n (N, gs, d) ≤ N - n)
    (hpart : 4 * max ((N - n - m4J X.O n (N, gs, d) + 3) / 2) (m4J X.O n (N, gs, d)) ≤
      3 * (N - n))
    (hS : 2 * m4J X.O n (N, gs, d) ≤ N - n) (hm5 : 5 ≤ N - n)
    {C : ℕ → Option ℕ → ℕ} {s : ℕ}
    {sIn : ℕ}
    (hsub : HSubSolves X body DV sub
      (fun J => SizeChild sIn (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D) J ∧
        StepChild w.1.length (N - n) (J.winSize, J.baseOpt)) C s)
    {s₀ : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s₀ G₀)
    (hs₀ : gs.length ≤ s₀) (hG₀ : GensData.denote N gs ≤ G₀) {sS Lt Bge Bst Btr Bgt : ℕ}
    (hB4 : M4Charges X (n + m4J X.O n (N, gs, d)) N (m4PS X.O n (N, gs, d)).1.2.1
      (msLeaf X.O (n + m4J X.O n (N, gs, d)) (m4PS X.O n (N, gs, d)).1) sS Lt Bge Bst Btr Bgt)
    {Lg Blift Bgen Bo Bk Bcr Bd uB : ℕ} (hB : RDBounds X DV n N sIn Lg Blift Bgen Bo Bk Bcr)
    (hs : s ≤ sIn) (hLg : max (N - n) uB.factorial * (sIn + 1) ≤ Lg)
    (hKs : (m4K X.O n (N, gs, d)).2.1.length ≤ sIn)
    (hLR : m4R (N - n) (m4J X.O n (N, gs, d)) * (sIn + 1) ≤ Lg)
    (hD : ∀ gs' d' O, RDSet DV n N gs w L (m4K X.O n (N, gs, d)).2.1 sIn gs' d' O →
      RDOrbit X body DV n N w L (m4St X.O n (N, gs, d)) sIn Bd gs' d' O)
    (hu : ∀ gs' d' O, RDSet DV n N gs w L (m4K X.O n (N, gs, d)).2.1 sIn gs' d' O →
      ((labJUD (m4St X.O n (N, gs, d)).2.1.2.1.length
        (markArr (N - n) (m4St X.O n (N, gs, d)).2.1.1) (m4St X.O n (N, gs, d)).2.1.2.2.2 L O).getD
          (O.headD 0) []).length ≤ uB) :
    ∃ (ans : AnswerData D) (ch : List (ℕ × Option ℕ)),
      RunsWithin X body
        (Main.m4StepProg sub (((xy, w, σd, N, gs, d), n₀, n, some L) : HInstData D)) ans
        ((ch.map fun x => C x.1 x.2).sum +
          m4StepCost N (N - n) (m4J X.O n (N, gs, d)) s₀ B.Borb B.Bstab B.Btr sS Lt Bge Bst Btr
            Bgt w.1.length sIn
            (rdOrbitWork N n w.1.length s sIn (max (N - n) uB.factorial) Bd Blift Bgen Bo 0)
            Bo Bgen) ∧
      InstData.OK (D := D) (xy, w, σd, N, gs, d) DV ans ∧
      (∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sIn) ∧
      ChildList w.1.length ((m4Reps X.O n (N, gs, d)).length * max (N - n) uB.factorial)
        (StepChild w.1.length (N - n)) ch ∧
      (m4Reps X.O n (N, gs, d)).length ≤ m4R (N - n) (m4J X.O n (N, gs, d)) := by
  have hinv : IsInvariant (GensData.denote N gs) (baseSet n N) := hI.base_inv
  refine m4_core hO hPre hI htr hng hk4 B hs₀ hG₀ hB4
    fun gsH gsK dK o hinvH hHden hK ho hKv hKden hKG hrs hcov hR hout hlkj => ?_
  have hKs' : gsK.length ≤ sIn := by
    have := hKs
    rw [hK] at this
    exact this
  have hLr : (m4Reps X.O n (N, gs, d)).length * (sIn + 1) ≤ Lg :=
    (Nat.mul_le_mul_right _ hR).trans hLR
  have hst : m4St X.O n (N, gs, d) = m4StD (N - n) (m4J X.O n (N, gs, d)) o := by
    unfold m4St
    rw [ho]
  have hD' : ∀ gs' d' O, RDSet DV n N gs w L gsK sIn gs' d' O →
      RDOrbit X body DV n N w L (m4StD (N - n) (m4J X.O n (N, gs, d)) o) sIn Bd gs' d' O := by
    intro gs' d' O hset
    have := hD gs' d' O (by rw [hK]; exact hset)
    rw [hst] at this
    exact this
  have hKb : IsInvariant (GensData.denote N gsK) (baseSet n N) :=
    fun x hx u hu => hinv x (hKG hx) u hu
  have hHle : GensData.denote N gsH ≤ GensData.denote N gs := by
    rw [hHden]
    exact fixFirst_le _ _ _
  have hjN : n + m4J X.O n (N, gs, d) ≤ N := by omega
  have hk' : msK (n + m4J X.O n (N, gs, d)) N = N - n - m4J X.O n (N, gs, d) := by
    rw [msK_eq]
    omega
  rcases hout with ⟨p₀, ho', hp₀⟩ | ⟨J, ho', hJ, htrim, hdisj⟩
  · obtain ⟨hpv, hpK⟩ := m4_part_facts hinv hHle hinvH hKden hKb hjN ho' hp₀
    have hst1 : (m4StD (N - n) (m4J X.O n (N, gs, d)) o).1 ≠ 2 := by
      show (extD (N - n) (m4L (N - n) (m4J X.O n (N, gs, d))) o).1 ≠ 2
      rw [m4_extD_one (m4_tag_inl ho')]
      decide
    have ht : 4 * max ((msK (n + m4J X.O n (N, gs, d)) N + 3) / 2) (m4J X.O n (N, gs, d)) ≤
        3 * (N - n) := by
      rw [hk']
      exact hpart
    have hLg' : (N - n) * (sIn + 1) ≤ Lg :=
      (Nat.mul_le_mul_right _ (le_max_left _ _)).trans hLg
    obtain ⟨ans, ch, hrun, hok, hg, hcl⟩ := RunsWithin.rdProg_part_ns hO hPre hI hsub hB hs hLg'
      hKv hKG hKs' hrs hcov hLr hD' hst1 hKb hpv hpK ht (by omega)
    refine ⟨ans, ch, hrun.mono ?_, hok, hg, ⟨hcl.sum_le.trans ?_, hcl.pred, hcl.pos⟩⟩
    · exact Nat.add_le_add_left (rdCost_mono_wh (rdOrbitWork_mono (le_max_left _ _))) _
    · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (le_max_left _ _))
  · obtain ⟨h2, hJv, hJ', hKcj, hq⟩ := m4_cj_facts hinv hHle hinvH hKden hKb hjN ho' hJ htrim
      hdisj (hlkj (m4_tag_inr ho')) hS
    have hu' : ∀ gs' d' O, RDSet DV n N gs w L gsK sIn gs' d' O →
        ((labJUD (m4StD (N - n) (m4J X.O n (N, gs, d)) o).2.1.2.1.length
          (markArr (N - n) (m4StD (N - n) (m4J X.O n (N, gs, d)) o).2.1.1)
          (m4StD (N - n) (m4J X.O n (N, gs, d)) o).2.1.2.2.2 L O).getD
            (O.headD 0) []).length ≤ uB := by
      intro gs' d' O hset
      have := hu gs' d' O (by rw [hK]; exact hset)
      rw [hst] at this
      exact this
    exact RunsWithin.rdProg_cj_ns hO hPre hI hsub hB hs hLg hKv hKG hKs' hrs hcov hLr hD' h2 hKb
      hJv hJ' hKcj hq hm5 hu'

end NoStuck

/-! ### The computed degree and the transitivity bound -/

section Degree

variable {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}

/-- **The computed degree is at most the true degree of transitivity**: if the base action is not
`(d + 1)`-transitive, the computed degree is at most `d`. -/
theorem m4_deg_le (hO : MeetsContractOn DV degreeOps X.O) {N s n : ℕ}
    {G₀ : Subgroup (Perm (Fin N))} (B : Solver.BackendBounds X DV N s G₀) {gs : GensData}
    {dd : D.denote} (hG : GroupValid DV N gs dd) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N) {d : ℕ}
    (hnot : ¬ IsMultiplyPretransitive (baseHom (GensData.denote N gs) n hinv).range
      (Fin (N - n)) (d + 1)) :
    m4Deg X.O n (N, gs, dd) ≤ d := by
  show degreeModel X.O n (N - n - 2) (N, gs, dd) ≤ d
  obtain ⟨hle, hmt, -⟩ := degreeModel_spec hO B hG hs hG₀ hinv hn (cap := N - n - 2) (by omega)
  by_contra h
  apply hnot
  have := hmt
  exact MulAction.isMultiplyPretransitive_of_le (n := degreeModel X.O n (N - n - 2) (N, gs, dd))
    (by omega) (by simp; omega)

/-- **Under `TransitivityBound T`**, the computed degree of a base action not containing the
alternating group is at most `T m`. So `j = dg − 1 < T m`, and the numeric conditions of
`RunsWithin.m4StepProg_ns` hold once `2 T(m) + 6 ≤ m` (`m4_numeric`). -/
theorem m4_deg_le_T {T : ℕ → ℕ} (hT : AltQuot.TransitivityBound T)
    (hO : MeetsContractOn DV degreeOps X.O) {N s n : ℕ} {G₀ : Subgroup (Perm (Fin N))}
    (B : Solver.BackendBounds X DV N s G₀) {gs : GensData} {dd : D.denote}
    (hG : GroupValid DV N gs dd) (hs : gs.length ≤ s) (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n ≤ N)
    (hP : ¬ alternatingGroup (Fin (N - n)) ≤ (baseHom (GensData.denote N gs) n hinv).range) :
    m4Deg X.O n (N, gs, dd) ≤ T (N - n) := by
  show degreeModel X.O n (N - n - 2) (N, gs, dd) ≤ T (N - n)
  obtain ⟨hle, hmt, -⟩ := degreeModel_spec hO B hG hs hG₀ hinv hn (cap := N - n - 2) (by omega)
  have := hT (Fin (N - n)) _ (degreeModel X.O n (N - n - 2) (N, gs, dd))
    (by simp; omega) hmt hP
  simpa using this

/-- **The numeric conditions of M4** from `2j + 6 ≤ m`: at least four remaining base points, a
partition leaf extended by the individualized points has `4t ≤ 3m`, and the individualized
points are at most half of the base. -/
theorem m4_numeric {m j : ℕ} (h : 2 * j + 6 ≤ m) :
    4 + j ≤ m ∧ 4 * max ((m - j + 3) / 2) j ≤ 3 * m ∧ 2 * j ≤ m ∧ 5 ≤ m := by
  refine ⟨by omega, ?_, by omega, by omega⟩
  rcases le_total ((m - j + 3) / 2) j with hc | hc
  · rw [max_eq_right hc]
    omega
  · rw [max_eq_left hc]
    omega

end Degree

/-! ### The leaf stabilizer's charges -/

section Charges

variable {D : Ty}

/-- **The leaf stabilizer's charges are satisfiable**, by their own values (they are charges on
specific inputs, for any context). -/
theorem m4Charges_exact (X : Ctx (groupSig D)) (n' N : ℕ) (gs : GensData) (o : OutD) :
    M4Charges X n' N gs o (osStab X.O N (msR n' N gs o) gs (msImgs n' N gs o)).2.1.length
      (osTrans X.O N (msR n' N gs o) gs (msImgs n' N gs o)).length
      (X.B.call GroupOp.generate (N + msR n' N gs o, os_extGens N (msR n' N gs o) gs
        (msImgs n' N gs o)) (osGroup X.O N (msR n' N gs o) gs (msImgs n' N gs o)))
      (X.B.call GroupOp.stabilizer (osGroup X.O N (msR n' N gs o) gs (msImgs n' N gs o), N)
        (osStab X.O N (msR n' N gs o) gs (msImgs n' N gs o)))
      (X.B.call GroupOp.orbitTransversal
        (osGroup X.O N (msR n' N gs o) gs (msImgs n' N gs o), N)
        (osTrans X.O N (msR n' N gs o) gs (msImgs n' N gs o)))
      (X.B.call GroupOp.generate (N, (osStab X.O N (msR n' N gs o) gs
        (msImgs n' N gs o)).2.1.map (PermData.truncTo N))
        (orbitStabModel X.O N (msR n' N gs o) gs (msImgs n' N gs o)).1) :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

end Charges

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

local macro "m4_mem" : tactic =>
  `(tactic| repeat (first | exact List.mem_cons_self | assumption | apply List.mem_cons_of_mem))

theorem wf_indColsProg {m₁ j₁ : var₁ .nat} {m₂ j₂ : var₂ .nat} (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (indColsProg m₁ j₁) (indColsProg m₂ j₂) := by
  unfold indColsProg mapList
  prog_wf

theorem wf_m4StProg {m₁ j₁ : var₁ .nat} {m₂ j₂ : var₂ .nat} {o₁ : var₁ outTy} {o₂ : var₂ outTy}
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (hj : ⟨.nat, j₁, j₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (m4StProg m₁ j₁ o₁) (m4StProg m₂ j₂ o₂) := by
  unfold m4StProg
  refine .bind (.prim _ (.cons ho .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (wf_indColsProg (by m4_mem) (by m4_mem)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  exact .prim _ (.cons (by m4_mem) (.cons (List.Mem.head _) .nil))

theorem wf_m4StepProg {sub₁ : var₁ (hinstTy D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (hinstTy D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {I₁ : var₁ (hinstTy D)} {I₂ : var₂ (hinstTy D)}
    (hI : ⟨hinstTy D, I₁, I₂⟩ ∈ Γ) :
    Prog.Wf r Γ (m4StepProg sub₁ I₁) (m4StepProg sub₂ I₂) := by
  unfold m4StepProg m4TailProg
  refine .bind (.prim _ (.cons hI .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by m4_mem) .nil))) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (wf_degreeProg (by m4_mem) (List.Mem.head _) (by m4_mem)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) (.cons (List.Mem.head _) .nil))) fun _ _ => ?_
  refine .bind (ms_wf_rangeFromProg (by m4_mem) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (wf_pointStabsProg (by m4_mem) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) (.cons (by m4_mem) .nil))) fun _ _ => ?_
  refine .bind (wf_m4StructProg (List.Mem.head _) (by m4_mem)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) .nil)) fun _ _ => ?_
  refine .bind (wf_prodRepsLProg (by m4_mem) (by m4_mem)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by m4_mem) (.cons (by m4_mem) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (List.Mem.head _) (.cons (by m4_mem) .nil))) fun _ _ => ?_
  refine .bind (ms_wf_rangeFromProg (by m4_mem) (List.Mem.head _)) fun _ _ => ?_
  refine .bind (Case2b.wf_extProg (by m4_mem) (List.Mem.head _) (by m4_mem)) fun _ _ => ?_
  refine .bind (wf_m4StProg (by m4_mem) (by m4_mem) (List.Mem.head _)) fun _ _ => ?_
  exact wf_rdProg (hsub.mono fun y hy => by m4_mem) (by m4_mem) (by m4_mem) (by m4_mem)
    (List.Mem.head _)

end Wf

end GraphIso.Main
