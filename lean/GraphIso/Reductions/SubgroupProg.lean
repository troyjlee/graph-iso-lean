module

public import GraphIso.Reductions.SequentialProg
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.List.Forall2

/-!
# Branching over a subgroup, as a program

`branchProg sub xy w σ K rs` solves the window `w` in the coset `σ • G` by branching over a
left cover `rs` of `G` by cosets of `K ≤ G`: for every `r ∈ rs` it computes `σ * r` and calls
`sub` on the coset `(σ * r) • K`. All branches are executed: a coset-valued answer must
recover every solution, not just the first witness. `combineProg` then

1. collects the successful branch answers `(τᵢ, Hᵢ)` in order;
2. returns `none` if there are none;
3. otherwise inverts the first representative `τ₀`, computes the differences `τ₀⁻¹ τᵢ` for the
   later branches, concatenates all branch generators followed by these differences
   (`combineGens`, exactly `Σ sᵢ + k - 1` generators: `length_combineGens`), and passes them to
   the backend operation `generate`, which is charged on that actual argument.

`RunsWithin.branchProg` proves that the result is a correct answer for `σ • G` and bounds the
cost by `|rs| (24 n + C + s + 45) + B_gen + 15`, where `C` bounds each branch call, `s` bounds
the branch output generators and `B_gen` bounds the charge of the final `generate` call on
lists of at most `|rs| (s + 1)` generators. The subgroup `K` need not be normal.
-/

@[expose] public section

namespace GraphIso

open Equiv Cost Pointwise

variable {D : Ty}

/-- The successful branch answers, in order. -/
def branchSuccesses (as : List (AnswerData D)) : List (CosetData D) := as.filterMap id

theorem mem_branchSuccesses {as : List (AnswerData D)} {c : CosetData D} :
    c ∈ branchSuccesses as ↔ some c ∈ as := by
  simp [branchSuccesses]

/-- The generators passed to `generate` after branching, with first representative `τ₀`. -/
def combineGens (τ₀ : PermData) (ss : List (CosetData D)) : GensData :=
  branchGens τ₀.inv (ss.map fun c => (c.1, c.2.gens))

/-- `s_out = Σ sᵢ + k - 1` for `k` successful branches. -/
theorem length_combineGens (τ₀ : PermData) (ss : List (CosetData D)) :
    (combineGens τ₀ ss).length = (ss.map fun c => c.2.gens.length).sum + (ss.length - 1) := by
  rw [combineGens, length_branchGens]
  simp [Function.comp_def]

/-- The result of combining branch answers, given the backend. -/
def combineModel (O : Oracle (groupSig D)) (n : ℕ) (as : List (AnswerData D)) : AnswerData D :=
  match branchSuccesses as with
  | [] => none
  | c₀ :: rest => some (c₀.1, O.run .generate (n, combineGens c₀.1 (c₀ :: rest)))

theorem exists_of_forall₂_mem {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => exact absurd hb (List.not_mem_nil)
  | @cons a b' l₁ l₂ hab _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := ih hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem successes_map_denote (n : ℕ) (as : List (AnswerData D)) :
    successes (as.map (AnswerData.denote n)) =
      (branchSuccesses as).map fun c => (PermData.denote n c.1, GensData.denote n c.2.gens) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    unfold successes branchSuccesses at *
    rcases a with _ | c
    · rw [List.map_cons, List.filterMap_cons_none rfl, List.filterMap_cons_none rfl]
      exact ih
    · rw [List.map_cons]
      show List.filterMap id (some _ :: _) = _
      rw [List.filterMap_cons_some (f := id) rfl, List.filterMap_cons_some (f := id) rfl,
        List.map_cons, ih]

/-- **Branch combination, represented.** If the branch answers are correct for the branch
cosets `(σ * r) • K` of a left cover `rs` of `G` by cosets of `K ≤ G`, and the backend meets its
contract, then `combineModel` is a correct answer for `σ • G`. -/
theorem AnsOK.combineModel {DV : ℕ → GensData → D.denote → Prop} {O : Oracle (groupSig D)}
    (hO : MeetsContractOn DV (· = .generate) O) {n : ℕ} {W : Set (Fin n)} {σd : PermData}
    {G K : Subgroup (Perm (Fin n))} {x y : Fin n → ℕ} (hW : IsInvariant G W) (hK : K ≤ G)
    (hσ : σd.Valid n) {rs : List PermData} (hrs : ∀ r ∈ rs, r.Valid n)
    (hcover : IsLeftCover G K fun i : Fin (rs.map (PermData.denote n)).length =>
      (rs.map (PermData.denote n)).get i)
    {as : List (AnswerData D)}
    (has : List.Forall₂ (fun r a => AnsOK DV n W (PermData.denote n (σd.mul r)) K x y a) rs as) :
    AnsOK DV n W (PermData.denote n σd) G x y (GraphIso.combineModel O n as) := by
  have hlen : (as.map (AnswerData.denote n)).length = (rs.map (PermData.denote n)).length := by
    simp [has.length_eq]
  have ha : ∀ i : Fin (rs.map (PermData.denote n)).length,
      Answer.IsCorrect ((as.map (AnswerData.denote n)).get (i.cast hlen.symm)) W
        (PermData.denote n σd * (rs.map (PermData.denote n)).get i) K x y := by
    intro i
    obtain ⟨hl, hget⟩ := List.forall₂_iff_get.1 has
    have hi₁ : i.val < rs.length := by simpa using i.2
    have hi₂ : i.val < as.length := hl ▸ hi₁
    have h := (hget i.val hi₁ hi₂).isCorrect
    rw [PermData.denote_mul hσ (hrs _ (List.get_mem _ _))] at h
    simpa using h
  have hcomb := Answer.IsCorrect.combineBranches hW hcover hK hlen ha
  unfold Answer.IsCorrect GraphIso.combineBranches at hcomb
  rw [successes_map_denote] at hcomb
  have hval : ∀ c ∈ branchSuccesses as, c.1.Valid n ∧ GensData.AllValid n c.2.gens := by
    intro c hc
    obtain ⟨r, -, hr⟩ := exists_of_forall₂_mem has (mem_branchSuccesses.1 hc)
    exact ⟨hr.1, hr.2.2.1.1⟩
  unfold GraphIso.combineModel
  rcases hss : branchSuccesses as with _ | ⟨c₀, rest⟩
  · rw [hss] at hcomb
    exact hcomb.symm
  · rw [hss] at hcomb hval
    simp only [List.map_cons, Answer.denote_some] at hcomb
    have hv : ∀ p ∈ (c₀.1, c₀.2.gens) :: rest.map (fun c => (c.1, c.2.gens)),
        p.1.Valid n ∧ GensData.AllValid n p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hval c₀ List.mem_cons_self
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
        exact hval c (List.mem_cons_of_mem _ hc)
    have hgv : GensData.AllValid n (combineGens c₀.1 (c₀ :: rest)) :=
      allValid_branchGens (hval c₀ List.mem_cons_self).1.inv fun p hp => by
        simpa using hv p (by simpa using hp)
    have hpost := hO .generate (n, combineGens c₀.1 (c₀ :: rest)) rfl hgv
    dsimp only
    rcases hH : O.run GroupOp.generate (n, combineGens c₀.1 (c₀ :: rest)) with ⟨n', hs, e⟩
    rw [hH] at hpost
    obtain ⟨rfl, hGv, hden⟩ := hpost
    refine ⟨(hval c₀ List.mem_cons_self).1, rfl, hGv, ?_⟩
    change PermData.denote n' c₀.1 • (GensData.denote n' hs : Set (Perm (Fin n'))) = _
    rw [hden, ← hcomb, combineGens, List.map_cons,
      denote_branchGens (hval c₀ List.mem_cons_self).1 hv]
    simp [Function.comp_def]

/-- **Point-stabilizer transversal.** The exact output of the `orbitTransversal` operation (one
element `r_v ∈ G` with `r_v u = v` for each point `v` of the orbit of `u`, without repeated
points) is a left transversal of `G` by cosets of the point stabilizer `G_u`. -/
theorem isLeftTransversal_of_orbitTransversal {n : ℕ} {G : Subgroup (Perm (Fin n))}
    {u : ℕ} (hu : u < n) {rs : List (ℕ × PermData)} (hnd : (rs.map Prod.fst).Nodup)
    (horb : ∀ j, j ∈ rs.map Prod.fst ↔ SameOrbit G u j)
    (hrs : ∀ vr ∈ rs, PermData.Valid n vr.2 ∧ PermData.denote n vr.2 ∈ G ∧ get vr.2.1 u = vr.1) :
    IsLeftTransversal G (pointStab G ⟨u, hu⟩)
      fun i : Fin ((rs.map Prod.snd).map (PermData.denote n)).length =>
        ((rs.map Prod.snd).map (PermData.denote n)).get i := by
  have hget : ∀ i : Fin ((rs.map Prod.snd).map (PermData.denote n)).length,
      ∃ h : i.val < rs.length, ((rs.map Prod.snd).map (PermData.denote n)).get i =
        PermData.denote n (rs.get ⟨i, h⟩).2 := fun i => by
    have h : i.val < rs.length := by simpa using i.2
    exact ⟨h, by simp⟩
  -- the representative of index `i` maps `u` to the `i`-th listed point
  have happly : ∀ (i : ℕ) (h : i < rs.length),
      (PermData.denote n (rs.get ⟨i, h⟩).2 ⟨u, hu⟩).val = (rs.get ⟨i, h⟩).1 := fun i h => by
    have := hrs (rs.get ⟨i, h⟩) (List.get_mem _ _)
    rw [PermData.val_denote_apply this.1]
    exact this.2.2
  refine ⟨⟨fun i => ?_, fun g hg => ?_⟩, fun i j hij => ?_⟩
  · obtain ⟨h, e⟩ := hget i
    rw [e]
    exact (hrs _ (List.get_mem _ _)).2.1
  · -- `g u` lies in the orbit, so some listed point equals it
    have hv : (g ⟨u, hu⟩).val ∈ rs.map Prod.fst := (horb _).2 ⟨hu, (g ⟨u, hu⟩).2, g, hg, rfl⟩
    obtain ⟨vr, hvr, hfst⟩ := List.mem_map.1 hv
    obtain ⟨⟨k, hk⟩, rfl⟩ := List.get_of_mem hvr
    refine ⟨⟨k, by simpa using hk⟩, ?_⟩
    obtain ⟨h, e⟩ := hget ⟨k, by simpa using hk⟩
    rw [e, mem_pointStab]
    have hr := hrs (rs.get ⟨k, h⟩) (List.get_mem _ _)
    refine ⟨mul_mem (inv_mem hr.2.1) hg, ?_⟩
    rw [Perm.mul_apply, Perm.inv_eq_iff_eq]
    apply Fin.ext
    rw [happly k h]
    exact hfst.symm
  · -- equal cosets of `G_u` send `u` to the same listed point
    obtain ⟨hi, ei⟩ := hget i
    obtain ⟨hj, ej⟩ := hget j
    rw [ei, ej, mem_pointStab, Perm.mul_apply, Perm.inv_eq_iff_eq] at hij
    have hpts : (rs.get ⟨i, hi⟩).1 = (rs.get ⟨j, hj⟩).1 := by
      rw [← happly i hi, ← happly j hj, hij.2]
    have := (List.Nodup.get_inj_iff (l := rs.map Prod.fst) hnd
      (i := ⟨i, by simpa using hi⟩) (j := ⟨j, by simpa using hj⟩)).1 (by simpa using hpts)
    exact Fin.ext (by simpa using congrArg Fin.val this)

end GraphIso

namespace GraphIso.Programs

open Equiv Cost

variable {rec : Ty × Ty} {var : Ty → Type} {D : Ty}

/-- Solve the branch `(σ * r) • K`. -/
def branchCall (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (w : var Ty.win) (σ : var Ty.perm) (K : var (Ty.group D))
    (r : var Ty.perm) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (permMul σ r) fun σr =>
  .bind (.op2 .pair σr K) fun c =>
  .bind (.op2 .pair w c) fun wc =>
  .bind (.op2 .pair xy wc) fun I =>
  sub I

/-- Combine the branch answers into an answer for the whole coset. -/
def combineProg (n : var .nat) (as : var (.list (Ty.answer D))) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList as nil fun acc a => .caseOption a (.ret acc) fun c => .op2 .cons c acc)
    fun revS =>
  .bind (.op1 .reverse revS) fun ss =>
  .caseList ss (.op0 .none) fun c₀ rest =>
    .bind (.op1 .fst c₀) fun τ₀ =>
    .bind (permInv τ₀) fun τ₀inv =>
    .bind (mapList rest fun c => .bind (.op1 .fst c) fun τ => permMul τ₀inv τ) fun diffs =>
    .bind (.foldList revS diffs fun acc c =>
        .bind (.op1 .snd c) fun H => .bind (.op1 .snd H) fun gd => .bind (.op1 .fst gd)
          fun gs => .op2 .append gs acc) fun gens =>
    .bind (.op2 .pair n gens) fun arg =>
    .bind (Prog.call (S := groupSig D) GroupOp.generate arg) fun H =>
    .bind (.op2 .pair τ₀ H) fun c =>
    .op1 .some c

/-- Branch over the cover `rs`, then combine. -/
def branchProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (xy : var Ty.strs) (w : var Ty.win) (σ : var Ty.perm) (K : var (Ty.group D))
    (rs : var Ty.gens) : Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst K) fun n =>
  .bind (mapList rs fun r => branchCall sub xy w σ K r) fun as =>
  combineProg n as

section Specs

variable {a b : Ty} {X : Ctx (groupSig D)} {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b}
  {DV : ℕ → GensData → D.denote → Prop}

/-- The cost of `combineProg` on actual branch answers, with `Bgen` bounding the `generate`
charge. -/
def combineCost (n : ℕ) (as : List (AnswerData D)) (Bgen : ℕ) : ℕ :=
  16 + 4 * as.length + ((branchSuccesses as).length - 1) * (12 * n + 17) +
    ((branchSuccesses as).map fun c => c.2.gens.length + 5).sum + Bgen

private theorem foldl_filter (as : List (AnswerData D)) (acc : List (CosetData D)) :
    as.foldl (fun acc a => a.elim acc fun c => c :: acc) acc =
      (branchSuccesses as).reverse ++ acc := by
  induction as generalizing acc with
  | nil => rfl
  | cons a as ih =>
    rcases a with _ | c
    · simpa [branchSuccesses] using ih acc
    · rw [List.foldl_cons]
      exact (ih (c :: acc)).trans (by simp [branchSuccesses])

private theorem foldl_gens (ss : List (CosetData D)) (init : GensData) :
    ss.reverse.foldl (fun acc c => c.2.gens ++ acc) init =
      (ss.map fun c => c.2.gens).flatten ++ init := by
  rw [List.foldl_reverse]
  induction ss with
  | nil => rfl
  | cons c ss ih => simp [ih]

theorem RunsWithin.combineProg (hPre : ∀ x, GroupPre DV .generate x → X.Pre .generate x)
    {n s Bgen : ℕ}
    {as : List (AnswerData D)}
    (hvalid : ∀ c ∈ branchSuccesses as, c.1.Valid n ∧ GensData.AllValid n c.2.gens)
    (hs : ∀ c ∈ branchSuccesses as, c.2.gens.length ≤ s)
    (hB : ∀ c₀ rest, branchSuccesses as = c₀ :: rest →
      X.B.call GroupOp.generate (n, combineGens c₀.1 (c₀ :: rest))
        (X.O.run GroupOp.generate (n, combineGens c₀.1 (c₀ :: rest))) ≤ Bgen) :
    RunsWithin X body (Programs.combineProg n as) (combineModel X.O n as)
      (combineCost n as Bgen) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (cf := fun _ => 2)
    (a' := Ty.answer D) (b' := .list (Ty.coset D))
    (f := fun (acc : List (CosetData D)) (a : AnswerData D) =>
      Prog.caseOption (a := Ty.coset D) a (.ret acc) fun c => .op2 .cons c acc)
    (F := fun acc a => a.elim acc fun c => c :: acc) as [] fun acc a _ => by
      rcases a with _ | c
      · exact (RunsWithin.caseOption_none (q := fun c => Prog.op2 Prim.cons c acc)
          (RunsWithin.ret _)).mono (by omega)
      · exact RunsWithin.caseOption_some (p := Prog.ret acc)
          (q := fun c => Prog.op2 Prim.cons c acc) (RunsWithin.prim_le rfl le_rfl)
  rw [foldl_filter, List.append_nil, sum_map_const] at hfold
  have hk : (branchSuccesses as).length ≤ as.length := List.length_filterMap_le _ _
  unfold Programs.combineProg
  unfold combineModel
  rcases hss : branchSuccesses as with _ | ⟨c₀, rest⟩
  · rw [hss] at hfold
    refine RunsWithin.bind_le (c₂ := as.length * (2 + 1) + 3) (RunsWithin.prim _ _) ?_ ?_
    · refine RunsWithin.bind_le (c₂ := 3) hfold ?_ (Nat.le_refl _)
      refine RunsWithin.bind_le (c₂ := 2) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      exact RunsWithin.caseList_nil (RunsWithin.prim _ _)
    · simp only [combineCost, hss, Prim.cost]
      omega
  · rw [hss] at hfold
    have hv₀ := hvalid c₀ (by rw [hss]; exact List.mem_cons_self)
    have hvr : ∀ c ∈ rest, c.1.Valid n ∧ GensData.AllValid n c.2.gens :=
      fun c hc => hvalid c (by rw [hss]; exact List.mem_cons_of_mem _ hc)
    set gens := combineGens c₀.1 (c₀ :: rest) with hgens
    have hgens_eq : (c₀ :: rest).reverse.foldl (fun acc c => c.2.gens ++ acc)
        (rest.map fun c => PermData.mul c₀.1.inv c.1) = gens := by
      rw [foldl_gens, hgens, combineGens, branchGens]
      simp [Function.comp_def]
    have hgv : GensData.AllValid n gens := by
      rw [hgens, combineGens]
      refine allValid_branchGens hv₀.1.inv fun p hp => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      exact hvalid c (by rw [hss]; exact hc)
    have hglen : gens.length ≤ as.length * (s + 1) := by
      rw [hgens, length_combineGens]
      have hsum : ((c₀ :: rest).map fun c => c.2.gens.length).sum ≤ (c₀ :: rest).length * s :=
        sum_map_le _ _ _ fun c hc => hs c (by rw [hss]; exact hc)
      have hk' : rest.length + 1 ≤ as.length := by simpa [hss] using hk
      simp only [List.length_cons, Nat.add_sub_cancel] at hsum ⊢
      nlinarith [Nat.mul_le_mul_right s hk']
    have hmap := RunsWithin.mapList_le (X := X) (body := body) (c := 12 * n + 14)
      (a' := Ty.coset D) (b' := Ty.perm)
      (xs := rest) (F := fun c => PermData.mul c₀.1.inv c.1)
      (f := fun c => .bind (.op1 .fst c) fun τ => Programs.permMul (PermData.inv c₀.1) τ)
      fun c hc =>
        RunsWithin.bind_le (RunsWithin.prim _ _) (RunsWithin.permMul hv₀.1.inv (hvr c hc).1)
          (by simp [Prim.cost]; omega)
    have hgfold := RunsWithin.foldList_of (X := X) (body := body)
      (a' := Ty.coset D) (b' := Ty.gens) (cf := fun (c : CosetData D) => c.2.gens.length + 4)
      (f := fun (acc : GensData) (c : CosetData D) =>
        Prog.bind (.op1 (Prim.snd (a := Ty.perm) (b := Ty.group D)) c) fun H =>
          .bind (.op1 (Prim.snd (a := .nat) (b := .prod Ty.gens D)) H) fun gd =>
          .bind (.op1 (Prim.fst (a := Ty.gens) (b := D)) gd) fun gs => .op2 .append gs acc)
      (F := fun acc (c : CosetData D) => c.2.gens ++ acc) (c₀ :: rest).reverse
      (rest.map fun c => PermData.mul c₀.1.inv c.1) fun acc c _ => by
        refine RunsWithin.bind_le (c₂ := (GroupData.gens c.2).length + 3)
          (RunsWithin.prim _ _) ?_ (by simp [Prim.cost]; omega)
        refine RunsWithin.bind_le (c₂ := (GroupData.gens c.2).length + 2)
          (RunsWithin.prim _ _) ?_ (by simp [Prim.cost]; omega)
        refine RunsWithin.bind_le (c₂ := (GroupData.gens c.2).length + 1)
          (RunsWithin.prim _ _) ?_ (by simp [Prim.cost]; omega)
        refine RunsWithin.prim_le rfl ?_
        simp [Prim.cost, Prim.eval, GroupData.gens]
    rw [hgens_eq] at hgfold
    have hBc := hB c₀ rest hss
    -- the costs of the remaining steps
    set G₀ := ((c₀ :: rest).reverse.map fun c => c.2.gens.length + 4 + 1).sum with hG₀
    set Bc := X.B.call GroupOp.generate (n, gens) (X.O.run GroupOp.generate (n, gens))
    set M := rest.length * (12 * n + 14 + 3) + 2
    have hcall := RunsWithin.call (X := X) (body := body) (op := GroupOp.generate)
      (x := (n, gens)) (hPre _ hgv)
    refine RunsWithin.bind_le (c₂ := as.length * (2 + 1) + ((c₀ :: rest).length + 1 +
        (1 + (1 + (3 + (M + (G₀ + (1 + (Bc + 2)))))))))
      (RunsWithin.prim _ _) ?_ ?_
    · refine RunsWithin.bind_le hfold ?_ (Nat.le_refl _)
      refine RunsWithin.bind_le (c₂ := 1 + (1 + (3 + (M + (G₀ + (1 + (Bc + 2)))))))
        (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      simp only [Prim.eval, List.reverse_reverse]
      refine RunsWithin.caseList_cons ?_
      refine RunsWithin.bind_le (c₂ := 3 + (M + (G₀ + (1 + (Bc + 2))))) (RunsWithin.prim _ _) ?_
        (by simp [Prim.cost])
      refine RunsWithin.bind_le (c₂ := M + (G₀ + (1 + (Bc + 2)))) (RunsWithin.permInv _) ?_
        (Nat.le_refl _)
      refine RunsWithin.bind_le (c₂ := G₀ + (1 + (Bc + 2))) hmap ?_ (Nat.le_refl _)
      refine RunsWithin.bind_le (c₂ := 1 + (Bc + 2)) hgfold ?_ (Nat.le_refl _)
      refine RunsWithin.bind_le (c₂ := Bc + 2) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      refine RunsWithin.bind_le (c₂ := 2) hcall ?_ (Nat.le_refl _)
      refine RunsWithin.bind_le (c₂ := 1) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
      exact RunsWithin.prim _ _
    · have hG₀' : G₀ = ((c₀ :: rest).map fun c => c.2.gens.length + 5).sum := by
        rw [hG₀, List.map_reverse, List.sum_reverse]
      simp only [combineCost, hss, Prim.cost, List.length_cons, Nat.add_sub_cancel, ← hG₀', M,
        show 12 * n + 14 + 3 = 12 * n + 17 by omega]
      have hk' : rest.length + 1 ≤ as.length := by simpa [hss] using hk
      omega

/-- The coarse cost bound of `combineProg`. -/
theorem combineCost_le {n s Bgen : ℕ} {as : List (AnswerData D)}
    (hs : ∀ c ∈ branchSuccesses as, c.2.gens.length ≤ s) :
    combineCost n as Bgen ≤ as.length * (12 * n + s + 26) + Bgen + 16 := by
  have hk : (branchSuccesses as).length ≤ as.length := List.length_filterMap_le _ _
  have hsum : ((branchSuccesses as).map fun c => c.2.gens.length + 5).sum ≤
      (branchSuccesses as).length * (s + 5) := by
    exact sum_map_le _ _ _ fun c hc => by have := hs c hc; omega
  unfold combineCost
  have h1 : ((branchSuccesses as).length - 1) * (12 * n + 17) ≤ as.length * (12 * n + 17) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : (branchSuccesses as).length * (s + 5) ≤ as.length * (s + 5) :=
    Nat.mul_le_mul_right _ hk
  nlinarith

/-- **Branching reduction.** Branch over a left cover `rs` of `G` by cosets of `K ≤ G` (with
`K` not necessarily normal), solving each branch coset with `sub`, and combine. The answer
is correct for `σ • G`; the cost covers the representatives `σ * r`, every branch call, the
collection of branch generators and representative differences, and the final `generate`
call. If the backend's `generate` returns at most `sGen` generators, so does the answer. -/
theorem RunsWithin.branchProg (hO : MeetsContractOn DV (· = .generate) X.O)
    (hPre : ∀ x, GroupPre DV .generate x → X.Pre .generate x)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {w : WinData} {σd : PermData} {n : ℕ} {ks : GensData}
    {e : D.denote} {G : Subgroup (Perm (Fin n))} {rs : List PermData} {Cb s Bgen : ℕ}
    (hw : w.Valid n) (hσ : σd.Valid n) (hKv : GroupValid DV n ks e)
    (hKG : GensData.denote n ks ≤ G) (hWG : IsInvariant G (w.denote n))
    (hrs : ∀ r ∈ rs, r.Valid n)
    (hcover : IsLeftCover G (GensData.denote n ks)
      fun i : Fin (rs.map (PermData.denote n)).length => (rs.map (PermData.denote n)).get i)
    (hsub : SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧ I.2.2.2 = (n, ks, e) ∧
      (∃ r ∈ rs, I.2.2.1 = σd.mul r) ∧ I.Valid DV) (fun _ => Cb) s)
    (hB : ∀ gs : GensData, GensData.AllValid n gs → gs.length ≤ rs.length * (s + 1) →
      GensData.denote n gs ≤ G →
      X.B.call GroupOp.generate (n, gs) (X.O.run GroupOp.generate (n, gs)) ≤ Bgen) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Programs.branchProg sub xy w σd (n, ks, e) rs) ans
        (rs.length * (24 * n + Cb + s + 45) + Bgen + 19) ∧
      AnsOK DV n (w.denote n) (PermData.denote n σd) G (xy.1.denote n) (xy.2.denote n) ans ∧
      ∀ sGen, (∀ gs, GensData.AllValid n gs → GensData.denote n gs ≤ G →
          (X.O.run GroupOp.generate (n, gs)).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  have hbr : ∀ r ∈ rs, ∃ v : AnswerData D,
      RunsWithin X body (Programs.branchCall sub xy w σd (n, ks, e) r) v (12 * n + 16 + Cb) ∧
        (AnsOK DV n (w.denote n) (PermData.denote n (σd.mul r)) (GensData.denote n ks)
          (xy.1.denote n) (xy.2.denote n) v ∧
          ∀ c : CosetData D, v = some c → c.2.gens.length ≤ s) := by
    intro r hr
    obtain ⟨v, hv, hok, hg⟩ := hsub (xy, w, σd.mul r, n, ks, e)
      ⟨rfl, rfl, rfl, ⟨r, hr, rfl⟩, ⟨hw, hσ.mul (hrs r hr), hKv, hWG.mono hKG⟩⟩
    refine ⟨v, ?_, hok, hg⟩
    unfold Programs.branchCall
    refine RunsWithin.bind_le (c₂ := 3 + Cb) (RunsWithin.permMul hσ (hrs r hr)) ?_ (by omega)
    refine RunsWithin.bind_le (c₂ := 2 + Cb) (RunsWithin.prim _ _) ?_
      (by simp [Prim.cost]; omega)
    refine RunsWithin.bind_le (c₂ := 1 + Cb) (RunsWithin.prim _ _) ?_
      (by simp [Prim.cost]; omega)
    refine RunsWithin.bind_le (c₂ := Cb) (RunsWithin.prim _ _) ?_ (by simp [Prim.cost])
    exact hv
  obtain ⟨as, has_run, has⟩ := RunsWithin.mapList_exists (X := X) (body := body)
    (a' := Ty.perm) (b' := Ty.answer D) hbr
  have hlen : as.length = rs.length := has.length_eq.symm
  have hmem : ∀ c ∈ branchSuccesses as, (c.1.Valid n ∧ GensData.AllValid n c.2.gens) ∧
      c.2.gens.length ≤ s := by
    intro c hc
    obtain ⟨r, -, hok, hg⟩ := exists_of_forall₂_mem has (mem_branchSuccesses.1 hc)
    exact ⟨⟨hok.1, hok.2.2.1.1⟩, hg c rfl⟩
  have hok := AnsOK.combineModel hO hWG hKG hσ hrs hcover (has.imp fun _ _ h => h.1)
  -- the combined generators are valid, not too many, and generate a subgroup of `G`
  have hcg : ∀ c₀ rest, branchSuccesses as = c₀ :: rest →
      GensData.AllValid n (combineGens c₀.1 (c₀ :: rest)) ∧
      (combineGens c₀.1 (c₀ :: rest)).length ≤ rs.length * (s + 1) ∧
      GensData.denote n (combineGens c₀.1 (c₀ :: rest)) ≤ G := by
    intro c₀ rest hss
    have hv₀ := (hmem c₀ (by rw [hss]; exact List.mem_cons_self)).1
    have hgv : GensData.AllValid n (combineGens c₀.1 (c₀ :: rest)) := by
      rw [combineGens]
      refine allValid_branchGens hv₀.1.inv fun p hp => ?_
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
      exact (hmem c (by rw [hss]; exact hc)).1
    refine ⟨hgv, ?_, ?_⟩
    · rw [length_combineGens]
      have hsum : ((c₀ :: rest).map fun c => c.2.gens.length).sum ≤ (c₀ :: rest).length * s :=
        sum_map_le _ _ _ fun c hc => (hmem c (by rw [hss]; exact hc)).2
      have hk : (c₀ :: rest).length ≤ rs.length := by
        rw [← hss, ← hlen]; exact List.length_filterMap_le _ _
      simp only [List.length_cons, Nat.add_sub_cancel] at hsum hk ⊢
      nlinarith
    · have hpost := hO .generate (n, combineGens c₀.1 (c₀ :: rest)) rfl hgv
      have hok' := hok
      unfold combineModel at hok'
      rw [hss] at hok'
      dsimp only at hok'
      rcases hH : X.O.run GroupOp.generate (n, combineGens c₀.1 (c₀ :: rest)) with ⟨n', hs', e'⟩
      rw [hH] at hpost hok'
      obtain ⟨-, -, hden⟩ := hpost
      have haut := AnsOK.eq_aut hWG hok'
      change GensData.denote n hs' = _ at haut
      change GensData.denote n hs' = GensData.denote n (combineGens c₀.1 (c₀ :: rest)) at hden
      rw [← hden, haut]
      exact aut_le _ _
  have hcomb := RunsWithin.combineProg (X := X) (body := body) (Bgen := Bgen) hPre
    (fun c hc => (hmem c hc).1) (fun c hc => (hmem c hc).2) fun c₀ rest hss =>
      hB _ (hcg c₀ rest hss).1 (hcg c₀ rest hss).2.1 (hcg c₀ rest hss).2.2
  have hcl := combineCost_le (n := n) (Bgen := Bgen) (as := as) (fun c hc => (hmem c hc).2)
  refine ⟨combineModel X.O n as, ?_, hok, ?_⟩
  · unfold Programs.branchProg
    refine RunsWithin.bind_le
      (c₂ := rs.length * (12 * n + 16 + Cb + 3) + 2 + combineCost n as Bgen)
      (RunsWithin.prim _ _) ?_ ?_
    · exact RunsWithin.bind has_run hcomb
    · rw [hlen] at hcl
      simp only [Prim.cost]
      nlinarith
  · intro sGen hgen c hc
    unfold combineModel at hc
    split at hc
    · cases hc
    · rename_i c₀ rest hss
      cases hc
      exact hgen _ (hcg c₀ rest hss).1 (hcg c₀ rest hss).2.2

end Specs

section Wf

variable {var₁ var₂ : Ty → Type} {r : Bool} {Γ : WfCtx var₁ var₂}

theorem wf_combineProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {as₁ : var₁ (.list (Ty.answer D))}
    {as₂ : var₂ (.list (Ty.answer D))} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (has : ⟨.list (Ty.answer D), as₁, as₂⟩ ∈ Γ) :
    Prog.Wf (rec := rec) r Γ (combineProg n₁ as₁) (combineProg n₂ as₂) := by
  unfold combineProg permInv permMul mapArray mapList
  prog_wf

theorem wf_branchProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs}
    {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win} {σ₁ : var₁ Ty.perm} {σ₂ : var₂ Ty.perm}
    {K₁ : var₁ (Ty.group D)} {K₂ : var₂ (Ty.group D)} {rs₁ : var₁ Ty.gens} {rs₂ : var₂ Ty.gens}
    (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ) (hσ : ⟨Ty.perm, σ₁, σ₂⟩ ∈ Γ)
    (hK : ⟨Ty.group D, K₁, K₂⟩ ∈ Γ) (hrs : ⟨Ty.gens, rs₁, rs₂⟩ ∈ Γ) :
    Prog.Wf r Γ (branchProg sub₁ xy₁ w₁ σ₁ K₁ rs₁) (branchProg sub₂ xy₂ w₂ σ₂ K₂ rs₂) := by
  unfold branchProg
  refine .bind (.prim _ (.cons hK .nil)) fun n₁ n₂ => .bind ?_ fun as₁ as₂ =>
    wf_combineProg (by simp) (by simp)
  refine wf_mapList (by simp [hrs]) fun Γ' hΓ' r₁ r₂ hr => ?_
  unfold branchCall permMul mapArray mapList
  prog_wf
  all_goals first
    | exact hΓ' (by simp [hxy, hw, hσ, hK])
    | exact hsub _ (fun y hy => by simp [hΓ' (List.mem_cons_of_mem _ hy)]) _ _ (by simp)

end Wf

end GraphIso.Programs
