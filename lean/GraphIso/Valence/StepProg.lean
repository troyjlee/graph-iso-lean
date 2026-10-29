module

public import GraphIso.Valence.Ind
public import GraphIso.Valence.LevelsProg
public import GraphIso.Graph.LiftProg

/-!
# Programs of one layer step for maximum degree `Δ`: subsets, induced generators, layer string

Programs of the cost language computing the functional models of
`GraphIso/Valence/StepModel.lean` and `GraphIso/Valence/Ind.lean`, with exact results and
explicit costs:

* `subsProg Δ Lr`: the sublists `subsR Δ Lr`, by one fold over `Lr` from the right
  (`subsStepProg` extends the sublists of fewer than `Δ` elements by the new point). For `ℓ`
  points it costs at most `ℓ ((ℓ + 1)^Δ (Δ + 12) + 7) + 4` (`subsCost`).
* `findSubProg Sb s`: the index of the first member of `Sb` with the elements of `s`, by a
  linear search; `indProg N Sb g`: the induced generator, which equals `indData Δ N Lr g` for
  `Sb = subsR Δ Lr` (`indDataB_eq`).
* `xSubProg Δ`: the layer string of a subset (`xSub`); `xArrProg Δ`: the layer-string array
  (`xArr`).

The element costs use `cE Δ = 6 Δ² + 12 Δ + 6` (a neighbourhood test against a subset) and
`cF Δ = 6 Δ² + 6 Δ + 10` (one step of the search). Each program is well-formed (`wf_*`).
-/

@[expose] public section

namespace GraphIso.Graph.Valence

open Equiv Cost Programs Sims

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The list has fewer than `Δ` elements. -/
def shortLtProg (Δ : ℕ) (s : var (.list .nat)) : Prog S rec var .bool :=
  .bind (.op1 .length s) fun k => .bind (.op0 (.natLit Δ)) fun d => .op2 .natLt k d

/-- One step of the sublists: keep `acc`, and extend its members of fewer than `Δ` elements by
`x`. -/
def subsStepProg (Δ : ℕ) (acc : var (.list (.list .nat))) (x : var .nat) :
    Prog S rec var (.list (.list .nat)) :=
  .bind (Luks.filterList acc fun s => shortLtProg Δ s) fun sm =>
  .bind (mapList sm fun s => .op2 .cons x s) fun ext => .op2 .append acc ext

/-- **The sublists of `Lr` with at most `Δ` elements.** -/
def subsProg (Δ : ℕ) (Lr : var (.list .nat)) : Prog S rec var (.list (.list .nat)) :=
  .bind (.op1 .reverse Lr) fun rl => .bind (.op0 .nil) fun e => .bind (.op0 .nil) fun ee =>
  .bind (.op2 .cons e ee) fun init => .foldList rl init fun acc x => subsStepProg Δ acc x

/-- One step of the search for a member with the elements of `s`. -/
def subFindStepProg (s : var (.list .nat)) (st : var (.prod .nat .bool))
    (u : var (.list .nat)) : Prog S rec var (.prod .nat .bool) :=
  .bind (.op1 .snd st) fun found => .ite found (.ret st)
    (.bind (seteqProg u s) fun e => .bind (.op1 .fst st) fun i =>
      .ite e (.bind (.op0 (.boolLit true)) fun t => .op2 .pair i t)
        (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' =>
          .op2 .pair i' found))

/-- The index of the first member of `Sb` with the elements of `s`. -/
def findSubProg (Sb : var (.list (.list .nat))) (s : var (.list .nat)) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.boolLit false)) fun f =>
  .bind (.op2 .pair z f) fun st₀ =>
  .bind (.foldList Sb st₀ fun st u => subFindStepProg s st u) fun st => .op1 .fst st

/-- The induced image of the subset `s` under the forward array `f`. -/
def imgProg (N : var .nat) (Sb : var (.list (.list .nat))) (f : var (.array .nat))
    (s : var (.list .nat)) : Prog S rec var .nat :=
  .bind (mapGetProg f s) fun s' => .bind (findSubProg Sb s') fun i => .op2 .add N i

/-- The induced array of `f`. -/
def indArrProg (N : var .nat) (Sb : var (.list (.list .nat))) (f : var (.array .nat)) :
    Prog S rec var (.array .nat) :=
  .bind (.op1 .arrayToList f) fun fl =>
  .bind (mapList Sb fun s => imgProg N Sb f s) fun ts =>
  .bind (.op2 .append fl ts) fun l => .op1 .arrayOfList l

/-- **The induced generator.** -/
def indProg (N : var .nat) (Sb : var (.list (.list .nat))) (g : var Ty.perm) :
    Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun g₁ => .bind (.op1 .snd g) fun g₂ =>
  .bind (indArrProg N Sb g₁) fun a₁ => .bind (indArrProg N Sb g₂) fun a₂ => .op2 .pair a₁ a₂

/-- The edge test of a list. -/
def edgeLProg (G : var Ty.graph) (s : var (.list .nat)) : Prog S rec var .bool :=
  .caseList s (.op0 (.boolLit false)) fun x t =>
    .caseList t (.op0 (.boolLit false)) fun y t' =>
      .caseList t' (adjProg G x y) fun _ _ => .op0 (.boolLit false)

/-- The layer string of the subset `s`; `New` lists the points of level `r + 1`. -/
def xSubProg (Δ : ℕ) (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat)
    (New : var (.list .nat)) (s : var (.list .nat)) : Prog S rec var .nat :=
  .bind (Luks.filterList New fun w => nbEqProg G lev r s w) fun cl =>
  .bind (.op1 .length cl) fun c => .bind (edgeLProg G s) fun e =>
  .ite e (.bind (.op0 (.natLit (Δ + 1))) fun k => .op2 .add c k) (.ret c)

/-- **The layer-string array**: `0` on the `N` graph points, then the subsets `Sb`. -/
def xArrProg (Δ : ℕ) (G : var Ty.graph) (lev : var (.array .nat)) (N r : var .nat)
    (New : var (.list .nat)) (Sb : var (.list (.list .nat))) : Prog S rec var Ty.str :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk N z) fun za =>
  .bind (.op1 .arrayToList za) fun zl =>
  .bind (mapList Sb fun s => xSubProg Δ G lev r New s) fun xs =>
  .bind (.op2 .append zl xs) fun l => .op1 .arrayOfList l

end Prog

/-! ### Models -/

/-- One step of the sublists. -/
def subsStep (Δ : ℕ) (acc : List (List ℕ)) (x : ℕ) : List (List ℕ) :=
  acc ++ (acc.filter fun s => decide (s.length < Δ)).map (x :: ·)

theorem foldl_subsStep (Δ : ℕ) (l : List ℕ) : l.reverse.foldl (subsStep Δ) [[]] = subsR Δ l := by
  rw [List.foldl_reverse]
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldr_cons, ih]; rfl

/-- One step of the search. -/
def subFindStep (s : List ℕ) (st : ℕ × Bool) (u : List ℕ) : ℕ × Bool :=
  if st.2 then st else if seteqB u s then (st.1, true) else (st.1 + 1, st.2)

theorem subFindStep_found (s : List ℕ) :
    ∀ (l : List (List ℕ)) (i : ℕ), l.foldl (subFindStep s) (i, true) = (i, true)
  | [], _ => rfl
  | _ :: l, i => by
    simp only [List.foldl_cons, subFindStep, ↓reduceIte]
    exact subFindStep_found s l i

theorem subFindStep_fold (s : List ℕ) : ∀ (l : List (List ℕ)) (i : ℕ),
    (l.foldl (subFindStep s) (i, false)).1 = i + l.findIdx fun u => seteqB u s
  | [], i => by simp
  | u :: l, i => by
    rw [List.foldl_cons, List.findIdx_cons]
    cases h : seteqB u s
    · simp only [subFindStep, h, Bool.false_eq_true, ↓reduceIte]
      rw [subFindStep_fold s l (i + 1)]
      omega
    · simp [subFindStep, h, subFindStep_found]

/-- The induced image of a subset, as computed. -/
def imgB (N : ℕ) (Sb : List (List ℕ)) (f : Array ℕ) (s : List ℕ) : ℕ :=
  N + Sb.findIdx fun u => seteqB u (mapGet f s)

/-- The induced array, as computed. -/
def indArr (N : ℕ) (Sb : List (List ℕ)) (f : Array ℕ) : Array ℕ :=
  (f.toList ++ Sb.map (imgB N Sb f)).toArray

/-- The induced data, as computed. -/
def indDataB (N : ℕ) (Sb : List (List ℕ)) (g : PermData) : PermData :=
  (indArr N Sb g.1, indArr N Sb g.2)

section IndModel

variable {Δ N : ℕ} {Lr : List ℕ}

theorem indArr_eq (hlt : ∀ x ∈ Lr, x < N) {f : Array ℕ}
    {π : Perm (Fin N)} (hf : f.size = N) (hfπ : ∀ i < N, get f i = act π i) :
    indArr N (subsR Δ Lr) f = ((List.range (domSize Δ N Lr)).map (indFun Δ N Lr π)).toArray := by
  unfold indArr
  congr 1
  refine List.ext_getElem (by simp [hf, domSize]) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < N
  · rw [List.getElem_append_left (by simpa [hf] using hi)]
    simp only [Array.getElem_toList]
    rw [← get_eq_getElem (by omega), hfπ i hi]
    simp [indFun, hi]
  · have hlen : f.toList.length = N := by simp [hf]
    have ht : i - N < nsub Δ Lr := by
      show i - N < (subsR Δ Lr).length
      simp only [List.length_append, List.length_map, hlen] at h₁
      omega
    rw [List.getElem_append_right (by omega)]
    simp only [List.getElem_map, hlen]
    have hmap : mapGet f (subsR Δ Lr)[i - N] = (subAt Δ Lr (i - N)).map (act π) := by
      rw [subAt_eq ht]
      unfold mapGet
      refine List.map_congr_left fun x hx => hfπ x (hlt x ?_)
      rw [← subAt_eq ht] at hx
      exact mem_of_mem_subAt ht hx
    unfold imgB
    rw [hmap, indFun_ge (by omega) (by simp only [domSize] at h₂ ⊢; simpa using h₂)]
    rfl

/-- **The computed induced data are `indData`.** -/
theorem indDataB_eq (hlt : ∀ x ∈ Lr, x < N) {g : PermData} (hg : g.Valid N) :
    indDataB N (subsR Δ Lr) g = indData Δ N Lr g := by
  unfold indDataB indData PermData.ofFun
  rw [indArr_eq hlt hg.size_fwd (fun i hi => get_fst_of_valid hg hi),
    indArr_eq hlt hg.size_inv (fun i hi => get_snd_of_valid hg hi)]

end IndModel

/-! ### Costs -/

/-- The cost bound of a neighbourhood test against a subset. -/
def cE (Δ : ℕ) : ℕ := 6 * Δ * Δ + 12 * Δ + 6

/-- The cost bound of one step of the search. -/
def cF (Δ : ℕ) : ℕ := 6 * Δ * Δ + 6 * Δ + 10

/-- The cost bound of the sublists of `ℓ` points. -/
def subsCost (Δ ℓ : ℕ) : ℕ := ℓ * ((ℓ + 1) ^ Δ * (Δ + 12) + 7) + 4

/-- The cost bound of one induced array, with `m` subsets. -/
def indArrCost (Δ N m : ℕ) : ℕ := m * (m * (cF Δ + 1) + 4 * Δ + 11) + 3 * N + 5

/-- The cost bound of the layer string of one subset. -/
def xSubCost (Δ N : ℕ) : ℕ := N * (cE Δ + 5) + 3 * Δ + 15

theorem seteq_cost_le {Δ : ℕ} {l₁ l₂ : List ℕ} (h₁ : l₁.length ≤ Δ) (h₂ : l₂.length ≤ Δ) :
    l₁.length * (3 * l₂.length + 3) + l₂.length * (3 * l₁.length + 3) + 3 ≤
      6 * Δ * Δ + 6 * Δ + 3 := by
  have a : l₁.length * (3 * l₂.length + 3) ≤ Δ * (3 * Δ + 3) := Nat.mul_le_mul h₁ (by omega)
  have b : l₂.length * (3 * l₁.length + 3) ≤ Δ * (3 * Δ + 3) := Nat.mul_le_mul h₂ (by omega)
  nlinarith

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.shortLtProg (Δ : ℕ) (s : List ℕ) :
    RunsWithin X body (Valence.shortLtProg Δ s) (decide (s.length < Δ)) (s.length + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    omega

theorem RunsWithin.subsStepProg (Δ : ℕ) {acc : List (List ℕ)} (hacc : ∀ s ∈ acc, s.length ≤ Δ)
    (x : ℕ) :
    RunsWithin X body (Valence.subsStepProg Δ acc x) (subsStep Δ acc x)
      (acc.length * (Δ + 12) + 5) := by
  have hf := Luks.RunsWithin.filterList (X := X) (body := body) (a' := .list .nat) (xs := acc)
    (p := fun s => Valence.shortLtProg Δ s) (P := fun s => decide (s.length < Δ))
    (c := Δ + 3) fun s hs => (RunsWithin.shortLtProg Δ s).mono (by have := hacc s hs; omega)
  have hlen := List.length_filter_le (fun s : List ℕ => decide (s.length < Δ)) acc
  apply RunsWithin.mono
  case h =>
    run_step hf
    run_step (RunsWithin.mapList_le (c := 1) fun s _ => RunsWithin.prim_le rfl le_rfl)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    nlinarith

/-- The fold of `subsProg`, from the sublists of a suffix `t`. -/
theorem RunsWithin.subsFold (Δ M : ℕ) : ∀ (xs t : List ℕ), (xs.reverse ++ t).Nodup →
    ((xs.reverse ++ t).length + 1) ^ Δ ≤ M →
    RunsWithin X body (.foldList (a := .nat) (b := .list (.list .nat)) xs (subsR Δ t)
      fun acc x => Valence.subsStepProg Δ acc x) (subsR Δ (xs.reverse ++ t))
      (xs.length * (M * (Δ + 12) + 6))
  | [], t, _, _ => by simpa using RunsWithin.foldList_nil
  | x :: xs, t, hnd, hM => by
    have e : (x :: xs).reverse ++ t = xs.reverse ++ (x :: t) := by simp
    rw [e] at hnd hM ⊢
    have ht : t.Nodup := (hnd.sublist (List.sublist_append_right _ _)).sublist
      (List.sublist_cons_self x t)
    have hlt : (t.length + 1) ^ Δ ≤ M := by
      refine le_trans (Nat.pow_le_pow_left ?_ Δ) hM
      simp only [List.length_append, List.length_cons]
      omega
    have hacc : ∀ s ∈ subsR Δ t, s.length ≤ Δ := fun s hs => (mem_subsR.1 hs).2
    have h₁ := RunsWithin.subsStepProg (X := X) (body := body) Δ hacc x
    have hc₁ : (subsR Δ t).length * (Δ + 12) + 5 ≤ M * (Δ + 12) + 5 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ ((length_subsR_le Δ ht).trans hlt)) _
    have h₂ := RunsWithin.subsFold Δ M xs (x :: t) hnd hM
    refine (RunsWithin.foldList_cons (h₁.mono hc₁) h₂).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem RunsWithin.subsProg (Δ : ℕ) {Lr : List ℕ} (hnd : Lr.Nodup) :
    RunsWithin X body (Valence.subsProg Δ Lr) (subsR Δ Lr) (subsCost Δ Lr.length) := by
  have hfold := RunsWithin.subsFold (X := X) (body := body) Δ ((Lr.length + 1) ^ Δ)
    Lr.reverse [] (by simpa using hnd) (by simp)
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons, subsCost]
    have : Lr.length * ((Lr.length + 1) ^ Δ * (Δ + 12) + 6) + Lr.length =
        Lr.length * ((Lr.length + 1) ^ Δ * (Δ + 12) + 7) := by ring
    omega

theorem RunsWithin.subFindStepProg {Δ : ℕ} {s : List ℕ} (hs : s.length ≤ Δ) (st : ℕ × Bool)
    {u : List ℕ} (hu : u.length ≤ Δ) :
    RunsWithin X body (Valence.subFindStepProg s st u) (subFindStep s st u) (cF Δ) := by
  have hse := seteq_cost_le hu hs
  rcases st with ⟨i, _ | _⟩
  · cases he : seteqB u s
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval]) _
        run_step (RunsWithin.seteqProg u s)
        run_step (RunsWithin.prim _ _)
        rw [he]
        run_with RunsWithin.ite_neg rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, subFindStep, he]) le_rfl
      case hc =>
        simp only [Prim.cost, cF]
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval]) _
        run_step (RunsWithin.seteqProg u s)
        run_step (RunsWithin.prim _ _)
        rw [he]
        run_with RunsWithin.ite_pos rfl _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, subFindStep, he]) le_rfl
      case hc =>
        simp only [Prim.cost, cF]
        omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (by simp [Prim.eval]) _
      exact (RunsWithin.ret _).of_eq (by simp [subFindStep])
    case hc =>
      simp only [Prim.cost, cF]
      omega

theorem RunsWithin.findSubProg {Δ : ℕ} {Sb : List (List ℕ)} (hSb : ∀ u ∈ Sb, u.length ≤ Δ)
    {s : List ℕ} (hs : s.length ≤ Δ) :
    RunsWithin X body (Valence.findSubProg Sb s) (Sb.findIdx fun u => seteqB u s)
      (Sb.length * (cF Δ + 1) + 4) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat)
    (b' := .prod .nat .bool) (cf := fun _ => cF Δ) (F := subFindStep s)
    (f := fun st u => Valence.subFindStepProg s st u) Sb (0, false)
    fun st u hu => RunsWithin.subFindStepProg hs st (hSb u hu)
  rw [sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le (by simp [Prim.eval, subFindStep_fold]) le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.imgProg {Δ : ℕ} (N : ℕ) {Sb : List (List ℕ)}
    (hSb : ∀ u ∈ Sb, u.length ≤ Δ) (f : Array ℕ) {s : List ℕ} (hs : s.length ≤ Δ) :
    RunsWithin X body (Valence.imgProg N Sb f s) (imgB N Sb f s)
      (Sb.length * (cF Δ + 1) + 4 * Δ + 7) := by
  have hs' : (mapGet f s).length ≤ Δ := by simpa [mapGet] using hs
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mapGetProg f s)
    run_step (RunsWithin.findSubProg hSb hs')
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.indArrProg {Δ N : ℕ} {Sb : List (List ℕ)} (hSb : ∀ u ∈ Sb, u.length ≤ Δ)
    {f : Array ℕ} (hf : f.size = N) :
    RunsWithin X body (Valence.indArrProg N Sb f) (indArr N Sb f)
      (indArrCost Δ N Sb.length) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun s hs => RunsWithin.imgProg N hSb f (hSb s hs))
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_map,
      Array.length_toList, hf, indArrCost]
    nlinarith

theorem RunsWithin.indProg {Δ N : ℕ} {Sb : List (List ℕ)} (hSb : ∀ u ∈ Sb, u.length ≤ Δ)
    {g : PermData} (hg : g.Valid N) :
    RunsWithin X body (Valence.indProg N Sb g) (indDataB N Sb g)
      (2 * indArrCost Δ N Sb.length + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.indArrProg hSb hg.size_fwd)
    run_step (RunsWithin.indArrProg hSb hg.size_inv)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.nbEqProg {Δ : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (lev : Array ℕ) (r : ℕ) {T : List ℕ} (hT : T.length ≤ Δ) (w : ℕ) :
    RunsWithin X body (Graph.nbEqProg G lev r T w) (seteqB (nbL G lev r w) T) (cE Δ) := by
  have h₁ := hGd w
  have h₂ := length_nbL_le G lev r w
  have hse := seteq_cost_le (l₁ := nbL G lev r w) (h₂.trans h₁) hT
  refine RunsWithin.bind_le (RunsWithin.nbLProg G lev r w) (RunsWithin.seteqProg _ T) ?_
  unfold cE
  omega

theorem RunsWithin.edgeLProg {Δ : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (s : List ℕ) : RunsWithin X body (Valence.edgeLProg G s) (edgeL G s) (3 * Δ + 5) := by
  rcases s with _ | ⟨x, _ | ⟨y, _ | ⟨z, t⟩⟩⟩
  · exact (RunsWithin.caseList_nil (RunsWithin.prim_le rfl le_rfl)).mono
      (by simp [Prim.cost])
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_nil
      (RunsWithin.prim_le rfl le_rfl))).mono (by simp [Prim.cost])
  · have := hGd x
    exact (RunsWithin.caseList_cons (RunsWithin.caseList_cons (RunsWithin.caseList_nil
      (RunsWithin.adjProg G x y)))).mono (by omega)
  · exact (RunsWithin.caseList_cons (RunsWithin.caseList_cons (RunsWithin.caseList_cons
      (RunsWithin.prim_le rfl le_rfl)))).mono (by simp [Prim.cost])

theorem RunsWithin.xSubProg {Δ N : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (lev : Array ℕ) (r : ℕ) (hm : (levList lev N (r + 1)).length ≤ N) {s : List ℕ}
    (hs : s.length ≤ Δ) :
    RunsWithin X body (Valence.xSubProg Δ G lev r (levList lev N (r + 1)) s)
      (xSub Δ G lev N r s) (xSubCost Δ N) := by
  have hfilt := Luks.RunsWithin.filterList (X := X) (body := body) (a' := .nat)
    (xs := levList lev N (r + 1)) fun w _ => RunsWithin.nbEqProg hGd lev r hs w
  have hc : (levList lev N (r + 1)).length * (cE Δ + 4) ≤ N * (cE Δ + 4) :=
    Nat.mul_le_mul_right _ hm
  cases he : edgeL G s
  · apply RunsWithin.mono
    case h =>
      run_step hfilt
      run_step (RunsWithin.prim_le (c := N + 1) rfl (by
        simp only [Prim.cost, Args.head_cons]
        exact Nat.succ_le_succ ((List.length_filter_le _ _).trans hm)))
      run_step (RunsWithin.edgeLProg hGd s)
      rw [he]
      run_with RunsWithin.ite_neg rfl _
      exact (RunsWithin.ret _).of_eq (by simp [xSub, Prim.eval, he])
    case hc =>
      simp only [xSubCost]
      nlinarith
  · apply RunsWithin.mono
    case h =>
      run_step hfilt
      run_step (RunsWithin.prim_le (c := N + 1) rfl (by
        simp only [Prim.cost, Args.head_cons]
        exact Nat.succ_le_succ ((List.length_filter_le _ _).trans hm)))
      run_step (RunsWithin.edgeLProg hGd s)
      rw [he]
      run_with RunsWithin.ite_pos rfl _
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [xSub, Prim.eval, he]) le_rfl
    case hc =>
      simp only [Prim.cost, xSubCost]
      nlinarith

theorem RunsWithin.xArrProg {Δ N : ℕ} {G : GraphData} (hGd : ∀ u, (nbrs G u).length ≤ Δ)
    (lev : Array ℕ) (r : ℕ) (hm : (levList lev N (r + 1)).length ≤ N) (Lr : List ℕ) :
    RunsWithin X body (Valence.xArrProg Δ G lev N r (levList lev N (r + 1)) (subsR Δ Lr))
      (xArr Δ G lev N r Lr) ((nsub Δ Lr) * (xSubCost Δ N + 4) + 4 * N + 8) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun s hs =>
      RunsWithin.xSubProg hGd lev r hm (mem_subsR.1 hs).2)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, xArr]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_map,
      Array.length_toList, Array.size_replicate]
    ring_nf
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_subsProg (Δ : ℕ) {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)}
    (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (subsProg Δ l₁) (subsProg Δ l₂) := by
  unfold subsProg subsStepProg shortLtProg Luks.filterList mapList
  prog_wf

theorem wf_indProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {Sb₁ : var₁ (.list (.list .nat))}
    {Sb₂ : var₂ (.list (.list .nat))} {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm}
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hSb : ⟨.list (.list .nat), Sb₁, Sb₂⟩ ∈ Γ)
    (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (indProg N₁ Sb₁ g₁) (indProg N₂ Sb₂ g₂) := by
  unfold indProg indArrProg imgProg findSubProg subFindStepProg seteqProg memProg mapGetProg
    allList anyList mapList
  prog_wf

theorem wf_xArrProg (Δ : ℕ) {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph}
    {l₁ : var₁ (.array .nat)} {l₂ : var₂ (.array .nat)} {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat}
    {New₁ : var₁ (.list .nat)} {New₂ : var₂ (.list .nat)} {Sb₁ : var₁ (.list (.list .nat))}
    {Sb₂ : var₂ (.list (.list .nat))} (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ)
    (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hNew : ⟨.list .nat, New₁, New₂⟩ ∈ Γ) (hSb : ⟨.list (.list .nat), Sb₁, Sb₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (xArrProg Δ G₁ l₁ N₁ r₁ New₁ Sb₁)
      (xArrProg Δ G₂ l₂ N₂ r₂ New₂ Sb₂) := by
  unfold xArrProg xSubProg edgeLProg nbEqProg nbLProg levEqProg seteqProg adjProg memProg
    Luks.filterList allList anyList mapList
  prog_wf

end Wf

end GraphIso.Graph.Valence
