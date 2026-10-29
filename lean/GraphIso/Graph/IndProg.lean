module

public import GraphIso.Graph.StepProg

/-!
# Programs of one layer step: the induced generators

* `levListProg`: the points of level `r` (`levList`).
* `posProg N Lr`: the position array `posArr N Lr`, with `get (posArr N Lr) x = Lr.idxOf x` for
  `x ∈ Lr` (`get_posArr`).
* `multsProg k m`: the array of `0, m, …, (k − 1) m` (`multsArr`); `mulProg a b`: `a * b`.
* `cidxProg`: the index array of the canonical triples, with
  `get (cidxArr …) (enc ℓ t) = (subsL ℓ).idxOf t` (`get_cidxArr`).
* `canonProg`: the canonical triple of three numbers (`canon`).
* `indProg`: the induced generator. With the position, offset and index arrays of `Lr` it
  computes `indData N Lr g` (`indDataB_eq`): the subset `(x, y, z)` goes to `N` plus the index of
  the canonical triple of the positions of `g x`, `g y`, `g z`.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims

/-! ### Models -/

/-- One write of the position array. -/
def posStep (st : ℕ × List (ℕ × ℕ)) (x : ℕ) : ℕ × List (ℕ × ℕ) := (st.1 + 1, (x, st.1) :: st.2)

/-- The writes of the position array. -/
def posWrites (Lr : List ℕ) : List (ℕ × ℕ) := (Lr.foldl posStep (0, [])).2

/-- The position array: `x ↦ Lr.idxOf x` on `Lr`. -/
def posArr (N : ℕ) (Lr : List ℕ) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate N 0) (posWrites Lr)

theorem posStep_fold : ∀ (Lr : List ℕ) (i : ℕ) (ws : List (ℕ × ℕ)),
    ((Lr.foldl posStep (i, ws)).2.map Prod.fst) = Lr.reverse ++ ws.map Prod.fst ∧
      (∀ e ∈ ws, e ∈ (Lr.foldl posStep (i, ws)).2) ∧
      ∀ t (ht : t < Lr.length), (Lr[t], i + t) ∈ (Lr.foldl posStep (i, ws)).2
  | [], i, ws => ⟨by simp, fun _ h => h, fun t ht => absurd ht (by simp)⟩
  | x :: Lr, i, ws => by
    obtain ⟨h₁, h₂, h₃⟩ := posStep_fold Lr (i + 1) ((x, i) :: ws)
    simp only [List.foldl_cons, posStep] at h₁ h₂ h₃ ⊢
    refine ⟨by rw [h₁]; simp, fun e he => h₂ e (List.mem_cons_of_mem _ he), fun t ht => ?_⟩
    rcases t with _ | t
    · exact h₂ _ List.mem_cons_self
    · have := h₃ t (by simpa using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

theorem get_posArr {N : ℕ} {Lr : List ℕ} (hnd : Lr.Nodup) (hlt : ∀ x ∈ Lr, x < N) {x : ℕ}
    (hx : x ∈ Lr) : get (posArr N Lr) x = Lr.idxOf x := by
  obtain ⟨h₁, -, h₃⟩ := posStep_fold Lr 0 []
  have hkeys : ((posWrites Lr).map Prod.fst).Nodup := by
    rw [posWrites, h₁]
    simpa using hnd
  have hi := List.idxOf_lt_length_of_mem hx
  have hmem : (x, Lr.idxOf x) ∈ posWrites Lr := by
    have := h₃ _ hi
    rw [List.getElem_idxOf hi, Nat.zero_add] at this
    exact this
  have h := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate N 0) hkeys hmem
    (by simpa using hlt x hx)
  unfold get posArr
  rw [Array.getD_eq_getD_getElem?, h]
  rfl

/-- One step of the multiples. -/
def multStep (m : ℕ) (st : ℕ × List ℕ) (_ : ℕ) : ℕ × List ℕ := (st.1 + m, st.1 :: st.2)

/-- The array `0, m, …, (k − 1) m`. -/
def multsArr (k m : ℕ) : Array ℕ := ((List.range k).map (· * m)).toArray

theorem multStep_fold (m : ℕ) : ∀ (k c : ℕ) (l : List ℕ),
    (List.range k).foldl (multStep m) (c, l) =
      (c + k * m, ((List.range k).map fun i => c + i * m).reverse ++ l)
  | 0, c, l => by simp
  | k + 1, c, l => by
    rw [List.range_succ, List.foldl_append, multStep_fold m k c l]
    simp only [List.foldl_cons, List.foldl_nil, multStep, List.map_append, List.map_cons,
      List.map_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [Prod.mk.injEq]
    exact ⟨by ring, rfl⟩

theorem get_multsArr {k m i : ℕ} (hi : i < k) : get (multsArr k m) i = i * m := by
  simp [multsArr, get, hi]

theorem mul_fold (b : ℕ) : ∀ (a c : ℕ),
    (List.range a).foldl (fun acc _ => acc + b) c = c + a * b
  | 0, c => by simp
  | a + 1, c => by
    rw [List.range_succ, List.foldl_append, mul_fold b a c]
    simp only [List.foldl_cons, List.foldl_nil]
    ring

/-- The key `off₁[i] + off₂[j] + k` of a triple. -/
def keyB (off₁ off₂ : Array ℕ) (t : ℕ × ℕ × ℕ) : ℕ := get off₁ t.1 + get off₂ t.2.1 + t.2.2

/-- One write of the index array. -/
def cidxStep (off₁ off₂ : Array ℕ) (st : ℕ × List (ℕ × ℕ)) (t : ℕ × ℕ × ℕ) :
    ℕ × List (ℕ × ℕ) :=
  (st.1 + 1, (keyB off₁ off₂ t, st.1) :: st.2)

/-- The index array: the index of each listed triple, at its key. -/
def cidxArr (M : ℕ) (off₁ off₂ : Array ℕ) (S : List (ℕ × ℕ × ℕ)) : Array ℕ :=
  Prim.applyWrites (a := .nat) (Array.replicate M 0) (S.foldl (cidxStep off₁ off₂) (0, [])).2

theorem cidxStep_fold (off₁ off₂ : Array ℕ) : ∀ (S : List (ℕ × ℕ × ℕ)) (i : ℕ)
    (ws : List (ℕ × ℕ)),
    ((S.foldl (cidxStep off₁ off₂) (i, ws)).2.map Prod.fst) =
        (S.map (keyB off₁ off₂)).reverse ++ ws.map Prod.fst ∧
      (∀ e ∈ ws, e ∈ (S.foldl (cidxStep off₁ off₂) (i, ws)).2) ∧
      ∀ t (ht : t < S.length), (keyB off₁ off₂ S[t], i + t) ∈
        (S.foldl (cidxStep off₁ off₂) (i, ws)).2
  | [], i, ws => ⟨by simp, fun _ h => h, fun t ht => absurd ht (by simp)⟩
  | x :: S, i, ws => by
    obtain ⟨h₁, h₂, h₃⟩ := cidxStep_fold off₁ off₂ S (i + 1) ((keyB off₁ off₂ x, i) :: ws)
    simp only [List.foldl_cons, cidxStep] at h₁ h₂ h₃ ⊢
    refine ⟨by rw [h₁]; simp, fun e he => h₂ e (List.mem_cons_of_mem _ he), fun t ht => ?_⟩
    rcases t with _ | t
    · exact h₂ _ List.mem_cons_self
    · have := h₃ t (by simpa using ht)
      simpa [Nat.add_assoc, Nat.add_comm 1 t] using this

theorem keyB_eq {ℓ : ℕ} {t : ℕ × ℕ × ℕ} (ht : t.1 < ℓ ∧ t.2.1 < ℓ ∧ t.2.2 < ℓ) :
    keyB (multsArr ℓ (ℓ * ℓ)) (multsArr ℓ ℓ) t = enc ℓ t.1 t.2.1 t.2.2 := by
  unfold keyB enc
  rw [get_multsArr ht.1, get_multsArr ht.2.1]
  ring

/-- **The index array finds the index of a canonical triple.** -/
theorem get_cidxArr {ℓ : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ subsL ℓ) :
    get (cidxArr (ℓ * ℓ * ℓ) (multsArr ℓ (ℓ * ℓ)) (multsArr ℓ ℓ) (subsL ℓ))
      (enc ℓ t.1 t.2.1 t.2.2) = (subsL ℓ).idxOf t := by
  obtain ⟨h₁, -, h₃⟩ := cidxStep_fold (multsArr ℓ (ℓ * ℓ)) (multsArr ℓ ℓ) (subsL ℓ) 0 []
  have hrange : ∀ u ∈ subsL ℓ, u.1 < ℓ ∧ u.2.1 < ℓ ∧ u.2.2 < ℓ := fun u hu =>
    (mem_subsL.1 hu).1
  have hkeys : (((subsL ℓ).foldl (cidxStep (multsArr ℓ (ℓ * ℓ)) (multsArr ℓ ℓ)) (0, [])).2.map
      Prod.fst).Nodup := by
    rw [h₁, List.map_nil, List.append_nil, List.nodup_reverse]
    refine (nodup_subsL ℓ).map_on fun u hu v hv he => ?_
    rw [keyB_eq (hrange u hu), keyB_eq (hrange v hv)] at he
    have hu' := hrange u hu
    have hv' := hrange v hv
    have := congrArg (dec ℓ) he
    rw [dec_enc hu'.2.1 hu'.2.2, dec_enc hv'.2.1 hv'.2.2] at this
    exact this
  have hi := List.idxOf_lt_length_of_mem ht
  have hmem := h₃ _ hi
  rw [List.getElem_idxOf hi, Nat.zero_add, keyB_eq (hrange t ht)] at hmem
  have h := getElem?_applyWrites_of_mem (a := .nat) (Array.replicate (ℓ * ℓ * ℓ) 0) hkeys hmem
    (by simpa using enc_lt (hrange t ht).1 (hrange t ht).2.1 (hrange t ht).2.2)
  unfold get cidxArr
  rw [Array.getD_eq_getD_getElem?, h]
  rfl

/-- The induced image of a subset, read through the position, offset and index arrays. -/
def imgB (N : ℕ) (pos off₁ off₂ cidx f : Array ℕ) (p : ℕ × ℕ × ℕ) : ℕ :=
  N + get cidx (keyB off₁ off₂ (canon (tmap (fun x => get pos (get f x)) p)))

/-- The induced array of `f`: `f` on the graph points, `imgB` on the subsets. -/
def indArr (N : ℕ) (pos off₁ off₂ cidx : Array ℕ) (P : List (ℕ × ℕ × ℕ)) (f : Array ℕ) :
    Array ℕ :=
  (f.toList ++ P.map (imgB N pos off₁ off₂ cidx f)).toArray

/-- The induced data, as computed. -/
def indDataB (N : ℕ) (pos off₁ off₂ cidx : Array ℕ) (P : List (ℕ × ℕ × ℕ)) (g : PermData) :
    PermData :=
  (indArr N pos off₁ off₂ cidx P g.1, indArr N pos off₁ off₂ cidx P g.2)

/-- The index array of the subsets of `Lr`. -/
abbrev cidxOf (Lr : List ℕ) : Array ℕ :=
  cidxArr (Lr.length * Lr.length * Lr.length) (multsArr Lr.length (Lr.length * Lr.length))
    (multsArr Lr.length Lr.length) (subsL Lr.length)

section IndModel

variable {N : ℕ} {Lr : List ℕ}

theorem indArr_eq (hnd : Lr.Nodup) (hlt : ∀ x ∈ Lr, x < N) {f : Array ℕ} {π : Perm (Fin N)}
    (hf : f.size = N) (hfπ : ∀ i < N, get f i = act π i) (hm : MapsL Lr π) :
    indArr N (posArr N Lr) (multsArr Lr.length (Lr.length * Lr.length))
        (multsArr Lr.length Lr.length) (cidxOf Lr) (ptrips Lr) f =
      ((List.range (domSize N Lr)).map (indFun N Lr π)).toArray := by
  unfold indArr
  congr 1
  refine List.ext_getElem (by simp [hf, length_ptrips, domSize]) fun i h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  by_cases hi : i < N
  · rw [List.getElem_append_left (by simpa [hf] using hi)]
    simp only [Array.getElem_toList]
    rw [← get_eq_getElem (by omega), hfπ i hi]
    simp [indFun, hi]
  · have hlen : f.toList.length = N := by simp [hf]
    have ht : i - N < nsub Lr := by
      simp only [List.length_append, List.length_map, length_ptrips, hlen] at h₁
      omega
    rw [List.getElem_append_right (by omega)]
    simp only [List.getElem_map, hlen]
    rw [getElem_ptrips ht]
    have e : tmap (fun x => get (posArr N Lr) (get f x)) (tmap (Lr.getD · 0) (subAt Lr (i - N))) =
        tmap (posImg N Lr π) (subAt Lr (i - N)) := by
      have hr := (mem_subsL.1 (subAt_mem ht)).1
      have c : ∀ c, c < Lr.length →
          get (posArr N Lr) (get f (Lr.getD c 0)) = posImg N Lr π c := fun c hc => by
        rw [hfπ _ (hlt _ (getD_mem hc)), get_posArr hnd hlt (hm _ (getD_mem hc))]
        rfl
      simp only [tmap]
      rw [c _ hr.1, c _ hr.2.1, c _ hr.2.2]
    have hcm := canon_posImg_mem hm ht
    unfold imgB
    rw [e, keyB_eq (mem_subsL.1 hcm).1, get_cidxArr hcm, indFun_ge (by omega) (by
      simp only [domSize] at h₂ ⊢
      simpa using h₂)]
    rfl

/-- **The computed induced data are `indData`.** -/
theorem indDataB_eq (hnd : Lr.Nodup) (hlt : ∀ x ∈ Lr, x < N) {g : PermData} (hg : g.Valid N)
    (hm : MapsL Lr (PermData.denote N g)) :
    indDataB N (posArr N Lr) (multsArr Lr.length (Lr.length * Lr.length))
        (multsArr Lr.length Lr.length) (cidxOf Lr) (ptrips Lr) g = indData N Lr g := by
  unfold indDataB indData PermData.ofFun
  rw [indArr_eq hnd hlt hg.size_fwd (fun i hi => get_fst_of_valid hg hi) hm,
    indArr_eq hnd hlt hg.size_inv (fun i hi => get_snd_of_valid hg hi) (mapsL_inv hm)]

end IndModel

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The points of level `r`. -/
def levListProg (N : var .nat) (lev : var (.array .nat)) (r : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op1 .range N) fun rN => Luks.filterList rN fun u => levEqProg lev r u

/-- One write of the position array. -/
def posStepProg (st : var (.prod .nat (.list (.prod .nat .nat)))) (x : var .nat) :
    Prog S rec var (.prod .nat (.list (.prod .nat .nat))) :=
  .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun ws => .bind (.op2 .pair x i) fun xi =>
  .bind (.op2 .cons xi ws) fun ws' => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .add i one) fun i' => .op2 .pair i' ws'

/-- The position array. -/
def posProg (N : var .nat) (Lr : var (.list .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk N z) fun za =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .pair z nl) fun st₀ =>
  .bind (.foldList Lr st₀ fun st x => posStepProg st x) fun st =>
  .bind (.op1 .snd st) fun ws => .op2 .arrayUpdate za ws

/-- One step of the multiples. -/
def multStepProg (m : var .nat) (st : var (.prod .nat (.list .nat))) :
    Prog S rec var (.prod .nat (.list .nat)) :=
  .bind (.op1 .fst st) fun c => .bind (.op1 .snd st) fun l => .bind (.op2 .cons c l) fun l' =>
  .bind (.op2 .add c m) fun c' => .op2 .pair c' l'

/-- The array `0, m, …, (k − 1) m`. -/
def multsProg (k m : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range k) fun rk => .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nl =>
  .bind (.op2 .pair z nl) fun st₀ =>
  .bind (.foldList rk st₀ fun st _ => multStepProg m st) fun st =>
  .bind (.op1 .snd st) fun l => .bind (.op1 .reverse l) fun l' => .op1 .arrayOfList l'

/-- The product `a * b`, by repeated addition. -/
def mulProg (a b : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .range a) fun ra => .bind (.op0 (.natLit 0)) fun z =>
  .foldList ra z fun acc _ => .op2 .add acc b

/-- Two numbers in increasing order. -/
def sort2Prog (a b : var .nat) : Prog S rec var (.prod .nat .nat) :=
  .bind (.op2 .natLt b a) fun lt => .ite lt (.op2 .pair b a) (.op2 .pair a b)

/-- The canonical triple of `(x, y, z)`. -/
def canonProg (x y z : var .nat) : Prog S rec var Ty.trip :=
  .bind (sort2Prog x y) fun p => .bind (.op1 .fst p) fun p₁ => .bind (.op1 .snd p) fun p₂ =>
  .bind (sort2Prog p₂ z) fun q => .bind (.op1 .fst q) fun q₁ => .bind (.op1 .snd q) fun q₂ =>
  .bind (sort2Prog p₁ q₁) fun s => .bind (.op1 .fst s) fun s₁ => .bind (.op1 .snd s) fun s₂ =>
  .bind (.op2 .natEq s₂ q₂) fun e =>
  .ite e (.bind (.op2 .pair s₁ q₂) fun t => .op2 .pair s₁ t)
    (.bind (.op2 .pair s₂ q₂) fun t => .op2 .pair s₁ t)

/-- The key `off₁[i] + off₂[j] + k` of a triple. -/
def keyProg (off₁ off₂ : var (.array .nat)) (t : var Ty.trip) : Prog S rec var .nat :=
  .bind (.op1 .fst t) fun i => .bind (.op1 .snd t) fun jk =>
  .bind (.op1 .fst jk) fun j => .bind (.op1 .snd jk) fun k =>
  .bind (.op2 .arrayGet off₁ i) fun oi => .bind (.op2 .arrayGet off₂ j) fun oj =>
  .bind (.op2 .add oi oj) fun s => .op2 .add s k

/-- One write of the index array. -/
def cidxStepProg (off₁ off₂ : var (.array .nat)) (st : var (.prod .nat (.list (.prod .nat .nat))))
    (t : var Ty.trip) : Prog S rec var (.prod .nat (.list (.prod .nat .nat))) :=
  .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun ws =>
  .bind (keyProg off₁ off₂ t) fun k => .bind (.op2 .pair k i) fun ki =>
  .bind (.op2 .cons ki ws) fun ws' => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .add i one) fun i' => .op2 .pair i' ws'

/-- The index array of the canonical triples `Sb`, of size `M`. -/
def cidxProg (M : var .nat) (off₁ off₂ : var (.array .nat)) (Sb : var (.list Ty.trip)) :
    Prog S rec var (.array .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk M z) fun za =>
  .bind (.op0 .nil) fun nl => .bind (.op2 .pair z nl) fun st₀ =>
  .bind (.foldList Sb st₀ fun st t => cidxStepProg off₁ off₂ st t) fun st =>
  .bind (.op1 .snd st) fun ws => .op2 .arrayUpdate za ws

/-- The induced image of a subset. -/
def imgProg (N : var .nat) (pos off₁ off₂ cidx f : var (.array .nat)) (p : var Ty.trip) :
    Prog S rec var .nat :=
  .bind (.op1 .fst p) fun x => .bind (.op1 .snd p) fun yz =>
  .bind (.op1 .fst yz) fun y => .bind (.op1 .snd yz) fun z =>
  .bind (.op2 .arrayGet f x) fun fx => .bind (.op2 .arrayGet pos fx) fun px =>
  .bind (.op2 .arrayGet f y) fun fy => .bind (.op2 .arrayGet pos fy) fun py =>
  .bind (.op2 .arrayGet f z) fun fz => .bind (.op2 .arrayGet pos fz) fun pz =>
  .bind (canonProg px py pz) fun c => .bind (keyProg off₁ off₂ c) fun k =>
  .bind (.op2 .arrayGet cidx k) fun ix => .op2 .add N ix

/-- The induced array of `f`. -/
def indArrProg (N : var .nat) (pos off₁ off₂ cidx : var (.array .nat))
    (P : var (.list Ty.trip)) (f : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .arrayToList f) fun fl =>
  .bind (mapList P fun p => imgProg N pos off₁ off₂ cidx f p) fun ts =>
  .bind (.op2 .append fl ts) fun l => .op1 .arrayOfList l

/-- The induced generator. -/
def indProg (N : var .nat) (pos off₁ off₂ cidx : var (.array .nat)) (P : var (.list Ty.trip))
    (g : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun g₁ => .bind (.op1 .snd g) fun g₂ =>
  .bind (indArrProg N pos off₁ off₂ cidx P g₁) fun a₁ =>
  .bind (indArrProg N pos off₁ off₂ cidx P g₂) fun a₂ => .op2 .pair a₁ a₂

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.levListProg (N : ℕ) (lev : Array ℕ) (r : ℕ) :
    RunsWithin X body (Graph.levListProg N lev r) (levList lev N r) (7 * N + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    refine (Luks.RunsWithin.filterList (a' := .nat) fun u _ =>
      RunsWithin.levEqProg lev r u).of_eq ?_
    simp only [Prim.eval, levList]
    exact List.filter_congr fun v _ => by rw [Bool.eq_iff_iff]; simp
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range]
    omega

theorem RunsWithin.posStepProg (st : ℕ × List (ℕ × ℕ)) (x : ℕ) :
    RunsWithin X body (Graph.posStepProg st x) (posStep st x) 7 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.posProg (N : ℕ) (Lr : List ℕ) :
    RunsWithin X body (Graph.posProg N Lr) (posArr N Lr) (2 * N + 9 * Lr.length + 6) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list (.prod .nat .nat))) (cf := fun _ => 7) (F := posStep) Lr (0, [])
    fun st x _ => RunsWithin.posStepProg st x
  rw [sum_map_const] at hfold
  have hlen : (posWrites Lr).length = Lr.length := by
    have := congrArg List.length (posStep_fold Lr 0 []).1
    simpa [posWrites] using this
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate]
    rw [show (List.foldl posStep (0, []) Lr).2 = posWrites Lr from rfl, hlen]
    omega

theorem RunsWithin.multStepProg (m : ℕ) (st : ℕ × List ℕ) (i : ℕ) :
    RunsWithin X body (Graph.multStepProg m st) (multStep m st i) 5 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.multsProg (k m : ℕ) :
    RunsWithin X body (Graph.multsProg k m) (multsArr k m) (9 * k + 8) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list .nat)) (cf := fun _ => 5) (F := multStep m) (List.range k) (0, [])
    fun st i _ => RunsWithin.multStepProg m st i
  rw [sum_map_const, List.length_range, multStep_fold] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, multsArr]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_reverse, List.length_append,
      List.length_map, List.length_range, List.length_nil]
    omega

theorem RunsWithin.mulProg (a' b' : ℕ) :
    RunsWithin X body (Graph.mulProg a' b') (a' * b') (3 * a' + 2) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (cf := fun _ => 1) (F := fun acc _ => acc + b') (f := fun acc _ => .op2 .add acc b')
    (List.range a') 0 fun acc i _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  rw [sum_map_const, List.length_range, mul_fold, Nat.zero_add] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons]
    omega

theorem RunsWithin.sort2Prog (a' b' : ℕ) :
    RunsWithin X body (Graph.sort2Prog a' b') (sort2 a' b') 3 := by
  by_cases h : b' < a'
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show decide (b' < a') = true by simpa using h) _
      exact RunsWithin.prim_le (by simp [Prim.eval, sort2, show ¬ a' ≤ b' by omega]) le_rfl
    case hc =>
      simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show decide (b' < a') = false by simpa using h) _
      exact RunsWithin.prim_le (by simp [Prim.eval, sort2, show a' ≤ b' by omega]) le_rfl
    case hc =>
      simp [Prim.cost]

theorem RunsWithin.canonProg (x y z : ℕ) :
    RunsWithin X body (Graph.canonProg x y z) (canon (x, y, z)) 19 := by
  by_cases he : (sort3 (x, y, z)).2.1 = (sort3 (x, y, z)).2.2
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.sort2Prog x y)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sort2Prog _ z)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sort2Prog _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (by simpa [Prim.eval, sort3] using he) _
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp only [canon, he, ↓reduceIte]; rfl) le_rfl
    case hc =>
      simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.sort2Prog x y)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sort2Prog _ z)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.sort2Prog _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (by simpa [Prim.eval, sort3] using he) _
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp only [canon, he, ↓reduceIte]; rfl) le_rfl
    case hc =>
      simp [Prim.cost]

theorem RunsWithin.keyProg (off₁ off₂ : Array ℕ) (t : ℕ × ℕ × ℕ) :
    RunsWithin X body (Graph.keyProg off₁ off₂ t) (keyB off₁ off₂ t) 8 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.cidxStepProg (off₁ off₂ : Array ℕ) (st : ℕ × List (ℕ × ℕ))
    (t : ℕ × ℕ × ℕ) :
    RunsWithin X body (Graph.cidxStepProg off₁ off₂ st t) (cidxStep off₁ off₂ st t) 15 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.keyProg off₁ off₂ t)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.cidxProg (M : ℕ) (off₁ off₂ : Array ℕ) (Sb : List (ℕ × ℕ × ℕ)) :
    RunsWithin X body (Graph.cidxProg M off₁ off₂ Sb) (cidxArr M off₁ off₂ Sb)
      (2 * M + 17 * Sb.length + 6) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := Ty.trip)
    (b' := .prod .nat (.list (.prod .nat .nat))) (cf := fun _ => 15) (F := cidxStep off₁ off₂)
    Sb (0, []) fun st t _ => RunsWithin.cidxStepProg off₁ off₂ st t
  rw [sum_map_const] at hfold
  have hlen : (Sb.foldl (cidxStep off₁ off₂) (0, [])).2.length = Sb.length := by
    have := congrArg List.length (cidxStep_fold off₁ off₂ Sb 0 []).1
    simpa using this
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate, hlen]
    omega

theorem RunsWithin.imgProg (N : ℕ) (pos off₁ off₂ cidx f : Array ℕ) (p : ℕ × ℕ × ℕ) :
    RunsWithin X body (Graph.imgProg N pos off₁ off₂ cidx f p)
      (imgB N pos off₁ off₂ cidx f p) 39 := by
  apply RunsWithin.mono
  case h =>
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
    run_step (RunsWithin.canonProg _ _ _)
    run_step (RunsWithin.keyProg off₁ off₂ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp [Prim.cost]

theorem RunsWithin.indArrProg (N : ℕ) (pos off₁ off₂ cidx : Array ℕ) (P : List (ℕ × ℕ × ℕ))
    (f : Array ℕ) :
    RunsWithin X body (Graph.indArrProg N pos off₁ off₂ cidx P f)
      (indArr N pos off₁ off₂ cidx P f) (3 * f.size + 43 * P.length + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun p _ => RunsWithin.imgProg N pos off₁ off₂ cidx f p)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_append, List.length_map,
      Array.length_toList]
    omega

theorem RunsWithin.indProg {N : ℕ} (pos off₁ off₂ cidx : Array ℕ) (P : List (ℕ × ℕ × ℕ))
    {g : PermData} (hg : g.Valid N) :
    RunsWithin X body (Graph.indProg N pos off₁ off₂ cidx P g)
      (indDataB N pos off₁ off₂ cidx P g) (6 * N + 86 * P.length + 13) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.indArrProg N pos off₁ off₂ cidx P g.1)
    run_step (RunsWithin.indArrProg N pos off₁ off₂ cidx P g.2)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, hg.size_fwd, hg.size_inv]
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_levListProg {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ)
    (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (levListProg N₁ l₁ r₁) (levListProg N₂ l₂ r₂) := by
  unfold levListProg
  refine .bind (.prim _ (.cons hN .nil)) fun rN₁ rN₂ =>
    wf_filterList (List.Mem.head _) fun Γ' hΓ u₁ u₂ hu =>
      wf_levEqProg (hΓ (by simp [hl])) (hΓ (by simp [hr])) hu

theorem wf_posProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {L₁ : var₁ (.list .nat)}
    {L₂ : var₂ (.list .nat)} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hL : ⟨.list .nat, L₁, L₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (posProg N₁ L₁) (posProg N₂ L₂) := by
  unfold posProg posStepProg
  prog_wf

theorem wf_multsProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (multsProg k₁ m₁) (multsProg k₂ m₂) := by
  unfold multsProg multStepProg
  prog_wf

theorem wf_mulProg {a₁ b₁ : var₁ .nat} {a₂ b₂ : var₂ .nat} (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ)
    (hb : ⟨.nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (mulProg a₁ b₁) (mulProg a₂ b₂) := by
  unfold mulProg
  prog_wf

theorem wf_cidxProg {M₁ : var₁ .nat} {M₂ : var₂ .nat} {o₁ q₁ : var₁ (.array .nat)}
    {o₂ q₂ : var₂ (.array .nat)} {S₁ : var₁ (.list Ty.trip)} {S₂ : var₂ (.list Ty.trip)}
    (hM : ⟨.nat, M₁, M₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ) (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ)
    (hS : ⟨.list Ty.trip, S₁, S₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (cidxProg M₁ o₁ q₁ S₁) (cidxProg M₂ o₂ q₂ S₂) := by
  unfold cidxProg cidxStepProg keyProg
  prog_wf

theorem wf_indProg {N₁ : var₁ .nat} {N₂ : var₂ .nat} {p₁ o₁ q₁ c₁ : var₁ (.array .nat)}
    {p₂ o₂ q₂ c₂ : var₂ (.array .nat)} {P₁ : var₁ (.list Ty.trip)} {P₂ : var₂ (.list Ty.trip)}
    {g₁ : var₁ Ty.perm} {g₂ : var₂ Ty.perm} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hp : ⟨.array .nat, p₁, p₂⟩ ∈ Γ) (ho : ⟨.array .nat, o₁, o₂⟩ ∈ Γ)
    (hq : ⟨.array .nat, q₁, q₂⟩ ∈ Γ) (hc : ⟨.array .nat, c₁, c₂⟩ ∈ Γ)
    (hP : ⟨.list Ty.trip, P₁, P₂⟩ ∈ Γ) (hg : ⟨Ty.perm, g₁, g₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (indProg N₁ p₁ o₁ q₁ c₁ P₁ g₁)
      (indProg N₂ p₂ o₂ q₂ c₂ P₂ g₂) := by
  unfold indProg indArrProg imgProg canonProg sort2Prog keyProg mapList
  prog_wf

end Wf

end GraphIso.Graph
