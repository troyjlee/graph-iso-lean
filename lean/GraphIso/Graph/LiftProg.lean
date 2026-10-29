module

public import GraphIso.Graph.IndProg

/-!
# Programs of one layer step: lifts and twin swaps

* `liftB G lev r New f w`: the canonical lift of the permutation with forward array `f` at the
  point `w`, computed with lists: the image class of `w` is filtered from the points `New` of
  level `r + 1`, and `w`'s rank in its own class picks the image. It equals `liftFun`
  (`liftB_eq`), so the computed lift data are `liftData` (`liftDataB_eq`).
* `swapData N w w'`: the transposition; `twinGens`: the transpositions of distinct points of
  level `r + 1` with the same neighbourhood, by two nested folds.
* **`nextGens_spec`**: if `hs` generates `HR r`, the lifts of `hs` and the twin transpositions
  are valid and generate `A_{r+1}`.
* The programs `idxOfProg`, `getDProg`, `liftProg`, `swapProg` and `twinsProg` compute these
  models within explicit costs.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Cost Programs Sims

/-! ### List folds -/

/-- One step of the index search. -/
def idxStep (v : ℕ) (s : ℕ × Bool) (x : ℕ) : ℕ × Bool :=
  if s.2 then s else if x == v then (s.1, true) else (s.1 + 1, s.2)

theorem idxStep_found (v : ℕ) : ∀ (l : List ℕ) (i : ℕ), l.foldl (idxStep v) (i, true) = (i, true)
  | [], _ => rfl
  | _ :: l, i => by simp only [List.foldl_cons, idxStep, ↓reduceIte]; exact idxStep_found v l i

theorem idxStep_fold (v : ℕ) : ∀ (l : List ℕ) (i : ℕ),
    (l.foldl (idxStep v) (i, false)).1 = i + l.idxOf v
  | [], i => by simp
  | x :: l, i => by
    rw [List.foldl_cons, List.idxOf_cons]
    by_cases h : x = v
    · subst h
      simp [idxStep, idxStep_found]
    · have : (x == v) = false := by simpa using h
      simp only [idxStep, this, Bool.false_eq_true, ↓reduceIte]
      rw [idxStep_fold v l (i + 1)]
      omega

/-- One step of the indexed read. -/
def getStep (s : ℕ × Option ℕ) (x : ℕ) : ℕ × Option ℕ :=
  match s.2 with
  | some _ => s
  | none => if s.1 == 0 then (s.1, some x) else (s.1 - 1, none)

theorem getStep_found : ∀ (l : List ℕ) (s : ℕ × Option ℕ) (y : ℕ), s.2 = some y →
    l.foldl getStep s = s
  | [], _, _, _ => rfl
  | _ :: l, s, y, h => by
    rw [List.foldl_cons, show getStep s _ = s by simp [getStep, h]]
    exact getStep_found l s y h

theorem getStep_fold : ∀ (l : List ℕ) (k : ℕ), (l.foldl getStep (k, none)).2 = l[k]?
  | [], _ => rfl
  | x :: l, k => by
    rw [List.foldl_cons]
    rcases k with _ | k
    · rw [show getStep (0, none) x = (0, some x) by simp [getStep],
        getStep_found l (0, some x) x rfl]
      rfl
    · rw [show getStep (k + 1, none) x = (k, none) by simp [getStep], getStep_fold l k]
      rfl

/-! ### The lift, computed with lists -/

/-- The image of a list under an array. -/
def mapGet (f : Array ℕ) (l : List ℕ) : List ℕ := l.map (get f)

/-- The points of `New` whose neighbours of level `r` are the elements of `T`. -/
def classB (G : GraphData) (lev : Array ℕ) (r : ℕ) (New T : List ℕ) : List ℕ :=
  New.filter fun u => seteqB (nbL G lev r u) T

/-- The canonical lift at `w`, computed with lists. -/
def liftB (G : GraphData) (lev : Array ℕ) (r : ℕ) (New : List ℕ) (f : Array ℕ) (w : ℕ) : ℕ :=
  if get lev w == r + 1 then
    (classB G lev r New (mapGet f (nbL G lev r w))).getD
      ((classB G lev r New (nbL G lev r w)).idxOf w) w
  else get f w

/-- The lift data, computed with lists. -/
def liftDataB (G : GraphData) (lev : Array ℕ) (N r : ℕ) (New : List ℕ) (d : PermData) :
    PermData :=
  (((List.range N).map (liftB G lev r New d.1)).toArray,
    ((List.range N).map (liftB G lev r New d.2)).toArray)

section LiftModel

variable {Δ N : ℕ} {G : GraphData} {lev : Array ℕ}

theorem classB_eq {r : ℕ} (T : List ℕ) :
    classB G lev r (levList lev N (r + 1)) T = cls G lev N r T.toFinset := by
  unfold classB levList cls
  rw [List.filter_filter]
  refine List.filter_congr fun w _ => ?_
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, seteqB_iff, toFinset_nbL]
  tauto

theorem liftB_eq (hG : G.ValidD Δ N) {r : ℕ} {f : Array ℕ} {π : Perm (Fin N)}
    (hf : ∀ v < N, get f v = act π v) {w : ℕ} (hw : w < N) :
    liftB G lev r (levList lev N (r + 1)) f w = liftFun N G lev r π w := by
  unfold liftB liftFun rankIn
  by_cases hl : get lev w = r + 1
  · have himg : (mapGet f (nbL G lev r w)).toFinset = (nb G lev r w).image (act π) := by
      ext u
      simp only [mapGet, List.mem_toFinset, List.mem_map, Finset.mem_image, ← toFinset_nbL]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, (hf a (hG.lt w a (List.mem_filter.1 ha).1)).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, ha, hf a (hG.lt w a (List.mem_filter.1 ha).1)⟩
    simp only [hl, beq_self_eq_true, ↓reduceIte, and_self, hw, classB_eq, himg, toFinset_nbL]
  · have : (get lev w == r + 1) = false := by simpa using hl
    simp only [this, Bool.false_eq_true, ↓reduceIte, hl, and_false]
    exact hf w hw

/-- The lift data of `d`. -/
def liftData (N : ℕ) (G : GraphData) (lev : Array ℕ) (r : ℕ) (d : PermData) : PermData :=
  PermData.ofFun N (liftFun N G lev r (PermData.denote N d))
    (liftFun N G lev r (PermData.denote N d)⁻¹)

theorem liftDataB_eq (hG : G.ValidD Δ N) {r : ℕ} {d : PermData} (hd : d.Valid N) :
    liftDataB G lev N r (levList lev N (r + 1)) d = liftData N G lev r d := by
  unfold liftDataB liftData PermData.ofFun
  congr 2
  · refine List.map_congr_left fun w hw => ?_
    exact liftB_eq hG (fun v hv => get_fst_of_valid hd hv) (List.mem_range.1 hw)
  · refine List.map_congr_left fun w hw => ?_
    exact liftB_eq hG (fun v hv => get_snd_of_valid hd hv) (List.mem_range.1 hw)

end LiftModel

/-! ### Transpositions and twins -/

/-- The transposition of `w` and `w'`, as a function. -/
def swapF (w w' v : ℕ) : ℕ := if v == w then w' else if v == w' then w else v

/-- The data of the transposition of `w` and `w'`. -/
def swapData (N w w' : ℕ) : PermData := PermData.ofFun N (swapF w w') (swapF w w')

theorem swapF_lt {N w w' v : ℕ} (hw : w < N) (hw' : w' < N) (hv : v < N) :
    swapF w w' v < N := by
  unfold swapF
  split
  · exact hw'
  · split
    · exact hw
    · exact hv

theorem swapF_swapF (w w' v : ℕ) : swapF w w' (swapF w w' v) = v := by
  unfold swapF
  by_cases h₁ : v = w <;> by_cases h₂ : v = w' <;> by_cases h₃ : w = w' <;> simp_all

theorem invPair_swapF {N w w' : ℕ} (hw : w < N) (hw' : w' < N) :
    InvPair N (swapF w w') (swapF w w') :=
  ⟨fun _ hv => swapF_lt hw hw' hv, fun _ hv => swapF_lt hw hw' hv,
    fun v _ => swapF_swapF w w' v, fun v _ => swapF_swapF w w' v⟩

theorem valid_swapData {N w w' : ℕ} (hw : w < N) (hw' : w' < N) : (swapData N w w').Valid N :=
  valid_ofFun (invPair_swapF hw hw')

theorem denote_swapData {N w w' : ℕ} (hw : w < N) (hw' : w' < N) :
    PermData.denote N (swapData N w w') = swap ⟨w, hw⟩ ⟨w', hw'⟩ :=
  denote_ofFun_eq (invPair_swapF hw hw') fun v _ => by
    rw [act_swap_eq]
    simp only [swapF, beq_iff_eq]

/-- One step of the inner twin fold. -/
def twinInner (G : GraphData) (lev : Array ℕ) (N r w : ℕ) (acc : GensData) (w' : ℕ) :
    GensData :=
  if w == w' then acc
  else if seteqB (nbL G lev r w) (nbL G lev r w') then swapData N w w' :: acc else acc

/-- The twin transpositions of the points `New` of level `r + 1`. -/
def twinGens (G : GraphData) (lev : Array ℕ) (N r : ℕ) (New : List ℕ) : GensData :=
  New.foldl (fun acc w => New.foldl (twinInner G lev N r w) acc) []

theorem mem_twinInner_fold {G : GraphData} {lev : Array ℕ} {N r w : ℕ} {x : PermData} :
    ∀ (l : List ℕ) (acc : GensData), x ∈ l.foldl (twinInner G lev N r w) acc ↔
      x ∈ acc ∨ ∃ w' ∈ l, w ≠ w' ∧ seteqB (nbL G lev r w) (nbL G lev r w') = true ∧
        x = swapData N w w'
  | [], acc => by simp
  | w' :: l, acc => by
    rw [List.foldl_cons, mem_twinInner_fold l]
    unfold twinInner
    by_cases h₁ : w = w'
    · subst h₁
      simp
    · have hb : (w == w') = false := by simpa using h₁
      by_cases h₂ : seteqB (nbL G lev r w) (nbL G lev r w') = true
      · simp only [hb, h₂, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.mem_cons,
          exists_eq_or_imp, ne_eq, h₁, not_false_eq_true, true_and]
        tauto
      · simp only [hb, h₂, Bool.false_eq_true, ↓reduceIte, List.mem_cons, exists_eq_or_imp,
          false_and, and_false, false_or]

theorem mem_twinGens {G : GraphData} {lev : Array ℕ} {N r : ℕ} {New : List ℕ} {x : PermData} :
    x ∈ twinGens G lev N r New ↔ ∃ w ∈ New, ∃ w' ∈ New, w ≠ w' ∧
      seteqB (nbL G lev r w) (nbL G lev r w') = true ∧ x = swapData N w w' := by
  have key : ∀ (l : List ℕ) (acc : GensData),
      x ∈ l.foldl (fun acc w => New.foldl (twinInner G lev N r w) acc) acc ↔
        x ∈ acc ∨ ∃ w ∈ l, ∃ w' ∈ New, w ≠ w' ∧
          seteqB (nbL G lev r w) (nbL G lev r w') = true ∧ x = swapData N w w' := by
    intro l
    induction l with
    | nil => simp
    | cons w l ih =>
      intro acc
      rw [List.foldl_cons, ih, mem_twinInner_fold]
      simp only [List.mem_cons, exists_eq_or_imp]
      rw [or_assoc]
  rw [twinGens, key]
  simp

theorem length_twinGens_le {G : GraphData} {lev : Array ℕ} {N r : ℕ} (New : List ℕ) :
    (twinGens G lev N r New).length ≤ New.length * New.length := by
  have hin : ∀ (w : ℕ) (l : List ℕ) (acc : GensData),
      (l.foldl (twinInner G lev N r w) acc).length ≤ acc.length + l.length := by
    intro w l
    induction l with
    | nil => simp
    | cons w' l ih =>
      intro acc
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      simp only [List.length_cons]
      unfold twinInner
      split
      · omega
      · split
        · simp only [List.length_cons]
          omega
        · omega
  have hout : ∀ (l : List ℕ) (acc : GensData),
      (l.foldl (fun acc w => New.foldl (twinInner G lev N r w) acc) acc).length ≤
        acc.length + l.length * New.length := by
    intro l
    induction l with
    | nil => simp
    | cons w l ih =>
      intro acc
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      have := hin w New acc
      simp only [List.length_cons, Nat.succ_mul]
      omega
  have := hout New []
  simpa [twinGens] using this

/-! ### The next generators -/

section Next

variable {Δ N : ℕ} {G : GraphData} {roots : List ℕ} {lev : Array ℕ}
  (hZ : LayeredD Δ N G roots lev)

include hZ in
theorem liftData_spec {r : ℕ} {d : PermData} (hh : PermData.denote N d ∈ HR N G lev Δ r) :
    (liftData N G lev r d).Valid N ∧ PermData.denote N (liftData N G lev r d) = liftPerm hZ hh := by
  have hp : InvPair N (liftFun N G lev r (PermData.denote N d))
      (liftFun N G lev r (PermData.denote N d)⁻¹) :=
    ⟨fun w hw => liftFun_lt hZ hh hw, fun w hw => liftFun_lt hZ (inv_mem hh) hw,
      fun w hw => by rw [liftFun_comp hZ (inv_mem hh) hh hw, inv_mul_cancel, liftFun_one],
      fun w hw => by rw [liftFun_comp hZ hh (inv_mem hh) hw, mul_inv_cancel, liftFun_one]⟩
  exact ⟨valid_ofFun hp, denote_ofFun_eq hp fun w _ => act_liftPerm hZ hh w⟩

theorem denoteSet_twinGens {r : ℕ} :
    GensData.denoteSet N (twinGens G lev N r (levList lev N (r + 1))) = twinSwaps N G lev r := by
  ext σ
  simp only [GensData.denoteSet, Set.mem_ofPred_eq, mem_twinGens, twinSwaps]
  constructor
  · rintro ⟨_, ⟨w, hw, w', hw', hne, hs, rfl⟩, rfl⟩
    obtain ⟨hwN, hlw⟩ := mem_levList.1 hw
    obtain ⟨hw'N, hlw'⟩ := mem_levList.1 hw'
    refine ⟨⟨w, hwN⟩, ⟨w', hw'N⟩, hlw, hlw', fun e => hne (congrArg Fin.val e), ?_,
      denote_swapData hwN hw'N⟩
    rw [← toFinset_nbL, ← toFinset_nbL]
    exact seteqB_iff.1 hs
  · rintro ⟨w, w', hlw, hlw', hne, hnb, rfl⟩
    refine ⟨swapData N w w', ⟨w, mem_levList.2 ⟨w.2, hlw⟩, w', mem_levList.2 ⟨w'.2, hlw'⟩,
      fun e => hne (Fin.ext e), ?_, rfl⟩, denote_swapData w.2 w'.2⟩
    rw [seteqB_iff, toFinset_nbL, toFinset_nbL]
    exact hnb

theorem allValid_twinGens {r : ℕ} :
    GensData.AllValid N (twinGens G lev N r (levList lev N (r + 1))) := by
  intro x hx
  obtain ⟨w, hw, w', hw', -, -, rfl⟩ := mem_twinGens.1 hx
  exact valid_swapData (mem_levList.1 hw).1 (mem_levList.1 hw').1

include hZ in
/-- **The next generators**: if `hs` generates `HR r`, the lifts of `hs` and the twin
transpositions are valid and generate `A_{r+1}`. -/
theorem nextGens_spec {r : ℕ} {hs : GensData} (hhs : GensData.AllValid N hs)
    (hden : GensData.denote N hs = HR N G lev Δ r) :
    GensData.AllValid N (hs.map (liftDataB G lev N r (levList lev N (r + 1))) ++
        twinGens G lev N r (levList lev N (r + 1))) ∧
      GensData.denote N (hs.map (liftDataB G lev N r (levList lev N (r + 1))) ++
        twinGens G lev N r (levList lev N (r + 1))) = AutR N G lev (r + 1) := by
  have hmem : ∀ d ∈ hs, PermData.denote N d ∈ HR N G lev Δ r := fun d hd =>
    hden ▸ GensData.mem_denote_of_mem hd
  have hlift : ∀ d ∈ hs, liftDataB G lev N r (levList lev N (r + 1)) d = liftData N G lev r d :=
    fun d hd => liftDataB_eq hZ.valid (hhs d hd)
  refine ⟨GensData.AllValid.append (fun l hl => ?_) allValid_twinGens, ?_⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hl
    rw [hlift d hd]
    exact (liftData_spec hZ (hmem d hd)).1
  · have hls : GensData.denoteSet N (hs.map (liftDataB G lev N r (levList lev N (r + 1)))) =
        liftSet hZ r (GensData.denoteSet N hs) := by
      ext σ
      simp only [GensData.denoteSet, List.mem_map, Set.mem_ofPred_eq, liftSet]
      constructor
      · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
        refine ⟨_, ⟨d, hd, rfl⟩, hmem d hd, ?_⟩
        rw [hlift d hd, (liftData_spec hZ (hmem d hd)).2]
      · rintro ⟨_, ⟨d, hd, rfl⟩, hh, rfl⟩
        exact ⟨_, ⟨d, hd, rfl⟩, by rw [hlift d hd, (liftData_spec hZ hh).2]⟩
    rw [GensData.denote, GensData.denoteSet_append, hls, denoteSet_twinGens]
    exact autR_succ_eq hZ hden

end Next

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One step of the index search. -/
def idxStepProg (v : var .nat) (s : var (.prod .nat .bool)) (x : var .nat) :
    Prog S rec var (.prod .nat .bool) :=
  .bind (.op1 .snd s) fun found => .ite found (.ret s)
    (.bind (.op2 .natEq x v) fun e => .bind (.op1 .fst s) fun i =>
      .ite e (.bind (.op0 (.boolLit true)) fun t => .op2 .pair i t)
        (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' =>
          .op2 .pair i' found))

/-- The index of `v` in `l`. -/
def idxOfProg (l : var (.list .nat)) (v : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.boolLit false)) fun f =>
  .bind (.op2 .pair z f) fun s₀ =>
  .bind (.foldList l s₀ fun s x => idxStepProg v s x) fun s => .op1 .fst s

/-- One step of the indexed read. -/
def getStepProg (s : var (.prod .nat (.option .nat))) (x : var .nat) :
    Prog S rec var (.prod .nat (.option .nat)) :=
  .bind (.op1 .fst s) fun j => .bind (.op1 .snd s) fun o =>
  .caseOption o
    (.bind (.op0 (.natLit 0)) fun z => .bind (.op2 .natEq j z) fun e =>
      .ite e (.bind (.op1 .some x) fun sx => .op2 .pair j sx)
        (.bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub j one) fun j' =>
          .bind (.op0 .none) fun nn => .op2 .pair j' nn))
    fun _ => .ret s

/-- The entry of `l` at `k`, or `d`. -/
def getDProg (l : var (.list .nat)) (k d : var .nat) : Prog S rec var .nat :=
  .bind (.op0 .none) fun nn => .bind (.op2 .pair k nn) fun s₀ =>
  .bind (.foldList l s₀ fun s x => getStepProg s x) fun s =>
  .bind (.op1 .snd s) fun o => .caseOption o (.ret d) fun x => .ret x

/-- The image of a list under an array. -/
def mapGetProg (f : var (.array .nat)) (l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList l fun u => .op2 .arrayGet f u

/-- The points of `New` whose neighbours of level `r` are the elements of `T`. -/
def classProg (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat)
    (New T : var (.list .nat)) : Prog S rec var (.list .nat) :=
  Luks.filterList New fun u => nbEqProg G lev r T u

/-- The canonical lift at `w`. -/
def liftBProg (G : var Ty.graph) (lev : var (.array .nat)) (r : var .nat)
    (New : var (.list .nat)) (f : var (.array .nat)) (w : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .arrayGet lev w) fun lw => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .add r one) fun r1 => .bind (.op2 .natEq lw r1) fun isNew =>
  .ite isNew
    (.bind (nbLProg G lev r w) fun nw => .bind (mapGetProg f nw) fun T' =>
      .bind (classProg G lev r New T') fun c' => .bind (classProg G lev r New nw) fun c =>
      .bind (idxOfProg c w) fun k => getDProg c' k w)
    (.op2 .arrayGet f w)

/-- The lifted array of `f`. -/
def liftArrProg (G : var Ty.graph) (lev : var (.array .nat)) (N r : var .nat)
    (New : var (.list .nat)) (f : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range N) fun rN => .bind (mapList rN fun w => liftBProg G lev r New f w)
    fun l => .op1 .arrayOfList l

/-- The lift data. -/
def liftProg (G : var Ty.graph) (lev : var (.array .nat)) (N r : var .nat)
    (New : var (.list .nat)) (d : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst d) fun d₁ => .bind (.op1 .snd d) fun d₂ =>
  .bind (liftArrProg G lev N r New d₁) fun a₁ => .bind (liftArrProg G lev N r New d₂)
    fun a₂ => .op2 .pair a₁ a₂

/-- The transposition of `w` and `w'` at `v`. -/
def swapFProg (w w' v : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .natEq v w) fun e₁ =>
  .ite e₁ (.ret w') (.bind (.op2 .natEq v w') fun e₂ => .ite e₂ (.ret w) (.ret v))

/-- The data of the transposition of `w` and `w'`. -/
def swapProg (N w w' : var .nat) : Prog S rec var Ty.perm :=
  .bind (.op1 .range N) fun rN => .bind (mapList rN fun v => swapFProg w w' v) fun l =>
  .bind (.op1 .arrayOfList l) fun a => .op2 .pair a a

/-- One step of the inner twin fold; `nw` lists the neighbours of `w`. -/
def twinInnerProg (G : var Ty.graph) (lev : var (.array .nat)) (N r w : var .nat)
    (nw : var (.list .nat)) (acc : var Ty.gens) (w' : var .nat) : Prog S rec var Ty.gens :=
  .bind (.op2 .natEq w w') fun e => .ite e (.ret acc)
    (.bind (nbLProg G lev r w') fun nw' => .bind (seteqProg nw nw') fun b =>
      .ite b (.bind (swapProg N w w') fun sd => .op2 .cons sd acc) (.ret acc))

/-- The twin transpositions. -/
def twinsProg (G : var Ty.graph) (lev : var (.array .nat)) (N r : var .nat)
    (New : var (.list .nat)) : Prog S rec var Ty.gens :=
  .bind (.op0 .nil) fun nl =>
  .foldList New nl fun acc w => .bind (nbLProg G lev r w) fun nw =>
    .foldList New acc fun acc w' => twinInnerProg G lev N r w nw acc w'

end Prog

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.idxStepProg (v : ℕ) (s : ℕ × Bool) (x : ℕ) :
    RunsWithin X body (Graph.idxStepProg v s x) (idxStep v s x) 8 := by
  rcases s with ⟨i, found⟩
  cases found
  · by_cases h : x = v
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by simp [Prim.eval, h]) _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, idxStep, h]) le_rfl
      case hc =>
        simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, h]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, idxStep, h]) le_rfl
      case hc =>
        simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos rfl _
      exact (RunsWithin.ret _).of_eq (by simp [idxStep])
    case hc =>
      simp [Prim.cost]

theorem RunsWithin.idxOfProg (l : List ℕ) (v : ℕ) :
    RunsWithin X body (Graph.idxOfProg l v) (l.idxOf v) (9 * l.length + 4) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .bool) (cf := fun _ => 8) (F := idxStep v) l (0, false)
    fun s x _ => RunsWithin.idxStepProg v s x
  rw [sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le (by simp [Prim.eval, idxStep_fold]) le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.getStepProg (s : ℕ × Option ℕ) (x : ℕ) :
    RunsWithin X body (Graph.getStepProg s x) (getStep s x) 10 := by
  rcases s with ⟨j, _ | y⟩
  · by_cases h : j = 0
    · subst h
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOption_eq_none rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by simp [Prim.eval]) _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, getStep]) le_rfl
      case hc =>
        simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseOption_eq_none rfl _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, h]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, getStep, h]) le_rfl
      case hc =>
        simp [Prim.cost]
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOption_eq_some rfl _
      exact (RunsWithin.ret _).of_eq (by simp [getStep])
    case hc =>
      simp [Prim.cost]

theorem RunsWithin.getDProg (l : List ℕ) (k d : ℕ) :
    RunsWithin X body (Graph.getDProg l k d) (l.getD k d) (11 * l.length + 4) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.option .nat)) (cf := fun _ => 10) (F := getStep) l (k, none)
    fun s x _ => RunsWithin.getStepProg s x
  rw [sum_map_const] at hfold
  have hv := getStep_fold l k
  rcases ho : (l.foldl getStep (k, none)) with ⟨j, o⟩
  rw [ho] at hfold hv
  simp only at hv
  rcases o with _ | x
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOption_eq_none rfl _
      exact (RunsWithin.ret _).of_eq (by rw [List.getD_eq_getElem?_getD, ← hv]; rfl)
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hfold
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseOption_eq_some rfl _
      exact (RunsWithin.ret _).of_eq (by rw [List.getD_eq_getElem?_getD, ← hv]; rfl)
    case hc =>
      simp only [Prim.cost]
      omega

theorem RunsWithin.mapGetProg (f : Array ℕ) (l : List ℕ) :
    RunsWithin X body (Graph.mapGetProg f l) (mapGet f l) (4 * l.length + 2) :=
  (RunsWithin.mapList_le (c := 1) fun u _ => RunsWithin.prim_le rfl le_rfl).mono (by omega)

theorem RunsWithin.classProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r : ℕ) (New : List ℕ) {T : List ℕ} (hT : T.length ≤ 3) :
    RunsWithin X body (Graph.classProg G lev r New T) (classB G lev r New T)
      (100 * New.length + 2) :=
  (Luks.RunsWithin.filterList (a' := .nat) fun u _ =>
    RunsWithin.nbEqProg hG3 lev r hT u).mono (by omega)

theorem length_classB_le (G : GraphData) (lev : Array ℕ) (r : ℕ) (New T : List ℕ) :
    (classB G lev r New T).length ≤ New.length :=
  List.length_filter_le _ _

theorem RunsWithin.liftBProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (r : ℕ) (New : List ℕ) (f : Array ℕ) (w : ℕ) :
    RunsWithin X body (Graph.liftBProg G lev r New f w) (liftB G lev r New f w)
      (220 * New.length + 60) := by
  have h₁ := hG3 w
  have h₂ := length_nbL_le G lev r w
  by_cases hl : get lev w = r + 1
  · have hT : (mapGet f (nbL G lev r w)).length ≤ 3 := by
      simp only [mapGet, List.length_map]
      omega
    have c₁ := length_classB_le G lev r New (mapGet f (nbL G lev r w))
    have c₂ := length_classB_le G lev r New (nbL G lev r w)
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (get lev w == r + 1) = true by simp [hl]) _
      run_step (RunsWithin.nbLProg G lev r w)
      run_step (RunsWithin.mapGetProg f _)
      run_step (RunsWithin.classProg hG3 lev r New hT)
      run_step (RunsWithin.classProg hG3 lev r New (by omega))
      run_step (RunsWithin.idxOfProg _ w)
      exact (RunsWithin.getDProg _ _ w).of_eq (by simp [liftB, hl])
    case hc =>
      simp only [Prim.cost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (get lev w == r + 1) = false by simpa using hl) _
      exact RunsWithin.prim_le (show get f w = _ by simp [liftB, hl]) le_rfl
    case hc =>
      simp only [Prim.cost]
      omega

theorem RunsWithin.liftArrProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (N r : ℕ) (New : List ℕ) (f : Array ℕ) :
    RunsWithin X body (Graph.liftArrProg G lev N r New f)
      ((List.range N).map (liftB G lev r New f)).toArray
      (N * (220 * New.length + 63) + 2 * N + 4) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun w _ => RunsWithin.liftBProg hG3 lev r New f w)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range]
    ring_nf
    omega

theorem RunsWithin.liftProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (N r : ℕ) (New : List ℕ) (d : PermData) :
    RunsWithin X body (Graph.liftProg G lev N r New d) (liftDataB G lev N r New d)
      (2 * (N * (220 * New.length + 63) + 2 * N + 4) + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.liftArrProg hG3 lev N r New d.1)
    run_step (RunsWithin.liftArrProg hG3 lev N r New d.2)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.swapFProg (w w' v : ℕ) :
    RunsWithin X body (Graph.swapFProg w w' v) (swapF w w' v) 5 := by
  by_cases h₁ : v = w
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (by simp [Prim.eval, h₁]) _
      exact (RunsWithin.ret _).of_eq (by simp [swapF, h₁])
    case hc =>
      simp [Prim.cost]
  · by_cases h₂ : v = w'
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, h₁]) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (by simp [Prim.eval, h₂]) _
        exact (RunsWithin.ret _).of_eq (by subst h₂; simp [swapF, h₁])
      case hc =>
        simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, h₁]) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, h₂]) _
        exact (RunsWithin.ret _).of_eq (by simp [swapF, h₁, h₂])
      case hc =>
        simp [Prim.cost]

theorem RunsWithin.swapProg (N w w' : ℕ) :
    RunsWithin X body (Graph.swapProg N w w') (swapData N w w') (10 * N + 5) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le fun v _ => RunsWithin.swapFProg w w' v)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_map, List.length_range]
    omega

theorem RunsWithin.twinInnerProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (N r w : ℕ) (acc : GensData) (w' : ℕ) :
    RunsWithin X body (Graph.twinInnerProg G lev N r w (nbL G lev r w) acc w')
      (twinInner G lev N r w acc w') (10 * N + 106) := by
  have h₁ := hG3 w
  have h₂ := length_nbL_le G lev r w
  have h₃ := hG3 w'
  have h₄ := length_nbL_le G lev r w'
  have hse : (nbL G lev r w).length * (3 * (nbL G lev r w').length + 3) +
      (nbL G lev r w').length * (3 * (nbL G lev r w).length + 3) + 3 ≤ 75 := by nlinarith
  by_cases he : w = w'
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (by simp [Prim.eval, he]) _
      exact (RunsWithin.ret _).of_eq (by simp [twinInner, he])
    case hc =>
      simp only [Prim.cost]
      omega
  · cases hb : seteqB (nbL G lev r w) (nbL G lev r w')
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, he]) _
        run_step (RunsWithin.nbLProg G lev r w')
        run_step (RunsWithin.seteqProg _ _)
        rw [hb]
        run_with RunsWithin.ite_neg rfl _
        exact (RunsWithin.ret _).of_eq (by simp [twinInner, he, hb])
      case hc =>
        simp only [Prim.cost]
        omega
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (by simp [Prim.eval, he]) _
        run_step (RunsWithin.nbLProg G lev r w')
        run_step (RunsWithin.seteqProg _ _)
        rw [hb]
        run_with RunsWithin.ite_pos rfl _
        run_step (RunsWithin.swapProg N w w')
        exact RunsWithin.prim_le (by simp [Prim.eval, twinInner, he, hb]) le_rfl
      case hc =>
        simp only [Prim.cost]
        omega

theorem RunsWithin.twinsProg {G : GraphData} (hG3 : ∀ u, (nbrs G u).length ≤ 3)
    (lev : Array ℕ) (N r : ℕ) (New : List ℕ) :
    RunsWithin X body (Graph.twinsProg G lev N r New) (twinGens G lev N r New)
      (New.length * (New.length * (10 * N + 107) + 22) + 1) := by
  have hin : ∀ (w : ℕ) (acc : GensData), RunsWithin X body
      (.bind (Graph.nbLProg G lev r w) fun nw => .foldList (a := .nat) New acc fun acc w' =>
        Graph.twinInnerProg G lev N r w nw acc w')
      (New.foldl (twinInner G lev N r w) acc) (New.length * (10 * N + 107) + 21) := by
    intro w acc
    have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := Ty.gens)
      (cf := fun _ => 10 * N + 106) (F := twinInner G lev N r w) New acc
      fun acc w' _ => RunsWithin.twinInnerProg hG3 lev N r w acc w'
    rw [sum_map_const] at hfold
    have h₁ := hG3 w
    refine RunsWithin.bind_le (RunsWithin.nbLProg G lev r w) hfold ?_
    ring_nf
    omega
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := Ty.gens)
    (cf := fun _ => New.length * (10 * N + 107) + 21)
    (F := fun acc w => New.foldl (twinInner G lev N r w) acc) New []
    fun acc w _ => hin w acc
  rw [sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost]
    ring_nf
    omega

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_idxOfProg {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)} {v₁ : var₁ .nat}
    {v₂ : var₂ .nat} (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (idxOfProg l₁ v₁) (idxOfProg l₂ v₂) := by
  unfold idxOfProg idxStepProg
  prog_wf

theorem wf_getDProg {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)} {k₁ d₁ : var₁ .nat}
    {k₂ d₂ : var₂ .nat} (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hd : ⟨.nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (getDProg l₁ k₁ d₁) (getDProg l₂ k₂ d₂) := by
  unfold getDProg getStepProg
  prog_wf

theorem wf_classProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {r₁ : var₁ .nat} {r₂ : var₂ .nat}
    {m₁ T₁ : var₁ (.list .nat)} {m₂ T₂ : var₂ (.list .nat)}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hm : ⟨.list .nat, m₁, m₂⟩ ∈ Γ) (hT : ⟨.list .nat, T₁, T₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (classProg G₁ l₁ r₁ m₁ T₁) (classProg G₂ l₂ r₂ m₂ T₂) :=
  wf_filterList hm fun _ hΓ _ _ hu => wf_nbEqProg (hΓ hG) (hΓ hl) (hΓ hr) (hΓ hT) hu

theorem wf_liftBProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ f₁ : var₁ (.array .nat)}
    {l₂ f₂ : var₂ (.array .nat)} {r₁ w₁ : var₁ .nat} {r₂ w₂ : var₂ .nat}
    {m₁ : var₁ (.list .nat)} {m₂ : var₂ (.list .nat)}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ)
    (hm : ⟨.list .nat, m₁, m₂⟩ ∈ Γ) (hf : ⟨.array .nat, f₁, f₂⟩ ∈ Γ)
    (hw : ⟨.nat, w₁, w₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (liftBProg G₁ l₁ r₁ m₁ f₁ w₁)
      (liftBProg G₂ l₂ r₂ m₂ f₂ w₂) := by
  unfold liftBProg
  refine .bind (.prim _ (.cons hl (.cons hw .nil))) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp [hr]) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))) fun _ _ =>
    .ite (List.Mem.head _) ?_ (.prim _ (.cons (by simp [hf]) (.cons (by simp [hw]) .nil)))
  refine .bind (wf_nbLProg (by simp [hG]) (by simp [hl]) (by simp [hr]) (by simp [hw]))
    fun _ _ => .bind (by unfold mapGetProg mapList; prog_wf) fun _ _ =>
    .bind (wf_classProg (by simp [hG]) (by simp [hl]) (by simp [hr]) (by simp [hm])
      (List.Mem.head _)) fun _ _ =>
    .bind (wf_classProg (by simp [hG]) (by simp [hl]) (by simp [hr]) (by simp [hm])
      (by simp)) fun _ _ =>
    .bind (wf_idxOfProg (List.Mem.head _) (by simp [hw])) fun _ _ =>
    wf_getDProg (by simp) (List.Mem.head _) (by simp [hw])

theorem wf_liftProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat}
    {m₁ : var₁ (.list .nat)} {m₂ : var₂ (.list .nat)} {d₁ : var₁ Ty.perm} {d₂ : var₂ Ty.perm}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) (hm : ⟨.list .nat, m₁, m₂⟩ ∈ Γ) (hd : ⟨Ty.perm, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (liftProg G₁ l₁ N₁ r₁ m₁ d₁)
      (liftProg G₂ l₂ N₂ r₂ m₂ d₂) := by
  have harr : ∀ (Γ' : WfCtx var₁ var₂), Γ ⊆ Γ' → ∀ f₁ f₂, ⟨.array .nat, f₁, f₂⟩ ∈ Γ' →
      Prog.Wf (S := S) (rec := rec) r Γ' (liftArrProg G₁ l₁ N₁ r₁ m₁ f₁)
        (liftArrProg G₂ l₂ N₂ r₂ m₂ f₂) := by
    intro Γ' hΓ f₁ f₂ hf
    unfold liftArrProg
    refine .bind (.prim _ (.cons (hΓ hN) .nil)) fun _ _ => .bind (wf_mapList (List.Mem.head _)
      fun Γ'' hΓ' w₁ w₂ hw => ?_) fun _ _ => .prim _ (.cons (List.Mem.head _) .nil)
    have hsub : ∀ e, e ∈ Γ → e ∈ Γ'' := fun e he => hΓ' (by simp [hΓ he])
    exact wf_liftBProg (hsub _ hG) (hsub _ hl) (hsub _ hr) (hsub _ hm)
      (hΓ' (by simp [hf])) hw
  unfold liftProg
  refine .bind (.prim _ (.cons hd .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hd]) .nil))
    fun _ _ => .bind (harr _ (fun e he => by simp [he]) _ _ (by simp)) fun _ _ =>
    .bind (harr _ (fun e he => by simp [he]) _ _ (by simp)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (List.Mem.head _) .nil))

theorem wf_swapProg {N₁ w₁ v₁ : var₁ .nat} {N₂ w₂ v₂ : var₂ .nat} (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hw : ⟨.nat, w₁, w₂⟩ ∈ Γ) (hv : ⟨.nat, v₁, v₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (swapProg N₁ w₁ v₁) (swapProg N₂ w₂ v₂) := by
  unfold swapProg swapFProg mapList
  prog_wf

theorem wf_twinsProg {G₁ : var₁ Ty.graph} {G₂ : var₂ Ty.graph} {l₁ : var₁ (.array .nat)}
    {l₂ : var₂ (.array .nat)} {N₁ r₁ : var₁ .nat} {N₂ r₂ : var₂ .nat}
    {m₁ : var₁ (.list .nat)} {m₂ : var₂ (.list .nat)}
    (hG : ⟨Ty.graph, G₁, G₂⟩ ∈ Γ) (hl : ⟨.array .nat, l₁, l₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ)
    (hr : ⟨.nat, r₁, r₂⟩ ∈ Γ) (hm : ⟨.list .nat, m₁, m₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (twinsProg G₁ l₁ N₁ r₁ m₁) (twinsProg G₂ l₂ N₂ r₂ m₂) := by
  unfold twinsProg
  refine .bind (.prim _ .nil) fun _ _ => .foldList (by simp [hm]) (List.Mem.head _)
    fun _ _ w₁ w₂ => .bind (wf_nbLProg (by simp [hG]) (by simp [hl]) (by simp [hr])
      (by simp)) fun _ _ => .foldList (by simp [hm]) (by simp) fun _ _ w₁' w₂' => ?_
  unfold twinInnerProg
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (List.Mem.head _) (.ret (by simp)) (.bind (wf_nbLProg (by simp [hG]) (by simp [hl])
      (by simp [hr]) (by simp)) fun _ _ => .bind (wf_seteqProg (by simp) (List.Mem.head _))
        fun _ _ => .ite (List.Mem.head _) (.bind (wf_swapProg (by simp [hN]) (by simp)
          (by simp)) fun _ _ => .prim _ (.cons (List.Mem.head _) (.cons (by simp) .nil)))
          (.ret (by simp)))

end Wf

end GraphIso.Graph
