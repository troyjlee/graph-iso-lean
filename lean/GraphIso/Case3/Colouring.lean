module

public import GraphIso.CertProg.CertIso
public import GraphIso.Giant.Aggregate
public import GraphIso.Coherent.TuplesProg
public import GraphIso.Programs.Validate

/-!
# Case 3: the colouring of `k`-tuples by certificate equivalence

Stage 14i, item 1 (`PLAN-14.md` §13). In Case 3 the support `S` of the full group has fewer than
`m/2` points, and the ordered `k`-tuples of `V = Γ ∖ S` are coloured by the equivalence of their
certificates (milestone 13's `SameColour`). The colour names must be consistent across the two
strings `x`, `y`, so that every isomorphism carries the colouring of `x` to that of `y`; they
need not be canonical one string at a time.

* **The model** (`certIso_refl`, `certIso_symm`, `certIso_trans`, `certIso_of_relabel`):
  milestone 13's `CertIso` is an equivalence across strings, and an isomorphism of the strings
  is an equivalence of the certificates of a tuple and of its image. `CertIsoL` restates it for
  lists of base indices, the form `certIsoProg` decides.
* **The colourings on data.** `V` is a duplicate-free list of base indices (`vx` for `x`, `vy`
  for `y`, numbered `Fin m'` in list order); the tuples are milestone 10's digit lists
  `tupList k m'`, in the order of their codes. `colXD`: a tuple with a repetition has colour
  `0`; a tuple `T` without has colour `1 + i` for the first tuple `T_i` (in code order) with
  `CertIso(x, x, T_i, T)`. `colYD`: a tuple `T'` of `y` without repetition has colour `1 + i` for
  the first `T_i` of `x` with `CertIso(x, y, T_i, T')`, and otherwise `1 + m'^k + j` for the
  first `T'_j` of `y` with `CertIso(y, y, T'_j, T')`. The comparisons enter as Boolean functions
  on digit lists, which `RunsWithin.tupleColProg` supplies from `certIsoProg`.
* **`tupleCol_iso`**: if `g` is an isomorphism of `x` onto `y` whose base action carries the
  `i`-th point of `vx` to the `π i`-th point of `vy`, then `colY (π ∘ T) = colX T` for every
  tuple `T` (through milestone 10's `toFun`).
* **`colX_eq_iff`**: two tuples of `x` have the same colour exactly when they are both repeated,
  or both injective with equivalent certificates (milestone 13's `SameColour`).
* **`RunsWithin.tupleColProg`**: the program computes both colourings with `certIsoProg`, at
  most `3 m'^(2k)` comparisons (one scan of the tuples for each tuple of `x`, at most two for
  each tuple of `y`), under the sub-solver hypotheses of stage 14e for the string pairs
  `(x, x)`, `(x, y)` and `(y, y)`. Its value is `(colXD cXX, colYD cXY cYY)` for comparison
  functions that decide certificate equivalence on repetition-free tuples.
-/

@[expose] public section

namespace GraphIso.Case3

open Equiv MulAction Pointwise GraphIso GraphIso.Toolkit GraphIso.Certificates GraphIso.CertProg
  Cost GraphIso.Programs GraphIso.Solver

/-! ### The model: certificate equivalence -/

section Model

variable {Ω Γ : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Γ] [DecidableEq Γ]
variable {G : Subgroup (Perm Ω)} (φ : G →* Perm Γ) {L : Type*}

omit [DecidableEq Ω] [Fintype Γ] in
/-- Certificate equivalence is reflexive. -/
theorem certIso_refl (x : Ω → L) {k : ℕ} (T : Fin k → Γ) : CertIso φ x x T T :=
  ⟨1, fun i => by simp, by simp, fun j _ => by simp⟩

omit [DecidableEq Ω] [Fintype Γ] in
/-- Certificate equivalence is symmetric. -/
theorem certIso_symm {x x' : Ω → L} {k : ℕ} {T T' : Fin k → Γ} (h : CertIso φ x x' T T') :
    CertIso φ x' x T' T := by
  obtain ⟨g, hT, hW, hx⟩ := h
  refine ⟨g⁻¹, fun i => ?_, ?_, fun j hj => ?_⟩
  · rw [← hT i, map_inv]
    exact perm_inv_apply_self _ _
  · rw [← hW, inv_smul_smul]
  · rw [← hW] at hj
    obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.1 hj
    rw [inv_smul_smul, hx u hu]

omit [DecidableEq Ω] [Fintype Γ] in
/-- Certificate equivalence is transitive. -/
theorem certIso_trans {x x' x'' : Ω → L} {k : ℕ} {T T' T'' : Fin k → Γ}
    (h : CertIso φ x x' T T') (h' : CertIso φ x' x'' T' T'') : CertIso φ x x'' T T'' := by
  obtain ⟨g, hT, hW, hx⟩ := h
  obtain ⟨g', hT', hW', hx'⟩ := h'
  refine ⟨g' * g, fun i => ?_, ?_, fun j hj => ?_⟩
  · rw [map_mul, Perm.mul_apply, hT i, hT' i]
  · rw [mul_smul, hW, hW']
  · have hgj : g • j ∈ beardW φ (Finset.univ.image T') x' := by
      rw [← hW]
      exact Set.smul_mem_smul_set hj
    rw [mul_smul, hx' _ hgj, hx j hj]

omit [DecidableEq Ω] [Fintype Γ] in
/-- **An isomorphism of the strings is an equivalence of certificates**: if `g` carries `x` to
`y` (`y (g • j) = x j` for every point), the certificate of `T` for `x` is equivalent to that of
`φ g ∘ T` for `y`. -/
theorem certIso_of_relabel {x y : Ω → L} (g : G) (hg : ∀ j, y (g • j) = x j) {k : ℕ}
    (T : Fin k → Γ) : CertIso φ x y T (φ g ∘ T) := by
  have hy : smulStr g x = y := by
    funext j
    rw [smulStr, ← hg (g⁻¹ • j), smul_inv_smul]
  have hA : Finset.univ.image (φ g ∘ T) = φ g • Finset.univ.image T := by
    rw [Finset.smul_finset_def, Finset.image_image]
    rfl
  refine ⟨g, fun i => rfl, ?_, fun j _ => hg j⟩
  unfold beardW
  rw [hA, ← hy, (beard_relabel φ g _ x _).1]

end Model

/-! ### Certificate equivalence of lists of base indices -/

section ListModel

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  (φ : strGroup hC →* Perm (Fin (N - n)))

/-- **Certificate equivalence of two lists of base indices**, read as `k`-tuples: the form
`certIsoProg` decides. -/
def CertIsoL (x x' : Fin n → ℕ) (k : ℕ) (l l' : List ℕ) : Prop :=
  ∃ (h : ∀ i < k, l.getD i 0 < N - n) (h' : ∀ i < k, l'.getD i 0 < N - n),
    CertIso φ x x' (tupleD (N - n) k l h) (tupleD (N - n) k l' h')

theorem certIsoL_iff {x x' : Fin n → ℕ} {k : ℕ} {l l' : List ℕ}
    (h : ∀ i < k, l.getD i 0 < N - n) (h' : ∀ i < k, l'.getD i 0 < N - n) :
    CertIsoL φ x x' k l l' ↔
      CertIso φ x x' (tupleD (N - n) k l h) (tupleD (N - n) k l' h') :=
  ⟨fun ⟨_, _, hc⟩ => hc, fun hc => ⟨h, h', hc⟩⟩

theorem certIsoL_refl (x : Fin n → ℕ) {k : ℕ} {l : List ℕ}
    (h : ∀ i < k, l.getD i 0 < N - n) : CertIsoL φ x x k l l :=
  ⟨h, h, certIso_refl φ x _⟩

theorem certIsoL_symm {x x' : Fin n → ℕ} {k : ℕ} {l l' : List ℕ}
    (hc : CertIsoL φ x x' k l l') : CertIsoL φ x' x k l' l := by
  obtain ⟨h, h', hc⟩ := hc
  exact ⟨h', h, certIso_symm φ hc⟩

theorem certIsoL_trans {x x' x'' : Fin n → ℕ} {k : ℕ} {l l' l'' : List ℕ}
    (hc : CertIsoL φ x x' k l l') (hc' : CertIsoL φ x' x'' k l' l'') :
    CertIsoL φ x x'' k l l'' := by
  obtain ⟨h, _, c₁⟩ := hc
  obtain ⟨_, h'', c₂⟩ := hc'
  exact ⟨h, h'', certIso_trans φ c₁ c₂⟩

/-- An isomorphism `g` of `x` onto `y` relates the certificates of a list `l` for `x` and of
its image `l'` (`l'[i] = φ g (l[i])`) for `y`. -/
theorem certIsoL_of_relabel {x y : Fin n → ℕ} (g : strGroup hC) (hg : ∀ j, y (g • j) = x j)
    {k : ℕ} {l l' : List ℕ} (h : ∀ i < k, l.getD i 0 < N - n)
    (hl' : ∀ (i : ℕ) (hi : i < k), l'.getD i 0 = (φ g ⟨l.getD i 0, h i hi⟩ : ℕ)) :
    CertIsoL φ x y k l l' := by
  have h' : ∀ i < k, l'.getD i 0 < N - n := fun i hi => by rw [hl' i hi]; exact Fin.isLt _
  refine ⟨h, h', ?_⟩
  have e : tupleD (N - n) k l' h' = φ g ∘ tupleD (N - n) k l h := by
    funext i
    exact Fin.ext (hl' i i.2)
  rw [e]
  exact certIso_of_relabel φ g hg _

end ListModel

/-! ### The colourings on data -/

section Data

/-- The base tuple of a digit list: the points of `vl` at the digits. -/
def tupD (vl ds : List ℕ) : List ℕ := ds.map fun i => vl.getD i 0

/-- The index of the first element satisfying `P`. -/
def firstIdx {α : Type*} (P : α → Bool) : List α → Option ℕ
  | [] => none
  | a :: l => if P a then some 0 else (firstIdx P l).map (· + 1)

/-- The colour of a tuple of `x`: `0` if it has a repetition, else `1 +` the index of the first
repetition-free tuple with an equivalent certificate. -/
def colXVal (cXX : List ℕ → List ℕ → Bool) (tups : List (List ℕ)) (dt : List ℕ) : ℕ :=
  if dt.Nodup then
    ((firstIdx (fun di => decide di.Nodup && cXX di dt) tups).map (· + 1)).getD 0
  else 0

/-- The colour of a tuple of `y`: `1 +` the index of the first equivalent tuple of `x`, else
`1 + |tups| +` the index of the first equivalent tuple of `y`; `0` with a repetition. -/
def colYVal (cXY cYY : List ℕ → List ℕ → Bool) (tups : List (List ℕ)) (dt : List ℕ) : ℕ :=
  if dt.Nodup then
    match firstIdx (fun di => decide di.Nodup && cXY di dt) tups with
    | some i => i + 1
    | none => ((firstIdx (fun dj => decide dj.Nodup && cYY dj dt) tups).map
        (tups.length + 1 + ·)).getD 0
  else 0

/-- **The colouring of `x`**, an array indexed by the codes of the `k`-tuples of `Fin m`. -/
def colXD (cXX : List ℕ → List ℕ → Bool) (k m : ℕ) : Array ℕ :=
  ((Coherent.tupList k m).map (colXVal cXX (Coherent.tupList k m))).toArray

/-- **The colouring of `y`.** -/
def colYD (cXY cYY : List ℕ → List ℕ → Bool) (k m : ℕ) : Array ℕ :=
  ((Coherent.tupList k m).map (colYVal cXY cYY (Coherent.tupList k m))).toArray

end Data

/-! ### The colourings: specifications -/

section DataSpec

theorem firstIdx_congr {α : Type*} {P Q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, P a = Q a) → firstIdx P l = firstIdx Q l
  | [], _ => rfl
  | a :: l, h => by
    simp only [firstIdx, h a List.mem_cons_self,
      firstIdx_congr fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem firstIdx_isSome {α : Type*} {P : α → Bool} :
    ∀ {l : List α} {a : α}, a ∈ l → P a = true → ∃ i, firstIdx P l = some i
  | b :: l, a, ha, hP => by
    simp only [firstIdx]
    split_ifs with hb
    · exact ⟨0, rfl⟩
    · rcases List.mem_cons.1 ha with rfl | ha
      · exact absurd hP hb
      · obtain ⟨i, hi⟩ := firstIdx_isSome ha hP
        exact ⟨i + 1, by rw [hi]; rfl⟩

theorem firstIdx_eq_some {α : Type*} {P : α → Bool} :
    ∀ {l : List α} {i : ℕ}, firstIdx P l = some i → ∃ h : i < l.length, P l[i] = true
  | [], _, h => by simp [firstIdx] at h
  | a :: l, i, h => by
    simp only [firstIdx] at h
    split_ifs at h with ha
    · cases h
      exact ⟨by simp, ha⟩
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨hl, hP⟩ := firstIdx_eq_some hj
      exact ⟨by simpa using hl, by simpa using hP⟩

/-- Reading an array built from a list of rows at the code of a tuple. -/
theorem c3c_get_map_toArray (f : List ℕ → ℕ) {k m : ℕ} (T : Coherent.Tup k m) :
    get ((Coherent.tupList k m).map f).toArray (Coherent.enc T) = f (Coherent.digits T) := by
  have hlt : Coherent.enc T < (Coherent.tupList k m).length := by
    rw [Coherent.length_tupList]
    exact Coherent.enc_lt T
  rw [get_eq_getElem (by simpa using hlt)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [← List.getD_eq_getElem _ [] hlt, Coherent.getD_tupList_enc]

theorem toFun_colXD (cXX : List ℕ → List ℕ → Bool) {k m : ℕ} (T : Coherent.Tup k m) :
    Coherent.toFun (colXD cXX k m) T = colXVal cXX (Coherent.tupList k m) (Coherent.digits T) :=
  c3c_get_map_toArray _ T

theorem toFun_colYD (cXY cYY : List ℕ → List ℕ → Bool) {k m : ℕ} (T : Coherent.Tup k m) :
    Coherent.toFun (colYD cXY cYY k m) T =
      colYVal cXY cYY (Coherent.tupList k m) (Coherent.digits T) :=
  c3c_get_map_toArray _ T

theorem digits_mem_tupList {k m : ℕ} (T : Coherent.Tup k m) :
    Coherent.digits T ∈ Coherent.tupList k m := by
  rw [← Coherent.getD_tupList_enc T]
  have hlt : Coherent.enc T < (Coherent.tupList k m).length := by
    rw [Coherent.length_tupList]
    exact Coherent.enc_lt T
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem _

theorem nodup_digits_iff {k m : ℕ} (T : Coherent.Tup k m) :
    (Coherent.digits T).Nodup ↔ Function.Injective T := by
  rw [Coherent.digits, List.nodup_ofFn]
  exact ⟨fun h a b e => h (congrArg Fin.val e), fun h a b e => h (Fin.ext e)⟩

theorem getD_tupD_digits {vl : List ℕ} {k m : ℕ} (T : Coherent.Tup k m) {i : ℕ} (hi : i < k) :
    (tupD vl (Coherent.digits T)).getD i 0 = vl.getD (T ⟨i, hi⟩) 0 := by
  rw [List.getD_eq_getElem _ _ (by simp [tupD, Coherent.digits, hi])]
  simp [tupD, Coherent.digits]

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  (φ : strGroup hC →* Perm (Fin (N - n)))

theorem c3c_tupD_lt {vl : List ℕ} {k m : ℕ} (hvl : vl.length = m) (hlt : ∀ a ∈ vl, a < N - n)
    (T : Coherent.Tup k m) : ∀ i < k, (tupD vl (Coherent.digits T)).getD i 0 < N - n := by
  intro i hi
  rw [getD_tupD_digits T hi]
  have : (T ⟨i, hi⟩ : ℕ) < vl.length := by rw [hvl]; exact (T ⟨i, hi⟩).2
  rw [List.getD_eq_getElem _ _ this]
  exact hlt _ (List.getElem_mem _)

/-- **The colourings are carried by every isomorphism.** Let `g` carry `x` to `y`, and let the
base action of `g` carry the `a`-th point of `vx` to the `π a`-th point of `vy`. If the
comparisons decide certificate equivalence on repetition-free tuples, the colour of `π ∘ T`
for `y` is the colour of `T` for `x`. -/
theorem tupleCol_iso {xs ys : Fin n → ℕ} {k m : ℕ} {vx vy : List ℕ} (hvx : vx.length = m)
    (hvxl : ∀ a ∈ vx, a < N - n)
    {cXX cXY cYY : List ℕ → List ℕ → Bool}
    (hXX : ∀ di ∈ Coherent.tupList k m, ∀ dt ∈ Coherent.tupList k m, di.Nodup → dt.Nodup →
      (cXX di dt = true ↔ CertIsoL φ xs xs k (tupD vx di) (tupD vx dt)))
    (hXY : ∀ di ∈ Coherent.tupList k m, ∀ dt ∈ Coherent.tupList k m, di.Nodup → dt.Nodup →
      (cXY di dt = true ↔ CertIsoL φ xs ys k (tupD vx di) (tupD vy dt)))
    (g : strGroup hC) (hg : ∀ j, ys (g • j) = xs j) (π : Perm (Fin m))
    (hπ : ∀ (a : Fin m) (h : vx.getD a 0 < N - n),
      vy.getD (π a) 0 = (φ g ⟨vx.getD a 0, h⟩ : ℕ))
    (T : Coherent.Tup k m) :
    Coherent.toFun (colYD cXY cYY k m) (π ∘ T) = Coherent.toFun (colXD cXX k m) T := by
  rw [toFun_colYD, toFun_colXD]
  set tups := Coherent.tupList k m
  have hnd : (Coherent.digits (π ∘ T)).Nodup ↔ (Coherent.digits T).Nodup := by
    rw [nodup_digits_iff, nodup_digits_iff]
    exact ⟨fun h a b e => h (by simp [e]), fun h => π.injective.comp h⟩
  by_cases hT : (Coherent.digits T).Nodup
  · have hT' := hnd.2 hT
    -- the certificate of `T` for `x` and that of `π ∘ T` for `y` are equivalent
    have hR : CertIsoL φ xs ys k (tupD vx (Coherent.digits T))
        (tupD vy (Coherent.digits (π ∘ T))) := by
      refine certIsoL_of_relabel φ g hg (c3c_tupD_lt hvx hvxl T) fun i hi => ?_
      rw [getD_tupD_digits (π ∘ T) hi, Function.comp_apply]
      have e := getD_tupD_digits (vl := vx) T hi
      have h2 : vx.getD (T ⟨i, hi⟩) 0 < N - n := e ▸ c3c_tupD_lt hvx hvxl T i hi
      rw [hπ _ h2]
      congr 2
      exact Fin.ext e.symm
    have hcongr : firstIdx (fun di => decide di.Nodup && cXY di (Coherent.digits (π ∘ T))) tups =
        firstIdx (fun di => decide di.Nodup && cXX di (Coherent.digits T)) tups := by
      refine firstIdx_congr fun di hdi => ?_
      by_cases hdn : di.Nodup
      · simp only [hdn, decide_true, Bool.true_and]
        rw [Bool.eq_iff_iff, hXY di hdi _ (digits_mem_tupList _) hdn hT',
          hXX di hdi _ (digits_mem_tupList _) hdn hT]
        exact ⟨fun h => certIsoL_trans φ h (certIsoL_symm φ hR),
          fun h => certIsoL_trans φ h hR⟩
      · simp [hdn]
    have hsome : ∃ i, firstIdx (fun di => decide di.Nodup && cXX di (Coherent.digits T))
        tups = some i :=
      firstIdx_isSome (digits_mem_tupList T) (by
        simp only [hT, decide_true, Bool.true_and]
        exact (hXX _ (digits_mem_tupList T) _ (digits_mem_tupList T) hT hT).2
          (certIsoL_refl φ xs (c3c_tupD_lt hvx hvxl T)))
    obtain ⟨i, hi⟩ := hsome
    have hX : colXVal cXX tups (Coherent.digits T) = i + 1 := by
      unfold colXVal
      rw [hi]
      simp [hT]
    have hY : colYVal cXY cYY tups (Coherent.digits (π ∘ T)) = i + 1 := by
      unfold colYVal
      rw [hcongr, hi]
      simp [hT']
    rw [hX, hY]
  · have hT'n : ¬ (Coherent.digits (π ∘ T)).Nodup := fun h => hT (hnd.1 h)
    simp [colYVal, colXVal, hT, hT'n]

/-- **The colouring of `x` is milestone 13's Case 3 colouring** (`SameColour`): two tuples have
the same colour exactly when both have repetitions, or both are injective with equivalent
certificates. -/
theorem colX_eq_iff {xs : Fin n → ℕ} {k m : ℕ} {vx : List ℕ} (hvx : vx.length = m)
    (hvxl : ∀ a ∈ vx, a < N - n) {cXX : List ℕ → List ℕ → Bool}
    (hXX : ∀ di ∈ Coherent.tupList k m, ∀ dt ∈ Coherent.tupList k m, di.Nodup → dt.Nodup →
      (cXX di dt = true ↔ CertIsoL φ xs xs k (tupD vx di) (tupD vx dt)))
    (T T' : Coherent.Tup k m) :
    Coherent.toFun (colXD cXX k m) T = Coherent.toFun (colXD cXX k m) T' ↔
      (¬ Function.Injective T ∧ ¬ Function.Injective T') ∨
        (Function.Injective T ∧ Function.Injective T' ∧
          CertIsoL φ xs xs k (tupD vx (Coherent.digits T)) (tupD vx (Coherent.digits T'))) := by
  rw [toFun_colXD, toFun_colXD, ← nodup_digits_iff, ← nodup_digits_iff]
  set tups := Coherent.tupList k m
  -- a repetition-free tuple has a positive colour, the first index of its class plus one
  have hpos : ∀ U : Coherent.Tup k m, (Coherent.digits U).Nodup → ∃ i,
      firstIdx (fun di => decide di.Nodup && cXX di (Coherent.digits U)) tups = some i ∧
        colXVal cXX tups (Coherent.digits U) = i + 1 := by
    intro U hU
    have hsome : ∃ i, firstIdx (fun di => decide di.Nodup && cXX di (Coherent.digits U))
        tups = some i :=
      firstIdx_isSome (digits_mem_tupList U) (by
        simp only [hU, decide_true, Bool.true_and]
        exact (hXX _ (digits_mem_tupList U) _ (digits_mem_tupList U) hU hU).2
          (certIsoL_refl φ xs (c3c_tupD_lt hvx hvxl U)))
    obtain ⟨i, hi⟩ := hsome
    refine ⟨i, hi, ?_⟩
    unfold colXVal
    rw [hi]
    simp [hU]
  by_cases hT : (Coherent.digits T).Nodup <;> by_cases hT' : (Coherent.digits T').Nodup
  · obtain ⟨i, hi, hci⟩ := hpos T hT
    obtain ⟨i', hi', hci'⟩ := hpos T' hT'
    rw [hci, hci']
    constructor
    · intro e
      have e' : i = i' := by omega
      subst e'
      obtain ⟨hl, hP⟩ := firstIdx_eq_some hi
      obtain ⟨_, hP'⟩ := firstIdx_eq_some hi'
      have hmem : tups[i] ∈ tups := List.getElem_mem _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP hP'
      have h₁ := (hXX _ hmem _ (digits_mem_tupList T) hP.1 hT).1 hP.2
      have h₂ := (hXX _ hmem _ (digits_mem_tupList T') hP'.1 hT').1 hP'.2
      exact Or.inr ⟨hT, hT', certIsoL_trans φ (certIsoL_symm φ h₁) h₂⟩
    · rintro (⟨h, -⟩ | ⟨-, -, hR⟩)
      · exact absurd hT h
      · have hcongr : firstIdx (fun di => decide di.Nodup && cXX di (Coherent.digits T)) tups =
            firstIdx (fun di => decide di.Nodup && cXX di (Coherent.digits T')) tups := by
          refine firstIdx_congr fun di hdi => ?_
          by_cases hdn : di.Nodup
          · simp only [hdn, decide_true, Bool.true_and]
            rw [Bool.eq_iff_iff, hXX di hdi _ (digits_mem_tupList _) hdn hT,
              hXX di hdi _ (digits_mem_tupList _) hdn hT']
            exact ⟨fun h => certIsoL_trans φ h hR,
              fun h => certIsoL_trans φ h (certIsoL_symm φ hR)⟩
          · simp [hdn]
        rw [hcongr, hi'] at hi
        cases hi
        rfl
  · obtain ⟨i, -, hci⟩ := hpos T hT
    rw [hci, show colXVal cXX tups (Coherent.digits T') = 0 by simp [colXVal, hT']]
    simp [hT, hT']
  · obtain ⟨i, -, hci⟩ := hpos T' hT'
    rw [hci, show colXVal cXX tups (Coherent.digits T) = 0 by simp [colXVal, hT]]
    simp [hT, hT']
  · simp [colXVal, hT, hT']

end DataSpec

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The base tuple of a digit list, read from the array of base indices (`tupD`). -/
def tupDProg (vA : var (.array .nat)) (ds : var (.list .nat)) : Prog S rec var (.list .nat) :=
  Programs.mapList ds fun i => .op2 .arrayGet vA i

/-- One step of the search for the first element passing a test: the state is the index of the
element and the index found so far. -/
def firstStep (test : var (.list .nat) → Prog S rec var .bool)
    (st : var (.prod .nat (.option .nat))) (d : var (.list .nat)) :
    Prog S rec var (.prod .nat (.option .nat)) :=
  .bind (.op1 .fst st) fun i => .bind (.op1 .snd st) fun r =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add i one) fun i' =>
  .caseOption r
    (.bind (test d) fun b =>
      .ite b (.bind (.op1 .some i) fun s => .op2 .pair i' s) (.op2 .pair i' r))
    (fun _ => .op2 .pair i' r)

/-- **The index of the first element passing a test** (`firstIdx`). -/
def firstIdxProg (test : var (.list .nat) → Prog S rec var .bool)
    (l : var (.list (.list .nat))) : Prog S rec var (.option .nat) :=
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .none) fun r₀ => .bind (.op2 .pair z r₀) fun st₀ =>
  .bind (.foldList l st₀ fun st d => firstStep test st d) fun st => .op1 .snd st

end Programs

section GroupPrograms

variable {D : Ty} {rec : Ty × Ty} {var : Ty → Type}

/-- **One comparison**: `certIsoProg` on the base tuples (read from `vA`, `vA'`) of two digit
lists. -/
def cmpProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N : var .nat) (xy : var Ty.strs) (G : var (Ty.group D)) (vA vA' : var (.array .nat))
    (di dt : var (.list .nat)) : Prog (groupSig D) rec var .bool :=
  .bind (tupDProg vA di) fun al => .bind (tupDProg vA' dt) fun al' =>
  .bind (Programs.mapList al fun a => Giant.agAddProg n a) fun pA =>
  .bind (Programs.posProg N pA) fun pos =>
  CertProg.certIsoProg sub n pos pA xy G al al'

/-- The test of a candidate representative: repetition-free, and an equivalent certificate. -/
def testProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N : var .nat) (xy : var Ty.strs) (G : var (Ty.group D)) (vA vA' : var (.array .nat))
    (di dt : var (.list .nat)) : Prog (groupSig D) rec var .bool :=
  .bind (Programs.nodupProg di) fun nd =>
  .ite nd (cmpProg sub n N xy G vA vA' di dt) (.op0 (.boolLit false))

/-- The colour of a tuple of `x` (`colXVal`). -/
def colXEntryProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N : var .nat) (xx : var Ty.strs) (G : var (Ty.group D)) (vA : var (.array .nat))
    (tups : var (.list (.list .nat))) (dt : var (.list .nat)) : Prog (groupSig D) rec var .nat :=
  .bind (Programs.nodupProg dt) fun nd =>
  .ite nd
    (.bind (firstIdxProg (fun di => testProg sub n N xx G vA vA di dt) tups) fun r =>
      .caseOption r (.op0 (.natLit 0)) fun i =>
        .bind (.op0 (.natLit 1)) fun one => .op2 .add i one)
    (.op0 (.natLit 0))

/-- The colour of a tuple of `y` (`colYVal`). -/
def colYEntryProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N : var .nat) (xy yy : var Ty.strs) (G : var (Ty.group D))
    (vxA vyA : var (.array .nat)) (tups : var (.list (.list .nat))) (len : var .nat)
    (dt : var (.list .nat)) : Prog (groupSig D) rec var .nat :=
  .bind (Programs.nodupProg dt) fun nd =>
  .ite nd
    (.bind (firstIdxProg (fun di => testProg sub n N xy G vxA vyA di dt) tups) fun r =>
      .caseOption r
        (.bind (firstIdxProg (fun dj => testProg sub n N yy G vyA vyA dj dt) tups) fun r' =>
          .caseOption r' (.op0 (.natLit 0)) fun j =>
            .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .add len one) fun l₁ =>
            .op2 .add l₁ j)
        fun i => .bind (.op0 (.natLit 1)) fun one => .op2 .add i one)
    (.op0 (.natLit 0))

/-- **The colourings of the `k`-tuples** of `vx` (for `x`) and of `vy` (for `y`), by
certificate equivalence with consistent names. -/
def tupleColProg (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n N k : var .nat) (vx vy : var (.list .nat)) (x y : var Ty.str) (G : var (Ty.group D)) :
    Prog (groupSig D) rec var (.prod (.array .nat) (.array .nat)) :=
  .bind (.op1 .length vx) fun m =>
  .bind (Coherent.tupsProg k m) fun tups =>
  .bind (.op1 .length tups) fun len =>
  .bind (.op1 .arrayOfList vx) fun vxA => .bind (.op1 .arrayOfList vy) fun vyA =>
  .bind (.op2 .pair x x) fun xx => .bind (.op2 .pair x y) fun xy =>
  .bind (.op2 .pair y y) fun yy =>
  .bind (Programs.mapList tups fun dt => colXEntryProg sub n N xx G vxA tups dt) fun cx =>
  .bind (Programs.mapList tups fun dt => colYEntryProg sub n N xy yy G vxA vyA tups len dt)
    fun cy =>
  .bind (.op1 .arrayOfList cx) fun cxA => .bind (.op1 .arrayOfList cy) fun cyA =>
  .op2 .pair cxA cyA

end GroupPrograms

/-! ### Specifications of the generic programs -/

section GenericSpecs

/-- The functional model of `firstStep`. -/
def firstStepD (P : List ℕ → Bool) (st : ℕ × Option ℕ) (d : List ℕ) : ℕ × Option ℕ :=
  (st.1 + 1, match st.2 with
    | none => if P d then some st.1 else none
    | some r => some r)

theorem foldl_firstStepD_some (P : List ℕ → Bool) :
    ∀ (l : List (List ℕ)) (i₀ r : ℕ), (l.foldl (firstStepD P) (i₀, some r)).2 = some r
  | [], _, _ => rfl
  | _ :: l, i₀, r => foldl_firstStepD_some P l (i₀ + 1) r

theorem foldl_firstStepD_none (P : List ℕ → Bool) :
    ∀ (l : List (List ℕ)) (i₀ : ℕ),
      (l.foldl (firstStepD P) (i₀, none)).2 = (firstIdx P l).map (i₀ + ·)
  | [], _ => rfl
  | d :: l, i₀ => by
    simp only [List.foldl_cons, firstIdx]
    by_cases hd : P d = true
    · simp only [firstStepD, hd, ite_true, Option.map_some, Nat.add_zero]
      exact foldl_firstStepD_some P l (i₀ + 1) i₀
    · simp only [firstStepD, hd, Bool.false_eq_true, ite_false]
      rw [foldl_firstStepD_none P l (i₀ + 1), Option.map_map]
      congr 1
      funext j
      simp only [Function.comp_apply]
      omega

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem c3c_caseOption_eq_none {a' t : Ty} {o : (Ty.option a').denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (ho : o = none) (h : RunsWithin X body p r k) :
    RunsWithin X body (.caseOption o p q) r (1 + k) := by
  subst ho
  exact RunsWithin.caseOption_none h

theorem c3c_caseOption_eq_some {a' t : Ty} {o : (Ty.option a').denote} {v : a'.denote}
    {p : Prog S (a, b) Ty.denote t} {q : a'.denote → Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (ho : o = some v) (h : RunsWithin X body (q v) r k) :
    RunsWithin X body (.caseOption o p q) r (1 + k) := by
  subst ho
  exact RunsWithin.caseOption_some h

theorem c3c_ite_pos {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (hc : c = true) (h : RunsWithin X body p r k) :
    RunsWithin X body (.ite c p q) r (1 + k) := by
  subst hc
  exact RunsWithin.ite_true h

theorem c3c_ite_neg {t : Ty} {c : Bool} {p q : Prog S (a, b) Ty.denote t} {r : t.denote}
    {k : ℕ} (hc : c = false) (h : RunsWithin X body q r k) :
    RunsWithin X body (.ite c p q) r (1 + k) := by
  subst hc
  exact RunsWithin.ite_false h

theorem RunsWithin.tupDProg (vl ds : List ℕ) :
    RunsWithin X body (Case3.tupDProg vl.toArray ds) (tupD vl ds) (ds.length * 4 + 2) := by
  unfold Case3.tupDProg tupD
  refine (RunsWithin.mapList_le (c := 1) fun i _ => RunsWithin.prim_le ?_ ?_).mono le_rfl
  · simp only [Prim.eval, Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    rfl
  · simp [Prim.cost]

theorem RunsWithin.firstStep {test : List ℕ → Prog S (a, b) Ty.denote .bool}
    {P : List ℕ → Bool} {c : ℕ} (st : ℕ × Option ℕ) {d : List ℕ}
    (ht : RunsWithin X body (test d) (P d) c) :
    RunsWithin X body (Case3.firstStep test st d) (firstStepD P st d) (c + 10) := by
  obtain ⟨i, r⟩ := st
  rcases r with _ | r
  · by_cases hP : P d = true
    · apply RunsWithin.mono
      case h =>
        unfold Case3.firstStep
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with c3c_caseOption_eq_none rfl _
        run_step ht
        run_with c3c_ite_pos hP _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, firstStepD, hP]) le_rfl
      case hc => simp only [Prim.cost]; omega
    · rw [Bool.not_eq_true] at hP
      apply RunsWithin.mono
      case h =>
        unfold Case3.firstStep
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with c3c_caseOption_eq_none rfl _
        run_step ht
        run_with c3c_ite_neg hP _
        exact RunsWithin.prim_le (by simp [Prim.eval, firstStepD, hP]) le_rfl
      case hc => simp only [Prim.cost]; omega
  · apply RunsWithin.mono
    case h =>
      unfold Case3.firstStep
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with c3c_caseOption_eq_some rfl _
      exact RunsWithin.prim_le (by simp [Prim.eval, firstStepD]) le_rfl
    case hc => simp only [Prim.cost]; omega

/-- The cost of `firstIdxProg` on `L` elements with tests of cost at most `c`. -/
def firstIdxCost (L c : ℕ) : ℕ := L * (c + 11) + 4

/-- **The first element passing a test.** -/
theorem RunsWithin.firstIdxProg {test : List ℕ → Prog S (a, b) Ty.denote .bool}
    {P : List ℕ → Bool} {c : ℕ} {l : List (List ℕ)}
    (ht : ∀ d ∈ l, RunsWithin X body (test d) (P d) c) :
    RunsWithin X body (Case3.firstIdxProg test l) (firstIdx P l) (firstIdxCost l.length c) := by
  have hfold := RunsWithin.foldList_inv (X := X) (body := body) (a' := .list .nat)
    (b' := .prod .nat (.option .nat)) (I := fun _ => True) (c := c + 10)
    (f := fun st d => Case3.firstStep test st d) (F := firstStepD P) l (0, none)
    (fun st _ d hd => ⟨RunsWithin.firstStep st (ht d hd), trivial⟩) trivial
  apply RunsWithin.mono
  case h =>
    unfold Case3.firstIdxProg
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold.1
    exact RunsWithin.prim_le (by simp [Prim.eval, foldl_firstStepD_none]) le_rfl
  case hc =>
    simp only [Prim.cost, firstIdxCost, Nat.add_assoc, Nat.reduceAdd]
    omega

end GenericSpecs

/-! ### Specifications of the comparisons -/

section CmpSpecs

theorem c3c_nodup_tupD {vl di : List ℕ} (hvl : vl.Nodup) (hdi : di.Nodup)
    (hdim : ∀ i ∈ di, i < vl.length) : (tupD vl di).Nodup := by
  refine hdi.map_on fun i hi j hj e => ?_
  rw [List.getD_eq_getElem _ _ (hdim i hi), List.getD_eq_getElem _ _ (hdim j hj)] at e
  exact (hvl.getElem_inj_iff).1 e

theorem c3c_tupD_mem_lt {vl di : List ℕ} {M : ℕ} (hvlm : ∀ a ∈ vl, a < M)
    (hdim : ∀ i ∈ di, i < vl.length) : ∀ a ∈ tupD vl di, a < M := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
  rw [List.getD_eq_getElem _ _ (hdim i hi)]
  exact hvlm _ (List.getElem_mem _)

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))} {hC : CertSetting G n}
  (φ : strGroup hC →* Perm (Fin (N - n)))

/-- `CertIsoL` at the length of the first list is `certIsoProg`'s answer. -/
theorem c3c_certIsoL_iff {x x' : Fin n → ℕ} {l l' : List ℕ} {k : ℕ} (hl : l.length = k)
    (h : ∀ i < l.length, l.getD i 0 < N - n) (h' : ∀ i < l.length, l'.getD i 0 < N - n) :
    CertIso φ x x' (tupleD (N - n) l.length l h) (tupleD (N - n) l.length l' h') ↔
      CertIsoL φ x x' k l l' := by
  subst hl
  exact (certIsoL_iff φ h h').symm

end CmpSpecs

section GroupSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}
variable {N n : ℕ} {gs : GensData} {hC : CertSetting (GensData.denote N gs) n}
  {φ : strGroup hC →* Perm (Fin (N - n))}

/-- The cost of one comparison, with `CI` the cost of `certIsoProg`. -/
def cmpCost (N k CI : ℕ) : ℕ := CI + 2 * N + 21 * k + 14

/-- **One comparison** decides the certificate equivalence of the base tuples of two
repetition-free digit lists. -/
theorem RunsWithin.cmpProg (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {vl vl' : List ℕ} (hvl : vl.Nodup) (hvl' : vl'.Nodup) (hvlm : ∀ a ∈ vl, a < N - n)
    (hvlm' : ∀ a ∈ vl', a < N - n) {k : ℕ} (h5 : 5 ≤ k) (hk : k + 2 ≤ N - n)
    {di dt : List ℕ} (hdi : di.Nodup) (hdt : dt.Nodup) (hdil : di.length = k)
    (hdtl : dt.length = k) (hdim : ∀ i ∈ di, i < vl.length) (hdtm : ∀ i ∈ dt, i < vl'.length)
    {xy : StrData × StrData} {s : ℕ} {G₀ : Subgroup (Perm (Fin N))}
    (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk : BackendBounds X DV k sk ⊤)
    (hsk : s ≤ k * (sk + 1)) {Bgen Bl Bgs : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsub : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) xy n k s) (fun _ => Cb) s) :
    ∃ r : Bool, RunsWithin X body
        (Case3.cmpProg sub n N xy (N, gs, d) vl.toArray vl'.toArray di dt) r
        (cmpCost N k (certIsoCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen
          Cb Bl Bgs)) ∧
      (r = true ↔ CertIsoL φ (strOn hC.le (xy.1.denote N)) (strOn hC.le (xy.2.denote N)) k
        (tupD vl di) (tupD vl' dt)) := by
  set al := tupD vl di with hal
  set al' := tupD vl' dt with hal'
  have hall : al.length = k := by simp [hal, tupD, hdil]
  have hall' : al'.length = al.length := by simp [hal', hal, tupD, hdil, hdtl]
  have halnd : al.Nodup := c3c_nodup_tupD hvl hdi hdim
  have halnd' : al'.Nodup := c3c_nodup_tupD hvl' hdt hdtm
  have halm : ∀ a ∈ al, a < N - n := c3c_tupD_mem_lt hvlm hdim
  have halm' : ∀ a ∈ al', a < N - n := c3c_tupD_mem_lt hvlm' hdtm
  have hwl : k = (winA N n al).1.length := by rw [length_winA, hall]
  obtain ⟨e1, e2, e3⟩ := Giant.ag_cast_bounds hwl Bk
  have hsk' : s ≤ (winA N n al).1.length * (sk + 1) := by rw [← hwl]; exact hsk
  have h5' : 5 ≤ al.length := by omega
  have hk' : al.length + 2 ≤ N - n := by omega
  have hBg' : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ al.length.factorial * (s + 1) →
        GensData.denote N gs' ≤ GensData.denote N gs →
          X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen := by
    rw [hall]
    exact hBg
  have hsub' : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) xy n al.length s) (fun _ => Cb) s := by
    rw [hall]
    exact hsub
  obtain ⟨res, hrun, hres⟩ := RunsWithin.certIsoProg (X := X) (body := body) (xy := xy) hO hPre
    hφ hGv hgiant halnd halnd' hall' halm halm' h5' hk' B hs hGG₀ (hwl ▸ Bk) hsk' hBg' hBl
    (hBgs al halnd hall halm) hsub'
  rw [e1, e2, e3, hall] at hrun
  refine ⟨res, ?_, ?_⟩
  · have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
      (xs := al) (f := fun a => Giant.agAddProg n a) (F := fun a => n + a) (c := 1)
      fun a _ => Giant.RunsWithin.agAddProg n a
    have hpos : RunsWithin X body (Programs.posProg N (al.map fun a => n + a))
        (WinData.pos N (winA N n al)) (2 * N + 9 * al.length + 8) := by
      have := GraphIso.Programs.RunsWithin.posProg (X := X) (body := body) N (winA N n al)
      rw [length_winA] at this
      exact this
    apply RunsWithin.mono
    case h =>
      unfold Case3.cmpProg
      run_step (RunsWithin.tupDProg vl di)
      run_step (RunsWithin.tupDProg vl' dt)
      run_step hmap
      run_step hpos
      exact hrun
    case hc =>
      simp only [cmpCost, hall, hdil, hdtl]
      omega
  · rw [hres]
    exact c3c_certIsoL_iff φ hall _ _

/-- The cost of the repetition check of a list of length `L`. -/
def nodupCost (L : ℕ) : ℕ := (L + 1) * (3 * L + 9) + 3

/-- The test of a candidate: the repetition check, then (if repetition-free) the comparison,
whose value is given by a function `c`. -/
theorem RunsWithin.testProg {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy : StrData × StrData} {Gd : GroupData D.denote} {vA vA' : Array ℕ}
    {c : List ℕ → List ℕ → Bool} {cC : ℕ} {di dt : List ℕ}
    (hc : di.Nodup → RunsWithin X body (Case3.cmpProg sub n N xy Gd vA vA' di dt) (c di dt) cC) :
    RunsWithin X body (Case3.testProg sub n N xy Gd vA vA' di dt) (decide di.Nodup && c di dt)
      (nodupCost di.length + cC + 2) := by
  by_cases hnd : di.Nodup
  · apply RunsWithin.mono
    case h =>
      unfold Case3.testProg
      run_step (Programs.RunsWithin.nodupProg di)
      run_with c3c_ite_pos (by simpa using hnd) _
      exact (hc hnd).of_eq (by simp [hnd])
    case hc => simp only [nodupCost]; omega
  · apply RunsWithin.mono
    case h =>
      unfold Case3.testProg
      run_step (Programs.RunsWithin.nodupProg di)
      run_with c3c_ite_neg (by simpa using hnd) _
      exact RunsWithin.prim_le (by simp [Prim.eval, hnd]) le_rfl
    case hc => simp only [nodupCost, Prim.cost]; omega

/-- The cost of the entry of one tuple of `x`, on `L` tuples of length `k`. -/
def entryXCost (L k cC : ℕ) : ℕ := nodupCost k + firstIdxCost L (nodupCost k + cC + 2) + 5

/-- The cost of the entry of one tuple of `y`. -/
def entryYCost (L k cC : ℕ) : ℕ :=
  nodupCost k + 2 * firstIdxCost L (nodupCost k + cC + 2) + 8

/-- **The colour of a tuple of `x`.** -/
theorem RunsWithin.colXEntryProg
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xx : StrData × StrData} {Gd : GroupData D.denote} {vA : Array ℕ}
    {cXX : List ℕ → List ℕ → Bool} {cC k : ℕ} {tups : List (List ℕ)} {dt : List ℕ}
    (hlen : ∀ d ∈ tups, d.length = k) (hdt : dt.length = k)
    (hc : dt.Nodup → ∀ di ∈ tups, di.Nodup →
      RunsWithin X body (Case3.cmpProg sub n N xx Gd vA vA di dt) (cXX di dt) cC) :
    RunsWithin X body (Case3.colXEntryProg sub n N xx Gd vA tups dt) (colXVal cXX tups dt)
      (entryXCost tups.length k cC) := by
  by_cases hnd : dt.Nodup
  · have hscan := RunsWithin.firstIdxProg (X := X) (body := body)
      (test := fun di => Case3.testProg sub n N xx Gd vA vA di dt)
      (P := fun di => decide di.Nodup && cXX di dt) (c := nodupCost k + cC + 2) (l := tups)
      fun di hdi => by
        have := RunsWithin.testProg (X := X) (body := body) (n := n) (N := N) (sub := sub)
          (xy := xx) (Gd := Gd) (vA := vA) (vA' := vA) (c := cXX) (cC := cC) (di := di)
          (dt := dt) (hc hnd di hdi)
        rwa [hlen di hdi] at this
    rcases hfi : firstIdx (fun di => decide di.Nodup && cXX di dt) tups with _ | i
    · apply RunsWithin.mono
      case h =>
        unfold Case3.colXEntryProg
        run_step (Programs.RunsWithin.nodupProg dt)
        run_with c3c_ite_pos (by simpa using hnd) _
        run_step hscan
        run_with c3c_caseOption_eq_none hfi _
        exact RunsWithin.prim_le (by simp [Prim.eval, colXVal, hnd, hfi]) le_rfl
      case hc => simp only [entryXCost, nodupCost, Prim.cost, hdt]; omega
    · apply RunsWithin.mono
      case h =>
        unfold Case3.colXEntryProg
        run_step (Programs.RunsWithin.nodupProg dt)
        run_with c3c_ite_pos (by simpa using hnd) _
        run_step hscan
        run_with c3c_caseOption_eq_some hfi _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, colXVal, hnd, hfi]) le_rfl
      case hc => simp only [entryXCost, nodupCost, Prim.cost, hdt]; omega
  · apply RunsWithin.mono
    case h =>
      unfold Case3.colXEntryProg
      run_step (Programs.RunsWithin.nodupProg dt)
      run_with c3c_ite_neg (by simpa using hnd) _
      exact RunsWithin.prim_le (by simp [Prim.eval, colXVal, hnd]) le_rfl
    case hc => simp only [entryXCost, nodupCost, Prim.cost, hdt]; omega

/-- **The colour of a tuple of `y`.** -/
theorem RunsWithin.colYEntryProg
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    {xy yy : StrData × StrData} {Gd : GroupData D.denote} {vxA vyA : Array ℕ}
    {cXY cYY : List ℕ → List ℕ → Bool} {cC k : ℕ} {tups : List (List ℕ)} {dt : List ℕ}
    (hlen : ∀ d ∈ tups, d.length = k) (hdt : dt.length = k)
    (hcXY : dt.Nodup → ∀ di ∈ tups, di.Nodup →
      RunsWithin X body (Case3.cmpProg sub n N xy Gd vxA vyA di dt) (cXY di dt) cC)
    (hcYY : dt.Nodup → ∀ di ∈ tups, di.Nodup →
      RunsWithin X body (Case3.cmpProg sub n N yy Gd vyA vyA di dt) (cYY di dt) cC) :
    RunsWithin X body (Case3.colYEntryProg sub n N xy yy Gd vxA vyA tups tups.length dt)
      (colYVal cXY cYY tups dt) (entryYCost tups.length k cC) := by
  by_cases hnd : dt.Nodup
  · have hscan₁ := RunsWithin.firstIdxProg (X := X) (body := body)
      (test := fun di => Case3.testProg sub n N xy Gd vxA vyA di dt)
      (P := fun di => decide di.Nodup && cXY di dt) (c := nodupCost k + cC + 2) (l := tups)
      fun di hdi => by
        have := RunsWithin.testProg (X := X) (body := body) (n := n) (N := N) (sub := sub)
          (xy := xy) (Gd := Gd) (vA := vxA) (vA' := vyA) (c := cXY) (cC := cC) (di := di)
          (dt := dt) (hcXY hnd di hdi)
        rwa [hlen di hdi] at this
    have hscan₂ := RunsWithin.firstIdxProg (X := X) (body := body)
      (test := fun di => Case3.testProg sub n N yy Gd vyA vyA di dt)
      (P := fun di => decide di.Nodup && cYY di dt) (c := nodupCost k + cC + 2) (l := tups)
      fun di hdi => by
        have := RunsWithin.testProg (X := X) (body := body) (n := n) (N := N) (sub := sub)
          (xy := yy) (Gd := Gd) (vA := vyA) (vA' := vyA) (c := cYY) (cC := cC) (di := di)
          (dt := dt) (hcYY hnd di hdi)
        rwa [hlen di hdi] at this
    rcases hf₁ : firstIdx (fun di => decide di.Nodup && cXY di dt) tups with _ | i
    · rcases hf₂ : firstIdx (fun di => decide di.Nodup && cYY di dt) tups with _ | j
      · apply RunsWithin.mono
        case h =>
          unfold Case3.colYEntryProg
          run_step (Programs.RunsWithin.nodupProg dt)
          run_with c3c_ite_pos (by simpa using hnd) _
          run_step hscan₁
          run_with c3c_caseOption_eq_none hf₁ _
          run_step hscan₂
          run_with c3c_caseOption_eq_none hf₂ _
          exact RunsWithin.prim_le (by simp [Prim.eval, colYVal, hnd, hf₁, hf₂]) le_rfl
        case hc => simp only [entryYCost, nodupCost, Prim.cost, hdt]; omega
      · apply RunsWithin.mono
        case h =>
          unfold Case3.colYEntryProg
          run_step (Programs.RunsWithin.nodupProg dt)
          run_with c3c_ite_pos (by simpa using hnd) _
          run_step hscan₁
          run_with c3c_caseOption_eq_none hf₁ _
          run_step hscan₂
          run_with c3c_caseOption_eq_some hf₂ _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.prim_le (by simp [Prim.eval, colYVal, hnd, hf₁, hf₂]) le_rfl
        case hc => simp only [entryYCost, nodupCost, Prim.cost, hdt]; omega
    · apply RunsWithin.mono
      case h =>
        unfold Case3.colYEntryProg
        run_step (Programs.RunsWithin.nodupProg dt)
        run_with c3c_ite_pos (by simpa using hnd) _
        run_step hscan₁
        run_with c3c_caseOption_eq_some hf₁ _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim_le (by simp [Prim.eval, colYVal, hnd, hf₁]) le_rfl
      case hc => simp only [entryYCost, nodupCost, Prim.cost, hdt]; omega
  · apply RunsWithin.mono
    case h =>
      unfold Case3.colYEntryProg
      run_step (Programs.RunsWithin.nodupProg dt)
      run_with c3c_ite_neg (by simpa using hnd) _
      exact RunsWithin.prim_le (by simp [Prim.eval, colYVal, hnd]) le_rfl
    case hc => simp only [entryYCost, nodupCost, Prim.cost, hdt]; omega

theorem mem_tupList_spec {k m : ℕ} {d : List ℕ} (hd : d ∈ Coherent.tupList k m) :
    d.length = k ∧ ∀ i ∈ d, i < m := by
  rw [Coherent.tupList_eq] at hd
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hd
  refine ⟨by simp [Coherent.digitsOf], fun i hi => ?_⟩
  simp only [Coherent.digitsOf, List.mem_ofFn] at hi
  obtain ⟨j, rfl⟩ := hi
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hk : k ≠ 0 := fun h => by subst h; exact j.elim0
    rw [List.mem_range, Nat.zero_pow (Nat.pos_of_ne_zero hk)] at ht
    exact absurd ht (Nat.not_lt_zero _)
  · exact Nat.mod_lt _ hm

/-- **The cost of the colourings**: the enumeration, and for each of the `m^k` tuples its two
entries, each at most `m^k` tests (one `certIsoProg` call of cost `CI` each). -/
def tupleColCost (N k m CI : ℕ) : ℕ :=
  Coherent.tupsCost k m + 3 * m + 3 * m ^ k + 20 +
    m ^ k * (entryXCost (m ^ k) k (cmpCost N k CI) + entryYCost (m ^ k) k (cmpCost N k CI) + 6)

/-- **The colourings of the `k`-tuples by certificate equivalence.** For lists `vx`, `vy` of
`m` base points (`Γ ∖ S` for `x` and for `y`), the program computes `colXD` and `colYD` with
comparisons that decide certificate equivalence on repetition-free tuples (for the string pairs
`(x, x)`, `(x, y)`, `(y, y)`), under stage 14e's sub-solver hypothesis for each pair, at cost
`tupleColCost`: at most `3 m^(2k)` calls of `certIsoProg` and a polynomial. -/
theorem RunsWithin.tupleColProg (hO : MeetsContractOn DV certOps X.O)
    (hPre : ∀ op x, certOps op → GroupPre DV op x → X.Pre op x) (hφ : IsPhi hC φ)
    {d : D.denote} (hGv : GroupValid DV N gs d)
    (hgiant : alternatingGroup (Fin (N - n)) ≤
      (baseHom (GensData.denote N gs) n hC.base).range)
    {vx vy : List ℕ} (hvx : vx.Nodup) (hvy : vy.Nodup) (hlen : vy.length = vx.length)
    (hvxm : ∀ a ∈ vx, a < N - n) (hvym : ∀ a ∈ vy, a < N - n) {k : ℕ} (h5 : 5 ≤ k)
    (hk : k + 2 ≤ N - n) {x y : StrData} {s : ℕ} {G₀ : Subgroup (Perm (Fin N))}
    (B : BackendBounds X DV N s G₀) (hs : gs.length ≤ s)
    (hGG₀ : GensData.denote N gs ≤ G₀) {sk : ℕ} (Bk : BackendBounds X DV k sk ⊤)
    (hsk : s ≤ k * (sk + 1)) {Bgen Bl Bgs : ℕ}
    (hBg : ∀ gs' : GensData, GensData.AllValid N gs' →
      gs'.length ≤ k.factorial * (s + 1) → GensData.denote N gs' ≤ GensData.denote N gs →
        X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    (hBl : ∀ π, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBgs : ∀ al : List ℕ, al.Nodup → al.length = k → (∀ a ∈ al, a < N - n) → ∀ b₁ b₂,
      X.B.call GroupOp.generate (N, giantGens X.O n (N, gs, d) al b₁ b₂)
        (giantSetStabModel X.O n (N, gs, d) al b₁ b₂) ≤ Bgs)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)} {Cb : ℕ}
    (hsubXX : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (x, x) n k s) (fun _ => Cb) s)
    (hsubXY : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (x, y) n k s) (fun _ => Cb) s)
    (hsubYY : SubSolves X body DV sub
      (StepSubP (DV := DV) (GensData.denote N gs) (y, y) n k s) (fun _ => Cb) s) :
    ∃ cXX cXY cYY : List ℕ → List ℕ → Bool,
      (∀ di ∈ Coherent.tupList k vx.length, ∀ dt ∈ Coherent.tupList k vx.length,
        di.Nodup → dt.Nodup →
          (cXX di dt = true ↔ CertIsoL φ (strOn hC.le (x.denote N)) (strOn hC.le (x.denote N))
            k (tupD vx di) (tupD vx dt))) ∧
      (∀ di ∈ Coherent.tupList k vx.length, ∀ dt ∈ Coherent.tupList k vx.length,
        di.Nodup → dt.Nodup →
          (cXY di dt = true ↔ CertIsoL φ (strOn hC.le (x.denote N)) (strOn hC.le (y.denote N))
            k (tupD vx di) (tupD vy dt))) ∧
      (∀ di ∈ Coherent.tupList k vx.length, ∀ dt ∈ Coherent.tupList k vx.length,
        di.Nodup → dt.Nodup →
          (cYY di dt = true ↔ CertIsoL φ (strOn hC.le (y.denote N)) (strOn hC.le (y.denote N))
            k (tupD vy di) (tupD vy dt))) ∧
      RunsWithin X body (Case3.tupleColProg sub n N k vx vy x y (N, gs, d))
        (colXD cXX k vx.length, colYD cXY cYY k vx.length)
        (tupleColCost N k vx.length (certIsoCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb
          Bk.Bstab Bgen Cb Bl Bgs)) := by
  set m := vx.length with hm
  set tups := Coherent.tupList k m with htups
  set CI := certIsoCost N n k s B.Bstab B.Btr B.Borb Bk.Bgen Bk.Borb Bk.Bstab Bgen Cb Bl Bgs
  have hmem : ∀ di ∈ tups, di.length = k ∧ ∀ i ∈ di, i < m := fun di hdi => mem_tupList_spec hdi
  -- the comparisons, as functions
  have hexXX : ∀ di dt : List ℕ, ∃ r : Bool, di ∈ tups → dt ∈ tups → di.Nodup → dt.Nodup →
      RunsWithin X body (Case3.cmpProg sub n N (x, x) (N, gs, d) vx.toArray vx.toArray di dt) r
        (cmpCost N k CI) ∧
      (r = true ↔ CertIsoL φ (strOn hC.le (x.denote N)) (strOn hC.le (x.denote N)) k
        (tupD vx di) (tupD vx dt)) := by
    intro di dt
    by_cases h : di ∈ tups ∧ dt ∈ tups ∧ di.Nodup ∧ dt.Nodup
    · obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨r, hr⟩ := RunsWithin.cmpProg (X := X) (body := body) (xy := (x, x)) hO hPre hφ hGv
        hgiant hvx hvx hvxm hvxm h5 hk h3 h4 (hmem di h1).1 (hmem dt h2).1 (hmem di h1).2
        (hmem dt h2).2 B hs hGG₀ Bk hsk hBg hBl hBgs hsubXX
      exact ⟨r, fun _ _ _ _ => hr⟩
    · exact ⟨false, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  have hexXY : ∀ di dt : List ℕ, ∃ r : Bool, di ∈ tups → dt ∈ tups → di.Nodup → dt.Nodup →
      RunsWithin X body (Case3.cmpProg sub n N (x, y) (N, gs, d) vx.toArray vy.toArray di dt) r
        (cmpCost N k CI) ∧
      (r = true ↔ CertIsoL φ (strOn hC.le (x.denote N)) (strOn hC.le (y.denote N)) k
        (tupD vx di) (tupD vy dt)) := by
    intro di dt
    by_cases h : di ∈ tups ∧ dt ∈ tups ∧ di.Nodup ∧ dt.Nodup
    · obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨r, hr⟩ := RunsWithin.cmpProg (X := X) (body := body) (xy := (x, y)) hO hPre hφ hGv
        hgiant hvx hvy hvxm hvym h5 hk h3 h4 (hmem di h1).1 (hmem dt h2).1 (hmem di h1).2
        (fun i hi => hlen ▸ (hmem dt h2).2 i hi) B hs hGG₀ Bk hsk hBg hBl hBgs hsubXY
      exact ⟨r, fun _ _ _ _ => hr⟩
    · exact ⟨false, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  have hexYY : ∀ di dt : List ℕ, ∃ r : Bool, di ∈ tups → dt ∈ tups → di.Nodup → dt.Nodup →
      RunsWithin X body (Case3.cmpProg sub n N (y, y) (N, gs, d) vy.toArray vy.toArray di dt) r
        (cmpCost N k CI) ∧
      (r = true ↔ CertIsoL φ (strOn hC.le (y.denote N)) (strOn hC.le (y.denote N)) k
        (tupD vy di) (tupD vy dt)) := by
    intro di dt
    by_cases h : di ∈ tups ∧ dt ∈ tups ∧ di.Nodup ∧ dt.Nodup
    · obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨r, hr⟩ := RunsWithin.cmpProg (X := X) (body := body) (xy := (y, y)) hO hPre hφ hGv
        hgiant hvy hvy hvym hvym h5 hk h3 h4 (hmem di h1).1 (hmem dt h2).1
        (fun i hi => hlen ▸ (hmem di h1).2 i hi) (fun i hi => hlen ▸ (hmem dt h2).2 i hi) B hs
        hGG₀ Bk hsk hBg hBl hBgs hsubYY
      exact ⟨r, fun _ _ _ _ => hr⟩
    · exact ⟨false, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩
  choose cXX hcXX using hexXX
  choose cXY hcXY using hexXY
  choose cYY hcYY using hexYY
  refine ⟨cXX, cXY, cYY, fun di hdi dt hdt h1 h2 => (hcXX di dt hdi hdt h1 h2).2,
    fun di hdi dt hdt h1 h2 => (hcXY di dt hdi hdt h1 h2).2,
    fun di hdi dt hdt h1 h2 => (hcYY di dt hdi hdt h1 h2).2, ?_⟩
  have hL : tups.length = m ^ k := Coherent.length_tupList k m
  have hX := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := .nat)
    (xs := tups) (f := fun dt => Case3.colXEntryProg sub n N (x, x) (N, gs, d) vx.toArray tups dt)
    (F := colXVal cXX tups) (c := entryXCost tups.length k (cmpCost N k CI))
    fun dt hdt => RunsWithin.colXEntryProg (fun di hdi => (hmem di hdi).1) (hmem dt hdt).1
      fun hdn di hdi hnd => (hcXX di dt hdi hdt hnd hdn).1
  have hY := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := .nat)
    (xs := tups)
    (f := fun dt => Case3.colYEntryProg sub n N (x, y) (y, y) (N, gs, d) vx.toArray vy.toArray
      tups tups.length dt)
    (F := colYVal cXY cYY tups) (c := entryYCost tups.length k (cmpCost N k CI))
    fun dt hdt => RunsWithin.colYEntryProg (fun di hdi => (hmem di hdi).1) (hmem dt hdt).1
      (fun hdn di hdi hnd => (hcXY di dt hdi hdt hnd hdn).1)
      (fun hdn di hdi hnd => (hcYY di dt hdi hdt hnd hdn).1)
  apply RunsWithin.mono
  case h =>
    unfold Case3.tupleColProg
    run_step (RunsWithin.prim _ _)
    run_step (Coherent.RunsWithin.tupsProg k _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hX
    run_step hY
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval, colXD, colYD, htups, hm]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_map, hL, tupleColCost, hlen,
      Coherent.length_tupList, ← hm]
    have hmv : vx.length = m := rfl
    have hd : m ^ k * (entryXCost (m ^ k) k (cmpCost N k CI) +
        entryYCost (m ^ k) k (cmpCost N k CI) + 6) =
        m ^ k * (entryXCost (m ^ k) k (cmpCost N k CI) + 3) +
          m ^ k * (entryYCost (m ^ k) k (cmpCost N k CI) + 3) := by ring
    omega

end GroupSpecs

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem c3c_wf_nodupProg {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)}
    (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (Programs.nodupProg l₁) (Programs.nodupProg l₂) := by
  unfold Programs.nodupProg Programs.nodupStep anyList
  prog_wf

theorem wf_tupDProg {vA₁ : var₁ (.array .nat)} {vA₂ : var₂ (.array .nat)}
    {ds₁ : var₁ (.list .nat)} {ds₂ : var₂ (.list .nat)} (hv : ⟨.array .nat, vA₁, vA₂⟩ ∈ Γ)
    (hd : ⟨.list .nat, ds₁, ds₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (tupDProg vA₁ ds₁) (tupDProg vA₂ ds₂) := by
  unfold tupDProg
  exact wf_mapList hd fun _ hΓ _ _ hi => .prim _ (.cons (hΓ hv) (.cons hi .nil))

theorem wf_firstStep {test₁ : var₁ (.list .nat) → Prog S rec var₁ .bool}
    {test₂ : var₂ (.list .nat) → Prog S rec var₂ .bool} (ht : WfFun r Γ test₁ test₂)
    {st₁ : var₁ (.prod .nat (.option .nat))} {st₂ : var₂ (.prod .nat (.option .nat))}
    {d₁ : var₁ (.list .nat)} {d₂ : var₂ (.list .nat)}
    (hst : ⟨.prod .nat (.option .nat), st₁, st₂⟩ ∈ Γ) (hd : ⟨.list .nat, d₁, d₂⟩ ∈ Γ) :
    Prog.Wf r Γ (firstStep test₁ st₁ d₁) (firstStep test₂ st₂ d₂) := by
  unfold firstStep
  refine .bind (.prim _ (.cons hst .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hst]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .caseOption (by simp) ?_ fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))
  refine .bind (ht _ (fun y hy => by simp [hy]) _ _ (by simp [hd])) fun _ _ => ?_
  exact .ite (by simp) (.bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil)))
    (.prim _ (.cons (by simp) (.cons (by simp) .nil)))

theorem wf_firstIdxProg {test₁ : var₁ (.list .nat) → Prog S rec var₁ .bool}
    {test₂ : var₂ (.list .nat) → Prog S rec var₂ .bool} (ht : WfFun r Γ test₁ test₂)
    {l₁ : var₁ (.list (.list .nat))} {l₂ : var₂ (.list (.list .nat))}
    (hl : ⟨.list (.list .nat), l₁, l₂⟩ ∈ Γ) :
    Prog.Wf r Γ (firstIdxProg test₁ l₁) (firstIdxProg test₂ l₂) := by
  unfold firstIdxProg
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ .nil) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ => ?_
  refine .bind (.foldList (by simp [hl]) (by simp) fun _ _ _ _ =>
    wf_firstStep (ht.mono fun _ h => by simp [h]) (List.Mem.head _) (by simp)) fun _ _ => ?_
  exact .prim _ (.cons (by simp) .nil)

theorem wf_cmpProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {vA₁ vA'₁ : var₁ (.array .nat)} {vA₂ vA'₂ : var₂ (.array .nat)}
    {di₁ dt₁ : var₁ (.list .nat)} {di₂ dt₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hv : ⟨.array .nat, vA₁, vA₂⟩ ∈ Γ) (hv' : ⟨.array .nat, vA'₁, vA'₂⟩ ∈ Γ)
    (hdi : ⟨.list .nat, di₁, di₂⟩ ∈ Γ) (hdt : ⟨.list .nat, dt₁, dt₂⟩ ∈ Γ) :
    Prog.Wf r Γ (cmpProg sub₁ n₁ N₁ xy₁ G₁ vA₁ vA'₁ di₁ dt₁)
      (cmpProg sub₂ n₂ N₂ xy₂ G₂ vA₂ vA'₂ di₂ dt₂) := by
  unfold cmpProg
  refine .bind (wf_tupDProg hv hdi) fun _ _ => ?_
  refine .bind (wf_tupDProg (by simp [hv']) (by simp [hdt])) fun _ _ => ?_
  refine .bind (wf_mapList (by simp) fun _ hΓ _ _ ha =>
    Giant.wf_agAddProg (hΓ (by simp [hn])) ha) fun _ _ => ?_
  refine .bind (Giant.ag_wf_posProg (by simp [hN]) (by simp)) fun _ _ => ?_
  exact CertProg.wf_certIsoProg (hsub.mono fun _ h => by simp [h]) (by simp [hn]) (by simp)
    (by simp) (by simp [hxy]) (by simp [hG]) (by simp) (by simp)

theorem wf_testProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {vA₁ vA'₁ : var₁ (.array .nat)} {vA₂ vA'₂ : var₂ (.array .nat)}
    {di₁ dt₁ : var₁ (.list .nat)} {di₂ dt₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hv : ⟨.array .nat, vA₁, vA₂⟩ ∈ Γ) (hv' : ⟨.array .nat, vA'₁, vA'₂⟩ ∈ Γ)
    (hdi : ⟨.list .nat, di₁, di₂⟩ ∈ Γ) (hdt : ⟨.list .nat, dt₁, dt₂⟩ ∈ Γ) :
    Prog.Wf r Γ (testProg sub₁ n₁ N₁ xy₁ G₁ vA₁ vA'₁ di₁ dt₁)
      (testProg sub₂ n₂ N₂ xy₂ G₂ vA₂ vA'₂ di₂ dt₂) := by
  unfold testProg
  refine .bind (c3c_wf_nodupProg hdi) fun _ _ => ?_
  exact .ite (by simp)
    (wf_cmpProg (hsub.mono fun _ h => by simp [h]) (by simp [hn]) (by simp [hN]) (by simp [hxy])
      (by simp [hG]) (by simp [hv]) (by simp [hv']) (by simp [hdi]) (by simp [hdt]))
    (.prim _ .nil)

theorem wf_colXEntryProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ : var₁ .nat} {n₂ N₂ : var₂ .nat}
    {xx₁ : var₁ Ty.strs} {xx₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    {vA₁ : var₁ (.array .nat)} {vA₂ : var₂ (.array .nat)}
    {tups₁ : var₁ (.list (.list .nat))} {tups₂ : var₂ (.list (.list .nat))}
    {dt₁ : var₁ (.list .nat)} {dt₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hxx : ⟨Ty.strs, xx₁, xx₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ)
    (hv : ⟨.array .nat, vA₁, vA₂⟩ ∈ Γ) (ht : ⟨.list (.list .nat), tups₁, tups₂⟩ ∈ Γ)
    (hdt : ⟨.list .nat, dt₁, dt₂⟩ ∈ Γ) :
    Prog.Wf r Γ (colXEntryProg sub₁ n₁ N₁ xx₁ G₁ vA₁ tups₁ dt₁)
      (colXEntryProg sub₂ n₂ N₂ xx₂ G₂ vA₂ tups₂ dt₂) := by
  unfold colXEntryProg
  refine .bind (c3c_wf_nodupProg hdt) fun _ _ => ?_
  refine .ite (by simp) ?_ (.prim _ .nil)
  refine .bind (wf_firstIdxProg (fun Γ' hΓ' _ _ hdi => wf_testProg
    (hsub.mono fun _ h => hΓ' (by simp [h])) (hΓ' (by simp [hn])) (hΓ' (by simp [hN]))
    (hΓ' (by simp [hxx])) (hΓ' (by simp [hG])) (hΓ' (by simp [hv])) (hΓ' (by simp [hv])) hdi
    (hΓ' (by simp [hdt]))) (by simp [ht])) fun _ _ => ?_
  exact .caseOption (by simp) (.prim _ .nil) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_colYEntryProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ len₁ : var₁ .nat} {n₂ N₂ len₂ : var₂ .nat}
    {xy₁ yy₁ : var₁ Ty.strs} {xy₂ yy₂ : var₂ Ty.strs} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} {vxA₁ vyA₁ : var₁ (.array .nat)} {vxA₂ vyA₂ : var₂ (.array .nat)}
    {tups₁ : var₁ (.list (.list .nat))} {tups₂ : var₂ (.list (.list .nat))}
    {dt₁ : var₁ (.list .nat)} {dt₂ : var₂ (.list .nat)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ)
    (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hyy : ⟨Ty.strs, yy₁, yy₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hvx : ⟨.array .nat, vxA₁, vxA₂⟩ ∈ Γ)
    (hvy : ⟨.array .nat, vyA₁, vyA₂⟩ ∈ Γ) (ht : ⟨.list (.list .nat), tups₁, tups₂⟩ ∈ Γ)
    (hlen : ⟨.nat, len₁, len₂⟩ ∈ Γ) (hdt : ⟨.list .nat, dt₁, dt₂⟩ ∈ Γ) :
    Prog.Wf r Γ (colYEntryProg sub₁ n₁ N₁ xy₁ yy₁ G₁ vxA₁ vyA₁ tups₁ len₁ dt₁)
      (colYEntryProg sub₂ n₂ N₂ xy₂ yy₂ G₂ vxA₂ vyA₂ tups₂ len₂ dt₂) := by
  unfold colYEntryProg
  refine .bind (c3c_wf_nodupProg hdt) fun _ _ => ?_
  refine .ite (by simp) ?_ (.prim _ .nil)
  refine .bind (wf_firstIdxProg (fun Γ' hΓ' _ _ hdi => wf_testProg
    (hsub.mono fun _ h => hΓ' (by simp [h])) (hΓ' (by simp [hn])) (hΓ' (by simp [hN]))
    (hΓ' (by simp [hxy])) (hΓ' (by simp [hG])) (hΓ' (by simp [hvx])) (hΓ' (by simp [hvy])) hdi
    (hΓ' (by simp [hdt]))) (by simp [ht])) fun _ _ => ?_
  refine .caseOption (by simp) ?_ fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))
  refine .bind (wf_firstIdxProg (fun Γ' hΓ' _ _ hdi => wf_testProg
    (hsub.mono fun _ h => hΓ' (by simp [h])) (hΓ' (by simp [hn])) (hΓ' (by simp [hN]))
    (hΓ' (by simp [hyy])) (hΓ' (by simp [hG])) (hΓ' (by simp [hvy])) (hΓ' (by simp [hvy])) hdi
    (hΓ' (by simp [hdt]))) (by simp [ht])) fun _ _ => ?_
  exact .caseOption (by simp) (.prim _ .nil) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp [hlen]) (.cons (by simp) .nil)))
      fun _ _ => .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_tupleColProg {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ N₁ k₁ : var₁ .nat} {n₂ N₂ k₂ : var₂ .nat}
    {vx₁ vy₁ : var₁ (.list .nat)} {vx₂ vy₂ : var₂ (.list .nat)} {x₁ y₁ : var₁ Ty.str}
    {x₂ y₂ : var₂ Ty.str} {G₁ : var₁ (Ty.group D)} {G₂ : var₂ (Ty.group D)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hN : ⟨.nat, N₁, N₂⟩ ∈ Γ) (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ)
    (hvx : ⟨.list .nat, vx₁, vx₂⟩ ∈ Γ) (hvy : ⟨.list .nat, vy₁, vy₂⟩ ∈ Γ)
    (hx : ⟨Ty.str, x₁, x₂⟩ ∈ Γ) (hy : ⟨Ty.str, y₁, y₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf r Γ (tupleColProg sub₁ n₁ N₁ k₁ vx₁ vy₁ x₁ y₁ G₁)
      (tupleColProg sub₂ n₂ N₂ k₂ vx₂ vy₂ x₂ y₂ G₂) := by
  unfold tupleColProg
  refine .bind (.prim _ (.cons hvx .nil)) fun _ _ => ?_
  refine .bind (Coherent.wf_tupsProg (by simp [hk]) (by simp)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hvx]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hvy]) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hx]) (.cons (by simp [hx]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hx]) (.cons (by simp [hy]) .nil))) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp [hy]) (.cons (by simp [hy]) .nil))) fun _ _ => ?_
  refine .bind (wf_mapList (by simp) fun Γ' hΓ' _ _ hdt => wf_colXEntryProg
    (hsub.mono fun _ h => hΓ' (by simp [h])) (hΓ' (by simp [hn])) (hΓ' (by simp [hN]))
    (hΓ' (by simp)) (hΓ' (by simp [hG])) (hΓ' (by simp)) (hΓ' (by simp)) hdt) fun _ _ => ?_
  refine .bind (wf_mapList (by simp) fun Γ' hΓ' _ _ hdt => wf_colYEntryProg
    (hsub.mono fun _ h => hΓ' (by simp [h])) (hΓ' (by simp [hn])) (hΓ' (by simp [hN]))
    (hΓ' (by simp)) (hΓ' (by simp)) (hΓ' (by simp [hG])) (hΓ' (by simp)) (hΓ' (by simp))
    (hΓ' (by simp)) (hΓ' (by simp)) hdt) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => ?_
  exact .prim _ (.cons (by simp) (.cons (by simp) .nil))

end Wf

end GraphIso.Case3
