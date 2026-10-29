module

public import GraphIso.Coherent.WLArray
public import GraphIso.Coherent.TuplesProg

/-!
# The Weisfeiler–Leman program

Programs of the cost language computing the refinement on arrays (`GraphIso/Coherent/WLArray.lean`):

* `sigProg` / `sig0Prog`: the signature of a tuple from the precomputed information, with the
  vectors sorted by insertion sort (`sigA`, `sig0A`);
* `rankProg`: the sorted list of the distinct signatures and the rank of every signature;
* `roundProg`: one round, `none` when the number of colours does not grow (`stepA`);
* `initProg`: round 0 (`initA`);
* `wlProg k m col`: the information on the tuples, round 0, and a loop of rounds; it returns
  `wlA k m col`, the array of the refinement and its colour list (`RunsWithin.wlProg`).

The loop is paid by the potential `(m^k + 1 − #colours) · (roundCost + 2)`: each round that
does not stop adds a colour (`wlStep_inv`), and there are at most `m^k` colours.
-/

@[expose] public section

namespace GraphIso.Coherent

open Cost Programs Sims

variable {k m : ℕ}

/-- Signatures, as a value type. -/
abbrev sigTy : Ty := .list (.list .nat)

/-- The state of the loop: the colouring, the number of colours and the colour list. -/
abbrev wlStTy : Ty := .prod (.array .nat) (.prod .nat (.list .nat))

/-! ### Programs -/

section Prog

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The colours of a list of codes. -/
def colsProg (col : var (.array .nat)) (l : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList l fun i => .op2 .arrayGet col i

/-- **The signature of a tuple.** -/
def sigProg (col : var (.array .nat)) (e : var infoTy) : Prog S rec var sigTy :=
  .bind (.op1 .fst e) fun t => .bind (.op1 .snd e) fun r₁ => .bind (.op1 .snd r₁) fun r₂ =>
  .bind (.op1 .fst r₂) fun nb => .bind (.op1 .snd r₂) fun mo =>
  .bind (.op2 .arrayGet col t) fun ct => .bind (.op0 .nil) fun nl =>
  .bind (.op2 .cons ct nl) fun hd => .bind (colsProg col mo) fun moC =>
  .bind (mapList nb fun v => colsProg col v) fun vs =>
  .bind (sortProg (fun a b => cmpNProg a b) vs) fun svs =>
  .bind (.op2 .cons moC svs) fun tl => .op2 .cons hd tl

/-- The round-0 signature of a tuple. -/
def sig0Prog (col : var (.array .nat)) (e : var infoTy) : Prog S rec var sigTy :=
  .bind (.op1 .fst e) fun t => .bind (.op1 .snd e) fun r₁ => .bind (.op1 .fst r₁) fun pat =>
  .bind (.op2 .arrayGet col t) fun ct => .bind (.op0 .nil) fun nl =>
  .bind (.op2 .cons ct nl) fun hd => .bind (.op0 .nil) fun nl' =>
  .bind (.op2 .cons pat nl') fun tl => .op2 .cons hd tl

/-- The previous colour at the head of a signature. -/
def sigColourProg (s : var sigTy) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 0)) fun z =>
  .caseList s (.ret z) fun h _ => .caseList h (.ret z) fun c _ => .ret c

/-- The sorted distinct signatures, and the rank of every signature. -/
def rankProg (sigs : var (.list sigTy)) : Prog S rec var (.prod (.array .nat) (.list sigTy)) :=
  .bind (dedupSortProg (fun a b => cmpLProg a b) sigs) fun sl =>
  .bind (mapList sigs fun s => idxOfProg (fun a b => cmpLProg a b) s sl) fun idx =>
  .bind (.op1 .arrayOfList idx) fun arr => .op2 .pair arr sl

/-- The new colour list. -/
def origProg (sl : var (.list sigTy)) (orig : var (.list .nat)) : Prog S rec var (.list .nat) :=
  .bind (.op1 .arrayOfList orig) fun oA =>
  mapList sl fun s => .bind (sigColourProg s) fun c => .op2 .arrayGet oA c

/-- **One round**, or `none` when the number of colours does not grow. -/
def roundProg (info : var (.list infoTy)) (st : var wlStTy) : Prog S rec var (.option wlStTy) :=
  .bind (.op1 .fst st) fun col => .bind (.op1 .snd st) fun rest =>
  .bind (.op1 .fst rest) fun n => .bind (.op1 .snd rest) fun orig =>
  .bind (mapList info fun e => sigProg col e) fun sigs =>
  .bind (rankProg sigs) fun rs => .bind (.op1 .fst rs) fun arr => .bind (.op1 .snd rs) fun sl =>
  .bind (.op1 .length sl) fun len => .bind (.op2 .natEq len n) fun same =>
  .ite same (.op0 .none)
    (.bind (origProg sl orig) fun orig' => .bind (.op2 .pair len orig') fun rest' =>
      .bind (.op2 .pair arr rest') fun st' => .op1 .some st')

/-- **Round 0.** -/
def initProg (info : var (.list infoTy)) (col : var (.array .nat)) : Prog S rec var wlStTy :=
  .bind (mapList info fun e => sig0Prog col e) fun sigs =>
  .bind (rankProg sigs) fun rs => .bind (.op1 .fst rs) fun arr => .bind (.op1 .snd rs) fun sl =>
  .bind (.op1 .length sl) fun len => .bind (mapList sl fun s => sigColourProg s) fun orig =>
  .bind (.op2 .pair len orig) fun rest => .op2 .pair arr rest

/-- Round 0 and the loop of rounds, from the information on the tuples. -/
def wlRunProg (info : var (.list infoTy)) (col : var (.array .nat)) :
    Prog S rec var (.prod (.array .nat) (.list .nat)) :=
  .bind (initProg info col) fun st₀ =>
  .bind (.loop st₀ fun st => roundProg info st) fun st =>
  .bind (.op1 .fst st) fun arr => .bind (.op1 .snd st) fun rest =>
  .bind (.op1 .snd rest) fun orig => .op2 .pair arr orig

/-- **The `k`-ary Weisfeiler–Leman refinement** of the colouring `col` of the `k`-tuples of
`Fin m`, indexed by codes: the stable colouring and its colour list. -/
def wlProg (k m : var .nat) (col : var (.array .nat)) :
    Prog S rec var (.prod (.array .nat) (.list .nat)) :=
  .bind (infoProg k m) fun info => wlRunProg info col

end Prog

/-! ### Shapes and costs -/

/-- The shape of the information on a tuple: a pattern of `k²` entries, `K` codes of
rearrangements, `m` vectors of `k` codes of neighbours. -/
def InfoShape (k m K : ℕ) (e : Info) : Prop :=
  e.2.1.length = k * k ∧ e.2.2.2.length = K ∧ e.2.2.1.length = m ∧ ∀ v ∈ e.2.2.1, v.length = k

theorem length_patRowM (dA : Array ℕ) (k : ℕ) : (patRowM dA k).length = k * k := by
  simp [patRowM, List.length_flatMap]

theorem infoShape_infoL {e : Info} (he : e ∈ infoL k m) : InfoShape k m (k ^ k) e := by
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 he
  refine ⟨length_patRowM _ _, ?_, ?_, ?_⟩
  · simp [infoAt, monoRowM, length_mapsArr]
  · simp [infoAt, nbrRowM]
  · intro v hv
    simp only [infoAt, nbrRowM, List.mem_map] at hv
    obtain ⟨z, _, rfl⟩ := hv
    simp

theorem length_infoL : (infoL k m).length = m ^ k := by
  simp [infoL]

/-- The cost of a signature. -/
def sigCost (k m K : ℕ) : ℕ := 4 * K + m * (4 * k + 5) + m * (m * (14 * k + 20) + 10) + m + 16

/-- The cost of ranking `N` signatures whose comparisons cost at most `ce`. -/
def rankCost (N ce : ℕ) : ℕ :=
  N * (N * (ce + 15) + 10) + 1 + (N * (N * (ce + 10) + 9) + 2) + N + 2

/-- A bound on the cost of comparing a signature of a round. -/
def ceSig (k m K : ℕ) : ℕ := (m + 2) * (14 * (K + k + 1) + 17) + 8

/-- A bound on the cost of comparing a round-0 signature. -/
def ceSig0 (k : ℕ) : ℕ := 2 * (14 * (k * k + 1) + 17) + 8

/-- The cost of a round on `N` tuples. -/
def roundCost (N k m K : ℕ) : ℕ :=
  (N * (sigCost k m K + 3) + 2) + rankCost N (ceSig k m K) + 2 * N + 7 * N + 20

/-- The cost of round 0 on `N` tuples. -/
def initCost (N k : ℕ) : ℕ := (N * 12 + 2) + rankCost N (ceSig0 k) + (N + 1) + (N * 6 + 2) + 4

/-- The cost of round 0 and the loop of rounds. -/
def wlRunCost (k m : ℕ) : ℕ :=
  initCost (m ^ k) k + (m ^ k + 1) * (roundCost (m ^ k) k m (k ^ k) + 2) + 4

/-- **The cost of the refinement.** -/
def wlCost (k m : ℕ) : ℕ := infoCost k m + wlRunCost k m

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem RunsWithin.colsProg (col : Array ℕ) (l : List ℕ) :
    RunsWithin X body (Coherent.colsProg col l) (l.map (get col)) (l.length * 4 + 2) := by
  have := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat) (c := 1)
    (f := fun i => .op2 .arrayGet col i) (F := get col) (xs := l)
    fun i _ => RunsWithin.prim_le (by simp [Prim.eval, get, Array.getD_eq_getD_getElem?,
      Ty.default]) le_rfl
  exact this

theorem RunsWithin.sigProg (col : Array ℕ) {e : Info} {K : ℕ} (he : InfoShape k m K e) :
    RunsWithin X body (Coherent.sigProg col e) (sigA col e) (sigCost k m K) := by
  obtain ⟨t, pat, nb, mo⟩ := e
  obtain ⟨-, hmo, hnb, hv⟩ := he
  simp only at hmo hnb hv
  have hvs := RunsWithin.mapList_le (X := X) (body := body) (a' := .list .nat) (b' := .list .nat)
    (c := k * 4 + 2) (f := fun v => Coherent.colsProg col v) (F := fun v => v.map (get col))
    (xs := nb) fun v hv' => by rw [← hv v hv']; exact RunsWithin.colsProg col v
  have hsort := RunsWithin.sortProg (X := X) (body := body) (t := .list .nat)
    (cmp := fun a b => Coherent.cmpNProg a b) (e := ord3) (fun _ _ => rfl) (ce := 14 * k + 8)
    (l := nb.map fun v => v.map (get col)) fun x hx y => by
      obtain ⟨v, hv', rfl⟩ := List.mem_map.1 hx
      have := RunsWithin.cmpNProg (X := X) (body := body) (v.map (get col)) y
      rwa [List.length_map, hv v hv'] at this
  rw [List.length_map, hnb] at hsort
  rw [hnb] at hvs
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
    run_step (RunsWithin.colsProg col mo)
    run_step hvs
    run_step hsort
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    simp [Prim.eval, sigA, get, Array.getD_eq_getD_getElem?, Ty.default]
  case hc =>
    simp only [Prim.cost, hmo, sigCost]
    nlinarith

theorem RunsWithin.sig0Prog (col : Array ℕ) (e : Info) :
    RunsWithin X body (Coherent.sig0Prog col e) (sig0A col e) 9 := by
  obtain ⟨t, pat, nb, mo⟩ := e
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
    refine (RunsWithin.prim _ _).of_eq ?_
    simp [Prim.eval, sig0A, get, Array.getD_eq_getD_getElem?, Ty.default]
  case hc => simp [Prim.cost]

theorem RunsWithin.sigColourProg (s : List (List ℕ)) :
    RunsWithin X body (Coherent.sigColourProg s) (sigColour s) 3 := by
  rcases s with _ | ⟨h, s⟩
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.caseList_eq_nil rfl _
      exact (RunsWithin.ret _).of_eq (by simp [Prim.eval, sigColour])
    case hc => simp [Prim.cost]
  · rcases h with _ | ⟨c, h⟩
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_eq_cons rfl _
        run_with RunsWithin.caseList_eq_nil rfl _
        exact (RunsWithin.ret _).of_eq (by simp [Prim.eval, sigColour])
      case hc => simp [Prim.cost]
    · apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.caseList_eq_cons rfl _
        run_with RunsWithin.caseList_eq_cons rfl _
        exact (RunsWithin.ret _).of_eq (by simp [sigColour])
      case hc => simp [Prim.cost]

/-- **Ranking signatures.** -/
theorem RunsWithin.rankProg {sigs : List (List (List ℕ))} {L w : ℕ}
    (hs : ∀ s ∈ sigs, s.length ≤ L ∧ ∀ z ∈ s, z.length ≤ w) :
    RunsWithin X body (Coherent.rankProg sigs)
      ((sigs.map fun s => (sigs.toFinset.sort (· ≤ ·)).idxOf s).toArray,
        sigs.toFinset.sort (· ≤ ·)) (rankCost sigs.length (L * (14 * w + 17) + 8)) := by
  have hcmp : ∀ x ∈ sigs, ∀ y, RunsWithin X body (Coherent.cmpLProg x y) (ord3 x y)
      (L * (14 * w + 17) + 8) := fun x hx y =>
    (RunsWithin.cmpLProg (hs x hx).2 y).mono (by
      have := Nat.mul_le_mul_right (14 * w + 17) (hs x hx).1
      omega)
  have hsl : (sigs.toFinset.sort (· ≤ ·)).length ≤ sigs.length := by
    rw [Finset.length_sort]
    exact List.toFinset_card_le _
  have hdd := RunsWithin.dedupSortProg (X := X) (body := body) (t := .list (.list .nat))
    (cmp := fun a b => Coherent.cmpLProg a b) (e := ord3) (fun _ _ => rfl) hcmp
  have hidx := RunsWithin.mapList_le (X := X) (body := body) (a' := .list (.list .nat))
    (b' := .nat) (c := sigs.length * (L * (14 * w + 17) + 8 + 10) + 6)
    (f := fun s => Coherent.idxOfProg (fun a b => Coherent.cmpLProg a b) s
      (sigs.toFinset.sort (· ≤ ·)))
    (F := fun s => (sigs.toFinset.sort (· ≤ ·)).idxOf s) (xs := sigs) fun s hs' =>
      (RunsWithin.idxOfProg (t := .list (.list .nat)) (fun _ _ => rfl)
        (fun y => hcmp s hs' y) _).mono (by
          have := Nat.mul_le_mul_right (L * (14 * w + 17) + 8 + 10) hsl
          omega)
  apply RunsWithin.mono
  case h =>
    run_step hdd
    run_step hidx
    run_step (RunsWithin.prim _ _)
    exact (RunsWithin.prim _ _).of_eq (by simp [Prim.eval])
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_map, rankCost]
    have h1 : sigs.length * (sigs.length * (L * (14 * w + 17) + 8 + 10) + 6 + 3) =
        sigs.length * (sigs.length * (L * (14 * w + 17) + 8 + 10) + 9) := rfl
    omega

theorem RunsWithin.origProg (sl : List (List (List ℕ))) (orig : List ℕ) :
    RunsWithin X body (Coherent.origProg sl orig) (sl.map fun s => orig.getD (sigColour s) 0)
      (orig.length + 1 + (sl.length * 7 + 2)) := by
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .list (.list .nat))
    (b' := .nat) (c := 4) (f := fun s => .bind (Coherent.sigColourProg s) fun c =>
      .op2 .arrayGet orig.toArray c) (F := fun s => orig.getD (sigColour s) 0) (xs := sl)
    fun s _ => RunsWithin.bind_le (RunsWithin.sigColourProg s) (RunsWithin.prim_le (by
      simp [Prim.eval, Ty.default, List.getD_eq_getElem?_getD]) le_rfl) (by simp [Prim.cost])
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact hmap
  case hc => simp only [Prim.cost, Args.head_cons]; omega

end Specs

theorem sigA_shape {col : Array ℕ} {e : Info} {K : ℕ} (he : InfoShape k m K e) :
    (sigA col e).length ≤ m + 2 ∧ ∀ z ∈ sigA col e, z.length ≤ K + k + 1 := by
  obtain ⟨t, pat, nb, mo⟩ := e
  obtain ⟨-, hmo, hnb, hv⟩ := he
  simp only at hmo hnb hv
  refine ⟨by simp [sigA, List.length_insertionSort, hnb], fun z hz => ?_⟩
  simp only [sigA, List.mem_cons, List.mem_insertionSort, List.mem_map] at hz
  rcases hz with rfl | rfl | ⟨v, hv', rfl⟩
  · simp
  · simp [hmo]; omega
  · simp [hv v hv']; omega

theorem sig0A_shape {col : Array ℕ} {e : Info} {K : ℕ} (he : InfoShape k m K e) :
    (sig0A col e).length ≤ 2 ∧ ∀ z ∈ sig0A col e, z.length ≤ k * k + 1 := by
  obtain ⟨t, pat, nb, mo⟩ := e
  obtain ⟨hpat, -⟩ := he
  simp only at hpat
  refine ⟨by simp [sig0A], fun z hz => ?_⟩
  simp only [sig0A, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  · simp
  · simp [hpat]

theorem length_sort_le (l : List (List (List ℕ))) :
    (l.toFinset.sort (· ≤ ·)).length ≤ l.length := by
  rw [Finset.length_sort]
  exact List.toFinset_card_le _

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- **One round.** -/
theorem RunsWithin.roundProg {info : List Info} {K : ℕ} (hsh : ∀ e ∈ info, InfoShape k m K e)
    (st : Array ℕ × ℕ × List ℕ) (horig : st.2.2.length ≤ info.length) :
    RunsWithin X body (Coherent.roundProg info st) (roundA (info.map (sigA st.1)) st.2.1 st.2.2)
      (roundCost info.length k m K) := by
  obtain ⟨col, n, orig⟩ := st
  simp only at horig ⊢
  set sigs := info.map (sigA col) with hsigs
  have hsig := RunsWithin.mapList_le (X := X) (body := body) (a' := infoTy) (b' := sigTy)
    (c := sigCost k m K) (f := fun e => Coherent.sigProg col e) (F := sigA col) (xs := info)
    fun e he => RunsWithin.sigProg col (hsh e he)
  have hrank := RunsWithin.rankProg (X := X) (body := body) (sigs := sigs) (L := m + 2)
    (w := K + k + 1) fun s hs => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
      exact sigA_shape (hsh e he)
  have hlen : sigs.length = info.length := by simp [hsigs]
  rw [hlen] at hrank
  have hsl := length_sort_le sigs
  rw [hlen] at hsl
  set sl := sigs.toFinset.sort (· ≤ ·) with hsl_def
  by_cases hsame : sl.length = n
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hsig
      run_step hrank
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (sl.length == n) = true by simpa using hsame) _
      refine (RunsWithin.prim _ _).of_eq ?_
      simp [Prim.eval, roundA, ← hsl_def, hsame]
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, roundCost, ceSig]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step hsig
      run_step hrank
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_neg (show (sl.length == n) = false by simpa using hsame) _
      run_step (RunsWithin.origProg _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      refine (RunsWithin.prim _ _).of_eq ?_
      simp [Prim.eval, roundA, ← hsl_def, hsame]
    case hc =>
      simp only [Prim.cost, Prim.eval, Args.head_cons, roundCost, ceSig]
      omega

/-- **Round 0.** -/
theorem RunsWithin.initProg {info : List Info} {K : ℕ} (hsh : ∀ e ∈ info, InfoShape k m K e)
    (col : Array ℕ) :
    RunsWithin X body (Coherent.initProg info col)
      (((info.map (sig0A col)).map fun s =>
          ((info.map (sig0A col)).toFinset.sort (· ≤ ·)).idxOf s).toArray,
        ((info.map (sig0A col)).toFinset.sort (· ≤ ·)).length,
        ((info.map (sig0A col)).toFinset.sort (· ≤ ·)).map sigColour)
      (initCost info.length k) := by
  set sigs := info.map (sig0A col) with hsigs
  have hsig := RunsWithin.mapList_le (X := X) (body := body) (a' := infoTy) (b' := sigTy)
    (c := 9) (f := fun e => Coherent.sig0Prog col e) (F := sig0A col) (xs := info)
    fun e _ => RunsWithin.sig0Prog col e
  have hrank := RunsWithin.rankProg (X := X) (body := body) (sigs := sigs) (L := 2)
    (w := k * k + 1) fun s hs => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hs
      exact sig0A_shape (hsh e he)
  have hlen : sigs.length = info.length := by simp [hsigs]
  rw [hlen] at hrank
  have hsl := length_sort_le sigs
  rw [hlen] at hsl
  set sl := sigs.toFinset.sort (· ≤ ·) with hsl_def
  have hcol := RunsWithin.mapList_le (X := X) (body := body) (a' := sigTy) (b' := .nat)
    (c := 3) (f := fun s => Coherent.sigColourProg s) (F := sigColour) (xs := sl)
    fun s _ => RunsWithin.sigColourProg s
  apply RunsWithin.mono
  case h =>
    run_step hsig
    run_step hrank
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hcol
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    simp [Prim.eval]
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, initCost, ceSig0]
    have : sl.length * (3 + 3) ≤ info.length * 6 := Nat.mul_le_mul_right 6 hsl
    omega

end Specs

/-! ### The loop -/

/-- The invariant of the loop: the array state of a state of the model with as many colours as
its number, and a colour list of that length. -/
def LoopInv (k m : ℕ) (st : Array ℕ × ℕ × List ℕ) : Prop :=
  ∃ ws : WLState k m, st = repSt ws ∧ ws.2.1 = numColours ws.1 ∧ ws.2.2.length = ws.2.1

theorem loopInv_init (col : Array ℕ) : LoopInv k m (initA k m col) :=
  ⟨wlInit (toFun col), initA_eq col, wlInit_inv _, by simp [wlInit]⟩

theorem LoopInv.le {st : Array ℕ × ℕ × List ℕ} (h : LoopInv k m st) :
    st.2.1 ≤ m ^ k ∧ st.2.2.length = st.2.1 := by
  obtain ⟨ws, rfl, hn, hl⟩ := h
  exact ⟨hn ▸ numColours_le _, hl⟩

theorem LoopInv.step {st st' : Array ℕ × ℕ × List ℕ} (h : LoopInv k m st)
    (hs : stepA k m st = some st') : LoopInv k m st' ∧ st.2.1 < st'.2.1 := by
  obtain ⟨ws, rfl, hn, -⟩ := h
  rw [stepA_repSt] at hs
  rcases hw : wlStep ws with _ | ws'
  · rw [hw] at hs
    cases hs
  · rw [hw] at hs
    obtain rfl := Option.some.inj hs
    obtain ⟨hn', hlt⟩ := wlStep_inv hn hw
    have hl' : ws'.2.2.length = ws'.2.1 := by
      unfold wlStep at hw
      split at hw
      · cases hw
      · obtain rfl := Option.some.inj hw
        simp
    exact ⟨⟨ws', rfl, hn', hl'⟩, hlt⟩

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- **Round 0 and the loop of rounds.** -/
theorem RunsWithin.wlRunProg (k m : ℕ) (col : Array ℕ) :
    RunsWithin X body (Coherent.wlRunProg (infoL k m) col) (wlA k m col) (wlRunCost k m) := by
  have hinit := RunsWithin.initProg (X := X) (body := body) (info := infoL k m)
    (fun e he => infoShape_infoL he) col
  rw [length_infoL] at hinit
  set R := roundCost (m ^ k) k m (k ^ k) with hR
  set Φ : Array ℕ × ℕ × List ℕ → ℕ := fun st => (m ^ k + 1 - st.2.1) * (R + 2) with hΦ
  have hf : ∀ st, LoopInv k m st → ∃ c, RunsWithin X body (Coherent.roundProg (infoL k m) st)
      (stepA k m st) c ∧ (stepA k m st = none → c + 1 ≤ Φ st) ∧
      ∀ st', stepA k m st = some st' → LoopInv k m st' ∧ c + 1 + Φ st' ≤ Φ st := by
    intro st hI
    obtain ⟨hn, hl⟩ := hI.le
    have hrun := RunsWithin.roundProg (X := X) (body := body) (info := infoL k m)
      (fun e he => infoShape_infoL he) st (by rw [hl, length_infoL]; exact hn)
    rw [length_infoL] at hrun
    refine ⟨R, hrun, fun _ => ?_, fun st' hs => ?_⟩
    · have : 1 ≤ m ^ k + 1 - st.2.1 := by omega
      have := Nat.mul_le_mul_right (R + 2) this
      simp only [hΦ]
      omega
    · obtain ⟨hI', hlt⟩ := hI.step hs
      obtain ⟨hn', -⟩ := hI'.le
      refine ⟨hI', ?_⟩
      have h1 : m ^ k + 1 - st'.2.1 ≤ m ^ k - st.2.1 := by omega
      have h2 : m ^ k + 1 - st.2.1 = m ^ k - st.2.1 + 1 := by omega
      have := Nat.mul_le_mul_right (R + 2) h1
      simp only [hΦ, h2, Nat.succ_mul]
      omega
  have hloop := RunsWithin.loop_pot (X := X) (body := body) (s := wlStTy) (F := stepA k m)
    (I := LoopInv k m) (Φ := Φ) (f := fun st => Coherent.roundProg (infoL k m) st) hf
    (Φ (initA k m col) + m ^ k + 2) (initA k m col) (loopInv_init col) (by omega)
  rw [iter_stepA_of_le col (by omega)] at hloop
  have hΦ₀ : Φ (initA k m col) ≤ (m ^ k + 1) * (R + 2) :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  apply RunsWithin.mono
  case h =>
    run_step hinit
    run_step hloop
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    refine (RunsWithin.prim _ _).of_eq ?_
    simp [Prim.eval, wlA]
  case hc =>
    simp only [Prim.cost, wlRunCost, ← hR]
    omega

/-- **The `k`-ary Weisfeiler–Leman refinement**: `wlProg k m col` returns the array of the
refinement of the colouring `toFun col` and its colour list (`wlA_eq`), at cost at most
`wlCost k m`. -/
theorem RunsWithin.wlProg (k m : ℕ) (col : Array ℕ) :
    RunsWithin X body (Coherent.wlProg k m col) (wlA k m col) (wlCost k m) :=
  (RunsWithin.infoProg k m).bind (RunsWithin.wlRunProg k m col)

end Specs

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_colsProg {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)}
    {l₁ : var₁ (.list .nat)} {l₂ : var₂ (.list .nat)} (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ)
    (hl : ⟨.list .nat, l₁, l₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (colsProg col₁ l₁) (colsProg col₂ l₂) :=
  wf_mapList hl fun _ hΓ _ _ hi => .prim _ (.cons (hΓ hcol) (.cons hi .nil))

theorem wf_sigProg {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)}
    {e₁ : var₁ infoTy} {e₂ : var₂ infoTy} (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ)
    (he : ⟨infoTy, e₁, e₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sigProg col₁ e₁) (sigProg col₂ e₂) := by
  unfold sigProg
  refine .bind (.prim _ (.cons he .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [he]) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp [hcol]) (.cons (by simp) .nil))) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil)))
    fun _ _ => .bind (wf_colsProg (by simp [hcol]) (by simp)) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ hΓ _ _ hv => wf_colsProg (hΓ (by simp [hcol])) hv)
    fun _ _ => .bind (wf_sortProg wfCmp_cmpN (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_sig0Prog {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)}
    {e₁ : var₁ infoTy} {e₂ : var₂ infoTy} (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ)
    (he : ⟨infoTy, e₁, e₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sig0Prog col₁ e₁) (sig0Prog col₂ e₂) := by
  unfold sig0Prog
  prog_wf

theorem wf_sigColourProg {s₁ : var₁ sigTy} {s₂ : var₂ sigTy} (hs : ⟨sigTy, s₁, s₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (sigColourProg s₁) (sigColourProg s₂) := by
  unfold sigColourProg
  prog_wf

theorem wf_rankProg {sigs₁ : var₁ (.list sigTy)} {sigs₂ : var₂ (.list sigTy)}
    (hs : ⟨.list sigTy, sigs₁, sigs₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (rankProg sigs₁) (rankProg sigs₂) := by
  unfold rankProg
  exact .bind (wf_dedupSortProg wfCmp_cmpL hs) fun _ _ =>
    .bind (wf_mapList (by simp [hs]) fun _ hΓ _ _ hx =>
      wf_idxOfProg (wfCmp_cmpL.mono hΓ) hx (hΓ (by simp))) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_origProg {sl₁ : var₁ (.list sigTy)} {sl₂ : var₂ (.list sigTy)}
    {o₁ : var₁ (.list .nat)} {o₂ : var₂ (.list .nat)} (hsl : ⟨.list sigTy, sl₁, sl₂⟩ ∈ Γ)
    (ho : ⟨.list .nat, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (origProg sl₁ o₁) (origProg sl₂ o₂) := by
  unfold origProg
  exact .bind (.prim _ (.cons ho .nil)) fun _ _ =>
    wf_mapList (by simp [hsl]) fun _ hΓ _ _ hx =>
      .bind (wf_sigColourProg hx) fun _ _ =>
        .prim _ (.cons (by simp [hΓ (List.mem_cons_self)]) (.cons (by simp) .nil))

theorem wf_roundProg {i₁ : var₁ (.list infoTy)} {i₂ : var₂ (.list infoTy)}
    {st₁ : var₁ wlStTy} {st₂ : var₂ wlStTy} (hi : ⟨.list infoTy, i₁, i₂⟩ ∈ Γ)
    (hst : ⟨wlStTy, st₁, st₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (roundProg i₁ st₁) (roundProg i₂ st₂) := by
  unfold roundProg
  refine .bind (.prim _ (.cons hst .nil)) fun _ _ => .bind (.prim _ (.cons (by simp [hst]) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp [hi]) fun _ hΓ _ _ he => wf_sigProg (hΓ (by simp)) he)
    fun _ _ => .bind (wf_rankProg (by simp)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) (.prim _ .nil) (.bind (wf_origProg (by simp) (by simp)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .prim _ (.cons (by simp) .nil))

theorem wf_initProg {i₁ : var₁ (.list infoTy)} {i₂ : var₂ (.list infoTy)}
    {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)} (hi : ⟨.list infoTy, i₁, i₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (initProg i₁ col₁) (initProg i₂ col₂) := by
  unfold initProg
  exact .bind (wf_mapList hi fun _ hΓ _ _ he => wf_sig0Prog (hΓ hcol) he) fun _ _ =>
    .bind (wf_rankProg (by simp)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .bind (wf_mapList (by simp) fun _ _ _ _ hs => wf_sigColourProg hs) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_wlRunProg {i₁ : var₁ (.list infoTy)} {i₂ : var₂ (.list infoTy)}
    {col₁ : var₁ (.array .nat)} {col₂ : var₂ (.array .nat)} (hi : ⟨.list infoTy, i₁, i₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (wlRunProg i₁ col₁) (wlRunProg i₂ col₂) := by
  unfold wlRunProg
  exact .bind (wf_initProg hi hcol) fun _ _ =>
    .bind (.loop (by simp) fun _ _ => wf_roundProg (by simp [hi]) (by simp)) fun _ _ =>
    .bind (.prim _ (.cons (by simp) .nil)) fun _ _ => .bind (.prim _ (.cons (by simp) .nil))
    fun _ _ => .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
    .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_wlProg {k₁ m₁ : var₁ .nat} {k₂ m₂ : var₂ .nat} {col₁ : var₁ (.array .nat)}
    {col₂ : var₂ (.array .nat)} (hk : ⟨.nat, k₁, k₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hcol : ⟨.array .nat, col₁, col₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (wlProg k₁ m₁ col₁) (wlProg k₂ m₂ col₂) := by
  unfold wlProg
  exact .bind (wf_infoProg hk hm) fun _ _ => wf_wlRunProg (by simp) (by simp [hcol])

end Wf

end GraphIso.Coherent
