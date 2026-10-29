module

public import GraphIso.Toolkit.BaseBlocks
public import GraphIso.Reductions.BlockKernelProg

/-!
# Orbital configurations of the base action

`PLAN-14.md` §6 item 7. For a group `G` of degree `N` acting transitively on its base positions
`[n, N)`, `orbitalProg` computes the `m × m` array (`m = N - n`, row-major) of orbital indices
of the base action `ψ(G)`:

* the transversal `r_u` of the first base point `n` (`orbitTransversal`), so `r_u (n) = n + u`;
* the orbits of its stabilizer `G_n` on the base positions (`stabilizer`, `orbits`), indexed
  by `blockIdx`;
* the entry `(u, v)` is the index of the `G_n`-orbit of `r_u⁻¹ (n + v)`.

Two entries are equal exactly when the pairs lie in one orbital (`orbitalModel_spec`): this is
the hypothesis `hc` of `orbital_uniprimitive` and `orbital_config`. `relColProg` turns the array
into the colouring `relCol R` of the orbital `R` of a chosen pair (`relColModel_spec`,
`arrRel_orbital`), the input of `wlRel` in stage 14a.

The cost language has no multiplication, so the row offsets `u m` are produced by a fold
(`rowsProg`, `mulProg`).
-/

@[expose] public section

namespace GraphIso.Toolkit

open Equiv MulAction Cost Programs GraphIso.Recursion GraphIso.Solver

/-! ### Square arrays -/

/-- The `m × m` array of `F u v`, row-major. -/
def matrixOf (m : ℕ) (F : ℕ → ℕ → ℕ) : Array ℕ :=
  ((List.range m).map fun u => (List.range m).map (F u)).flatten.toArray

/-- Reading a flattened list of rows of length `m`. -/
theorem getD_flatten_rows {m : ℕ} :
    ∀ (rows : List (List ℕ)), (∀ r ∈ rows, r.length = m) → ∀ {u v : ℕ}, v < m →
      rows.flatten.getD (u * m + v) 0 = (rows.getD u []).getD v 0
  | [], _, u, v, _ => by simp
  | r :: rs, h, u, v, hv => by
    have hr : r.length = m := h r List.mem_cons_self
    rw [List.flatten_cons]
    rcases u with _ | u
    · simp only [Nat.zero_mul, Nat.zero_add, List.getD_cons_zero]
      exact List.getD_append _ _ _ _ (by omega)
    · rw [List.getD_append_right _ _ _ _ (by rw [hr, Nat.succ_mul]; omega), hr,
        show (u + 1) * m + v - m = u * m + v by rw [Nat.succ_mul]; omega,
        getD_flatten_rows rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr')) hv]
      simp

theorem get_matrixOf {m u v : ℕ} (hu : u < m) (hv : v < m) (F : ℕ → ℕ → ℕ) :
    get (matrixOf m F) (u * m + v) = F u v := by
  unfold matrixOf get
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD,
    getD_flatten_rows _ (by simp) hv]
  simp [List.getD_eq_getElem?_getD, hu, hv]

theorem size_matrixOf (m : ℕ) (F : ℕ → ℕ → ℕ) : (matrixOf m F).size = m * m := by
  simp [matrixOf, Function.comp_def, List.map_const', List.sum_replicate]

section Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The pairs `(u, u m)` for `u < m`. -/
def rowsProg (m : var .nat) : Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op1 .range m) fun is =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 .nil) fun nil => .bind (.op2 .pair z nil) fun st₀ =>
  .bind (.foldList is st₀ fun st u =>
      .bind (.op1 .fst st) fun off => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .pair u off) fun p => .bind (.op2 .cons p acc) fun acc' =>
      .bind (.op2 .add off m) fun off' => .op2 .pair off' acc') fun fin =>
  .bind (.op1 .snd fin) fun racc => .op1 .reverse racc

/-- `a m`, by repeated addition. -/
def mulProg (a m : var .nat) : Prog S rec var .nat :=
  .bind (.op1 .range a) fun is => .bind (.op0 (.natLit 0)) fun z =>
  .foldList is z fun acc _ => .op2 .add acc m

/-- The `m × m` array of an entry program, row-major. The entry program receives the row, the
row offset `u m` and the column. -/
def matrixProg (m : var .nat) (f : var .nat → var .nat → var .nat → Prog S rec var .nat) :
    Prog S rec var (.array .nat) :=
  .bind (rowsProg m) fun prs => .bind (.op1 .range m) fun is =>
  .bind (mapList prs fun p => .bind (.op1 .fst p) fun u => .bind (.op1 .snd p) fun off =>
      mapList is fun v => f u off v) fun rows =>
  .bind (.op1 .reverse rows) fun rrows =>
  .bind (.op0 .nil) fun nil =>
  .bind (.foldList rrows nil fun acc row => .op2 .append row acc) fun flat =>
  .op1 .arrayOfList flat

/-- The orbital index of `(u, v)`: the orbit index of `r_u⁻¹ (n + v)`. -/
def orbEntryProg (n : var .nat) (oi : var (.array .nat)) (TA : var (.array Ty.perm))
    (u v : var .nat) : Prog S rec var .nat :=
  .bind (.op2 .add n u) fun nu => .bind (.op2 .arrayGet TA nu) fun r =>
  .bind (.op1 .snd r) fun ri => .bind (.op2 .add n v) fun nv =>
  .bind (.op2 .arrayGet ri nv) fun a => .op2 .arrayGet oi a

/-- **The orbital configuration of the base action.** -/
def orbitalProg (n : var .nat) (G : var (Ty.group D)) : Prog (groupSig D) rec var (.array .nat) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (.op2 .pair G n) fun Gn =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbitTransversal Gn) fun tr =>
  .bind (Prog.call (S := groupSig D) GroupOp.stabilizer Gn) fun H =>
  .bind (rangeFromProg n m) fun pts => .bind (mkWindow N pts) fun w =>
  .bind (.op2 .pair H w) fun Hw =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits Hw) fun os =>
  .bind (blockIdxProg N os) fun oi =>
  .bind (.op0 .nil) fun e => .bind (.op1 .arrayOfList e) fun ea =>
  .bind (.op2 .pair ea ea) fun p₀ =>
  .bind (.op2 .arrayMk N p₀) fun blank =>
  .bind (.prim .arrayUpdate (.cons blank (.cons tr .nil))) fun TA =>
  matrixProg m fun u _ v => orbEntryProg n oi TA u v

/-- The colour `0` on the diagonal, `1` where the entry of `L` is `c`, `2` elsewhere. -/
def relEntryProg (L : var (.array .nat)) (c : var .nat) (u off v : var .nat) :
    Prog S rec var .nat :=
  .bind (.op2 .natEq u v) fun e =>
  .ite e (.op0 (.natLit 0))
    (.bind (.op2 .add off v) fun i => .bind (.op2 .arrayGet L i) fun x =>
     .bind (.op2 .natEq x c) fun e' => .ite e' (.op0 (.natLit 1)) (.op0 (.natLit 2)))

/-- **The colouring by the orbital of `(a, b)`**, from an `m × m` array `L`. -/
def relColProg (L : var (.array .nat)) (m a b : var .nat) : Prog S rec var (.array .nat) :=
  .bind (mulProg a m) fun am => .bind (.op2 .add am b) fun ab =>
  .bind (.op2 .arrayGet L ab) fun c =>
  matrixProg m fun u off v => relEntryProg L c u off v

end Programs

/-! ### Specs of the array programs -/

/-- The cost of `matrixProg` for `m` rows and entries of cost `c`. -/
def matrixCost (m c : ℕ) : ℕ := m * (m * (c + 3) + 7) + m * (m + 2) + m * m + 11 * m + 13

section ArraySpecs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

theorem foldl_rows (m : ℕ) : ∀ k,
    (List.range k).foldl (fun (st : ℕ × List (ℕ × ℕ)) u => (st.1 + m, (u, st.1) :: st.2)) (0, []) =
      (k * m, ((List.range k).map fun u => (u, u * m)).reverse)
  | 0 => by simp
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, foldl_rows m k]
    simp [Nat.succ_mul]

theorem RunsWithin.rowsProg (m : ℕ) :
    RunsWithin X body (Toolkit.rowsProg m) ((List.range m).map fun u => (u, u * m))
      (9 * m + 7) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat (.list (.prod .nat .nat)))
    (f := fun st u => Prog.bind (.op1 .fst st) fun off => .bind (.op1 .snd st) fun acc =>
      .bind (.op2 .pair u off) fun p => .bind (.op2 .cons p acc) fun acc' =>
      .bind (.op2 .add off m) fun off' => .op2 .pair off' acc')
    (F := fun st u => (st.1 + m, (u, st.1) :: st.2)) (cf := fun _ => 6) (List.range m) (0, [])
    fun st u _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
  rw [foldl_rows, sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le (by simp [Prim.eval]) le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, List.length_reverse,
      List.length_map]
    omega

theorem RunsWithin.mulProg (a' m : ℕ) :
    RunsWithin X body (Toolkit.mulProg a' m) (a' * m) (3 * a' + 2) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat) (b' := .nat)
    (f := fun acc _ => Prog.op2 .add acc m) (F := fun acc _ => acc + m) (cf := fun _ => 1)
    (List.range a') 0 fun acc _ _ => RunsWithin.prim _ _
  have e : ∀ k, (List.range k).foldl (fun acc _ => acc + m) 0 = k * m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [List.range_succ, List.foldl_append, ih]; simp [Nat.succ_mul]
  rw [e, sum_map_const] at hfold
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hfold
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_range]
    omega

theorem foldl_append_rev : ∀ (rows : List (List ℕ)),
    rows.reverse.foldl (fun acc row => row ++ acc) [] = rows.flatten := by
  intro rows
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.reverse_cons, List.foldl_append, ih]
    simp

/-- **Square arrays from an entry program**: if the entry program at row `u`, offset `u m` and
column `v` computes `F u v` at cost `c`, `matrixProg` computes `matrixOf m F`. -/
theorem RunsWithin.matrixProg {m c : ℕ} {f : ℕ → ℕ → ℕ → Prog S (a, b) Ty.denote .nat}
    {F : ℕ → ℕ → ℕ} (hf : ∀ u < m, ∀ v < m, RunsWithin X body (f u (u * m) v) (F u v) c) :
    RunsWithin X body (Toolkit.matrixProg m f) (matrixOf m F) (matrixCost m c) := by
  have hrows := RunsWithin.rowsProg (X := X) (body := body) m
  have hmap := RunsWithin.mapList_le (X := X) (body := body) (a' := .prod .nat .nat)
    (b' := .list .nat) (xs := (List.range m).map fun u => (u, u * m))
    (f := fun p => Prog.bind (.op1 .fst p) fun u => .bind (.op1 .snd p) fun off =>
      mapList (a' := .nat) (b' := .nat) (List.range m : (Ty.list .nat).denote) fun v => f u off v)
    (F := fun p => (List.range m).map (F p.1)) (c := m * (c + 3) + 4) fun p hp => by
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hp
      rw [List.mem_range] at hu
      have hin : RunsWithin X body
          (mapList (a' := .nat) (b' := .nat) (List.range m : (Ty.list .nat).denote)
            fun v => f u (u * m) v)
          ((List.range m).map (F u)) ((List.range m).length * (c + 3) + 2) :=
        RunsWithin.mapList_le fun v hv => hf u hu v (List.mem_range.1 hv)
      rw [List.length_range] at hin
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact hin
      case hc =>
        simp only [Prim.cost]
        omega
  set rows := ((List.range m).map fun u => (u, u * m)).map fun p => (List.range m).map (F p.1)
    with hrowsdef
  have hlen : ∀ r ∈ rows.reverse, r.length = m := by
    intro r hr
    rw [List.mem_reverse, hrowsdef, List.mem_map] at hr
    obtain ⟨p, -, rfl⟩ := hr
    simp
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .list .nat)
    (b' := .list .nat) (f := fun acc row => Prog.op2 .append row acc)
    (F := fun acc row => row ++ acc) (cf := fun row => row.length + 1) rows.reverse []
    fun acc row _ => RunsWithin.prim_le rfl (by simp [Prim.cost])
  have hsum : (rows.reverse.map fun row => row.length + 1 + 1).sum = m * (m + 2) := by
    rw [List.map_congr_left (g := fun _ => m + 2) fun r hr => by rw [hlen r hr]]
    rw [sum_map_const]
    simp [hrowsdef]
  rw [foldl_append_rev, hsum] at hfold
  have hflat : rows.flatten.length = m * m := by
    rw [List.length_flatten, List.map_congr_left (g := fun _ => m)
      fun r hr => hlen r (List.mem_reverse.2 hr), sum_map_const]
    simp [hrowsdef]
  have hval : rows.flatten.toArray = matrixOf m F := by
    simp [hrowsdef, matrixOf, List.map_map, Function.comp_def]
  apply RunsWithin.mono
  case h =>
    run_step hrows
    run_step (RunsWithin.prim _ _)
    run_step hmap
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    exact RunsWithin.prim_le (by simp [Prim.eval, hval]) le_rfl
  case hc =>
    have hrl : rows.length = m := by simp [hrowsdef]
    have e7 : m * (m * (c + 3) + 4 + 3) = m * (m * (c + 3) + 7) := by ring
    simp only [Prim.cost, Args.head_cons, List.length_range, List.length_map, hflat,
      matrixCost]
    omega

theorem RunsWithin.orbEntryProg (n : ℕ) (oi : Array ℕ) (TA : Array PermData) (u v : ℕ) :
    RunsWithin X body (Toolkit.orbEntryProg n oi TA u v)
      (get oi (get (TA.getD (n + u) (#[], #[])).2 (n + v))) 6 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

end ArraySpecs

/-- A list of nonempty lists has at most as many members as entries. -/
theorem length_le_length_flatten : ∀ (os : List (List ℕ)), (∀ o ∈ os, o ≠ []) →
    os.length ≤ os.flatten.length
  | [], _ => by simp
  | o :: rest, hne => by
    have h1 : 1 ≤ o.length := List.length_pos_iff.2 (hne o List.mem_cons_self)
    have h2 := length_le_length_flatten rest fun o' ho' => hne o' (List.mem_cons_of_mem _ ho')
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-! ### Writes into arrays -/

theorem getD_foldl_set_of_not_mem {α : Type} (d : α) :
    ∀ (ws : List (ℕ × α)) (arr : Array α) {k : ℕ}, k ∉ ws.map Prod.fst →
      (ws.foldl (fun arr w => arr.setIfInBounds w.1 w.2) arr).getD k d = arr.getD k d
  | [], arr, k, _ => rfl
  | w :: ws, arr, k, hk => by
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [List.foldl_cons]
    rw [getD_foldl_set_of_not_mem d ws _ hk.2]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, Ne.symm hk.1,
      ↓reduceIte]

theorem getD_foldl_set_of_mem {α : Type} (d : α) :
    ∀ (ws : List (ℕ × α)) (arr : Array α) {k : ℕ} {x : α}, (ws.map Prod.fst).Nodup →
      (k, x) ∈ ws → k < arr.size →
      (ws.foldl (fun arr w => arr.setIfInBounds w.1 w.2) arr).getD k d = x
  | [], arr, k, x, _, hmem, _ => by simp at hmem
  | w :: ws, arr, k, x, hnd, hmem, hk => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hmem with h | h
    · subst h
      rw [getD_foldl_set_of_not_mem d ws _ hnd.1]
      simp [Array.getD_eq_getD_getElem?, hk]
    · exact getD_foldl_set_of_mem d ws _ hnd.2 h (by simpa using hk)

/-! ### The orbital model -/

section OrbitalModel

variable {D : Ty}

/-- The transversal elements, by position. -/
def transArr (N : ℕ) (tr : List (ℕ × PermData)) : Array PermData :=
  Prim.applyWrites (a := Ty.perm) (Array.replicate N ((#[], #[]) : PermData)) tr

/-- The orbital index of `(u, v)`: the orbit index of `r_u⁻¹ (n + v)`. -/
def orbEntry (n : ℕ) (oi : Array ℕ) (TA : Array PermData) (u v : ℕ) : ℕ :=
  get oi (get (TA.getD (n + u) (#[], #[])).2 (n + v))

/-- The orbits of the stabilizer of the first base position, as computed by the backend. -/
def orbitsModel (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : List (List ℕ) :=
  O.run .orbits (O.run .stabilizer (G, n), WinData.ofPoints G.1 (basePts n G.1))

/-- The model of `orbitalProg`. -/
def orbitalModel (O : Oracle (groupSig D)) (n : ℕ) (G : GroupData D.denote) : Array ℕ :=
  matrixOf (G.1 - n)
    (orbEntry n (blockIdx G.1 (orbitsModel O n G)) (transArr G.1 (O.run .orbitTransversal (G, n))))

end OrbitalModel

/-- The operations the orbital program calls. -/
def orbitalOps (op : GroupOp) : Prop :=
  op = .orbitTransversal ∨ op = .stabilizer ∨ op = .orbits

/-- The cost of `orbitalProg`. -/
def orbitalCost (N m Btr Bstab Borb : ℕ) : ℕ :=
  Btr + Bstab + Borb + matrixCost m 6 + 7 * N + 25 * m + 30

section OrbitalSpecs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- **The cost of the orbital configuration.** -/
theorem RunsWithin.orbitalProg (hO : MeetsContractOn DV orbitalOps X.O)
    (hPre : ∀ op x, orbitalOps op → GroupPre DV op x → X.Pre op x)
    {N s n : ℕ} {G₀ : Subgroup (Perm (Fin N))} (B : BackendBounds X DV N s G₀)
    {gs : GensData} {d : D.denote} (hG : GroupValid DV N gs d) (hs : gs.length ≤ s)
    (hG₀ : GensData.denote N gs ≤ G₀)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n < N) :
    RunsWithin X body (Toolkit.orbitalProg n (N, gs, d)) (orbitalModel X.O n (N, gs, d))
      (orbitalCost N (N - n) B.Btr B.Bstab B.Borb) := by
  set G := GensData.denote N gs with hGdef
  have hpre₁ : GroupPre DV GroupOp.orbitTransversal ((N, gs, d), n) := ⟨hG, hn⟩
  have hpre₂ : GroupPre DV GroupOp.stabilizer ((N, gs, d), n) := ⟨hG, hn⟩
  have hctr := B.transversal gs d n hs hG₀ hpre₁
  have hcst := B.stabilizer gs d n hs hG₀ hpre₂
  have htrpost := hO GroupOp.orbitTransversal _ (Or.inl rfl) hpre₁
  have hstpost := hO GroupOp.stabilizer _ (Or.inr (Or.inl rfl)) hpre₂
  have hout := B.stabOut gs d n hG₀ hpre₂
  -- the length of the transversal
  have htrlen : (X.O.run GroupOp.orbitTransversal ((N, gs, d), n)).length ≤ N := by
    obtain ⟨hnd, hiff, -⟩ := htrpost
    have hsub : (X.O.run GroupOp.orbitTransversal ((N, gs, d), n)).map Prod.fst ⊆
        List.range N := fun j hj => List.mem_range.2 ((hiff j).1 hj).2.1
    have h1 := (hnd.subperm hsub).length_le
    have h2 : (List.map Prod.fst (X.O.run GroupOp.orbitTransversal ((N, gs, d), n) :
        List (ℕ × PermData))).length =
        (X.O.run GroupOp.orbitTransversal ((N, gs, d), n) : List (ℕ × PermData)).length :=
      List.length_map _
    have h3 : (List.range N).length = N := List.length_range
    omega
  rcases hH : X.O.run GroupOp.stabilizer ((N, gs, d), n) with ⟨N', hs', e⟩
  rw [hH] at hstpost hout hcst
  obtain ⟨hN', hHv, hHden⟩ := hstpost
  change N' = N at hN'
  subst hN'
  have hHG : GensData.denote N' hs' ≤ G := by
    rw [hHden hn]
    exact inf_le_left
  have hwv : (WinData.ofPoints N' (basePts n N')).Valid N' :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hpre₃ : GroupPre DV GroupOp.orbits ((N', hs', e), WinData.ofPoints N' (basePts n N')) :=
    ⟨hHv, hwv, by
      rw [denote_basePts]
      exact fun g hg u hu => hinv g (hHG hg) u hu⟩
  have hcorb := B.orbits hs' e _ hout (hHG.trans hG₀) hpre₃
  have hopost := hO GroupOp.orbits _ (Or.inr (Or.inr rfl)) hpre₃
  set os : List (List ℕ) :=
    X.O.run GroupOp.orbits ((N', hs', e), WinData.ofPoints N' (basePts n N')) with hos
  have hflat : os.flatten.length = N' - n := by
    rw [hopost.1.length_eq, WinData.ofPoints_fst, length_basePts]
  have hoslen : os.length ≤ N' - n := by
    rw [← hflat]
    exact length_le_length_flatten os fun o ho => (hopost.2 o ho).1
  have hmat := RunsWithin.matrixProg (X := X) (body := body) (m := N' - n) (c := 6)
    (f := fun u _ v => Toolkit.orbEntryProg n (blockIdx N' os)
      (transArr N' (X.O.run GroupOp.orbitTransversal ((N', gs, d), n))) u v)
    (F := orbEntry n (blockIdx N' os)
      (transArr N' (X.O.run GroupOp.orbitTransversal ((N', gs, d), n))))
    fun u _ v _ => RunsWithin.orbEntryProg _ _ _ _ _
  have hval : orbitalModel X.O n (N', gs, d) = matrixOf (N' - n) (orbEntry n (blockIdx N' os)
      (transArr N' (X.O.run GroupOp.orbitTransversal ((N', gs, d), n)))) := by
    simp only [orbitalModel, orbitsModel, hH, os]
  rw [hval]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call (hPre _ _ (Or.inl rfl) hpre₁))
    run_step (RunsWithin.call (hPre _ _ (Or.inr (Or.inl rfl)) hpre₂))
    simp only [Prim.eval]
    rw [hH]
    run_step (RunsWithin.rangeFromProg _ _)
    run_step (RunsWithin.mkWindow _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call (hPre _ _ (Or.inr (Or.inr rfl)) hpre₃))
    run_step (RunsWithin.blockIdxProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hmat
  case hc =>
    have hrl : (basePts n N').length = N' - n := length_basePts n N'
    have hpairEq : Prim.eval (Prim.pair (a := (groupSig D).res GroupOp.stabilizer) (b := Ty.win))
        (Args.cons (N', hs', e) (Args.cons
          (WinData.ofPoints N' (List.map (fun x => n + x) (List.range (N' - n)))) Args.nil)) =
        ((N', hs', e), WinData.ofPoints N' (basePts n N')) := rfl
    have hcostU : ∀ (A : (Ty.array Ty.perm).denote) (W : (Ty.list (.prod .nat Ty.perm)).denote),
        Prim.cost (Prim.arrayUpdate (a := Ty.perm)) (Args.cons A (Args.cons W Args.nil)) =
          A.size + W.length + 1 := fun _ _ => rfl
    rw [hpairEq, ← hos]
    erw [hcostU]
    simp only [Prim.cost, Prim.eval, Args.head_cons, hflat, hH,
      Array.size_replicate, List.length_nil, orbitalCost, List.length_map, List.length_range]
    omega

/-- The stored transversal element at a point of the orbit of `n`. -/
theorem transArr_spec {N n : ℕ} {G : Subgroup (Perm (Fin N))} {tr : List (ℕ × PermData)}
    (hnd : (tr.map Prod.fst).Nodup) (hiff : ∀ j, j ∈ tr.map Prod.fst ↔ SameOrbit G n j)
    (hall : ∀ vr ∈ tr, PermData.Valid N vr.2 ∧ PermData.denote N vr.2 ∈ G ∧ get vr.2.1 n = vr.1)
    {k : ℕ} (hk : SameOrbit G n k) :
    PermData.Valid N ((transArr N tr).getD k (#[], #[])) ∧
      PermData.denote N ((transArr N tr).getD k (#[], #[])) ∈ G ∧
      get ((transArr N tr).getD k (#[], #[])).1 n = k := by
  obtain ⟨⟨k', pr⟩, hmem, hk'⟩ := List.mem_map.1 ((hiff k).2 hk)
  simp only at hk'
  subst hk'
  obtain ⟨-, hlt, -⟩ := hk
  have hget : (transArr N tr).getD k' (#[], #[]) = pr :=
    getD_foldl_set_of_mem _ tr _ hnd hmem (by simpa using hlt)
  rw [hget]
  exact hall _ hmem

theorem basePos_injective {n N : ℕ} : Function.Injective (basePos (n := n) (N := N)) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [basePos] at this
  exact Fin.ext (by omega)

/-- **The meaning of the orbital configuration**: for a transitive base action, two entries are
equal exactly when the pairs lie in one orbital. -/
theorem orbitalModel_spec (hO : MeetsContractOn DV orbitalOps X.O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n < N)
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hinv g γ = δ) (u v u' v' : Fin (N - n)) :
    get (orbitalModel X.O n (N, gs, d)) (u.val * (N - n) + v.val) =
        get (orbitalModel X.O n (N, gs, d)) (u'.val * (N - n) + v'.val) ↔
      ∃ g : ↥(baseHom (GensData.denote N gs) n hinv).range, g • u = u' ∧ g • v = v' := by
  have hpos : 0 < N - n := by omega
  obtain ⟨hnd, hiff, hall⟩ := hO GroupOp.orbitTransversal ((N, gs, d), n) (Or.inl rfl) ⟨hG, hn⟩
  set tr : List (ℕ × PermData) := X.O.run GroupOp.orbitTransversal ((N, gs, d), n) with htr'
  -- the transversal elements `ρ u` with `ρ u (n) = n + u`
  have hsame : ∀ u : Fin (N - n), SameOrbit (GensData.denote N gs) n (n + u.val) := by
    intro u
    obtain ⟨g, hg⟩ := htr ⟨0, hpos⟩ u
    have h1 := baseHom_apply (hG := hinv) g ⟨0, hpos⟩
    rw [hg] at h1
    refine ⟨hn, by omega, g.1, g.2, ?_⟩
    have h2 := congrArg Fin.val h1
    simp only [basePos, Nat.add_zero] at h2
    exact Fin.ext h2.symm
  have hρ := fun u : Fin (N - n) => transArr_spec hnd hiff hall (hsame u)
  set P : Fin (N - n) → PermData := fun u => (transArr N tr).getD (n + u.val) (#[], #[])
    with hPdef
  set ρ : Fin (N - n) → Perm (Fin N) := fun u => PermData.denote N (P u) with hρdef
  have hρG : ∀ u, ρ u ∈ (GensData.denote N gs) := fun u => (hρ u).2.1
  have hρn : ∀ u, ρ u ⟨n, hn⟩ = basePos u := fun u =>
    Fin.ext (by rw [PermData.val_denote_apply (hρ u).1]; exact (hρ u).2.2)
  have hρn' : ∀ u, (ρ u)⁻¹ (basePos u) = ⟨n, hn⟩ := fun u => by
    rw [Perm.inv_eq_iff_eq, hρn]
  have hρinv : ∀ u (x : Fin N), ρ u ((ρ u)⁻¹ x) = x := fun u x => (ρ u).apply_symm_apply x
  -- the stabilizer and its orbits
  have hstpost := hO GroupOp.stabilizer ((N, gs, d), n) (Or.inr (Or.inl rfl)) ⟨hG, hn⟩
  rcases hH : X.O.run GroupOp.stabilizer ((N, gs, d), n) with ⟨N', hs', e⟩
  rw [hH] at hstpost
  obtain ⟨hN', hHv, hHden⟩ := hstpost
  change N' = N at hN'
  subst N'
  have hK : GensData.denote N hs' = pointStab (GensData.denote N gs) ⟨n, hn⟩ := hHden hn
  have hwv : (WinData.ofPoints N (basePts n N)).Valid N :=
    WinData.valid_ofPoints (basePts_nodup _ _) fun i hi => (mem_basePts.1 hi).2
  have hpre₃ : GroupPre DV GroupOp.orbits ((N, hs', e), WinData.ofPoints N (basePts n N)) :=
    ⟨hHv, hwv, by
      rw [denote_basePts, hK]
      exact fun g hg u hu => hinv g (mem_pointStab.1 hg).1 u hu⟩
  have hpart := hO GroupOp.orbits _ (Or.inr (Or.inr rfl)) hpre₃
  set os : List (List ℕ) :=
    X.O.run GroupOp.orbits ((N, hs', e), WinData.ofPoints N (basePts n N)) with hos
  have hbl : IsBlockList (WinData.ofPoints N (basePts n N)) os :=
    ⟨hpart.1, fun o ho => (hpart.2 o ho).1⟩
  -- block indices of base points
  have hidx : ∀ x : Fin N, x ∈ baseSet n N → ∃ t, ∃ ht : t < os.length,
      x.val ∈ os[t] ∧ get (blockIdx N os) x.val = t := by
    intro x hx
    have hxw : x.val ∈ (WinData.ofPoints N (basePts n N)).1 := by
      rw [WinData.ofPoints_fst]
      exact mem_basePts.2 ⟨hx, x.2⟩
    obtain ⟨t, ht, hxt⟩ := GraphIso.exists_block hbl hxw
    exact ⟨t, ht, hxt, get_blockIdx hwv hbl ht hxt⟩
  have hidx_eq : ∀ x y : Fin N, x ∈ baseSet n N → y ∈ baseSet n N →
      (get (blockIdx N os) x.val = get (blockIdx N os) y.val ↔
        ∃ h ∈ pointStab (GensData.denote N gs) ⟨n, hn⟩, h x = y) := by
    intro x y hx hy
    obtain ⟨t, ht, hxt, hxi⟩ := hidx x hx
    have hor := (hpart.2 os[t] (List.getElem_mem ht)).2 x.val hxt y.val
    rw [hK] at hor
    constructor
    · intro hxy
      obtain ⟨t', ht', hyt, hyi⟩ := hidx y hy
      rw [hxi, hyi] at hxy
      subst hxy
      obtain ⟨_, _, h, hh, hhe⟩ := hor.1 hyt
      exact ⟨h, hh, hhe⟩
    · rintro ⟨h, hh, hhe⟩
      have hyt : y.val ∈ os[t] := hor.2 ⟨x.2, y.2, h, hh, hhe⟩
      rw [hxi, get_blockIdx hwv hbl ht hyt]
  -- the entries
  have hentry : ∀ u v : Fin (N - n), get (orbitalModel X.O n (N, gs, d))
      (u.val * (N - n) + v.val) = get (blockIdx N os) ((ρ u)⁻¹ (basePos v)).val := by
    intro u v
    have hval : orbitalModel X.O n (N, gs, d) = matrixOf (N - n)
        (orbEntry n (blockIdx N os) (transArr N tr)) := by
      simp only [orbitalModel, orbitsModel, hH, os, tr]
    rw [hval, get_matrixOf u.2 v.2, orbEntry, PermData.val_denote_inv_apply (hρ u).1]
    rfl
  have hbase : ∀ u v : Fin (N - n), (ρ u)⁻¹ (basePos v) ∈ baseSet n N := fun u v =>
    hinv _ (inv_mem (hρG u)) _ (basePos_mem v)
  rw [hentry, hentry, hidx_eq _ _ (hbase u v) (hbase u' v')]
  constructor
  · rintro ⟨h, hh, hhe⟩
    obtain ⟨hhG, hhn⟩ := mem_pointStab.1 hh
    have hg : ρ u' * h * (ρ u)⁻¹ ∈ GensData.denote N gs :=
      mul_mem (mul_mem (hρG u') hhG) (inv_mem (hρG u))
    refine ⟨⟨baseHom (GensData.denote N gs) n hinv ⟨_, hg⟩, ⟨_, hg⟩, rfl⟩, ?_, ?_⟩
    · apply basePos_injective
      change basePos (baseHom (GensData.denote N gs) n hinv ⟨_, hg⟩ u) = _
      rw [baseHom_apply]
      change ρ u' (h ((ρ u)⁻¹ (basePos u))) = _
      rw [hρn', hhn, hρn]
    · apply basePos_injective
      change basePos (baseHom (GensData.denote N gs) n hinv ⟨_, hg⟩ v) = _
      rw [baseHom_apply]
      change ρ u' (h ((ρ u)⁻¹ (basePos v))) = _
      rw [hhe, hρinv]
  · rintro ⟨⟨g', g, rfl⟩, hgu, hgv⟩
    have hgu' : g.1 (basePos u) = basePos u' := by
      rw [← baseHom_apply (hG := hinv)]
      exact congrArg basePos hgu
    have hgv' : g.1 (basePos v) = basePos v' := by
      rw [← baseHom_apply (hG := hinv)]
      exact congrArg basePos hgv
    refine ⟨(ρ u')⁻¹ * g.1 * ρ u, mem_pointStab.2 ⟨mul_mem (mul_mem (inv_mem (hρG u')) g.2)
      (hρG u), ?_⟩, ?_⟩
    · rw [Perm.mul_apply, Perm.mul_apply, hρn, hgu', hρn']
    · rw [Perm.mul_apply, Perm.mul_apply, hρinv, hgv']

end OrbitalSpecs

/-! ### The colouring by one orbital -/

/-- The colour of `(u, v)` by the relation `L[u m + v] = L[a m + b]` of an `m × m` array: `0`
on the diagonal, `1` in the relation, `2` otherwise. -/
def relColEntry (L : Array ℕ) (m a b u v : ℕ) : ℕ :=
  if u = v then 0 else if get L (u * m + v) = get L (a * m + b) then 1 else 2

/-- The model of `relColProg`. -/
def relColModel (L : Array ℕ) (m a b : ℕ) : Array ℕ := matrixOf m (relColEntry L m a b)

/-- The relation of the entry `(a, b)` of an `m × m` array: equal entries. -/
def arrRel (L : Array ℕ) (m a b : ℕ) (u v : Fin m) : Prop :=
  get L (u.val * m + v.val) = get L (a * m + b)

instance (L : Array ℕ) (m a b : ℕ) : DecidableRel (arrRel L m a b) :=
  fun u v => inferInstanceAs (Decidable (get L (u.val * m + v.val) = get L (a * m + b)))

/-- The cost of `relColProg`. -/
def relColCost (m a : ℕ) : ℕ := 3 * a + matrixCost m 7 + 4

section RelColSpecs

variable {S : Signature} {a' b' : Ty} {X : Ctx S}
  {body : a'.denote → Prog S (a', b') Ty.denote b'}

theorem RunsWithin.relEntryProg (L : Array ℕ) (m a b u v : ℕ) :
    RunsWithin X body (Toolkit.relEntryProg L (get L (a * m + b)) u (u * m) v)
      (relColEntry L m a b u v) 7 := by
  by_cases huv : u = v
  · have he : Prim.eval Prim.natEq (Args.cons u (Args.cons v Args.nil)) = true := by
      simp [Prim.eval, huv]
    rw [show relColEntry L m a b u v = 0 by simp [relColEntry, huv]]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      rw [he]
      exact RunsWithin.ite_true (RunsWithin.prim _ _)
    case hc => simp [Prim.cost]
  · have he : Prim.eval Prim.natEq (Args.cons u (Args.cons v Args.nil)) = false := by
      simp [Prim.eval, huv]
    by_cases hx : get L (u * m + v) = get L (a * m + b)
    · have he' : Prim.eval Prim.natEq (Args.cons (Prim.eval (Prim.arrayGet (a := .nat))
          (Args.cons L (Args.cons (Prim.eval Prim.add (Args.cons (u * m) (Args.cons v Args.nil)))
            Args.nil))) (Args.cons (get L (a * m + b)) Args.nil)) = true := by
        change (get L (u * m + v) == get L (a * m + b)) = true
        simp [hx]
      rw [show relColEntry L m a b u v = 1 by simp [relColEntry, huv, hx]]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        rw [he]
        apply RunsWithin.ite_false
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        rw [he']
        exact RunsWithin.ite_true (RunsWithin.prim _ _)
      case hc => simp [Prim.cost]
    · have he' : Prim.eval Prim.natEq (Args.cons (Prim.eval (Prim.arrayGet (a := .nat))
          (Args.cons L (Args.cons (Prim.eval Prim.add (Args.cons (u * m) (Args.cons v Args.nil)))
            Args.nil))) (Args.cons (get L (a * m + b)) Args.nil)) = false := by
        change (get L (u * m + v) == get L (a * m + b)) = false
        simp [hx]
      rw [show relColEntry L m a b u v = 2 by simp [relColEntry, huv, hx]]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        rw [he]
        apply RunsWithin.ite_false
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        rw [he']
        exact RunsWithin.ite_false (RunsWithin.prim _ _)
      case hc => simp [Prim.cost]

/-- **The cost of the orbital colouring.** -/
theorem RunsWithin.relColProg (L : Array ℕ) (m a b : ℕ) :
    RunsWithin X body (Toolkit.relColProg L m a b) (relColModel L m a b) (relColCost m a) := by
  have hmat := RunsWithin.matrixProg (X := X) (body := body) (m := m) (c := 7)
    (f := fun u off v => Toolkit.relEntryProg L (get L (a * m + b)) u off v)
    (F := relColEntry L m a b) fun u _ v _ => RunsWithin.relEntryProg L m a b u v
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mulProg _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hmat
  case hc =>
    simp only [Prim.cost, relColCost]
    omega

end RelColSpecs

/-- **The meaning of the colouring**: the entry `(u, v)` of `relColModel` is `relCol` of the
relation `arrRel`. -/
theorem relColModel_spec (L : Array ℕ) {m : ℕ} (a b : ℕ) (u v : Fin m) :
    get (relColModel L m a b) (u.val * m + v.val) = relCol (arrRel L m a b) u v := by
  rw [relColModel, get_matrixOf u.2 v.2]
  unfold relColEntry relCol
  by_cases huv : u = v
  · subst huv
    simp
  · have huv' : u.val ≠ v.val := fun h => huv (Fin.ext h)
    by_cases hx : arrRel L m a b u v
    · have hx' : get L (u.val * m + v.val) = get L (a * m + b) := hx
      simp [huv, huv', hx, hx']
    · have hx' : get L (u.val * m + v.val) ≠ get L (a * m + b) := hx
      simp [huv, huv', hx, hx']

/-- **The relation of an orbital entry is the orbital**: for a transitive base action, the
relation `arrRel` of the orbital array at `(a, b)` is the orbital of `(a, b)`, the hypothesis
`hR` of `wlRel_spec`. -/
theorem arrRel_orbital {D : Ty} {X : Ctx (groupSig D)} {DV : ℕ → GensData → D.denote → Prop}
    (hO : MeetsContractOn DV orbitalOps X.O) {N n : ℕ} {gs : GensData}
    {d : D.denote} (hG : GroupValid DV N gs d)
    (hinv : IsInvariant (GensData.denote N gs) (baseSet n N)) (hn : n < N)
    (htr : ∀ γ δ : Fin (N - n), ∃ g : ↥(GensData.denote N gs),
      baseHom (GensData.denote N gs) n hinv g γ = δ) (a b u v : Fin (N - n)) :
    arrRel (orbitalModel X.O n (N, gs, d)) (N - n) a b u v ↔
      ∃ g : ↥(baseHom (GensData.denote N gs) n hinv).range, g • a = u ∧ g • b = v := by
  unfold arrRel
  rw [eq_comm]
  exact orbitalModel_spec hO hG hinv hn htr a b u v

/-! ### Well-formedness -/

section Wf

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_orbitalProg {n₁ : var₁ .nat} {n₂ : var₂ .nat} {G₁ : var₁ (Ty.group D)}
    {G₂ : var₂ (Ty.group D)} (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) :
    Prog.Wf (S := groupSig D) (rec := rec) r Γ (orbitalProg n₁ G₁) (orbitalProg n₂ G₂) := by
  unfold orbitalProg matrixProg rowsProg orbEntryProg rangeFromProg mkWindow blockIdxProg
    mapList
  prog_wf

theorem wf_relColProg {L₁ : var₁ (.array .nat)} {L₂ : var₂ (.array .nat)} {m₁ a₁ b₁ : var₁ .nat}
    {m₂ a₂ b₂ : var₂ .nat} (hL : ⟨.array .nat, L₁, L₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (ha : ⟨.nat, a₁, a₂⟩ ∈ Γ) (hb : ⟨.nat, b₁, b₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (relColProg L₁ m₁ a₁ b₁) (relColProg L₂ m₂ a₂ b₂) := by
  unfold relColProg mulProg matrixProg rowsProg relEntryProg mapList
  prog_wf

end Wf

end GraphIso.Toolkit
