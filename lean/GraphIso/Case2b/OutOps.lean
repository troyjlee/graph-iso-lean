module

public import GraphIso.Align.PartOps
public import GraphIso.Align.JohnOps

/-!
# Leaves of Split-or-Johnson as structures for Align

Stage 14h, item 2 (`PLAN-14.md` §12). The leaves of Case 2b are stage 14d's leaf data `OutD`:
tag `1` a colored partition (`cpartOf`), tag `2` a trimmed Johnson embedding (`jembOf`).
`outOps` makes them structures for Align (stage 14f's `StructOps`):

* the stabilizer generators and the isomorphism search of `partOps` or `johnOps` on the
  component of the tag, and no isomorphism between leaves of different tags;
* `OutValid`: a colored partition with `PartValid`, or a trimmed Johnson embedding with `JValid`;
* `outOps_spec`: the specification Align needs. `Perm (Fin m)` acts on
  `Option (Out (Fin m))` componentwise, so stabilizers and isomorphisms reduce to the component,
  and no permutation carries a colored partition to a Johnson embedding.
* `outGensProg`, `outIsoProg`: programs dispatching on the tag to stage 14f's programs, with
  `RunsWithin` specs and polynomial costs (`outGensCost_le`, `outIsoCost_le`).
-/

@[expose] public section

namespace GraphIso.Case2b

open Equiv GraphIso GraphIso.SplitJohnson GraphIso.SoJProg GraphIso.SoJTree GraphIso.Align
  GraphIso.Cost GraphIso.Programs GraphIso.Sims

/-! ### The operations -/

section Ops

/-- The stabilizer generators of a leaf, by its tag. -/
def outGensD (m : ℕ) (o : OutD) : List PermData :=
  if o.1 = 1 then partGensD m o.2.1 else if o.1 = 2 then johnGensD m o.2.2 else []

/-- An isomorphism of two leaves, by their tags (none across tags). -/
def outIsoD (m : ℕ) (o o' : OutD) : Option PermData :=
  if o.1 = 1 then (if o'.1 = 1 then isoPartD m o.2.1 o'.2.1 else none)
  else if o.1 = 2 then (if o'.1 = 2 then johnIsoD m o.2.2 o'.2.2 else none)
  else none

/-- **Leaves as structures for Align.** -/
def outOps (m : ℕ) : StructOps m OutD (Option (Out (Fin m))) where
  dec := decodeOut m
  gens := outGensD m
  iso := outIsoD m

/-- The representation invariant: a valid colored partition or a valid trimmed Johnson
embedding. -/
def OutValid (m : ℕ) (o : OutD) : Prop :=
  (o.1 = 1 ∧ PartValid m o.2.1) ∨ (o.1 = 2 ∧ JValid m o.2.2)

variable {m : ℕ}

theorem oo_dec_one {o : OutD} (h : o.1 = 1) :
    decodeOut m o = some (Sum.inl ((partOps m).dec o.2.1)) :=
  ld_decodeOut_one h

theorem oo_dec_two {o : OutD} (h : o.1 = 2) :
    decodeOut m o = some (Sum.inr ((johnOps m).dec o.2.2)) :=
  ld_decodeOut_two h

theorem oo_smul_inl (σ : Perm (Fin m)) (p : CPart (Fin m)) :
    σ • (some (Sum.inl p) : Option (Out (Fin m))) = some (Sum.inl (σ • p)) := by
  rw [Option.smul_some, Sum.smul_inl]

theorem oo_smul_inr (σ : Perm (Fin m)) (J : JEmb (Fin m)) :
    σ • (some (Sum.inr J) : Option (Out (Fin m))) = some (Sum.inr (σ • J)) := by
  rw [Option.smul_some, Sum.smul_inr]

theorem oo_stab_inl (p : CPart (Fin m)) :
    MulAction.stabilizer (Perm (Fin m)) (some (Sum.inl p) : Option (Out (Fin m))) =
      MulAction.stabilizer (Perm (Fin m)) p := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, oo_smul_inl]
  constructor
  · intro h
    exact Sum.inl_injective (Option.some_injective _ h)
  · intro h
    rw [h]

theorem oo_stab_inr (J : JEmb (Fin m)) :
    MulAction.stabilizer (Perm (Fin m)) (some (Sum.inr J) : Option (Out (Fin m))) =
      MulAction.stabilizer (Perm (Fin m)) J := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, oo_smul_inr]
  constructor
  · intro h
    exact Sum.inr_injective (Option.some_injective _ h)
  · intro h
    rw [h]

/-- **Leaves satisfy what Align needs.** -/
theorem outOps_spec (m : ℕ) : (outOps m).Spec (OutValid m) where
  gens_valid := by
    rintro o (⟨h1, hv⟩ | ⟨h2, hv⟩) g hg
    · simp only [outOps, outGensD, h1, ite_true] at hg
      exact (partOps_spec m).gens_valid _ hv g hg
    · simp only [outOps, outGensD, h2, ite_true] at hg
      exact (johnOps_spec m).gens_valid _ hv g hg
  gens_closure := by
    rintro o (⟨h1, hv⟩ | ⟨h2, hv⟩)
    · have hg : (outOps m).gens o = (partOps m).gens o.2.1 := by
        simp only [outOps, outGensD, h1, ite_true]; rfl
      show Subgroup.closure _ = MulAction.stabilizer _ (decodeOut m o)
      rw [oo_dec_one h1, oo_stab_inl, ← (partOps_spec m).gens_closure _ hv, hg]
    · have hg : (outOps m).gens o = (johnOps m).gens o.2.2 := by
        simp only [outOps, outGensD, h2, ite_true]; rfl
      show Subgroup.closure _ = MulAction.stabilizer _ (decodeOut m o)
      rw [oo_dec_two h2, oo_stab_inr, ← (johnOps_spec m).gens_closure _ hv, hg]
  iso_some := by
    rintro o o' (⟨h1, hv⟩ | ⟨h2, hv⟩) (⟨h1', hv'⟩ | ⟨h2', hv'⟩) σ hσ
    · simp only [outOps, outIsoD, h1, h1', ite_true] at hσ
      obtain ⟨hval, hsm⟩ := (partOps_spec m).iso_some _ _ hv hv' σ hσ
      refine ⟨hval, ?_⟩
      show _ • decodeOut m o = decodeOut m o'
      rw [oo_dec_one h1, oo_dec_one h1', oo_smul_inl]
      exact congrArg (fun p => some (Sum.inl p)) hsm
    · have : o'.1 ≠ 1 := by omega
      simp only [outOps, outIsoD, h1, this, ite_true, ite_false] at hσ
      exact absurd hσ (by simp)
    · simp only [outOps, outIsoD, h2, h1', ite_true] at hσ
      exact absurd hσ (by simp)
    · simp only [outOps, outIsoD, h2, h2', ite_true] at hσ
      obtain ⟨hval, hsm⟩ := (johnOps_spec m).iso_some _ _ hv hv' σ hσ
      refine ⟨hval, ?_⟩
      show _ • decodeOut m o = decodeOut m o'
      rw [oo_dec_two h2, oo_dec_two h2', oo_smul_inr]
      exact congrArg (fun J => some (Sum.inr J)) hsm
  iso_none := by
    rintro o o' (⟨h1, hv⟩ | ⟨h2, hv⟩) (⟨h1', hv'⟩ | ⟨h2', hv'⟩) hn σ hσ
    · simp only [outOps, outIsoD, h1, h1', ite_true] at hn
      refine (partOps_spec m).iso_none _ _ hv hv' hn σ ?_
      have hσ' : σ • decodeOut m o = decodeOut m o' := hσ
      rw [oo_dec_one h1, oo_dec_one h1', oo_smul_inl] at hσ'
      exact Sum.inl_injective (Option.some_injective _ hσ')
    · have hσ' : σ • decodeOut m o = decodeOut m o' := hσ
      rw [oo_dec_one h1, oo_dec_two h2', oo_smul_inl] at hσ'
      exact absurd (Option.some_injective _ hσ') Sum.inl_ne_inr
    · have hσ' : σ • decodeOut m o = decodeOut m o' := hσ
      rw [oo_dec_two h2, oo_dec_one h1', oo_smul_inr] at hσ'
      exact absurd (Option.some_injective _ hσ') Sum.inr_ne_inl
    · simp only [outOps, outIsoD, h2, h2', ite_true] at hn
      refine (johnOps_spec m).iso_none _ _ hv hv' hn σ ?_
      have hσ' : σ • decodeOut m o = decodeOut m o' := hσ
      rw [oo_dec_two h2, oo_dec_two h2', oo_smul_inr] at hσ'
      exact Sum.inr_injective (Option.some_injective _ hσ')

/-! ### The number of generators -/

/-- A bound on the number of stabilizer generators of a valid leaf on `Fin m`. -/
def outGensB (m : ℕ) : ℕ := 3 * (m * m) + m

theorem oo_length_partGensD (m : ℕ) (x : Array ℕ × Array (List ℕ)) :
    (partGensD m x).length ≤ m * m + m := by
  have hW : (withinGensD m x.2).length ≤ m * m := by
    refine (po_length_flatMap_le _ fun r _ => ?_).trans
      (Nat.mul_le_mul_right m (po_length_reps m x.2))
    rw [List.length_map]
    exact (List.length_filter_le _ _).trans (po_length_blkL m x.2 r)
  have hE : (exchGensD m x.1 x.2).length ≤ m := by
    rw [exchGensD, List.length_map]
    exact (List.length_filter_le _ _).trans (po_length_reps m x.2)
  rw [partGensD, List.length_append]
  omega

/-- The cells of valid Johnson data have at most `m` points in all. -/
theorem oo_length_flatten_cells {d : JData} (hv : JValid m d) : d.2.1.flatten.length ≤ m := by
  refine jo_length_le_of_nodup (List.nodup_flatten.2 ⟨hv.cell_nodup, ?_⟩) fun a ha => ?_
  · exact hv.cell_disj.imp fun h a ha hb => h a ha hb
  · obtain ⟨c, hc, hac⟩ := List.mem_flatten.1 ha
    exact hv.cell_lt c hc a hac

theorem oo_sum_sq_le {L : List (List ℕ)} {B : ℕ} (hB : (L.map List.length).sum ≤ B) :
    (L.map fun c => c.length * c.length).sum ≤ B * B := by
  have hle : ∀ c ∈ L, c.length ≤ B := fun c hc =>
    (List.le_sum_of_mem (List.mem_map_of_mem (f := List.length) hc)).trans hB
  calc (L.map fun c => c.length * c.length).sum ≤ (L.map fun c => c.length * B).sum :=
        List.sum_le_sum fun c hc => Nat.mul_le_mul_left _ (hle c hc)
    _ = (L.map List.length).sum * B := by
        rw [← List.sum_map_mul_right]
    _ ≤ B * B := Nat.mul_le_mul_right _ hB

theorem oo_length_johnGensD {d : JData} (hv : JValid m d) :
    (johnGensD m d).length ≤ 3 * (m * m) := by
  have hflat := oo_length_flatten_cells hv
  have hsum : (d.2.1.map List.length).sum ≤ m := by rwa [← List.length_flatten]
  -- the number of cells: each is nonempty
  have hk : d.2.1.length ≤ m := by
    refine le_trans ?_ hsum
    calc d.2.1.length = (d.2.1.map fun _ => 1).sum := by simp
      _ ≤ (d.2.1.map List.length).sum := List.sum_le_sum fun c hc =>
          List.length_pos_iff.2 (hv.cell_ne c hc)
  have h₁ : (d.2.1.flatMap fun c => (pairsD c).map fun p => swapPD m p.1 p.2).length ≤ m * m := by
    rw [List.length_flatMap]
    refine le_trans (List.sum_le_sum fun c _ => ?_) (oo_sum_sq_le hsum)
    rw [List.length_map]
    exact length_pairsD_le c
  have h₂ : ((pairsD (jrest m d)).map fun p => swapPD m p.1 p.2).length ≤ m * m := by
    rw [List.length_map]
    exact (length_pairsD_le _).trans
      (Nat.mul_le_mul (jrest_length_le m d) (jrest_length_le m d))
  have h₃ : ((List.range d.2.1.length).flatMap fun i =>
      ((List.range d.2.1.length).filter fun j => i != j &&
        (d.2.1.getD i []).length == (d.2.1.getD j []).length).map
          fun j => cellSwapPD m d i j).length ≤ m * m := by
    refine (po_length_flatMap_le (k := d.2.1.length) _ fun i _ => ?_).trans ?_
    · rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by rw [List.length_range])
    · rw [List.length_range]
      exact Nat.mul_le_mul hk hk
  rw [johnGensD, List.length_append, List.length_append]
  omega

/-- **The number of stabilizer generators of a valid leaf** is at most `3 m² + m`. -/
theorem length_outGensD_le {o : OutD} (hv : OutValid m o) :
    (outGensD m o).length ≤ outGensB m := by
  rcases hv with ⟨h1, -⟩ | ⟨h2, hj⟩
  · rw [outGensD, ite_eq_left h1]
    have := oo_length_partGensD m o.2.1
    unfold outGensB
    omega
  · have h1 : o.1 ≠ 1 := by omega
    rw [outGensD, ite_eq_right h1, ite_eq_left h2]
    have := oo_length_johnGensD hj
    unfold outGensB
    omega

end Ops

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **The stabilizer generators of a leaf** (`outGensD`), dispatching on the tag. -/
def outGensProg (m : var .nat) (o : var outTy) : Prog S rec var (.list Ty.perm) :=
  .bind (.op1 .fst o) fun tag => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1
    (.bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun x => partGensProg m x)
    (.bind (.op0 (.natLit 2)) fun two => .bind (.op2 .natEq tag two) fun is2 =>
      .ite is2 (.bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun d => johnGensProg m d)
        (.op0 .nil))

/-- **An isomorphism of two leaves** (`outIsoD`), dispatching on the tags. -/
def outIsoProg (m : var .nat) (o o' : var outTy) : Prog S rec var (.option Ty.perm) :=
  .bind (.op1 .fst o) fun tag => .bind (.op1 .fst o') fun tag' =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op0 (.natLit 2)) fun two =>
  .bind (.op2 .natEq tag one) fun is1 =>
  .ite is1
    (.bind (.op2 .natEq tag' one) fun is1' =>
      .ite is1'
        (.bind (.op1 .snd o) fun r => .bind (.op1 .fst r) fun x =>
          .bind (.op1 .snd o') fun r' => .bind (.op1 .fst r') fun x' => partIsoProg m x x')
        (.op0 .none))
    (.bind (.op2 .natEq tag two) fun is2 =>
      .ite is2
        (.bind (.op2 .natEq tag' two) fun is2' =>
          .ite is2'
            (.bind (.op1 .snd o) fun r => .bind (.op1 .snd r) fun d =>
              .bind (.op1 .snd o') fun r' => .bind (.op1 .snd r') fun d' => johnIsoProg m d d')
            (.op0 .none))
        (.op0 .none))

end Programs

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of `outGensProg`: block lists of at most `L` points for a colored partition,
Johnson data bounded by `B ≥ m`. -/
def outGensCost (m L B : ℕ) : ℕ := partGensCost m L + johnGensCost B + 12

/-- The cost of `outIsoProg`: block lists of at most `Lx`, `Ly` points, Johnson data bounded by
`B ≥ m`. -/
def outIsoCost (m Lx Ly B : ℕ) : ℕ := partIsoCost m Lx Ly + johnIsoCost B + 20

theorem RunsWithin.outGensProg (m : ℕ) (o : OutD) {L B : ℕ}
    (hL : o.1 = 1 → ∀ v, (o.2.1.2.getD v []).length ≤ L) (hm : m ≤ B)
    (hB : o.1 = 2 → JBound B o.2.2) :
    RunsWithin X body (Case2b.outGensProg m o) (outGensD m o) (outGensCost m L B) := by
  unfold outGensD
  by_cases h1 : o.1 = 1
  · rw [ite_eq_left h1]
    apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h1]) _
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.partGensProg m o.2.1 (hL h1)
    case hc =>
      simp only [Prim.cost, outGensCost]
      omega
  · rw [ite_eq_right h1]
    by_cases h2 : o.1 = 2
    · rw [ite_eq_left h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h2]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.johnGensProg hm o.2.2 (hB h2)
      case hc =>
        simp only [Prim.cost, outGensCost]
        omega
    · rw [ite_eq_right h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h2]) (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost, outGensCost]
        omega

theorem RunsWithin.outIsoProg (m : ℕ) (o o' : OutD) {Lx Ly B : ℕ}
    (hx : o.1 = 1 → ∀ v, (o.2.1.2.getD v []).length ≤ Lx)
    (hy : o'.1 = 1 → ∀ v, (o'.2.1.2.getD v []).length ≤ Ly) (hm : m ≤ B)
    (hB : o.1 = 2 → JBound B o.2.2) (hB' : o'.1 = 2 → JBound B o'.2.2) :
    RunsWithin X body (Case2b.outIsoProg m o o') (outIsoD m o o') (outIsoCost m Lx Ly B) := by
  unfold outIsoD
  by_cases h1 : o.1 = 1
  · rw [ite_eq_left h1]
    by_cases h1' : o'.1 = 1
    · rw [ite_eq_left h1']
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (o'.1 == 1) = true by simp [h1']) _
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.partIsoProg m o.2.1 o'.2.1 (hx h1) (hy h1')
      case hc =>
        simp only [Prim.cost, outIsoCost]
        omega
    · rw [ite_eq_right h1']
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_pos (show (o.1 == 1) = true by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_neg (show (o'.1 == 1) = false by simp [h1']) (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost, outIsoCost]
        omega
  · rw [ite_eq_right h1]
    by_cases h2 : o.1 = 2
    · rw [ite_eq_left h2]
      by_cases h2' : o'.1 = 2
      · rw [ite_eq_left h2']
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h2]) _
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (show (o'.1 == 2) = true by simp [h2']) _
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.johnIsoProg hm o.2.2 o'.2.2 (hB h2) (hB' h2')
        case hc =>
          simp only [Prim.cost, outIsoCost]
          omega
      · rw [ite_eq_right h2']
        apply RunsWithin.mono
        case h =>
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
          run_step (RunsWithin.prim _ _)
          run_with RunsWithin.ite_pos (show (o.1 == 2) = true by simp [h2]) _
          run_step (RunsWithin.prim _ _)
          exact RunsWithin.ite_neg (show (o'.1 == 2) = false by simp [h2']) (RunsWithin.prim _ _)
        case hc =>
          simp only [Prim.cost, outIsoCost]
          omega
    · rw [ite_eq_right h2]
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        run_with RunsWithin.ite_neg (show (o.1 == 1) = false by simp [h1]) _
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.ite_neg (show (o.1 == 2) = false by simp [h2]) (RunsWithin.prim _ _)
      case hc =>
        simp only [Prim.cost, outIsoCost]
        omega

end Specs

/-! ### Polynomial bounds -/

section Bounds

/-- The cost of the generators is at most a polynomial in `m`, the block size bound `L` and the
Johnson bound `B`. -/
theorem outGensCost_le (m L B : ℕ) :
    outGensCost m L B ≤ 200 * (m + 1) ^ 3 * (L + 1) + johnGensCost B + 12 := by
  unfold outGensCost
  have := partGensCost_le m L
  omega

/-- The cost of the isomorphism search is at most a polynomial in `m`, the block size bounds
and the Johnson bound `B`. -/
theorem outIsoCost_le (m Lx Ly B : ℕ) :
    outIsoCost m Lx Ly B ≤ 300 * (m + 1) ^ 4 * (Lx + Ly + 1) + johnIsoCost B + 20 := by
  unfold outIsoCost
  have := partIsoCost_le m Lx Ly
  omega

end Bounds

/-! ### Well-formedness -/

section Wf

variable {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂} {m₁ : var₁ .nat} {m₂ : var₂ .nat} {o₁ o'₁ : var₁ outTy}
  {o₂ o'₂ : var₂ outTy}

theorem wf_outGensProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (outGensProg m₁ o₁) (outGensProg m₂ o₂) := by
  unfold outGensProg
  refine .bind (.prim _ (.cons ho .nil)) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) ?_ ?_
  · exact .bind (.prim _ (.cons (by simp [ho]) .nil)) fun _ _ =>
      .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
        wf_partGensProg (by simp [hm]) (by simp)
  · exact .bind (.prim _ .nil) fun _ _ =>
      .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .ite (by simp)
        (.bind (.prim _ (.cons (by simp [ho]) .nil)) fun _ _ =>
          .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
            wf_johnGensProg (by simp [hm]) (by simp))
        (.prim _ .nil)

theorem wf_outIsoProg (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ) (ho : ⟨outTy, o₁, o₂⟩ ∈ Γ)
    (ho' : ⟨outTy, o'₁, o'₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (outIsoProg m₁ o₁ o'₁) (outIsoProg m₂ o₂ o'₂) := by
  unfold outIsoProg
  refine .bind (.prim _ (.cons ho .nil)) fun _ _ =>
    .bind (.prim _ (.cons (by simp [ho']) .nil)) fun _ _ =>
    .bind (.prim _ .nil) fun _ _ => .bind (.prim _ .nil) fun _ _ =>
    .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
    .ite (by simp) ?_ ?_
  · exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .ite (by simp)
        (.bind (.prim _ (.cons (by simp [ho]) .nil)) fun _ _ =>
          .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
          .bind (.prim _ (.cons (by simp [ho']) .nil)) fun _ _ =>
          .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
            wf_partIsoProg (by simp [hm]) (by simp) (by simp))
        (.prim _ .nil)
  · exact .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
      .ite (by simp)
        (.bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun _ _ =>
          .ite (by simp)
            (.bind (.prim _ (.cons (by simp [ho]) .nil)) fun _ _ =>
              .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
              .bind (.prim _ (.cons (by simp [ho']) .nil)) fun _ _ =>
              .bind (.prim _ (.cons (by simp) .nil)) fun _ _ =>
                wf_johnIsoProg (by simp [hm]) (by simp) (by simp))
            (.prim _ .nil))
        (.prim _ .nil)

end Wf

end GraphIso.Case2b
