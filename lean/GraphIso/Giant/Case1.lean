module

public import GraphIso.Align.PartOps
public import GraphIso.Align.AlignProg
public import GraphIso.Certificates.Cases

/-!
# Case 1 of the giant macro-step: the orbit partition

Stage 14g, item 3 (`PLAN-14.md` §11). In Case 1 the full group `F` has support at least half
of the base and no orbit of more than half of its points; the orbit-length colouring of the
base under `ψ(F)` is then a colored `⌊m/2⌋`-partition (milestone 13's `orbitPart_valid`), and
it is canonical. The macro-step aligns the partition for `x` with the one for `y`.

* **Orbit partitions** (model): `IsOrbitPart` determines the partition
  (`isOrbitPart_unique`), moves with the orbits (`isOrbitPart_smul`), and is always a colored
  partition of the whole base (`isColPart_of_isOrbitPart`, with the trivial block bound), so
  Align can use it whatever the case.
* **On data** (`orbitPartD`): from the backend's orbits of `F` on the base window, the colours
  (orbit lengths) and the blocks (the orbit, or all fixed points); `orbitPartD_spec`: it
  decodes to the orbit partition of `ψ(F)`. `orbitPartProg` computes it
  (`RunsWithin.orbitPartProg`, cubic cost).
* **Canonicity** (`orbitPart_canonical`): if `F` is a canonical map of the strings (local on
  the window, `F (relabel g x) = g F(x) g⁻¹`), every isomorphism of `x` with `y` carries the
  orbit partition for `x` to the one for `y`.
* **`case1Prog`**: the orbits of `F(x)` and `F(y)` on the base, their orbit partitions, and
  Align (`alignProg` with `partOps`). `RunsWithin.case1Prog`: the answer is correct for `G`,
  under the sub-solver hypothesis of Align; the alignment hypothesis comes from canonicity.
-/

@[expose] public section

namespace GraphIso.Giant

open Equiv MulAction Pointwise GraphIso GraphIso.SplitJohnson GraphIso.Certificates
  GraphIso.Toolkit GraphIso.Align GraphIso.SoJProg

/-! ### Orbit partitions -/

section OrbitPart

variable {Γ : Type} [Fintype Γ] [DecidableEq Γ]

omit [Fintype Γ] [DecidableEq Γ] in
/-- **The orbit partition is determined by the group.** -/
theorem isOrbitPart_unique {P : Subgroup (Perm Γ)} {p q : CPart Γ} (hp : IsOrbitPart P p)
    (hq : IsOrbitPart P q) : p = q := by
  obtain ⟨pc, pb⟩ := p
  obtain ⟨qc, qb⟩ := q
  have hc : pc = qc := funext fun γ => (hp γ).1.trans (hq γ).1.symm
  have hb : pb = qb := funext fun γ => Finset.coe_injective ((hp γ).2.trans (hq γ).2.symm)
  rw [hc, hb]

omit [DecidableEq Γ] in
theorem c1_card_orbit_pos (P : Subgroup (Perm Γ)) (γ : Γ) : 1 ≤ Nat.card (orbit P γ) :=
  haveI : Nonempty (orbit P γ) := ⟨⟨γ, mem_orbit_self γ⟩⟩
  Nat.card_pos

omit [Fintype Γ] in
/-- **The orbit partition moves with the orbits**: if the orbits of `Q` are the images under
`σ` of those of `P`, the orbit partition of `Q` is the image of that of `P`. -/
theorem isOrbitPart_smul {P Q : Subgroup (Perm Γ)} (σ : Perm Γ)
    (h : ∀ b c : Γ, c ∈ orbit Q b ↔ σ⁻¹ c ∈ orbit P (σ⁻¹ b)) {p : CPart Γ}
    (hp : IsOrbitPart P p) : IsOrbitPart Q (σ • p) := by
  have horb : ∀ b, orbit Q b = σ • orbit P (σ⁻¹ b) := fun b => by
    ext c
    rw [h b c, Set.mem_smul_set_iff_inv_smul_mem]
    rfl
  have hcard : ∀ b, Nat.card (orbit Q b) = Nat.card (orbit P (σ⁻¹ b)) := fun b => by
    rw [horb b, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Set.ncard_smul_set]
  intro γ
  refine ⟨?_, ?_⟩
  · rw [CPart.smul_col, (hp _).1, hcard]
    rfl
  · rw [CPart.smul_blk, Finset.coe_smul_finset]
    change σ • ((p.blk (σ⁻¹ γ) : Finset Γ) : Set Γ) = _
    rw [(hp _).2, hcard γ]
    by_cases h1 : Nat.card (orbit P (σ⁻¹ γ)) = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      ext δ
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      simp only [Set.mem_ofPred_eq, hcard δ]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1, horb γ]

omit [DecidableEq Γ] in
/-- **The orbit partition is a colored partition of the whole set** (with the trivial block
bound). -/
theorem isColPart_of_isOrbitPart {P : Subgroup (Perm Γ)} {p : CPart Γ} (hp : IsOrbitPart P p) :
    IsColPart Finset.univ (Fintype.card Γ) p := by
  have hfix : ∀ γ, Nat.card (orbit P γ) = 1 →
      p.blk γ = Finset.univ.filter fun δ => Nat.card (orbit P δ) = 1 := fun γ h => by
    apply Finset.coe_injective
    rw [(hp γ).2, ite_eq_left h]
    simp only [Finset.coe_filter, Finset.mem_univ, true_and]
  have horb : ∀ γ, Nat.card (orbit P γ) ≠ 1 → (p.blk γ : Set Γ) = orbit P γ := fun γ h => by
    rw [(hp γ).2, ite_eq_right h]
  have hcard : ∀ γ, Nat.card (orbit P γ) ≠ 1 → (p.blk γ).card = Nat.card (orbit P γ) :=
    fun γ h => by rw [← horb γ h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have hmem : ∀ γ, ∀ δ ∈ p.blk γ, Nat.card (orbit P δ) = Nat.card (orbit P γ) ∧
      p.blk δ = p.blk γ := by
    intro γ δ hδ
    by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h] at hδ ⊢
      have hδ1 : Nat.card (orbit P δ) = 1 := (Finset.mem_filter.mp hδ).2
      exact ⟨hδ1.trans h.symm, hfix δ hδ1⟩
    · have hδ' : δ ∈ orbit P γ := by rw [← horb γ h]; exact hδ
      have he : orbit P δ = orbit P γ := orbit_eq_iff.mpr hδ'
      refine ⟨by rw [he], Finset.coe_injective ?_⟩
      rw [horb γ h, horb δ (by rwa [he]), he]
  refine ⟨fun γ _ => ?_, fun _ _ => Finset.subset_univ _, fun γ _ δ hδ => (hmem γ δ hδ).2,
    fun γ _ δ hδ => ?_, fun γ _ δ _ hc => ?_, fun γ _ h1 δ _ hc => ?_,
    fun γ _ => Finset.card_le_univ _⟩
  · by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    · have : γ ∈ (p.blk γ : Set Γ) := by rw [horb γ h]; exact mem_orbit_self γ
      exact this
  · rw [(hp δ).1, (hp γ).1, (hmem γ δ hδ).1]
  · rw [(hp γ).1, (hp δ).1] at hc
    by_cases h : Nat.card (orbit P γ) = 1
    · rw [hfix γ h, hfix δ (hc ▸ h)]
    · rw [hcard γ h, hcard δ (hc ▸ h), hc]
  · rw [(hp γ).1, (hp δ).1] at hc
    by_cases h : Nat.card (orbit P γ) = 1
    · have hδ : δ ∈ p.blk γ := by
        rw [hfix γ h]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.trans h⟩
      exact Finset.card_eq_one.mp h1 |>.elim fun a ha => by
        have hγ : γ ∈ p.blk γ := by
          rw [hfix γ h]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        rw [ha] at hδ hγ
        rw [Finset.mem_singleton.mp hδ, Finset.mem_singleton.mp hγ]
    · exact absurd ((hcard γ h).symm.trans h1) h

end OrbitPart

/-! ### Orbit partitions on data -/

section Data

/-- The listed orbit containing `u`, or `[]`. -/
def orbitOfD (os : List (List ℕ)) (u : ℕ) : List ℕ :=
  (os.find? fun o => decide (u ∈ o)).getD []

/-- **The orbit partition on data**, from the orbits `os` of a group on the base window
`[n, n + m)`: the colour of the base point `b` is the length of its orbit, its block is its orbit
(shifted to base indices) or, for a fixed point, all fixed points. -/
def orbitPartD (n m : ℕ) (os : List (List ℕ)) : Array ℕ × Array (List ℕ) :=
  let obs := (List.range m).map fun b => orbitOfD os (n + b)
  let lens := (obs.map List.length).toArray
  let fixed := (List.range m).filter fun b => lens.getD b 0 == 1
  (lens, ((List.range m).map fun b =>
    if lens.getD b 0 == 1 then fixed else (obs.toArray.getD b []).map fun u => u - n).toArray)

theorem c1_getD_toArray {α : Type*} {m : ℕ} (f : ℕ → α) (d : α) {b : ℕ} (hb : b < m) :
    ((List.range m).map f).toArray.getD b d = f b := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  simp [hb]

theorem c1_getD_lens {n m : ℕ} (os : List (List ℕ)) {b : ℕ} (hb : b < m) :
    (((List.range m).map fun b => orbitOfD os (n + b)).map List.length).toArray.getD b 0 =
      (orbitOfD os (n + b)).length := by
  rw [List.map_map]
  exact c1_getD_toArray (fun b => (orbitOfD os (n + b)).length) 0 hb

variable {N n : ℕ} {F : Subgroup (Perm (Fin N))} {os : List (List ℕ)}

/-- The listed orbit of a base position is a listed orbit, contains it, and is its orbit. -/
theorem c1_orbitOfD (hos : IsOrbitPartition F (baseWin n N) os) {u : ℕ} (hu : n ≤ u)
    (hu' : u < N) : orbitOfD os u ∈ os ∧ u ∈ orbitOfD os u ∧
      ∀ j, j ∈ orbitOfD os u ↔ SameOrbit F u j := by
  obtain ⟨hperm, hblk⟩ := hos
  have hmem : u ∈ os.flatten := hperm.mem_iff.2 (mem_basePts.2 ⟨hu, hu'⟩)
  obtain ⟨o, ho, huo⟩ := List.mem_flatten.1 hmem
  have hsome : (os.find? fun o => decide (u ∈ o)).isSome := by
    rw [List.find?_isSome]
    exact ⟨o, ho, by simpa using huo⟩
  obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hsome
  have hmem' := List.mem_of_find?_eq_some ho'
  have hp := List.find?_some ho'
  have he : orbitOfD os u = o' := by rw [orbitOfD, ho']; rfl
  rw [he]
  have hu'' : u ∈ o' := by simpa using hp
  exact ⟨hmem', hu'', (hblk o' hmem').2 u hu''⟩

/-- The listed orbits lie in the base window, without repetition. -/
theorem c1_orbit_sub (hos : IsOrbitPartition F (baseWin n N) os) {o : List ℕ} (ho : o ∈ os) :
    o.Nodup ∧ ∀ u ∈ o, n ≤ u ∧ u < N := by
  obtain ⟨hperm, -⟩ := hos
  have hnd : os.flatten.Nodup := hperm.nodup_iff.2 (baseWin_valid n N).nodup
  refine ⟨(List.nodup_flatten.1 hnd).1 o ho, fun u hu => ?_⟩
  exact mem_basePts.1 (hperm.mem_iff.1 (List.mem_flatten.2 ⟨o, ho, hu⟩))

/-- Orbits of the base action: `c` is in the orbit of `b` exactly when some element of `F` maps
the position of `b` to that of `c`. -/
theorem c1_mem_orbit_range (hF : IsInvariant F (baseSet n N)) (b c : Fin (N - n)) :
    c ∈ orbit (baseHom F n hF).range b ↔ ∃ f ∈ F, f (basePos b) = basePos c := by
  rw [mem_orbit_iff]
  constructor
  · rintro ⟨⟨_, ⟨f, rfl⟩⟩, hc⟩
    refine ⟨f.1, f.2, ?_⟩
    rw [← baseHom_apply (hG := hF)]
    exact congrArg basePos hc
  · rintro ⟨f, hf, hc⟩
    refine ⟨⟨_, ⟨f, hf⟩, rfl⟩, ?_⟩
    apply Fin.ext
    have h := baseHom_apply (hG := hF) ⟨f, hf⟩ b
    rw [hc] at h
    have := congrArg Fin.val h
    simp only [basePos] at this
    show (baseHom F n hF ⟨f, hf⟩ b).val = c.val
    omega

theorem c1_sameOrbit_iff (hF : IsInvariant F (baseSet n N)) (b c : Fin (N - n)) :
    SameOrbit F (n + b) (n + c) ↔ c ∈ orbit (baseHom F n hF).range b := by
  rw [c1_mem_orbit_range hF]
  constructor
  · rintro ⟨_, _, f, hf, he⟩
    exact ⟨f, hf, Fin.ext (by simpa [basePos] using congrArg Fin.val he)⟩
  · rintro ⟨f, hf, he⟩
    exact ⟨by omega, by omega, f, hf, Fin.ext (by simpa [basePos] using congrArg Fin.val he)⟩

/-- The orbit of `b`, as the base indices of its listed orbit. -/
theorem c1_orbit_eq (hF : IsInvariant F (baseSet n N))
    (hos : IsOrbitPartition F (baseWin n N) os) (b : Fin (N - n)) :
    orbit (baseHom F n hF).range b = {c | n + c.val ∈ orbitOfD os (n + b)} := by
  obtain ⟨-, -, hj⟩ := c1_orbitOfD hos (u := n + b) (by omega) (by omega)
  ext c
  rw [Set.mem_ofPred_eq, hj, c1_sameOrbit_iff hF]

/-- The orbit length is the length of the listed orbit. -/
theorem c1_card_orbit (hF : IsInvariant F (baseSet n N))
    (hos : IsOrbitPartition F (baseWin n N) os) (b : Fin (N - n)) :
    Nat.card (orbit (baseHom F n hF).range b) = (orbitOfD os (n + b)).length := by
  obtain ⟨ho, -, -⟩ := c1_orbitOfD hos (u := n + b) (by omega) (by omega)
  obtain ⟨hnd, hlt⟩ := c1_orbit_sub hos ho
  set o := orbitOfD os (n + b)
  have hset : orbit (baseHom F n hF).range b =
      ↑(Finset.univ.filter fun c : Fin (N - n) => n + c.val ∈ o) := by
    rw [c1_orbit_eq hF hos b]
    ext c
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [hset, Nat.card_coe_set_eq, Set.ncard_coe_finset, ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_nbij' (fun c => n + c.val) (fun u => if h : u - n < N - n then
    ⟨u - n, h⟩ else ⟨0, by have := b.2; omega⟩) ?_ ?_ ?_ ?_
  · intro c hc
    simpa using hc
  · intro u hu
    have hu' := hlt u (List.mem_toFinset.1 hu)
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [dite_eq_left (by omega)]
    simp only
    rw [show n + (u - n) = u by omega]
    exact List.mem_toFinset.1 hu
  · intro c _
    simp only
    rw [dite_eq_left (by omega)]
    exact Fin.ext (by simp)
  · intro u hu
    have hu' := hlt u (List.mem_toFinset.1 hu)
    simp only
    rw [dite_eq_left (by omega)]
    simp only
    omega

/-- **The orbit partition on data** decodes to the orbit partition of `ψ(F)`. -/
theorem orbitPartD_spec (hF : IsInvariant F (baseSet n N))
    (hos : IsOrbitPartition F (baseWin n N) os) :
    IsOrbitPart (baseHom F n hF).range (decPart (N - n) (orbitPartD n (N - n) os)) := by
  intro b
  have hb := b.2
  have hcol : (decPart (N - n) (orbitPartD n (N - n) os)).col b =
      (orbitOfD os (n + b)).length := by
    show get _ b.val = _
    rw [get, orbitPartD]
    exact c1_getD_lens os hb
  refine ⟨by rw [hcol, c1_card_orbit hF hos], ?_⟩
  have hblk : (decPart (N - n) (orbitPartD n (N - n) os)).blk b =
      setOf (N - n) (if (orbitOfD os (n + b)).length == 1 then
        (List.range (N - n)).filter fun c => (orbitOfD os (n + c)).length == 1
      else (orbitOfD os (n + b)).map fun u => u - n) := by
    show SoJProg.setOf _ (Array.getD _ b.val []) = _
    simp only [orbitPartD]
    rw [c1_getD_toArray _ _ hb, c1_getD_lens os hb]
    congr 1
    split_ifs
    · apply List.filter_congr
      intro c hc
      rw [c1_getD_lens os (List.mem_range.1 hc)]
    · rw [c1_getD_toArray (fun b => orbitOfD os (n + b)) _ hb]
  rw [hblk, c1_card_orbit hF hos]
  by_cases h1 : (orbitOfD os (n + b)).length = 1
  · rw [ite_eq_left (by simpa using h1), ite_eq_left h1]
    ext c
    rw [Finset.mem_coe, mem_setOf, List.mem_filter, List.mem_range, Set.mem_ofPred_eq,
      c1_card_orbit hF hos c]
    simp [c.2]
  · rw [ite_eq_right (by simpa using h1), ite_eq_right h1, c1_orbit_eq hF hos b]
    obtain ⟨ho, -, -⟩ := c1_orbitOfD hos (u := n + b) (by omega) (by omega)
    obtain ⟨-, hlt⟩ := c1_orbit_sub hos ho
    ext c
    rw [Finset.mem_coe, mem_setOf, List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, hc⟩
      have := hlt u hu
      rwa [show n + c.val = u by omega]
    · intro hc
      exact ⟨n + c.val, hc, by omega⟩

end Data

/-! ### Canonicity -/

section Canonical

variable {N n : ℕ} {G : Subgroup (Perm (Fin N))}

/-- **The orbit partition is canonical.** If `F` is a canonical map of the strings into
subgroups of `G` (local on the window `W`, and `F (relabel g x) = g F(x) g⁻¹`), every
isomorphism `g` of `x` with `y` carries the orbit partition of `ψ(F(x))` to that of
`ψ(F(y))`. -/
theorem orbitPart_canonical (hG : IsInvariant G (baseSet n N)) {W : Set (Fin N)}
    (hW : IsInvariant G W) {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))}
    (hloc : ∀ x x', (∀ u ∈ W, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ G, ∀ x, Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {x y : Fin N → ℕ} {Fx Fy : Subgroup (Perm (Fin N))} (hFxe : Fx = Fmap x)
    (hFye : Fy = Fmap y) (hFx : IsInvariant Fx (baseSet n N)) (hFy : IsInvariant Fy (baseSet n N))
    {g : Perm (Fin N)} (hg : g ∈ iso W 1 G x y) {p q : CPart (Fin (N - n))}
    (hp : IsOrbitPart (baseHom Fx n hFx).range p) (hq : IsOrbitPart (baseHom Fy n hFy).range q) :
    baseHom G n hG ⟨g, (mem_iso_one.1 hg).1⟩ • p = q := by
  have hgG : g ∈ G := (mem_iso_one.1 hg).1
  have hy : Fy = Fx.map (MulAut.conj g).toMonoidHom := by
    rw [hFye, hFxe, ← heq g hgG x]
    exact (hloc _ _ (Recursion.relabel_eq_on_of_mem_iso hW hg)).symm
  set σ := baseHom G n hG ⟨g, hgG⟩ with hσ
  have hinv : ∀ j, basePos (σ⁻¹ j) = g⁻¹ (basePos j) := fun j => by
    rw [hσ, ← map_inv]
    exact baseHom_apply (hG := hG) ⟨g, hgG⟩⁻¹ j
  refine isOrbitPart_unique (isOrbitPart_smul σ (fun b c => ?_) hp) hq
  rw [c1_mem_orbit_range hFy, c1_mem_orbit_range hFx, hinv, hinv]
  constructor
  · rintro ⟨f', hf', he⟩
    rw [hy] at hf'
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hf'
    refine ⟨f, hf, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Perm.mul_apply] at he
    rw [← he, perm_inv_apply_self]
  · rintro ⟨f, hf, he⟩
    refine ⟨g * f * g⁻¹, ?_, ?_⟩
    · rw [hy]
      exact Subgroup.mem_map.2 ⟨f, hf, rfl⟩
    · rw [Perm.mul_apply, Perm.mul_apply, he, perm_apply_inv_self]

end Canonical

/-! ### The orbit partition as a program -/

section Programs

open Cost Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- The listed orbit containing `u` (`orbitOfD`). -/
def c1OrbitProg (os : var (.list (.list .nat))) (u : var .nat) : Prog S rec var (.list .nat) :=
  .bind (SoJProg.findProg os fun o => SoJProg.memProg u o) fun oo =>
  .caseOption oo (.op0 .nil) fun o => .ret o

/-- The listed orbit of the base point `b`. -/
def c1PosOrbitProg (n : var .nat) (os : var (.list (.list .nat))) (b : var .nat) :
    Prog S rec var (.list .nat) :=
  .bind (.op2 .add n b) fun u => c1OrbitProg os u

/-- Whether the base point `b` is fixed. -/
def c1FixTestProg (lens : var (.array .nat)) (b : var .nat) : Prog S rec var .bool :=
  .bind (.op2 .arrayGet lens b) fun l => .bind (.op0 (.natLit 1)) fun one => .op2 .natEq l one

/-- An orbit shifted to base indices. -/
def c1ShiftProg (n : var .nat) (o : var (.list .nat)) : Prog S rec var (.list .nat) :=
  mapList o fun u => .op2 .sub u n

/-- The block of the base point `b`. -/
def c1BlkRowProg (n : var .nat) (lens : var (.array .nat)) (obsA : var (.array (.list .nat)))
    (fixed : var (.list .nat)) (b : var .nat) : Prog S rec var (.list .nat) :=
  .bind (c1FixTestProg lens b) fun t =>
  .ite t (.ret fixed) (.bind (.op2 .arrayGet obsA b) fun o => c1ShiftProg n o)

/-- **The orbit partition on data** (`orbitPartD`). -/
def orbitPartProg (n m : var .nat) (os : var (.list (.list .nat))) :
    Prog S rec var (.prod (.array .nat) (.array (.list .nat))) :=
  .bind (.op1 .range m) fun bs =>
  .bind (mapList bs fun b => c1PosOrbitProg n os b) fun obs =>
  .bind (mapList obs fun o => .op1 .length o) fun ls =>
  .bind (.op1 .arrayOfList ls) fun lens =>
  .bind (Toolkit.filterList bs fun b => c1FixTestProg lens b) fun fixed =>
  .bind (.op1 .arrayOfList obs) fun obsA =>
  .bind (mapList bs fun b => c1BlkRowProg n lens obsA fixed b) fun rows =>
  .bind (.op1 .arrayOfList rows) fun blkA =>
  .op2 .pair lens blkA

end Programs

section ProgSpecs

open Cost Programs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of `c1OrbitProg` with `K` listed orbits of at most `L` points. -/
def c1OrbitCost (K L : ℕ) : ℕ := K * (3 * L + 5) + 4

theorem RunsWithin.c1OrbitProg (os : List (List ℕ)) (u : ℕ) {K L : ℕ} (hK : os.length ≤ K)
    (hL : ∀ o ∈ os, o.length ≤ L) :
    RunsWithin X body (Giant.c1OrbitProg os u) (orbitOfD os u) (c1OrbitCost K L) := by
  have hf := SoJProg.RunsWithin.findProg (X := X) (body := body) (t := .list .nat) os
    (p := fun o => SoJProg.memProg u o) (P := fun o => decide (u ∈ o)) (c := 3 * L + 1)
    fun o ho => (SoJProg.RunsWithin.memProg u o).mono (by have := hL o ho; omega)
  rw [show 3 * L + 1 + 4 = 3 * L + 5 by omega] at hf
  rcases h : os.find? (fun o => decide (u ∈ o)) with _ | o
  · rw [h] at hf
    have he : orbitOfD os u = [] := by rw [orbitOfD, h]; rfl
    rw [he]
    have hm := Nat.mul_le_mul_right (3 * L + 5) hK
    apply RunsWithin.mono
    case h =>
      run_step hf
      exact RunsWithin.caseOption_none (RunsWithin.prim _ _)
    case hc =>
      simp only [Prim.cost, c1OrbitCost]
      omega
  · rw [h] at hf
    have he : orbitOfD os u = o := by rw [orbitOfD, h]; rfl
    rw [he]
    apply RunsWithin.mono
    case h =>
      run_step hf
      exact RunsWithin.caseOption_some (RunsWithin.ret _)
    case hc =>
      have hm := Nat.mul_le_mul_right (3 * L + 5) hK
      simp only [c1OrbitCost]
      omega

theorem c1_length_orbitOfD (os : List (List ℕ)) (u : ℕ) {L : ℕ}
    (hL : ∀ o ∈ os, o.length ≤ L) : (orbitOfD os u).length ≤ L := by
  unfold orbitOfD
  rcases h : os.find? (fun o => decide (u ∈ o)) with _ | o
  · simp
  · exact hL o (List.mem_of_find?_eq_some h)

/-- The cost of `orbitPartProg` on `m` base points, `K` listed orbits of at most `L` points. -/
def orbitPartCost (m K L : ℕ) : ℕ :=
  m * (c1OrbitCost K L + 4) + m * (L + 4) + m * (4 * L + 15) + 12 * m + 30

theorem RunsWithin.orbitPartProg (n m : ℕ) (os : List (List ℕ)) {K L : ℕ}
    (hK : os.length ≤ K) (hL : ∀ o ∈ os, o.length ≤ L) :
    RunsWithin X body (Giant.orbitPartProg n m os) (orbitPartD n m os) (orbitPartCost m K L) := by
  set obs := (List.range m).map fun b => orbitOfD os (n + b) with hobs
  set lens := (obs.map List.length).toArray with hlens
  set fixed := (List.range m).filter fun b => lens.getD b 0 == 1 with hfixed
  have hlo : ∀ o ∈ obs, o.length ≤ L := by
    intro o ho
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ho
    exact c1_length_orbitOfD os _ hL
  have hfix : ∀ b, RunsWithin X body (Giant.c1FixTestProg lens b) (lens.getD b 0 == 1) 3 :=
    fun b => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.prim _ _
      case hc => simp [Prim.cost]
  have hrow : ∀ b ∈ List.range m, RunsWithin X body
      (Giant.c1BlkRowProg n lens obs.toArray fixed b)
      (if lens.getD b 0 == 1 then fixed else (obs.toArray.getD b []).map fun u => u - n)
      (4 * L + 12) := by
    intro b hb
    have hob : (obs.toArray.getD b []).length ≤ L := by
      rw [hobs, c1_getD_toArray _ _ (List.mem_range.1 hb)]
      exact c1_length_orbitOfD os _ hL
    by_cases ht : (lens.getD b 0 == 1) = true
    · rw [ite_eq_left ht]
      apply RunsWithin.mono
      case h =>
        run_step (hfix b)
        exact Sims.RunsWithin.ite_pos ht (RunsWithin.ret _)
      case hc => omega
    · rw [ite_eq_right ht]
      apply RunsWithin.mono
      case h =>
        run_step (hfix b)
        apply Sims.RunsWithin.ite_neg (Bool.eq_false_iff.mpr ht)
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.mapList_le (c := 1) fun u _ => RunsWithin.prim _ _
      case hc =>
        have hob' : (obs.toArray.getD b (Ty.list .nat).default).length ≤ L := hob
        simp only [Prim.cost, Prim.eval]
        omega
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le (c := c1OrbitCost K L + 1) fun b _ => by
      apply RunsWithin.mono
      case h =>
        run_step (RunsWithin.prim _ _)
        exact RunsWithin.c1OrbitProg os _ hK hL
      case hc => simp only [Prim.cost]; omega)
    run_step (RunsWithin.mapList_le (c := L + 1) fun o ho =>
      RunsWithin.prim_le rfl (by simp [Prim.cost]; exact hlo o ho))
    run_step (RunsWithin.prim _ _)
    run_step (Toolkit.RunsWithin.filterList fun b _ => hfix b)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.mapList_le hrow)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim _ _
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head, List.length_range, List.length_map,
      orbitPartCost]
    ring_nf
    omega

theorem orbitPartCost_le (m : ℕ) : orbitPartCost m m m ≤ 40 * (m + 1) ^ 3 := by
  simp only [orbitPartCost, c1OrbitCost]
  ring_nf
  nlinarith [Nat.zero_le (m * m * m), Nat.zero_le (m * m), Nat.zero_le m]

end ProgSpecs

/-! ### Case 1 -/

section Lengths

variable {N n : ℕ} {F : Subgroup (Perm (Fin N))} {os : List (List ℕ)}

theorem c1_length_le_flatten {α : Type*} :
    ∀ (os : List (List α)), (∀ o ∈ os, o ≠ []) → os.length ≤ os.flatten.length
  | [], _ => by simp
  | o :: os, h => by
    have h1 := c1_length_le_flatten os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    have h2 : o ≠ [] := h o List.mem_cons_self
    have h3 : 1 ≤ o.length := List.length_pos_iff.2 h2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- The listed orbits number at most the size of the base. -/
theorem c1_length_os (hos : IsOrbitPartition F (baseWin n N) os) : os.length ≤ N - n := by
  have h := c1_length_le_flatten os fun o ho => (hos.2 o ho).1
  rw [hos.1.length_eq] at h
  simpa [baseWin, WinData.ofPoints, length_basePts] using h

/-- Each listed orbit has at most `N - n` points. -/
theorem c1_length_orbit (hos : IsOrbitPartition F (baseWin n N) os) {o : List ℕ} (ho : o ∈ os) :
    o.length ≤ N - n := by
  obtain ⟨hnd, hlt⟩ := c1_orbit_sub hos ho
  rw [← List.toFinset_card_of_nodup hnd, ← Nat.card_Ico n N]
  exact Finset.card_le_card fun u hu => Finset.mem_Ico.2 (hlt u (List.mem_toFinset.1 hu))

theorem c1_getD_length_le {m : ℕ} {l : List (List ℕ)} (hl : ∀ o ∈ l, o.length ≤ m) (v : ℕ) :
    (l.toArray.getD v []).length ≤ m := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
  rcases h : l[v]? with _ | o
  · simp
  · exact hl o (List.mem_of_getElem? h)

end Lengths

/-- The representation invariant used for orbit partitions in Align: a colored partition of the
base, with blocks of at most `m` listed points. -/
def C1Valid (m : ℕ) (z : Array ℕ × Array (List ℕ)) : Prop :=
  PartValid m z ∧ ∀ v, (z.2.getD v []).length ≤ m

theorem c1_spec (m : ℕ) : (partOps m).Spec (C1Valid m) where
  gens_valid := fun x hx => (partOps_spec m).gens_valid x hx.1
  gens_closure := fun x hx => (partOps_spec m).gens_closure x hx.1
  iso_some := fun x y hx hy => (partOps_spec m).iso_some x y hx.1 hy.1
  iso_none := fun x y hx hy => (partOps_spec m).iso_none x y hx.1 hy.1

/-- The orbit partition on data satisfies the invariant. -/
theorem c1_valid_orbitPartD {N n : ℕ} {F : Subgroup (Perm (Fin N))} {os : List (List ℕ)}
    (hF : IsInvariant F (baseSet n N)) (hos : IsOrbitPartition F (baseWin n N) os) :
    C1Valid (N - n) (orbitPartD n (N - n) os) := by
  refine ⟨⟨_, isColPart_of_isOrbitPart (orbitPartD_spec hF hos)⟩, fun v => ?_⟩
  refine c1_getD_length_le (fun o ho => ?_) v
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ho
  have hL : ∀ o ∈ os, o.length ≤ N - n := fun o ho => c1_length_orbit hos ho
  split_ifs
  · exact (List.length_filter_le _ _).trans (by simp)
  · rw [List.length_map, c1_getD_toArray _ _ (List.mem_range.1 hb)]
    exact c1_length_orbitOfD os _ hL

section Case1Prog

open Cost Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- **Case 1**: the orbit partitions of `F(x)` and `F(y)` on the base, aligned. `Fx`, `Fy` are
the full groups for `x` and `y`. -/
def case1Prog (sub : var (Ty.inst D) → Prog (groupSig D) rec var (Ty.answer D))
    (n : var .nat) (xy : var Ty.strs) (w : var Ty.win) (G Fx Fy : var (Ty.group D)) :
    Prog (groupSig D) rec var (Ty.answer D) :=
  .bind (.op1 .fst G) fun N => .bind (.op2 .sub N n) fun m =>
  .bind (Toolkit.baseWinProg n N) fun bw =>
  .bind (.op2 .pair Fx bw) fun a₁ =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits a₁) fun osx =>
  .bind (.op2 .pair Fy bw) fun a₂ =>
  .bind (Prog.call (S := groupSig D) GroupOp.orbits a₂) fun osy =>
  .bind (orbitPartProg n m osx) fun X₀ =>
  .bind (orbitPartProg n m osy) fun Y₀ =>
  .bind (.op0 .nil) fun nil =>
  .bind (.op2 .cons Y₀ nil) fun Ys =>
  Align.alignProg sub (fun z => partGensProg m z) (fun z z' => partIsoProg m z z') n xy w G X₀ Ys

end Case1Prog

section Case1Specs

open Cost Programs

variable {D : Ty} {a b : Ty} {X : Ctx (groupSig D)}
  {body : a.denote → Prog (groupSig D) (a, b) Ty.denote b} {DV : ℕ → GensData → D.denote → Prop}

/-- The operations of Case 1. -/
def case1Ops (op : GroupOp) : Prop := alignOps op ∨ op = .orbits

/-- The orbits of a group on the base window, as computed by the backend. -/
def baseOrbits (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) : List (List ℕ) :=
  O.run GroupOp.orbits (F, baseWin n N)

/-- The orbit partition of a group on the base, as computed. -/
def orbitPartModel (O : Oracle (groupSig D)) (n N : ℕ) (F : GroupData D.denote) :
    Array ℕ × Array (List ℕ) :=
  orbitPartD n (N - n) (baseOrbits O n N F)

/-- The cost of Case 1: `g` generators of `G`, `k` stabilizer generators of the partition for
`x`, the two orbit charges, and Align's charges. -/
def case1Cost (n N g k Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s : ℕ) : ℕ :=
  baseWinCost n N + Box + Boy + 2 * orbitPartCost (N - n) (N - n) (N - n) +
    alignCost n N g k 1 (partGensCost (N - n) (N - n)) (partIsoCost (N - n) (N - n) (N - n))
      BgP Bmem Bk Bl Bg1 Bgen Cb s + 10

/-- **Case 1.** If `F` is a canonical map of the strings into subgroups of `G` and `Fx`, `Fy`
represent `F(x)`, `F(y)`, the answer is correct for `G`, under Align's sub-solver hypothesis
for the cosets of `G₁ = ψ⁻¹(Stab(X(x)) ∩ P)`. -/
theorem RunsWithin.case1Prog (hO : MeetsContractOn DV case1Ops X.O)
    (hPre : ∀ op x, case1Ops op → GroupPre DV op x → X.Pre op x)
    {n N : ℕ} {gs : GensData} {d : D.denote} (hGv : GroupValid DV N gs d)
    (hG : IsInvariant (GensData.denote N gs) (baseSet n N))
    (halt : alternatingGroup (Fin (N - n)) ≤ (baseHom _ n hG).range)
    {xy : StrData × StrData} {w : WinData} (hw : w.Valid N)
    (hWG : IsInvariant (GensData.denote N gs) (w.denote N))
    {Fmap : (Fin N → ℕ) → Subgroup (Perm (Fin N))} (hFG : ∀ x, Fmap x ≤ GensData.denote N gs)
    (hloc : ∀ x x', (∀ u ∈ w.denote N, x u = x' u) → Fmap x = Fmap x')
    (heq : ∀ g ∈ GensData.denote N gs, ∀ x,
      Fmap (relabel g x) = (Fmap x).map (MulAut.conj g).toMonoidHom)
    {fxs fys : GensData} {ex ey : D.denote} (hFxv : GroupValid DV N fxs ex)
    (hFyv : GroupValid DV N fys ey) (hFx : GensData.denote N fxs = Fmap (xy.1.denote N))
    (hFy : GensData.denote N fys = Fmap (xy.2.denote N))
    {Box Boy Cb s BgP Bmem Bk Bl Bg1 Bgen : ℕ}
    (hBox : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
      (baseOrbits X.O n N (N, fxs, ex)) ≤ Box)
    (hBoy : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
      (baseOrbits X.O n N (N, fys, ey)) ≤ Boy)
    (hBgP : X.B.call GroupOp.generate (N - n, gs.map (baseD n N))
      (X.O.run GroupOp.generate (N - n, gs.map (baseD n N))) ≤ BgP)
    (hBmem : ∀ g : PermData, g.Valid (N - n) → X.B.call GroupOp.mem (pModel X.O n (N, gs, d), g)
      (X.O.run GroupOp.mem (pModel X.O n (N, gs, d), g)) ≤ Bmem)
    (hBk : X.B.call GroupOp.kernel ((N, gs, d), baseWin n N) (kerModel X.O n (N, gs, d)) ≤ Bk)
    (hBl : ∀ π : PermData, X.B.call GroupOp.lift ((N, gs, d), (baseWin n N, π))
      (liftModel X.O n (N, gs, d) π) ≤ Bl)
    (hBg1 : X.B.call GroupOp.generate
      (N, (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (orbitPartModel X.O n N (N, fxs, ex))))).map
        (liftModel X.O n (N, gs, d)) ++ (kerModel X.O n (N, gs, d)).2.1)
      (preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (orbitPartModel X.O n N (N, fxs, ex)))))) ≤ Bg1)
    (hBgen : ∀ gs' : GensData, GensData.AllValid N gs' → gs'.length ≤ 1 * (s + 1) →
      GensData.denote N gs' ≤ GensData.denote N gs →
      X.B.call GroupOp.generate (N, gs') (X.O.run GroupOp.generate (N, gs')) ≤ Bgen)
    {sub : InstData D → Prog (groupSig D) (a, b) Ty.denote (Ty.answer D)}
    (hsub : SubSolves X body DV sub (fun I => I.1 = xy ∧ I.2.1 = w ∧
      I.2.2.2 = preModel X.O n (N, gs, d) (stabInPL (flagsModel X.O (pModel X.O n (N, gs, d))
        (partGensD (N - n) (orbitPartModel X.O n N (N, fxs, ex))))) ∧ I.Valid DV)
      (fun _ => Cb) s) :
    ∃ ans : AnswerData D,
      RunsWithin X body (Giant.case1Prog sub n xy w (N, gs, d) (N, fxs, ex) (N, fys, ey)) ans
        (case1Cost n N gs.length (partGensD (N - n) (orbitPartModel X.O n N (N, fxs, ex))).length
          Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s) ∧
      AnsOK DV N (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N) (xy.2.denote N) ans ∧
      ∀ sGen, (∀ gs', GensData.AllValid N gs' → GensData.denote N gs' ≤ GensData.denote N gs →
          (X.O.run GroupOp.generate (N, gs')).2.1.length ≤ sGen) →
        ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ sGen := by
  -- the orbits
  have hFxi : IsInvariant (GensData.denote N fxs) (baseSet n N) := hG.mono (hFx ▸ hFG _)
  have hFyi : IsInvariant (GensData.denote N fys) (baseSet n N) := hG.mono (hFy ▸ hFG _)
  have hprex : GroupPre DV .orbits ((N, fxs, ex), baseWin n N) :=
    ⟨hFxv, baseWin_valid n N, by rw [baseWin_denote]; exact hFxi⟩
  have hprey : GroupPre DV .orbits ((N, fys, ey), baseWin n N) :=
    ⟨hFyv, baseWin_valid n N, by rw [baseWin_denote]; exact hFyi⟩
  have hosx : IsOrbitPartition (GensData.denote N fxs) (baseWin n N)
      (baseOrbits X.O n N (N, fxs, ex)) := hO .orbits _ (Or.inr rfl) hprex
  have hosy : IsOrbitPartition (GensData.denote N fys) (baseWin n N)
      (baseOrbits X.O n N (N, fys, ey)) := hO .orbits _ (Or.inr rfl) hprey
  set X₀ := orbitPartModel X.O n N (N, fxs, ex) with hX₀
  set Y₀ := orbitPartModel X.O n N (N, fys, ey) with hY₀
  have hXv : C1Valid (N - n) X₀ := c1_valid_orbitPartD hFxi hosx
  have hYv : C1Valid (N - n) Y₀ := c1_valid_orbitPartD hFyi hosy
  -- the alignment hypothesis, from canonicity
  have halign : ∀ g ∈ iso (w.denote N) 1 (GensData.denote N gs) (xy.1.denote N)
      (xy.2.denote N), ∃ Y ∈ [Y₀], ∃ h : g ∈ GensData.denote N gs,
        baseHom _ n hG ⟨g, h⟩ • (partOps (N - n)).dec X₀ = (partOps (N - n)).dec Y := by
    intro g hg
    refine ⟨Y₀, List.mem_singleton_self _, (mem_iso_one.1 hg).1, ?_⟩
    exact orbitPart_canonical hG hWG hloc heq hFx hFy hFxi hFyi hg
      (orbitPartD_spec hFxi hosx) (orbitPartD_spec hFyi hosy)
  -- the programs on the structures
  have hgensP : ∀ z, C1Valid (N - n) z → RunsWithin X body (partGensProg (N - n) z)
      ((partOps (N - n)).gens z) (partGensCost (N - n) (N - n)) :=
    fun z hz => RunsWithin.partGensProg (N - n) z hz.2
  have hisoP : ∀ z z', C1Valid (N - n) z → C1Valid (N - n) z' →
      RunsWithin X body (partIsoProg (N - n) z z') ((partOps (N - n)).iso z z')
        (partIsoCost (N - n) (N - n) (N - n)) :=
    fun z z' hz hz' => RunsWithin.partIsoProg (N - n) z z' hz.2 hz'.2
  have halignO : MeetsContractOn DV alignOps X.O := fun op x h hx => hO op x (Or.inl h) hx
  have halignP : ∀ op x, alignOps op → GroupPre DV op x → X.Pre op x :=
    fun op x h hx => hPre op x (Or.inl h) hx
  obtain ⟨ans, hrun, hok, hgen⟩ := RunsWithin.alignProg (body := body)
    (τ := .prod (.array .nat) (.array (.list .nat))) (O := CPart (Fin (N - n))) halignO halignP
    hGv hG halt (S := partOps (N - n)) (c1_spec (N - n)) hgensP hisoP hXv (fun Y hY => by
      rw [List.mem_singleton.1 hY]; exact hYv) hw hWG halign hBgP hBmem hBk hBl hBg1 hBgen hsub
  refine ⟨ans, ?_, hok, hgen⟩
  -- the run
  have hKx := c1_length_os hosx
  have hKy := c1_length_os hosy
  have hLx : ∀ o ∈ baseOrbits X.O n N (N, fxs, ex), o.length ≤ N - n :=
    fun o ho => c1_length_orbit hosx ho
  have hLy : ∀ o ∈ baseOrbits X.O n N (N, fys, ey), o.length ≤ N - n :=
    fun o ho => c1_length_orbit hosy ho
  apply RunsWithin.mono
  case h =>
    unfold Giant.case1Prog
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.baseWinProg n N)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call (hPre _ _ (Or.inr rfl) hprex))
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.call (hPre _ _ (Or.inr rfl) hprey))
    run_step (RunsWithin.orbitPartProg n (N - n) _ hKx hLx)
    run_step (RunsWithin.orbitPartProg n (N - n) _ hKy hLy)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact hrun
  case hc =>
    simp only [Prim.cost, Prim.eval, case1Cost, List.length_cons, List.length_nil]
    have e1 : X.B.call GroupOp.orbits ((N, fxs, ex), baseWin n N)
        (X.O.run GroupOp.orbits ((N, fxs, ex), baseWin n N)) ≤ Box := hBox
    have e2 : X.B.call GroupOp.orbits ((N, fys, ey), baseWin n N)
        (X.O.run GroupOp.orbits ((N, fys, ey), baseWin n N)) ≤ Boy := hBoy
    have e3 : alignCost n N gs.length ((partOps (N - n)).gens X₀).length (0 + 1)
        (partGensCost (N - n) (N - n)) (partIsoCost (N - n) (N - n) (N - n)) BgP Bmem Bk Bl Bg1
        Bgen Cb s = alignCost n N gs.length (partGensD (N - n) X₀).length 1
        (partGensCost (N - n) (N - n)) (partIsoCost (N - n) (N - n) (N - n)) BgP Bmem Bk Bl Bg1
        Bgen Cb s := rfl
    omega

/-- The stabilizer generators of a colored partition of `m` points number at most `m² + m`. -/
theorem c1_length_partGensD (m : ℕ) (x : Array ℕ × Array (List ℕ)) :
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

theorem case1Cost_mono {n N g k k' Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s : ℕ} (h : k ≤ k') :
    case1Cost n N g k Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s ≤
      case1Cost n N g k' Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s := by
  unfold case1Cost alignCost alignCallCost isoInPCost stabInPCost preCost
  gcongr

/-- **The cost of Case 1, in closed form in the generator count**: `case1Cost` with the
partition's stabilizer generators bounded by `(N - n)² + (N - n)`. -/
theorem case1Cost_le (O : Oracle (groupSig D)) {n N g Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s : ℕ}
    (F : GroupData D.denote) :
    case1Cost n N g (partGensD (N - n) (orbitPartModel O n N F)).length Box Boy BgP Bmem Bk Bl
        Bg1 Bgen Cb s ≤
      case1Cost n N g ((N - n) * (N - n) + (N - n)) Box Boy BgP Bmem Bk Bl Bg1 Bgen Cb s :=
  case1Cost_mono (c1_length_partGensD _ _)

end Case1Specs

/-! ### Well-formedness -/

section Wf

open Cost Programs

variable {D : Ty} {S : Signature} {rec : Ty × Ty} {var₁ var₂ : Ty → Type} {r : Bool}
  {Γ : WfCtx var₁ var₂}

theorem wf_c1OrbitProg {os₁ : var₁ (.list (.list .nat))} {os₂ : var₂ (.list (.list .nat))}
    {u₁ : var₁ .nat} {u₂ : var₂ .nat} (hos : ⟨.list (.list .nat), os₁, os₂⟩ ∈ Γ)
    (hu : ⟨.nat, u₁, u₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (c1OrbitProg os₁ u₁) (c1OrbitProg os₂ u₂) := by
  unfold c1OrbitProg
  refine .bind (SoJProg.wf_findProg hos fun Γ' hΓ o₁ o₂ ho => SoJProg.wf_memProg (hΓ hu) ho)
    fun oo₁ oo₂ => ?_
  exact .caseOption (by simp) (.prim _ .nil) fun o₁ o₂ => .ret (by simp)

theorem wf_orbitPartProg {n₁ m₁ : var₁ .nat} {n₂ m₂ : var₂ .nat}
    {os₁ : var₁ (.list (.list .nat))} {os₂ : var₂ (.list (.list .nat))}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hm : ⟨.nat, m₁, m₂⟩ ∈ Γ)
    (hos : ⟨.list (.list .nat), os₁, os₂⟩ ∈ Γ) :
    Prog.Wf (S := S) (rec := rec) r Γ (orbitPartProg n₁ m₁ os₁) (orbitPartProg n₂ m₂ os₂) := by
  unfold orbitPartProg
  refine .bind (.prim _ (.cons hm .nil)) fun bs₁ bs₂ => ?_
  refine .bind (wf_mapList (by simp) fun Γ' hΓ b₁ b₂ hb => ?_) fun obs₁ obs₂ => ?_
  · unfold c1PosOrbitProg
    have hn' := hΓ (List.mem_cons_of_mem _ hn)
    have hos' := hΓ (List.mem_cons_of_mem _ hos)
    refine .bind (.prim _ (.cons hn' (.cons hb .nil))) fun u₁ u₂ => ?_
    exact wf_c1OrbitProg (List.mem_cons_of_mem _ hos') List.mem_cons_self
  refine .bind (wf_mapList (by simp) fun Γ' hΓ o₁ o₂ ho => .prim _ (.cons ho .nil))
    fun ls₁ ls₂ => ?_
  refine .bind (.prim _ (.cons (by simp) .nil)) fun l₁ l₂ => ?_
  refine .bind (Toolkit.wf_filterList (by simp) fun Γ' hΓ b₁ b₂ hb => ?_) fun f₁ f₂ => ?_
  · unfold c1FixTestProg
    have hl := hΓ (List.mem_cons_self (a := (⟨.array .nat, (l₁, l₂)⟩ : Σ t, var₁ t × var₂ t)))
    refine .bind (.prim _ (.cons hl (.cons hb .nil))) fun c₁ c₂ => ?_
    refine .bind (.prim _ .nil) fun o₁ o₂ => ?_
    exact .prim _ (.cons (by simp) (.cons (by simp) .nil))
  refine .bind (.prim _ (.cons (by simp) .nil)) fun oa₁ oa₂ => ?_
  refine .bind (wf_mapList (by simp) fun Γ' hΓ b₁ b₂ hb => ?_) fun rw₁ rw₂ => ?_
  · unfold c1BlkRowProg c1FixTestProg c1ShiftProg
    have hl : ⟨.array .nat, (l₁, l₂)⟩ ∈ Γ' := hΓ (by simp)
    have hoa : ⟨.array (.list .nat), (oa₁, oa₂)⟩ ∈ Γ' := hΓ (by simp)
    have hf : ⟨.list .nat, (f₁, f₂)⟩ ∈ Γ' := hΓ (by simp)
    have hn' : ⟨.nat, (n₁, n₂)⟩ ∈ Γ' := hΓ (by simp [hn])
    refine .bind (.bind (.prim _ (.cons hl (.cons hb .nil))) fun c₁ c₂ =>
      .bind (.prim _ .nil) fun o₁ o₂ => .prim _ (.cons (by simp) (.cons (by simp) .nil)))
      fun t₁ t₂ => ?_
    refine .ite (by simp) (.ret (List.mem_cons_of_mem _ hf)) ?_
    refine .bind (.prim _ (.cons (List.mem_cons_of_mem _ hoa)
      (.cons (List.mem_cons_of_mem _ hb) .nil))) fun o₁ o₂ => ?_
    exact wf_mapList (by simp) fun Γ'' hΓ'' u₁ u₂ hu =>
      .prim _ (.cons hu (.cons (hΓ'' (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn')))
        .nil))
  refine .bind (.prim _ (.cons (by simp) .nil)) fun ba₁ ba₂ => ?_
  exact .prim _ (.cons (by simp) (.cons (by simp) .nil))

theorem wf_case1Prog {sub₁ : var₁ (Ty.inst D) → Prog (groupSig D) rec var₁ (Ty.answer D)}
    {sub₂ : var₂ (Ty.inst D) → Prog (groupSig D) rec var₂ (Ty.answer D)}
    (hsub : WfFun r Γ sub₁ sub₂) {n₁ : var₁ .nat} {n₂ : var₂ .nat}
    {xy₁ : var₁ Ty.strs} {xy₂ : var₂ Ty.strs} {w₁ : var₁ Ty.win} {w₂ : var₂ Ty.win}
    {G₁ Fx₁ Fy₁ : var₁ (Ty.group D)} {G₂ Fx₂ Fy₂ : var₂ (Ty.group D)}
    (hn : ⟨.nat, n₁, n₂⟩ ∈ Γ) (hxy : ⟨Ty.strs, xy₁, xy₂⟩ ∈ Γ) (hw : ⟨Ty.win, w₁, w₂⟩ ∈ Γ)
    (hG : ⟨Ty.group D, G₁, G₂⟩ ∈ Γ) (hFx : ⟨Ty.group D, Fx₁, Fx₂⟩ ∈ Γ)
    (hFy : ⟨Ty.group D, Fy₁, Fy₂⟩ ∈ Γ) :
    Prog.Wf r Γ (case1Prog sub₁ n₁ xy₁ w₁ G₁ Fx₁ Fy₁) (case1Prog sub₂ n₂ xy₂ w₂ G₂ Fx₂ Fy₂) := by
  unfold case1Prog
  refine .bind (.prim _ (.cons hG .nil)) fun N₁ N₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp [hn]) .nil))) fun m₁ m₂ => ?_
  refine .bind (Toolkit.wf_baseWinProg (by simp [hn]) (by simp)) fun bw₁ bw₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hFx]) (.cons (by simp) .nil))) fun a₁ a₂ => ?_
  refine .bind (.call _ (.head _)) fun o₁ o₂ => ?_
  refine .bind (.prim _ (.cons (by simp [hFy]) (.cons (by simp) .nil))) fun b₁ b₂ => ?_
  refine .bind (.call _ (.head _)) fun p₁ p₂ => ?_
  refine .bind (wf_orbitPartProg (by simp [hn]) (by simp)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) fun X₁ X₂ => ?_
  refine .bind (wf_orbitPartProg (by simp [hn]) (by simp)
    (List.mem_cons_of_mem _ List.mem_cons_self)) fun Y₁ Y₂ => ?_
  refine .bind (.prim _ .nil) fun l₁ l₂ => ?_
  refine .bind (.prim _ (.cons (by simp) (.cons (by simp) .nil))) fun Ys₁ Ys₂ => ?_
  exact Align.wf_alignProg (hsub.mono fun z hz => by simp [hz])
    (fun Γ' hΓ' z₁ z₂ hz => wf_partGensProg (hΓ' (by simp)) hz)
    (fun Γ' hΓ' z₁ z₂ y₁ y₂ hz hy => wf_partIsoProg (hΓ' (by simp)) hz hy)
    (by simp [hn]) (by simp [hxy]) (by simp [hw]) (by simp [hG]) (by simp) (by simp)

end Wf

end GraphIso.Giant
