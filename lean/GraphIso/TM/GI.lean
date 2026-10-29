module

public import GraphIso.TM.Main
public import GraphIso.Wielandt.Final

/-!
# Graph isomorphism on Turing machines

Stage 17h (`PLAN-17.md` §11).

* **Graph pairs** (`GraphPair`): `n` and simple graphs `G`, `H` on `Fin n` with decidable
  adjacency. **The encoding** `GraphPair.enc`: the serialization (`ser Ty.giInput`) of `n` and of
  the adjacency lists of `G` and `H`; it is at least `n` long (`GraphPair.n_le_enc`).
* **The specification** `isoDecide`: brute force over the permutations of `Fin n` (it states the
  problem; it is not the algorithm), with
  `isoDecide_iff : isoDecide p = true ↔ Nonempty (p.G ≃g p.H)`.
* **The entries**: `giCosetEntry` is milestone 16's `giEntry` with Schreier–Sims substituted for
  the backend (`ssImpl`), and `giDecEntry` returns `true` exactly when `giCosetEntry` returns
  `some`; both are well formed. The programs `giCosetProg` and `giDecProg` are
  `mainProg (qpSolver 192 181) _` (17g).
* **Decision** (`gi_tm`): there are `c` and a `TM2ComputableInTime GraphPair.enc (ser .bool)
  isoDecide` whose machine is `toFinTM2 giDecProg .inp .out` and whose time on inputs of length
  `L` is at most `2 ^ (c (λ(L) + 1) ^ 8)` (`λ = Nat.log 2`); and on every pair, with `L` the
  length of its encoding, that machine outputs `ser .bool (isoDecide p)` within
  `2 ^ (c (λ(L) + 1) ^ 8)` steps (`gi_dec_exec`: the run of `main`).
* **The coset** (`gi_coset_tm`): there is `c` such that on every pair, with `L` the length of its
  encoding, the machine `toFinTM2 giCosetProg .inp .out` outputs `ser Ty.giCoset r` within
  `2 ^ (c (λ(L) + 1) ^ 8)` steps, where `r = none` exactly when `G` and `H` are not isomorphic,
  and `r = some (τ, hs)` gives valid data of a permutation and of generators such that the coset
  `τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms `G ≃g H`.

The time bounds combine milestone 16 (`gi_simpleGraph_final`, `giSolve_final`: local cost at
most `2 ^ (c₀ (λ(n) + 1) ^ 8)`, at most `4 gN(n)²` generators) with `main_exec` (17g): `n ≤ L`,
and the output (a Boolean, or valid permutation data) has length at most `16 (n + 1) ^ 6`
(`length_ser_coset_le`).
-/

@[expose] public section

namespace GraphIso.TM

open Equiv Pointwise GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion GraphIso.Sims
  GraphIso.Wielandt

/-! ### Graph pairs -/

/-- A pair of simple graphs on `Fin n`, with decidable adjacency. -/
structure GraphPair where
  /-- The number of vertices. -/
  n : ℕ
  /-- The first graph. -/
  G : SimpleGraph (Fin n)
  /-- The second graph. -/
  H : SimpleGraph (Fin n)
  /-- Adjacency in `G` is decidable. -/
  [decG : DecidableRel G.Adj]
  /-- Adjacency in `H` is decidable. -/
  [decH : DecidableRel H.Adj]

attribute [instance] GraphPair.decG GraphPair.decH

namespace GraphPair

/-- The input of the entry: `n` and the adjacency lists of `G` and `H`. -/
def data (p : GraphPair) : Ty.giInput.denote :=
  (p.n, GraphData.ofSimpleGraph p.G, GraphData.ofSimpleGraph p.H)

/-- **The encoding** of a pair: the serialization of its data. -/
def enc (p : GraphPair) : List Sym := ser Ty.giInput p.data

end GraphPair

/-- **The specification**: some permutation of the vertices maps `G` onto `H`, by brute force
over all permutations. -/
def isoDecide (p : GraphPair) : Bool :=
  decide (∃ σ : Perm (Fin p.n), ∀ u v, p.G.Adj u v ↔ p.H.Adj (σ u) (σ v))

theorem isoDecide_iff (p : GraphPair) : isoDecide p = true ↔ Nonempty (p.G ≃g p.H) := by
  unfold isoDecide
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨σ, fun {u v} => (hσ u v).symm⟩⟩
  · rintro ⟨e⟩
    exact ⟨e.toEquiv, fun u v => e.map_adj_iff.symm⟩

/-! ### Lengths of serializations -/

theorem length_le_serElems (a : Ty) (xs : List a.denote) : xs.length ≤ (serElems a xs).length := by
  rw [length_serElems]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- An array's serialization is at least as long as the array. -/
theorem size_le_ser_array (a : Ty) (v : Array a.denote) : v.size ≤ (ser (.array a) v).length := by
  have h := length_le_serElems a v.toList.reverse
  rw [List.length_reverse, Array.length_toList] at h
  show v.size ≤ (serElems a v.toList.reverse ++ [Sym.tag .nil]).length
  rw [List.length_append]
  omega

/-- **The encoding is at least `n` long**: the adjacency array of `G` has `n` entries. -/
theorem GraphPair.n_le_enc (p : GraphPair) : p.n ≤ p.enc.length := by
  have h : (GraphData.ofSimpleGraph p.G).size ≤
      (ser Ty.graph (GraphData.ofSimpleGraph p.G)).length :=
    size_le_ser_array (.list .nat) _
  have hs : (GraphData.ofSimpleGraph p.G).size = p.n := by simp [GraphData.ofSimpleGraph]
  show p.n ≤ (ser .nat p.n ++ (ser Ty.graph (GraphData.ofSimpleGraph p.G) ++
    ser Ty.graph (GraphData.ofSimpleGraph p.H))).length
  simp only [List.length_append]
  omega

theorem length_ser_nat_le (k : ℕ) : (ser .nat k).length ≤ k + 1 := by
  have := length_toBits_le k
  simp [ser, bits]
  omega

/-- An array of numbers below `n`: at most `n + 1` symbols per entry, plus one. -/
theorem length_ser_arrNat_le {n : ℕ} (v : Array ℕ) (hv : ∀ x ∈ v.toList, x < n) :
    (ser (.array .nat) v).length ≤ v.size * (n + 1) + 1 := by
  show (serElems .nat v.toList.reverse ++ [Sym.tag .nil]).length ≤ _
  rw [List.length_append, length_serElems]
  have h := List.sum_le_length_nsmul ((v.toList.reverse).map fun x => (ser .nat x).length + 1)
    (n + 1) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      have := hv x (List.mem_reverse.1 hx)
      have := length_ser_nat_le x
      omega)
  simp only [List.length_map, List.length_reverse, Array.length_toList, smul_eq_mul] at h
  simp only [List.length_singleton]
  omega

theorem permValid_mem_lt {n : ℕ} {d : PermData} (h : d.Valid n) :
    (∀ x ∈ d.1.toList, x < n) ∧ ∀ x ∈ d.2.toList, x < n := by
  constructor
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi₁ : i < d.1.size := by simpa using hi
    have := h.fwd_lt i (h.size_fwd ▸ hi₁)
    simpa [get, Array.getD, hi₁] using this
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi₁ : i < d.2.size := by simpa using hi
    have := h.inv_lt i (h.size_inv ▸ hi₁)
    simpa [get, Array.getD, hi₁] using this

/-- Valid permutation data: at most `2 (n (n + 1) + 1)` symbols. -/
theorem length_ser_perm_le {n : ℕ} {d : PermData} (h : d.Valid n) :
    (ser Ty.perm d).length ≤ 2 * (n * (n + 1) + 1) := by
  obtain ⟨h₁, h₂⟩ := permValid_mem_lt h
  have e₁ := length_ser_arrNat_le d.1 h₁
  have e₂ := length_ser_arrNat_le d.2 h₂
  rw [h.size_fwd] at e₁
  rw [h.size_inv] at e₂
  show (ser (.array .nat) d.1 ++ ser (.array .nat) d.2).length ≤ _
  rw [List.length_append]
  omega

/-- **The output of the coset machine is short**: at most `16 (n + 1) ^ 6` symbols, for valid
data with at most `4 gN(n)²` generators. -/
theorem length_ser_coset_le {n : ℕ} {r : Option (PermData × GensData)}
    (h : ∀ τ hs, r = some (τ, hs) → τ.Valid n ∧ GensData.AllValid n hs ∧
      hs.length ≤ 2 * gN n * (2 * gN n)) :
    (ser Ty.giCoset r).length ≤ 16 * (n + 1) ^ 6 := by
  have hm : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  rcases r with _ | ⟨τ, hs⟩
  · show 1 ≤ _
    omega
  obtain ⟨hτ, hv, hl⟩ := h τ hs rfl
  have hP : (ser Ty.perm τ).length ≤ 2 * (n * (n + 1) + 1) := length_ser_perm_le hτ
  have hgs : (ser Ty.gens hs).length ≤ hs.length * (2 * (n * (n + 1) + 1) + 1) + 1 := by
    show (serElems Ty.perm hs ++ [Sym.tag .nil]).length ≤ _
    rw [List.length_append, length_serElems]
    have := List.sum_le_length_nsmul (hs.map fun x => (ser Ty.perm x).length + 1)
      (2 * (n * (n + 1) + 1) + 1) (by
        intro y hy
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
        have := length_ser_perm_le (hv g hg)
        omega)
    simp only [List.length_map, smul_eq_mul] at this
    simp only [List.length_singleton]
    omega
  show (Sym.tag .some :: (ser Ty.perm τ ++ ser Ty.gens hs)).length ≤ _
  simp only [List.length_cons, List.length_append]
  have hm2 : n * (n + 1) + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have hgN : 2 * gN n * (2 * gN n) ≤ 4 * (n + 1) ^ 4 := by
    have : gN n ≤ (n + 1) ^ 2 := by unfold gN; nlinarith
    calc 2 * gN n * (2 * gN n) = 4 * (gN n * gN n) := by ring
      _ ≤ 4 * ((n + 1) ^ 2 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul this this)
      _ = 4 * (n + 1) ^ 4 := by ring
  have hk : hs.length * (2 * (n * (n + 1) + 1) + 1) ≤ 4 * (n + 1) ^ 4 * (3 * (n + 1) ^ 2) :=
    Nat.mul_le_mul (hl.trans hgN) (by omega)
  have h6 : 4 * (n + 1) ^ 4 * (3 * (n + 1) ^ 2) = 12 * (n + 1) ^ 6 := by ring
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
  omega

/-! ### The entries -/

/-- **The coset entry**: milestone 16's entry, with Schreier–Sims substituted for the
backend. -/
def giCosetEntry (var : Ty → Type) (x : var Ty.giInput) :
    Prog Signature.empty (hinstTy Ty.unit, Ty.answer Ty.unit) var Ty.giCoset :=
  (giEntry Ty.unit var x).subst ssImpl

/-- **The decision entry**: the coset entry, then `true` exactly when its result is `some`. -/
def giDecEntry (var : Ty → Type) (x : var Ty.giInput) :
    Prog Signature.empty (hinstTy Ty.unit, Ty.answer Ty.unit) var .bool :=
  .bind (giCosetEntry var x) fun r =>
    .caseOption r (.op0 (.boolLit false)) fun _ => .op0 (.boolLit true)

theorem giCosetEntry_wf {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput) (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (giCosetEntry var₁ x₁) (giCosetEntry var₂ x₂) :=
  (giEntry_wf (D := Ty.unit) x₁ x₂).subst ssImpl_wf

theorem giDecEntry_wf {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput) (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (giDecEntry var₁ x₁) (giDecEntry var₂ x₂) :=
  .bind (giCosetEntry_wf x₁ x₂) fun _ _ =>
    .caseOption (by simp) (.prim _ .nil) fun _ _ => .prim _ .nil

/-- The program of the decision machine. -/
def giDecProg : Program Stk Sym Rg Bool := mainProg (qpSolver 192 181) giDecEntry

/-- The program of the coset machine. -/
def giCosetProg : Program Stk Sym Rg Bool := mainProg (qpSolver 192 181) giCosetEntry

/-- The run of the decision entry: the run of the coset entry, a branch and a literal. -/
theorem runs_giDec {O : Oracle Signature.empty} {x : Ty.giInput.denote}
    {r : Option (PermData × GensData)} {tr : Trace Signature.empty}
    (hr : Runs O ((qpSolver 192 181).proc Ty.denote) (giCosetEntry Ty.denote x) r tr) :
    Runs O ((qpSolver 192 181).proc Ty.denote) (giDecEntry Ty.denote x) (Option.isSome r)
      (tr ++ [.local .branch 1, .local .prim 1]) := by
  refine runs_bind.2 ⟨r, tr, _, hr, ?_, rfl⟩
  cases r with
  | none => exact runs_caseOption_none.2 ⟨_, runs_prim.2 ⟨rfl, rfl⟩, rfl⟩
  | some _ => exact runs_caseOption_some.2 ⟨_, runs_prim.2 ⟨rfl, rfl⟩, rfl⟩

/-- **Milestone 16 at a graph pair**: the run of the coset entry, within local cost
`2 ^ (c (λ(n) + 1) ^ 8)`, with its answer and at most `4 gN(n)²` generators. -/
theorem gi_runs : ∃ c, ∀ p : GraphPair, ∃ (r : Option (PermData × GensData))
    (tr : Trace Signature.empty),
    Runs Ctx.empty.O ((qpSolver 192 181).proc Ty.denote) (giCosetEntry Ty.denote p.data) r tr ∧
    Trace.localCost tr ≤ 2 ^ (c * (lam p.n + 1) ^ 8) ∧
    (r = none ↔ IsEmpty (p.G ≃g p.H)) ∧
    ∀ τ hs, r = some (τ, hs) → τ.Valid p.n ∧ GensData.AllValid p.n hs ∧
      hs.length ≤ 2 * gN p.n * (2 * gN p.n) ∧
      {φ : Perm (Fin p.n) | ∃ e : p.G ≃g p.H, e.toEquiv = φ} =
        PermData.denote p.n τ • (GensData.denote p.n hs : Set (Perm (Fin p.n))) := by
  obtain ⟨c, hc⟩ := gi_simpleGraph_final
  obtain ⟨c', hc'⟩ := giSolve_final
  refine ⟨c, fun p => ?_⟩
  obtain ⟨r, tr, hr, hcost, hnone, hsome⟩ := hc p.G p.H
  have hG := valid_ofSimpleGraph (Δ := p.n) (H := p.G) fun v =>
    (p.G.degree_lt_card_verts v).le.trans (by simp)
  have hH := valid_ofSimpleGraph (Δ := p.n) (H := p.H) fun v =>
    (p.H.degree_lt_card_verts v).le.trans (by simp)
  obtain ⟨r', tr', hr', -, -, hsome'⟩ := hc' hG hH
  obtain ⟨rfl, -⟩ := hr.unique hr'
  refine ⟨r, tr, hr, hcost, hnone, fun τ hs h => ?_⟩
  obtain ⟨hv, hav, hset⟩ := hsome τ hs h
  obtain ⟨-, -, hlen, -⟩ := hsome' τ hs h
  exact ⟨hv, hav, hlen, hset⟩

/-! ### The time bound -/

theorem exp_arith {κ c₀ e : ℕ} (he : 1 ≤ e) :
    (κ + (c₀ * e + 2)) * 120 + 1 ≤ (120 * (κ + c₀ + 2) + 1) * e := by
  nlinarith [Nat.mul_le_mul_left κ he]

/-- `(κ (C + L + L' + 1)) ^ 120 + 1 ≤ 2 ^ ((120 (κ + c₀ + 2) + 1) e)` when `C`, `L` and `L'` are
at most `2 ^ (c₀ e)` and `e ≥ 1`. -/
theorem poly_le_exp {κ c₀ e C L L' : ℕ} (he : 1 ≤ e) (hC : C ≤ 2 ^ (c₀ * e))
    (hL : L ≤ 2 ^ (c₀ * e)) (hL' : L' ≤ 2 ^ (c₀ * e)) :
    (κ * (C + L + L' + 1)) ^ 120 + 1 ≤ 2 ^ ((120 * (κ + c₀ + 2) + 1) * e) := by
  have h1 : 1 ≤ 2 ^ (c₀ * e) := Nat.one_le_two_pow
  have hsum : C + L + L' + 1 ≤ 2 ^ (c₀ * e + 2) := by
    rw [pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
    omega
  have hprod : κ * (C + L + L' + 1) ≤ 2 ^ (κ + (c₀ * e + 2)) := by
    rw [pow_add]
    exact Nat.mul_le_mul Nat.lt_two_pow_self.le hsum
  have hpow : (κ * (C + L + L' + 1)) ^ 120 ≤ 2 ^ ((κ + (c₀ * e + 2)) * 120) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left hprod 120
  have hexp := exp_arith (κ := κ) (c₀ := c₀) he
  have h2 : 1 ≤ 2 ^ ((κ + (c₀ * e + 2)) * 120) := Nat.one_le_two_pow
  calc (κ * (C + L + L' + 1)) ^ 120 + 1
      ≤ 2 ^ ((κ + (c₀ * e + 2)) * 120) * 2 := by omega
    _ = 2 ^ ((κ + (c₀ * e + 2)) * 120 + 1) := (pow_succ _ _).symm
    _ ≤ 2 ^ ((120 * (κ + c₀ + 2) + 1) * e) := Nat.pow_le_pow_right (by norm_num) hexp

/-- **The bound on graph pairs**: with `n ≤ L`, a local cost of at most
`2 ^ (c (λ(n) + 1) ^ 8) + 2` and an output of at most `16 (n + 1) ^ 6` symbols, `mainPoly + 1`
is at most `2 ^ ((120 (κ + c + 12) + 1) (λ(L) + 1) ^ 8)`. -/
theorem gi_bound {a b t : Ty} (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var Ty.giInput → Prog Signature.empty (a, b) var t)
    {c n L C L' : ℕ} (hn : n ≤ L) (hC : C ≤ 2 ^ (c * (lam n + 1) ^ 8) + 2)
    (hL' : L' ≤ 16 * (n + 1) ^ 6) :
    mainPoly Pr E C L L' + 1 ≤
      2 ^ ((120 * (kappa (wt Ty.giInput) (wt t) (kP Pr E) (dP Pr E) (psize 1 (E Lv 0)) +
        (c + 10) + 2) + 1) * (lam L + 1) ^ 8) := by
  have he : 1 ≤ (lam L + 1) ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hlam : lam n + 1 ≤ lam L + 1 := Nat.add_le_add_right (Nat.log_mono_right hn) 1
  have hl8 : lam L + 1 ≤ (lam L + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hn8 : (lam n + 1) ^ 8 ≤ (lam L + 1) ^ 8 := Nat.pow_le_pow_left hlam 8
  have hLp : L < 2 ^ (lam L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have hnp : n + 1 ≤ 2 ^ (lam n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h16 : 16 * (n + 1) ^ 6 ≤ 2 ^ (4 + (lam n + 1) * 6) := by
    rw [pow_add, pow_mul, show (2 : ℕ) ^ 4 = 16 by norm_num]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnp 6)
  have hcn : 2 ^ (c * (lam n + 1) ^ 8) ≤ 2 ^ (c * (lam L + 1) ^ 8) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hn8)
  unfold mainPoly
  generalize (lam L + 1) ^ 8 = X at *
  have hC' : C ≤ 2 ^ ((c + 10) * X) := by
    have h₂ : 2 ^ (c * X) * 4 ≤ 2 ^ ((c + 10) * X) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul c 10 X]; omega)
    have h₃ : 1 ≤ 2 ^ (c * X) := Nat.one_le_two_pow
    omega
  have hL : L ≤ 2 ^ ((c + 10) * X) := by
    have h₂ : 2 ^ (lam L + 1) ≤ 2 ^ ((c + 10) * X) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul c 10 X]; omega)
    omega
  have hL'' : L' ≤ 2 ^ ((c + 10) * X) := by
    have h₃ : 2 ^ (4 + (lam n + 1) * 6) ≤ 2 ^ ((c + 10) * X) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul c 10 X]; omega)
    omega
  exact poly_le_exp he hC' hL hL''

/-! ### The machines -/

/-- **The run of the decision program**: there is `A` such that on every pair, with `L` the
length of its encoding, `main` of `giDecProg` runs from the input configuration of the encoding
to the output configuration of `ser .bool (isoDecide p)` within `2 ^ ((A + 1) (λ(L) + 1) ^ 8)`
steps. -/
theorem gi_dec_exec : ∃ A, ∀ p : GraphPair, ∃ n ≤ 2 ^ ((A + 1) * (lam p.enc.length + 1) ^ 8),
    Exec giDecProg (giDecProg.body giDecProg.main) (inCfg .inp p.enc)
      (inCfg .out (ser .bool (isoDecide p))) n := by
  obtain ⟨c, hc⟩ := gi_runs
  refine ⟨120 * (kappa (wt Ty.giInput) (wt .bool) (kP (qpSolver 192 181) giDecEntry)
      (dP (qpSolver 192 181) giDecEntry) (psize 1 (giDecEntry Lv 0)) + (c + 10) + 2),
    fun p => ?_⟩
  obtain ⟨r, tr, hr, hcost, hnone, -⟩ := hc p
  have hb : Option.isSome r = isoDecide p := by
    rw [Bool.eq_iff_iff, isoDecide_iff, Option.isSome_iff_ne_none, Ne, hnone, not_isEmpty_iff]
  obtain ⟨n, e, hn⟩ := main_exec (qpSolver 192 181) giDecEntry giDecEntry_wf Ctx.empty.O
    (runs_giDec hr)
  rw [hb] at e
  refine ⟨n, ?_, e⟩
  have hC : Trace.localCost (tr ++ [.local .branch 1, .local .prim 1]) ≤
      2 ^ (c * (lam p.n + 1) ^ 8) + 2 := by
    rw [Trace.localCost_append]
    exact Nat.add_le_add hcost le_rfl
  have hL' : (ser .bool (Option.isSome r)).length ≤ 16 * (p.n + 1) ^ 6 := by
    have := Nat.one_le_pow 6 (p.n + 1) (Nat.succ_pos _)
    show 1 ≤ _
    omega
  exact hn.trans (Nat.le_of_succ_le (gi_bound (qpSolver 192 181) giDecEntry p.n_le_enc hC hL'))

/-- `2 ^ ((A + 1) X) + 1 ≤ 2 ^ ((A + 2) X)` for `X = (λ(L) + 1) ^ 8`. -/
theorem exp_succ_le (A L : ℕ) :
    2 ^ ((A + 1) * (lam L + 1) ^ 8) + 1 ≤ 2 ^ ((A + 2) * (lam L + 1) ^ 8) := by
  have he : 1 ≤ (lam L + 1) ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  generalize (lam L + 1) ^ 8 = X at *
  have h1 : 1 ≤ 2 ^ ((A + 1) * X) := Nat.one_le_two_pow
  calc 2 ^ ((A + 1) * X) + 1 ≤ 2 ^ ((A + 1) * X) * 2 := by omega
    _ = 2 ^ ((A + 1) * X + 1) := (pow_succ _ _).symm
    _ ≤ 2 ^ ((A + 2) * X) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [Nat.add_mul A 1, Nat.add_mul A 2]; omega)

/-- **Graph isomorphism decided by a Turing machine in time `2 ^ (c (λ(L) + 1) ^ 8)`.** There are
`c` and a `TM2ComputableInTime` structure computing `isoDecide` from the encoding of a graph
pair, whose machine is `toFinTM2 giDecProg .inp .out` and whose time on inputs of length `L` is
at most `2 ^ (c (λ(L) + 1) ^ 8)`; and on every pair `p`, with `L` the length of its encoding,
that machine outputs `ser .bool (isoDecide p)` within `2 ^ (c (λ(L) + 1) ^ 8)` steps. -/
theorem gi_tm : ∃ c, ∃ M : Turing.TM2ComputableInTime GraphPair.enc (ser .bool) isoDecide,
    M.tm = toFinTM2 giDecProg .inp .out ∧ (∀ L, M.time L ≤ 2 ^ (c * (lam L + 1) ^ 8)) ∧
    ∀ p : GraphPair, Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) p.enc
      (some (ser .bool (isoDecide p))) (2 ^ (c * (lam p.enc.length + 1) ^ 8))) := by
  obtain ⟨A, hA⟩ := gi_dec_exec
  refine ⟨A + 2, computableInTime giDecProg .inp .out GraphPair.enc (ser .bool) isoDecide
    (fun L => 2 ^ ((A + 1) * (lam L + 1) ^ 8)) hA, rfl, exp_succ_le A, fun p => ?_⟩
  obtain ⟨n, hn, e⟩ := hA p
  have M := outputsInTime giDecProg .inp .out e
  refine ⟨{ toEvalsTo := M.toEvalsTo, steps_le_m := ?_ }⟩
  have h1 := M.steps_le_m
  exact h1.trans ((Nat.add_le_add_right hn 1).trans (exp_succ_le A _))

/-- **The coset of all isomorphisms output by a Turing machine in time
`2 ^ (c (λ(L) + 1) ^ 8)`.** There is `c` such that for every graph pair `p`, with `L` the length
of its encoding, the machine `toFinTM2 giCosetProg .inp .out` outputs `ser Ty.giCoset r` within
`2 ^ (c (λ(L) + 1) ^ 8)` steps, where `r = none` exactly when `G` and `H` are not isomorphic, and
`r = some (τ, hs)` gives valid data of a permutation and of generators such that the coset
`τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms `G ≃g H`. -/
theorem gi_coset_tm : ∃ c, ∀ p : GraphPair, ∃ r : Option (PermData × GensData),
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giCosetProg .inp .out) p.enc
      (some (ser Ty.giCoset r)) (2 ^ (c * (lam p.enc.length + 1) ^ 8))) ∧
    (r = none ↔ IsEmpty (p.G ≃g p.H)) ∧
    ∀ τ hs, r = some (τ, hs) → τ.Valid p.n ∧ GensData.AllValid p.n hs ∧
      {φ : Perm (Fin p.n) | ∃ e : p.G ≃g p.H, e.toEquiv = φ} =
        PermData.denote p.n τ • (GensData.denote p.n hs : Set (Perm (Fin p.n))) := by
  obtain ⟨c, hc⟩ := gi_runs
  refine ⟨120 * (kappa (wt Ty.giInput) (wt Ty.giCoset) (kP (qpSolver 192 181) giCosetEntry)
      (dP (qpSolver 192 181) giCosetEntry) (psize 1 (giCosetEntry Lv 0)) + (c + 10) + 2) + 1,
    fun p => ?_⟩
  obtain ⟨r, tr, hr, hcost, hnone, hsome⟩ := hc p
  refine ⟨r, ⟨?_⟩, hnone, fun τ hs h => ?_⟩
  · have M := main_tm (qpSolver 192 181) giCosetEntry giCosetEntry_wf Ctx.empty.O hr
    have hL' := length_ser_coset_le (n := p.n) (r := r) fun τ hs h =>
      (hsome τ hs h).elim fun h₁ h₂ => ⟨h₁, h₂.1, h₂.2.1⟩
    have hm := gi_bound (qpSolver 192 181) giCosetEntry p.n_le_enc
      (hcost.trans (Nat.le_add_right _ 2)) hL'
    refine { toEvalsTo := M.toEvalsTo, steps_le_m := ?_ }
    have h1 := M.steps_le_m
    exact h1.trans hm
  · obtain ⟨h₁, h₂, -, h₃⟩ := hsome τ hs h
    exact ⟨h₁, h₂, h₃⟩

end GraphIso.TM
