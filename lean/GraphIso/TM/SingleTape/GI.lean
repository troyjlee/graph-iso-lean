module

public import GraphIso.TM.Vertices
public import GraphIso.TM.SingleTape.Programs
public import GraphIso.TM.SingleTape.Compile

/-!
# Graph isomorphism on a single tape

Stage 18f (`PLAN-18.md` §7). The two machines of milestone 17, `toFinTM2 giDecProg .inp .out`
and `toFinTM2 giCosetProg .inp .out`, compiled by stage 18e to finite single-tape machines
(`giDecTM0`, `giCosetTM0`: mathlib's `TM0` machines with finitely many states and symbols, fixed
independently of the input). The input tape of a graph pair `p` is `encodeIn p.enc`, its
encoding framed by two marks (`L₀ = |p.enc| + 2` symbols), and the output tape is the framed
serialization of the answer. Only the transitions of the single-tape machines are counted,
including the preparation of the input and the cleanup of the output.

* **The growth** (`compile_growth`): `C (L + 2 ^ (c (λ(L) + 1) ^ 8) + 1)² ≤
  2 ^ ((C + 2 c + 4) (λ(L + 2) + 1) ^ 8)` for all `C`, `c`, `L` (`λ = Nat.log 2`): the
  compiler's quadratic overhead changes the constant, not the exponent `8`.
* **In the input's length** (`gi_tm0`, `gi_coset_tm0`): there is `c` such that on every graph
  pair `p` the single-tape machine outputs the framed answer on `encodeIn p.enc` within
  `2 ^ (c (λ(L₀) + 1) ^ 8)` transitions, `L₀` the length of the input tape. The decision's answer
  is `ser .bool (isoDecide p)`, with `isoDecide p = true ↔ Nonempty (p.G ≃g p.H)`
  (`isoDecide_iff`); the coset machine's answer `r` is `none` exactly when there is no
  isomorphism, and otherwise valid data whose left coset is the set of all isomorphisms.
* **In the number of vertices** (`gi_tm0_vertices`, `gi_coset_tm0_vertices`): the same machines
  and outputs within `2 ^ (c (λ(n) + 1) ^ 8)` transitions on graphs with `n` vertices
  (`GraphPair.lam_tape_le`: `λ(L₀) + 1 ≤ 8 (λ(n) + 1)`).
-/

@[expose] public section

namespace GraphIso.TM

open Equiv Pointwise GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion

/-- **The single-tape decision machine**: the decision machine of milestone 17 compiled to a
finite single-tape machine. -/
def giDecTM0 : SingleTape.FinTM0 :=
  SingleTape.compile (toFinTM2 giDecProg .inp .out) (finite_toFinTM2 giDecProg .inp .out)

/-- **The single-tape coset machine.** -/
def giCosetTM0 : SingleTape.FinTM0 :=
  SingleTape.compile (toFinTM2 giCosetProg .inp .out) (finite_toFinTM2 giCosetProg .inp .out)

/-- **The growth**: the compiler's quadratic overhead on a time `2 ^ (c (λ(L) + 1) ^ 8)` changes
the constant, not the exponent. -/
theorem compile_growth (C c L : ℕ) :
    C * (L + 2 ^ (c * (lam L + 1) ^ 8) + 1) ^ 2 ≤
      2 ^ ((C + 2 * c + 4) * (lam (L + 2) + 1) ^ 8) := by
  have hX : 1 ≤ (lam L + 1) ^ 8 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have haX : lam L + 1 ≤ (lam L + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hL : L + 1 ≤ 2 ^ (lam L + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have hmono : (lam L + 1) ^ 8 ≤ (lam (L + 2) + 1) ^ 8 :=
    Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.log_mono_right (by omega))) 8
  generalize (lam L + 1) ^ 8 = X at hX haX hmono ⊢
  generalize lam L + 1 = a at haX hL
  have h₁ : 2 ^ a ≤ 2 ^ (a + c * X) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₂ : 2 ^ (c * X) ≤ 2 ^ (a + c * X) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsum : L + 2 ^ (c * X) + 1 ≤ 2 ^ (a + c * X + 1) := by
    rw [pow_succ]
    omega
  have hC : C ≤ 2 ^ C := Nat.lt_two_pow_self.le
  have hCX : C * 1 ≤ C * X := Nat.mul_le_mul_left C hX
  calc C * (L + 2 ^ (c * X) + 1) ^ 2 ≤ 2 ^ C * (2 ^ (a + c * X + 1)) ^ 2 :=
        Nat.mul_le_mul hC (Nat.pow_le_pow_left hsum 2)
    _ = 2 ^ (C + 2 * (a + c * X + 1)) := by rw [← pow_mul, ← pow_add, Nat.mul_comm _ 2]
    _ ≤ 2 ^ ((C + 2 * c + 4) * X) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    _ ≤ 2 ^ ((C + 2 * c + 4) * (lam (L + 2) + 1) ^ 8) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hmono)

/-- **`λ(L₀) + 1 ≤ 8 (λ(n) + 1)`** for `L₀ = |p.enc| + 2` the length of the input tape of a pair
on `n` vertices. -/
theorem GraphPair.lam_tape_le (p : GraphPair) :
    lam (p.enc.length + 2) + 1 ≤ 8 * (lam p.n + 1) := by
  have hn : p.n + 1 ≤ 2 ^ (lam p.n + 1) := Nat.lt_pow_succ_log_self (by norm_num) p.n
  have hp : p.enc.length + 2 ≤ 2 ^ (3 + 3 * (lam p.n + 1)) := by
    have h₁ := p.enc_length_le
    have h₂ : 1 ≤ (p.n + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
    calc p.enc.length + 2 ≤ 8 * (p.n + 1) ^ 3 := by omega
      _ ≤ 8 * (2 ^ (lam p.n + 1)) ^ 3 := Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hn 3)
      _ = 2 ^ (3 + 3 * (lam p.n + 1)) := by
        rw [pow_add (2 : ℕ) 3 (3 * (lam p.n + 1)), Nat.mul_comm 3 (lam p.n + 1), pow_mul]
        norm_num
  have hlt : p.enc.length + 2 < 2 ^ (8 * (lam p.n + 1)) :=
    hp.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact Nat.log_lt_of_lt_pow (by omega) hlt

/-- `2 ^ (c (λ(L₀) + 1) ^ 8) ≤ 2 ^ (c 8⁸ (λ(n) + 1) ^ 8)`. -/
theorem exp_tape_le_vertices (c : ℕ) (p : GraphPair) :
    2 ^ (c * (lam (p.enc.length + 2) + 1) ^ 8) ≤ 2 ^ (c * 8 ^ 8 * (lam p.n + 1) ^ 8) := by
  apply Nat.pow_le_pow_right (by norm_num)
  calc c * (lam (p.enc.length + 2) + 1) ^ 8 ≤ c * (8 * (lam p.n + 1)) ^ 8 :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left p.lam_tape_le 8)
    _ = c * 8 ^ 8 * (lam p.n + 1) ^ 8 := by rw [mul_pow, mul_assoc]

/-- The input tape of the decision machine: `|p.enc| + 2` symbols. -/
theorem length_giDec_tape (p : GraphPair) :
    (SingleTape.encodeIn p.enc : List giDecTM0.Γ).length = p.enc.length + 2 :=
  SingleTape.length_encodeIn _

/-- The input tape of the coset machine: `|p.enc| + 2` symbols. -/
theorem length_giCoset_tape (p : GraphPair) :
    (SingleTape.encodeIn p.enc : List giCosetTM0.Γ).length = p.enc.length + 2 :=
  SingleTape.length_encodeIn _

/-! ### The machines -/

/-- **Graph isomorphism decided by a single-tape machine in time `2 ^ (c (λ(L₀) + 1) ^ 8)`.**
There is `c` such that on every graph pair `p` the finite single-tape machine `giDecTM0`, started
on the input tape `encodeIn p.enc` of length `L₀`, halts after at most `2 ^ (c (λ(L₀) + 1) ^ 8)`
transitions with the tape `encodeOut (ser .bool (isoDecide p))`, its head on the first symbol and
blanks elsewhere. -/
theorem gi_tm0 : ∃ c, ∀ p : GraphPair,
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn p.enc)
      (SingleTape.encodeOut (ser .bool (isoDecide p)))
      (2 ^ (c * (lam (SingleTape.encodeIn p.enc : List giDecTM0.Γ).length + 1) ^ 8)) := by
  obtain ⟨c, -, -, -, hc⟩ := gi_tm
  refine ⟨SingleTape.compileConst (toFinTM2 giDecProg .inp .out) + 2 * c + 4, fun p => ?_⟩
  obtain ⟨h⟩ := hc p
  rw [length_giDec_tape]
  exact (SingleTape.compile_outputs _ _ h).mono (compile_growth _ _ _)

/-- **The coset of all isomorphisms output by a single-tape machine in time
`2 ^ (c (λ(L₀) + 1) ^ 8)`.** There is `c` such that for every graph pair `p` the finite
single-tape machine `giCosetTM0`, started on `encodeIn p.enc` of length `L₀`, halts after at most
`2 ^ (c (λ(L₀) + 1) ^ 8)` transitions with the tape `encodeOut (ser Ty.giCoset r)`, where
`r = none` exactly when `G` and `H` are not isomorphic, and `r = some (τ, hs)` gives valid data
of a permutation and of generators such that the coset `τ • ⟨hs⟩` is exactly the set of the
permutations underlying the isomorphisms `G ≃g H`. -/
theorem gi_coset_tm0 : ∃ c, ∀ p : GraphPair, ∃ r : Option (PermData × GensData),
    SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn p.enc)
      (SingleTape.encodeOut (ser Ty.giCoset r))
      (2 ^ (c * (lam (SingleTape.encodeIn p.enc : List giCosetTM0.Γ).length + 1) ^ 8)) ∧
    (r = none ↔ IsEmpty (p.G ≃g p.H)) ∧
    ∀ τ hs, r = some (τ, hs) → τ.Valid p.n ∧ GensData.AllValid p.n hs ∧
      {φ : Perm (Fin p.n) | ∃ e : p.G ≃g p.H, e.toEquiv = φ} =
        PermData.denote p.n τ • (GensData.denote p.n hs : Set (Perm (Fin p.n))) := by
  obtain ⟨c, hc⟩ := gi_coset_tm
  refine ⟨SingleTape.compileConst (toFinTM2 giCosetProg .inp .out) + 2 * c + 4, fun p => ?_⟩
  obtain ⟨r, ⟨h⟩, hnone, hsome⟩ := hc p
  refine ⟨r, ?_, hnone, hsome⟩
  rw [length_giCoset_tape]
  exact (SingleTape.compile_outputs _ _ h).mono (compile_growth _ _ _)

/-- **Graph isomorphism decided by a single-tape machine in time `2 ^ (c (λ(n) + 1) ^ 8)` on
graphs with `n` vertices.** There is `c` such that on every graph pair `p` on `n` vertices the
finite single-tape machine `giDecTM0`, started on `encodeIn p.enc`, halts after at most
`2 ^ (c (λ(n) + 1) ^ 8)` transitions with the tape `encodeOut (ser .bool (isoDecide p))`. -/
theorem gi_tm0_vertices : ∃ c, ∀ p : GraphPair,
    SingleTape.TM0OutputsInTime giDecTM0 (SingleTape.encodeIn p.enc)
      (SingleTape.encodeOut (ser .bool (isoDecide p))) (2 ^ (c * (lam p.n + 1) ^ 8)) := by
  obtain ⟨c, hc⟩ := gi_tm0
  refine ⟨c * 8 ^ 8, fun p => (hc p).mono ?_⟩
  rw [length_giDec_tape]
  exact exp_tape_le_vertices c p

/-- **The coset of all isomorphisms output by a single-tape machine in time
`2 ^ (c (λ(n) + 1) ^ 8)` on graphs with `n` vertices**, with the full specification of
`gi_coset_tm0`. -/
theorem gi_coset_tm0_vertices : ∃ c, ∀ p : GraphPair, ∃ r : Option (PermData × GensData),
    SingleTape.TM0OutputsInTime giCosetTM0 (SingleTape.encodeIn p.enc)
      (SingleTape.encodeOut (ser Ty.giCoset r)) (2 ^ (c * (lam p.n + 1) ^ 8)) ∧
    (r = none ↔ IsEmpty (p.G ≃g p.H)) ∧
    ∀ τ hs, r = some (τ, hs) → τ.Valid p.n ∧ GensData.AllValid p.n hs ∧
      {φ : Perm (Fin p.n) | ∃ e : p.G ≃g p.H, e.toEquiv = φ} =
        PermData.denote p.n τ • (GensData.denote p.n hs : Set (Perm (Fin p.n))) := by
  obtain ⟨c, hc⟩ := gi_coset_tm0
  refine ⟨c * 8 ^ 8, fun p => ?_⟩
  obtain ⟨r, h, hnone, hsome⟩ := hc p
  refine ⟨r, h.mono ?_, hnone, hsome⟩
  rw [length_giCoset_tape]
  exact exp_tape_le_vertices c p

end GraphIso.TM
