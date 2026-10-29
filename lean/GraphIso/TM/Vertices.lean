module

public import GraphIso.TM.GI

/-!
# Graph isomorphism on Turing machines, in the number of vertices

Stage 18a (`PLAN-18.md` §2). The time bounds of `gi_tm` and `gi_coset_tm` are in the length `L`
of the input's encoding; here they are restated in the number of vertices `n`, for the same
machines and the same encoding.

* **The encoding's length.** For a list of naturals below `n`,
  `(ser (.list .nat) xs).length ≤ |xs| (n + 1) + 1` (`length_ser_natList_le`); for valid graph
  data on `n` points of degree at most `n` (`GraphData.ValidD n n`),
  `(ser Ty.graph X).length ≤ n (n (n + 1) + 2) + 1` (`length_ser_graph_le`); for every graph
  pair, `p.enc.length ≤ 5 (n + 1)³` (`GraphPair.enc_length_le`), and so
  `λ(L) + 1 ≤ 8 (λ(n) + 1)` (`GraphPair.lam_enc_le`, `λ = Nat.log 2`). The cubic bound is coarse
  (the encoding has `O(n² log n)` symbols); it only relates the two parameters.
* **`exp_enc_le_vertices`**: `2 ^ (c (λ(L) + 1) ^ 8) ≤ 2 ^ (c 8⁸ (λ(n) + 1) ^ 8)`, and
  `outputsInTime_mono`: a timed output within `m` steps is one within any `m' ≥ m`.
* **Decision** (`gi_tm_vertices`): there is `c` such that on every pair `p` the machine
  `toFinTM2 giDecProg .inp .out` outputs `ser .bool (isoDecide p)` on `p.enc` within
  `2 ^ (c (λ(n) + 1) ^ 8)` steps (`isoDecide_iff : isoDecide p = true ↔ Nonempty (p.G ≃g p.H)`).
* **The coset** (`gi_coset_tm_vertices`): `gi_coset_tm` with the time `2 ^ (c (λ(n) + 1) ^ 8)`:
  on every pair `p` the machine `toFinTM2 giCosetProg .inp .out` outputs `ser Ty.giCoset r`
  on `p.enc` within that time, where `r = none` exactly when `p.G` and `p.H` are not
  isomorphic, and `r = some (τ, hs)` gives valid data of a permutation and of generators such
  that the coset `τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms
  `p.G ≃g p.H`.

Both take the constant of the input-length theorem times `8⁸`, with the same runs. The
structure `TM2ComputableInTime` of `gi_tm` keeps its time in the input's length (its `time`
field is applied to the length of the encoding), so it is not restated.
-/

@[expose] public section

namespace GraphIso.TM

open Equiv Pointwise GraphIso.Cost GraphIso.Graph GraphIso.Main GraphIso.Recursion

/-! ### The encoding's length -/

/-- A list of naturals below `n` serializes to at most `|xs| (n + 1) + 1` symbols. -/
theorem length_ser_natList_le (n : ℕ) (xs : List ℕ) (hx : ∀ x ∈ xs, x < n) :
    (ser (.list .nat) xs).length ≤ xs.length * (n + 1) + 1 := by
  rw [ser_list, List.length_append, length_serElems]
  have h := List.sum_le_length_nsmul (xs.map fun x => (ser .nat x).length + 1) (n + 1) (by
    intro y hy
    obtain ⟨x, hx', rfl⟩ := List.mem_map.1 hy
    have := hx x hx'
    have := length_ser_nat_le x
    omega)
  simp only [List.length_map, smul_eq_mul] at h
  simp only [List.length_singleton]
  omega

/-- Valid graph data on `n` points of degree at most `n` serializes to at most
`n (n (n + 1) + 2) + 1` symbols. -/
theorem length_ser_graph_le {n : ℕ} (G : GraphData) (hG : G.ValidD n n) :
    (ser Ty.graph G).length ≤ n * (n * (n + 1) + 2) + 1 := by
  change (ser (.array (.list .nat)) G).length ≤ _
  rw [ser_array, List.length_append, length_serElems]
  have h := List.sum_le_length_nsmul
    (G.toList.reverse.map fun xs => (ser (.list .nat) xs).length + 1) (n * (n + 1) + 2) (by
      intro y hy
      obtain ⟨xs, hxs, rfl⟩ := List.mem_map.1 hy
      obtain ⟨i, hi, heq⟩ := List.getElem_of_mem (List.mem_reverse.1 hxs)
      have hiG : i < G.size := by simpa using hi
      have hnbr : nbrs G i = xs := by
        simpa [nbrs, Array.getD, hiG] using heq
      have hdeg : xs.length ≤ n := hnbr ▸ hG.deg i
      have hlt : ∀ x ∈ xs, x < n := fun x hx =>
        hG.lt i x (by simpa [Adj, hnbr] using hx)
      have hl := length_ser_natList_le n xs hlt
      have hm := Nat.mul_le_mul_right (n + 1) hdeg
      omega)
  simp only [List.length_map, List.length_reverse, Array.length_toList, hG.size,
    smul_eq_mul] at h
  simp only [List.length_singleton]
  omega

/-- **The encoding of a graph pair on `n` vertices has at most `5 (n + 1)³` symbols.** -/
theorem GraphPair.enc_length_le (p : GraphPair) : p.enc.length ≤ 5 * (p.n + 1) ^ 3 := by
  have hG := valid_ofSimpleGraph (Δ := p.n) (H := p.G) fun v =>
    (p.G.degree_lt_card_verts v).le.trans (by simp)
  have hH := valid_ofSimpleGraph (Δ := p.n) (H := p.H) fun v =>
    (p.H.degree_lt_card_verts v).le.trans (by simp)
  have hg := length_ser_graph_le _ hG
  have hh := length_ser_graph_le _ hH
  have hn := length_ser_nat_le p.n
  show (ser .nat p.n ++ (ser Ty.graph (GraphData.ofSimpleGraph p.G) ++
    ser Ty.graph (GraphData.ofSimpleGraph p.H))).length ≤ _
  simp only [List.length_append]
  have hb : p.n + 1 + ((p.n * (p.n * (p.n + 1) + 2) + 1) +
      (p.n * (p.n * (p.n + 1) + 2) + 1)) ≤ 5 * (p.n + 1) ^ 3 := by
    nlinarith only [Nat.zero_le (p.n ^ 3), Nat.zero_le (p.n ^ 2), Nat.zero_le p.n]
  exact (Nat.add_le_add hn (Nat.add_le_add hg hh)).trans hb

/-- **`λ(L) + 1 ≤ 8 (λ(n) + 1)`** for `L` the length of the encoding of a pair on `n`
vertices (`λ = Nat.log 2`). -/
theorem GraphPair.lam_enc_le (p : GraphPair) : lam p.enc.length + 1 ≤ 8 * (lam p.n + 1) := by
  by_cases hz : p.enc.length = 0
  · rw [hz]
    change (0 : ℕ) + 1 ≤ _
    omega
  have hn : p.n + 1 ≤ 2 ^ (lam p.n + 1) := Nat.lt_pow_succ_log_self (by norm_num) p.n
  have hp : p.enc.length ≤ 2 ^ (3 + 3 * (lam p.n + 1)) := by
    calc p.enc.length ≤ 5 * (p.n + 1) ^ 3 := p.enc_length_le
      _ ≤ 8 * (2 ^ (lam p.n + 1)) ^ 3 :=
        Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hn 3)
      _ = 2 ^ (3 + 3 * (lam p.n + 1)) := by
        rw [pow_add (2 : ℕ) 3 (3 * (lam p.n + 1)), Nat.mul_comm 3 (lam p.n + 1), pow_mul]
        norm_num
  have hlt : p.enc.length < 2 ^ (8 * (lam p.n + 1)) :=
    hp.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  exact Nat.log_lt_of_lt_pow hz hlt

/-- `2 ^ (c (λ(L) + 1) ^ 8) ≤ 2 ^ (c 8⁸ (λ(n) + 1) ^ 8)` for `L` the length of the encoding of a
pair on `n` vertices. -/
theorem exp_enc_le_vertices (c : ℕ) (p : GraphPair) :
    2 ^ (c * (lam p.enc.length + 1) ^ 8) ≤ 2 ^ (c * 8 ^ 8 * (lam p.n + 1) ^ 8) := by
  apply Nat.pow_le_pow_right (by norm_num)
  calc c * (lam p.enc.length + 1) ^ 8 ≤ c * (8 * (lam p.n + 1)) ^ 8 :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left p.lam_enc_le 8)
    _ = c * 8 ^ 8 * (lam p.n + 1) ^ 8 := by rw [mul_pow, mul_assoc]

/-- A timed output within `m` steps is one within any `m' ≥ m`. -/
def outputsInTime_mono {tm : Turing.FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m m' : ℕ} (h : Turing.TM2OutputsInTime tm l l' m)
    (hm : m ≤ m') : Turing.TM2OutputsInTime tm l l' m' :=
  { toEvalsTo := h.toEvalsTo, steps_le_m := h.steps_le_m.trans hm }

/-! ### The machines -/

/-- **Graph isomorphism decided by a Turing machine in time `2 ^ (c (λ(n) + 1) ^ 8)` on graphs
with `n` vertices.** There is `c` such that on every graph pair `p` the machine
`toFinTM2 giDecProg .inp .out` outputs `ser .bool (isoDecide p)` on `p.enc` within
`2 ^ (c (λ(n) + 1) ^ 8)` steps. -/
theorem gi_tm_vertices : ∃ c, ∀ p : GraphPair,
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giDecProg .inp .out) p.enc
      (some (ser .bool (isoDecide p))) (2 ^ (c * (lam p.n + 1) ^ 8))) := by
  obtain ⟨c, -, -, -, hc⟩ := gi_tm
  exact ⟨c * 8 ^ 8, fun p => (hc p).map fun h => outputsInTime_mono h (exp_enc_le_vertices c p)⟩

/-- **The coset of all isomorphisms output by a Turing machine in time
`2 ^ (c (λ(n) + 1) ^ 8)` on graphs with `n` vertices.** There is `c` such that for every graph
pair `p` the machine `toFinTM2 giCosetProg .inp .out` outputs `ser Ty.giCoset r` on `p.enc`
within `2 ^ (c (λ(n) + 1) ^ 8)` steps, where `r = none` exactly when `G` and `H` are not
isomorphic, and `r = some (τ, hs)` gives valid data of a permutation and of generators such that
the coset `τ • ⟨hs⟩` is exactly the set of the permutations underlying the isomorphisms
`G ≃g H`. -/
theorem gi_coset_tm_vertices : ∃ c, ∀ p : GraphPair, ∃ r : Option (PermData × GensData),
    Nonempty (Turing.TM2OutputsInTime (toFinTM2 giCosetProg .inp .out) p.enc
      (some (ser Ty.giCoset r)) (2 ^ (c * (lam p.n + 1) ^ 8))) ∧
    (r = none ↔ IsEmpty (p.G ≃g p.H)) ∧
    ∀ τ hs, r = some (τ, hs) → τ.Valid p.n ∧ GensData.AllValid p.n hs ∧
      {φ : Perm (Fin p.n) | ∃ e : p.G ≃g p.H, e.toEquiv = φ} =
        PermData.denote p.n τ • (GensData.denote p.n hs : Set (Perm (Fin p.n))) := by
  obtain ⟨c, hc⟩ := gi_coset_tm
  refine ⟨c * 8 ^ 8, fun p => ?_⟩
  obtain ⟨r, hM, hnone, hsome⟩ := hc p
  exact ⟨r, hM.map fun h => outputsInTime_mono h (exp_enc_le_vertices c p), hnone, hsome⟩

end GraphIso.TM
