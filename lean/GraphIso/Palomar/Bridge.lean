module

public import GraphIso.TM.SingleTape.GI
public import GraphIso.Palomar.Statement

/-!
# The Palomar statements: their proofs

`PLAN-19.md` §5–§6. The statements of `GraphIso.Palomar.Statement` (Appendices A and B), proved
from the single-tape theorems `GraphIso.TM.gi_tm0_vertices` and `gi_coset_tm0_vertices` of
milestone 18:

* **The encodings agree**, for every map `f` of the symbols that writes digits, `endNum`, `cons`
  and `nil` as a map `g` writes the library's `bit b`, `nd`, `tag cons`, `tag nil` (`Writes f
  g`): Mathlib's `Nat.bits` is the library's `toBits` (`bits_eq_toBits`); the words `natWord`,
  `listWord`, `graphWord`, `permWord` map to the serializations `ser .nat`, `ser (.list .nat)`,
  `ser Ty.graph` of `GraphData.ofSimpleGraph`, `ser Ty.perm` of valid data
  (`Writes.permWord_map`); so the input word maps to the input tape `encodeIn p.enc` of the pair
  `p = ⟨n, G, H⟩` (`Writes.input_map`).
* **The decision machine** `giDecTM0` (Appendix A): the symbol embedding `symbolEmbedding` into
  its tape alphabet sends the digits, `endNum`, `cons` and `nil` to the input symbols, the marks
  to the marks, `yes` and `no` to the output symbols `tag tt` and `tag ff`; it is injective, and
  no symbol goes to the blank. The output word of `b` maps to the output tape
  `encodeOut (ser .bool b)` (`output_map`). **`gi_singleTape_proof`**: the machine, the
  embedding and the constant of `gi_tm0_vertices`, with `b = isoDecide p` (`isoDecide_iff`);
  `TM0OutputsInTime` unfolds to the iterate of `TM0.step` in the statement.
* **The coset machine** `giCosetTM0` (Appendix B) reads input symbols and writes output symbols,
  so it has two embeddings into its alphabet: `cosetIn`, as `symbolEmbedding`, and `cosetOut`,
  which sends the digits, `endNum`, `cons` and `nil` to the output symbols, `yes` and `no` to
  `tag some` and `tag none`, the marks to the marks. The answer `r` is the denotation
  `cosetData n` of the output data, and for valid data its word maps to the output tape
  `encodeOut (ser Ty.giCoset r)` (`cosetWord_map`). **`gi_coset_singleTape_proof`**: from
  `gi_coset_tm0_vertices`; its coset equality `{φ | ∃ e, e.toEquiv = φ} = τ • ⟨gs⟩` is the
  statement's `(∃ e, e.toEquiv = φ) ↔ τ⁻¹ * φ ∈ ⟨gs⟩` (`mem_leftCoset_iff'`).
* **The coset word determines the answer** (`cosetWord_injective_proof`): numbers, lists of
  words of a prefix code, and permutations are prefix codes (`PrefixCode`): a number's word ends
  at its first `endNum`, `Nat.bits` is injective, and a permutation is determined by its
  images.
-/

@[expose] public section

namespace GraphIsoPalomar

open Equiv GraphIso GraphIso.TM GraphIso.Cost GraphIso.Graph GraphIso.Main

/-- **Mathlib's binary digits are the library's**: least significant first, no trailing zeros. -/
theorem bits_eq_toBits (n : ℕ) : Nat.bits n = toBits n := by
  induction n using Nat.binaryRec' with
  | zero => simp [toBits]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    have hn : b.toNat + 2 * n ≠ 0 := by
      cases b <;> simp_all
    have hb : Nat.bit b n = b.toNat + 2 * n := by
      cases b <;> simp [Nat.bit, Nat.add_comm]
    rw [hb, toBits_bit hn, ih]

/-! ### The encodings, for any map of the symbols -/

section Writes

variable {W : Type}

/-- `f` writes the symbols of numbers and lists as `g` writes the library's serialization
symbols: the digits as `bit b`, `endNum` as `nd`, `cons` and `nil` as the tags. -/
structure Writes (f : Sym → SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym)
    (g : GraphIso.TM.Sym → SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym) : Prop where
  digit (b : Bool) : f (.digit b) = g (.bit b)
  endNum : f .endNum = g .nd
  cons : f .cons = g (.tag .cons)
  nil : f .nil = g (.tag .nil)

namespace Writes

variable {f : Sym → SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym}
  {g : GraphIso.TM.Sym → SingleTape.Sym W GraphIso.TM.Sym GraphIso.TM.Sym}

/-- A number's word is its serialization. -/
theorem natWord_map (h : Writes f g) (n : ℕ) : (natWord n).map f = (ser .nat n).map g := by
  simp [natWord, bits_eq_toBits, ser, bits, List.map_map, Function.comp_def, h.digit, h.endNum]

theorem listWord_map (h : Writes f g) (ws : List (List Sym)) :
    (listWord ws).map f =
      (ws.map fun w => g (.tag .cons) :: w.map f).flatten ++ [g (.tag .nil)] := by
  simp [listWord, List.map_flatten, List.map_map, Function.comp_def, h.cons, h.nil]

/-- A list of numbers' word is its serialization. -/
theorem numberList_map (h : Writes f g) (ns : List ℕ) :
    (listWord (ns.map natWord)).map f = (ser (.list .nat) ns).map g := by
  simp only [h.listWord_map, List.map_map, Function.comp_def, h.natWord_map]
  simp only [ser, List.map_append, List.map_cons, List.map_nil, List.map_flatten, List.map_map,
    Function.comp_def]

/-- A graph's word is the serialization of its adjacency lists. -/
theorem graphWord_map (h : Writes f g) {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (graphWord G).map f = (ser Ty.graph (GraphData.ofSimpleGraph G)).map g := by
  simp only [graphWord, h.listWord_map, List.map_map, Function.comp_def]
  simp only [ser, GraphData.ofSimpleGraph, Array.toList_ofFn, List.ofFn_eq_map,
    List.map_reverse, List.map_map, List.map_flatten, List.map_append, List.map_cons,
    List.map_nil, Function.comp_def, nbrs]
  simp only [h.natWord_map, ser, List.map_append, List.map_cons, List.map_nil]

/-- **The input word is the input tape** of the pair `⟨n, G, H⟩`, for a map that writes the
input symbols and the marks. -/
theorem input_map (h : Writes f .inp) (hl : f .lmark = .lmark) (hr : f .rmark = .rmark)
    {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (input G H).map f = SingleTape.encodeIn (GraphPair.enc ⟨n, G, H⟩) := by
  simp only [input, List.map_append, List.map_cons, List.map_nil, h.natWord_map,
    h.graphWord_map, hl, hr]
  simp only [SingleTape.encodeIn, GraphPair.enc, GraphPair.data, ser, List.map_append,
    List.append_assoc]

/-- A permutation's word is the serialization of valid data for it: the forward and the inverse
arrays, each from its last entry. -/
theorem permWord_map (h : Writes f g) {n : ℕ} {d : PermData} (hd : PermData.Valid n d) :
    (permWord (PermData.denote n d)).map f = (ser Ty.perm d).map g := by
  have h₁ : (List.finRange n).reverse.map (fun i => natWord (PermData.denote n d i)) =
      d.1.toList.reverse.map natWord := by
    simp [PermData.fwd_eq_ofFn hd, List.ofFn_eq_map, List.map_reverse, Function.comp_def]
  have h₂ : (List.finRange n).reverse.map (fun i => natWord ((PermData.denote n d).symm i)) =
      d.2.toList.reverse.map natWord := by
    simp [PermData.inv_eq_ofFn hd, List.ofFn_eq_map, List.map_reverse, Function.comp_def,
      Perm.inv_def]
  rw [permWord, List.map_append, h₁, h₂, h.numberList_map, h.numberList_map]
  simp [ser]

/-- A list of permutations' word is the serialization of valid data for them. -/
theorem gensWord_map (h : Writes f g) {n : ℕ} {hs : GensData} (hhs : GensData.AllValid n hs) :
    (listWord ((hs.map (PermData.denote n)).map permWord)).map f = (ser Ty.gens hs).map g := by
  induction hs with
  | nil => simp [listWord, ser, h.nil]
  | cons d hs ih =>
    obtain ⟨hd, hhs⟩ := hhs.of_cons
    have e := ih hhs
    simp only [listWord, List.map_cons, List.flatten_cons, List.map_append] at e ⊢
    simp only [ser, List.map_cons, List.flatten_cons, List.map_append] at e ⊢
    rw [h.cons, h.permWord_map hd, List.append_assoc, e, List.append_assoc]
    simp [ser]

end Writes

end Writes

/-! ### The decision machine -/

/-- The tape alphabet of the single-tape decision machine: `giDecTM0.Γ`, unfolded. -/
abbrev TapeAlphabet : Type :=
  SingleTape.Sym (SingleTape.WorkSym (toFinTM2 giDecProg .inp .out)) GraphIso.TM.Sym
    GraphIso.TM.Sym

theorem tapeAlphabet_eq : TapeAlphabet = giDecTM0.Γ :=
  rfl

/-- The symbols in the machine's tape alphabet. -/
def symbolMap : Sym → TapeAlphabet
  | .digit b => .inp (.bit b)
  | .endNum => .inp .nd
  | .cons => .inp (.tag .cons)
  | .nil => .inp (.tag .nil)
  | .lmark => .lmark
  | .rmark => .rmark
  | .yes => .out (.tag .tt)
  | .no => .out (.tag .ff)

theorem symbolMap_injective : Function.Injective symbolMap := by
  intro x y h
  cases x <;> cases y <;> simp_all [symbolMap]

/-- **The symbol embedding** into the machine's tape alphabet. -/
def symbolEmbedding : Sym ↪ TapeAlphabet :=
  ⟨symbolMap, symbolMap_injective⟩

/-- No symbol is mapped to the blank. -/
theorem symbolEmbedding_ne_default (s : Sym) : symbolEmbedding s ≠ default := by
  change symbolMap s ≠ SingleTape.Sym.work _
  cases s <;> simp [symbolMap]

theorem writes_symbolEmbedding : Writes symbolEmbedding SingleTape.Sym.inp :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- A number's word is its serialization. -/
theorem natWord_map (n : ℕ) :
    (natWord n).map symbolEmbedding =
      (ser .nat n).map (SingleTape.Sym.inp : GraphIso.TM.Sym → TapeAlphabet) :=
  writes_symbolEmbedding.natWord_map n

theorem listWord_map (ws : List (List Sym)) :
    (listWord ws).map symbolEmbedding =
      (ws.map fun w => SingleTape.Sym.inp (.tag .cons) :: w.map symbolEmbedding).flatten ++
        [SingleTape.Sym.inp (.tag .nil)] :=
  writes_symbolEmbedding.listWord_map ws

/-- A list of numbers' word is its serialization. -/
theorem numberList_map (ns : List ℕ) :
    (listWord (ns.map natWord)).map symbolEmbedding =
      (ser (.list .nat) ns).map (SingleTape.Sym.inp : GraphIso.TM.Sym → TapeAlphabet) :=
  writes_symbolEmbedding.numberList_map ns

/-- A graph's word is the serialization of its adjacency lists. -/
theorem graphWord_map {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (graphWord G).map symbolEmbedding =
      (ser Ty.graph (GraphData.ofSimpleGraph G)).map
        (SingleTape.Sym.inp : GraphIso.TM.Sym → TapeAlphabet) :=
  writes_symbolEmbedding.graphWord_map G

/-- **The input word is the input tape** of the pair `⟨n, G, H⟩`. -/
theorem input_map {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel H.Adj] :
    (input G H).map symbolEmbedding = SingleTape.encodeIn (GraphPair.enc ⟨n, G, H⟩) :=
  writes_symbolEmbedding.input_map rfl rfl G H

/-- **The output word is the output tape** of the answer `b`. -/
theorem output_map (b : Bool) :
    (output b).map symbolEmbedding = SingleTape.encodeOut (ser .bool b) := by
  cases b <;> rfl

/-- **Graph isomorphism is decided by a single-tape Turing machine in quasipolynomial time**:
the statement of `PLAN-19.md`, Appendix A (in the Palomar submission, `gi_singleTape`). -/
theorem gi_singleTape_proof :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ), Finite Γ ∧ Finite Λ ∧
      ∃ (M : Turing.TM0.Machine Γ Λ) (ι : Sym ↪ Γ) (c : ℕ), (∀ s, ι s ≠ default) ∧
        ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
          ∃ b : Bool, (b = true ↔ Nonempty (G ≃g H)) ∧
            ∃ k ≤ 2 ^ (c * (Nat.log 2 n + 1) ^ 8), ∃ q : Λ,
              (flip bind (Turing.TM0.step M))^[k]
                  (some (Turing.TM0.init ((input G H).map ι))) =
                some ⟨q, Turing.Tape.mk₁ ((output b).map ι)⟩ ∧
              Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((output b).map ι)⟩ = none := by
  obtain ⟨c, hc⟩ := gi_tm0_vertices
  refine ⟨TapeAlphabet, giDecTM0.Λ, (inferInstance : Inhabited giDecTM0.Γ), inferInstance,
    (inferInstance : Finite giDecTM0.Γ), inferInstance, giDecTM0.machine, symbolEmbedding, c,
    symbolEmbedding_ne_default, ?_⟩
  intro n G H _ _
  let p : GraphPair := ⟨n, G, H⟩
  refine ⟨isoDecide p, isoDecide_iff p, ?_⟩
  obtain ⟨q, k, hk, hr, hh⟩ := hc p
  refine ⟨k, hk, q, ?_, ?_⟩
  · rw [input_map, output_map]
    exact hr
  · rw [output_map]
    exact hh

/-! ### The coset machine -/

/-- The tape alphabet of the single-tape coset machine: `giCosetTM0.Γ`, unfolded. -/
abbrev CosetAlphabet : Type :=
  SingleTape.Sym (SingleTape.WorkSym (toFinTM2 giCosetProg .inp .out)) GraphIso.TM.Sym
    GraphIso.TM.Sym

theorem cosetAlphabet_eq : CosetAlphabet = giCosetTM0.Γ :=
  rfl

/-- The symbols read by the coset machine: as `symbolMap`, in its alphabet. -/
def cosetInMap : Sym → CosetAlphabet
  | .digit b => .inp (.bit b)
  | .endNum => .inp .nd
  | .cons => .inp (.tag .cons)
  | .nil => .inp (.tag .nil)
  | .lmark => .lmark
  | .rmark => .rmark
  | .yes => .out (.tag .tt)
  | .no => .out (.tag .ff)

/-- The symbols written by the coset machine: the digits, `endNum`, `cons` and `nil` as output
symbols, `yes` and `no` as the tags `some` and `none`. -/
def cosetOutMap : Sym → CosetAlphabet
  | .digit b => .out (.bit b)
  | .endNum => .out .nd
  | .cons => .out (.tag .cons)
  | .nil => .out (.tag .nil)
  | .lmark => .lmark
  | .rmark => .rmark
  | .yes => .out (.tag .some)
  | .no => .out (.tag .none)

theorem cosetInMap_injective : Function.Injective cosetInMap := by
  intro x y h
  cases x <;> cases y <;> simp_all [cosetInMap]

theorem cosetOutMap_injective : Function.Injective cosetOutMap := by
  intro x y h
  cases x <;> cases y <;> simp_all [cosetOutMap]

/-- **The coset machine's input embedding.** -/
def cosetIn : Sym ↪ CosetAlphabet :=
  ⟨cosetInMap, cosetInMap_injective⟩

/-- **The coset machine's output embedding.** -/
def cosetOut : Sym ↪ CosetAlphabet :=
  ⟨cosetOutMap, cosetOutMap_injective⟩

theorem cosetIn_ne_default (s : Sym) : cosetIn s ≠ default := by
  change cosetInMap s ≠ SingleTape.Sym.work _
  cases s <;> simp [cosetInMap]

theorem cosetOut_ne_default (s : Sym) : cosetOut s ≠ default := by
  change cosetOutMap s ≠ SingleTape.Sym.work _
  cases s <;> simp [cosetOutMap]

theorem writes_cosetIn : Writes cosetIn SingleTape.Sym.inp :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

theorem writes_cosetOut : Writes cosetOut SingleTape.Sym.out :=
  ⟨fun _ => rfl, rfl, rfl, rfl⟩

/-- **The coset machine's input word is its input tape.** -/
theorem cosetIn_input_map {n : ℕ} (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    [DecidableRel H.Adj] :
    (input G H).map cosetIn = SingleTape.encodeIn (GraphPair.enc ⟨n, G, H⟩) :=
  writes_cosetIn.input_map rfl rfl G H

/-- The answer denoted by the coset machine's output data: the permutations of the data. -/
def cosetData (n : ℕ) (r : Option (PermData × GensData)) :
    Option (Perm (Fin n) × List (Perm (Fin n))) :=
  r.map fun x => (PermData.denote n x.1, x.2.map (PermData.denote n))

/-- **The output word is the output tape**, for valid data. -/
theorem cosetWord_map {n : ℕ} {r : Option (PermData × GensData)}
    (hr : ∀ τ hs, r = some (τ, hs) → PermData.Valid n τ ∧ GensData.AllValid n hs) :
    (cosetWord (cosetData n r)).map cosetOut = SingleTape.encodeOut (ser Ty.giCoset r) := by
  rcases r with _ | ⟨τ, hs⟩
  · rfl
  · obtain ⟨hτ, hhs⟩ := hr τ hs rfl
    simp only [cosetData, Option.map_some, cosetWord, List.map_append, List.map_cons,
      writes_cosetOut.permWord_map hτ, writes_cosetOut.gensWord_map hhs]
    simp [SingleTape.encodeOut, ser, cosetOut, cosetOutMap]

/-! ### The coset word determines the answer -/

/-- `e` is a prefix code: a word of `e` followed by anything determines the value and the
rest. -/
def PrefixCode {α : Type} (e : α → List Sym) : Prop :=
  ∀ a b s t, e a ++ s = e b ++ t → a = b ∧ s = t

/-- Two words without `x`, each followed by `x`: the first `x` ends them. -/
theorem eq_of_append_cons {x : Sym} :
    ∀ {u v s t : List Sym}, x ∉ u → x ∉ v → u ++ x :: s = v ++ x :: t → u = v ∧ s = t
  | [], [], _, _, _, _, h => by simpa using h
  | [], y :: v, _, _, _, hv, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hv
  | y :: u, [], _, _, hu, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hu
  | y :: u, z :: v, _, _, hu, hv, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ :=
      eq_of_append_cons (List.not_mem_of_not_mem_cons hu) (List.not_mem_of_not_mem_cons hv) h
    exact ⟨rfl, rfl⟩

/-- A number's word ends at its first `endNum`, and `Nat.bits` is injective. -/
theorem natWord_prefixCode : PrefixCode natWord := by
  intro a b s t h
  simp only [natWord, List.append_assoc, List.singleton_append] at h
  obtain ⟨h₁, h₂⟩ := eq_of_append_cons (by simp) (by simp) h
  refine ⟨?_, h₂⟩
  have e := List.map_injective_iff.2 (fun _ _ e => Sym.digit.inj e) h₁
  rw [bits_eq_toBits, bits_eq_toBits] at e
  rw [← ofBits_toBits a, ← ofBits_toBits b, e]

theorem listWord_cons (w : List Sym) (ws : List (List Sym)) :
    listWord (w :: ws) = Sym.cons :: (w ++ listWord ws) := by
  simp [listWord]

/-- The lists of the words of a prefix code form a prefix code. -/
theorem PrefixCode.list {α : Type} {e : α → List Sym} (h : PrefixCode e) :
    PrefixCode fun xs : List α => listWord (xs.map e) := by
  intro xs
  induction xs with
  | nil =>
    rintro (_ | ⟨y, ys⟩) s t hst
    · simpa [listWord] using hst
    · simp [listWord] at hst
  | cons x xs ih =>
    rintro (_ | ⟨y, ys⟩) s t hst
    · simp [listWord] at hst
    · simp only [List.map_cons, listWord_cons, List.cons_append, List.cons.injEq, true_and,
        List.append_assoc] at hst
      obtain ⟨rfl, hst'⟩ := h x y _ _ hst
      obtain ⟨rfl, rfl⟩ := ih ys s t hst'
      exact ⟨rfl, rfl⟩

/-- A permutation's word is a prefix code: the images determine the permutation. -/
theorem permWord_prefixCode (n : ℕ) : PrefixCode (permWord (n := n)) := by
  intro σ σ' s t h
  have hw : ∀ π : Perm (Fin n), (List.finRange n).reverse.map (fun i => natWord (π i)) =
      ((List.finRange n).reverse.map fun i => (π i : ℕ)).map natWord := by
    intro π
    simp [List.map_map, Function.comp_def]
  simp only [permWord, List.append_assoc, hw σ, hw σ'] at h
  obtain ⟨h₁, h₂⟩ := natWord_prefixCode.list _ _ _ _ h
  obtain rfl : σ = σ' := by
    ext i
    exact List.map_inj_left.1 h₁ i (by simp)
  exact ⟨rfl, List.append_cancel_left h₂⟩

/-- **The coset machine's output determines its answer**: the statement of `PLAN-19.md`,
Appendix B (in the Palomar submission, `cosetWord_injective`). -/
theorem cosetWord_injective_proof (n : ℕ) : Function.Injective (cosetWord (n := n)) := by
  rintro (_ | ⟨τ, gs⟩) (_ | ⟨τ', gs'⟩) h
  · rfl
  · simp [cosetWord] at h
  · simp [cosetWord] at h
  · simp only [cosetWord, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := permWord_prefixCode n τ τ' _ _ h
    obtain ⟨rfl, -⟩ := (permWord_prefixCode n).list gs gs' _ _ h'
    rfl

/-- **All isomorphisms of two graphs, by a single-tape Turing machine in quasipolynomial
time**: the statement of `PLAN-19.md`, Appendix B (in the Palomar submission,
`gi_coset_singleTape`). -/
theorem gi_coset_singleTape_proof :
    ∃ (Γ Λ : Type) (_ : Inhabited Γ) (_ : Inhabited Λ), Finite Γ ∧ Finite Λ ∧
      ∃ (M : Turing.TM0.Machine Γ Λ) (ιin ιout : Sym ↪ Γ) (c : ℕ),
        (∀ s, ιin s ≠ default) ∧ (∀ s, ιout s ≠ default) ∧
        ∀ (n : ℕ) (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj],
          ∃ r : Option (Equiv.Perm (Fin n) × List (Equiv.Perm (Fin n))),
            (r = none ↔ IsEmpty (G ≃g H)) ∧
            (∀ τ gs, r = some (τ, gs) → ∀ φ : Equiv.Perm (Fin n),
              (∃ e : G ≃g H, e.toEquiv = φ) ↔ τ⁻¹ * φ ∈ Subgroup.closure {g | g ∈ gs}) ∧
            ∃ k ≤ 2 ^ (c * (Nat.log 2 n + 1) ^ 8), ∃ q : Λ,
              (flip bind (Turing.TM0.step M))^[k]
                  (some (Turing.TM0.init ((input G H).map ιin))) =
                some ⟨q, Turing.Tape.mk₁ ((cosetWord r).map ιout)⟩ ∧
              Turing.TM0.step M ⟨q, Turing.Tape.mk₁ ((cosetWord r).map ιout)⟩ = none := by
  obtain ⟨c, hc⟩ := gi_coset_tm0_vertices
  refine ⟨CosetAlphabet, giCosetTM0.Λ, (inferInstance : Inhabited giCosetTM0.Γ), inferInstance,
    (inferInstance : Finite giCosetTM0.Γ), inferInstance, giCosetTM0.machine, cosetIn, cosetOut,
    c, cosetIn_ne_default, cosetOut_ne_default, ?_⟩
  intro n G H _ _
  let p : GraphPair := ⟨n, G, H⟩
  obtain ⟨r, hM, hnone, hsome⟩ := hc p
  refine ⟨cosetData n r, ?_, ?_, ?_⟩
  · exact (by simp [cosetData] : cosetData n r = none ↔ r = none).trans hnone
  · intro τ gs hr φ
    obtain ⟨⟨τd, hs⟩, rfl, he⟩ := Option.map_eq_some_iff.1 hr
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hset : GensData.denoteSet n hs = {g | g ∈ hs.map (PermData.denote n)} := by
      ext g
      simp [GensData.denoteSet]
    refine (Set.ext_iff.1 (hsome τd hs rfl).2.2 φ).trans ?_
    rw [mem_leftCoset_iff', GensData.denote, hset]
  · obtain ⟨q, k, hk, hrun, hh⟩ := hM
    have hw : (cosetWord (cosetData n r)).map cosetOut =
        SingleTape.encodeOut (ser Ty.giCoset r) :=
      cosetWord_map fun τ hs h => ⟨(hsome τ hs h).1, (hsome τ hs h).2.1⟩
    refine ⟨k, hk, q, ?_, ?_⟩
    · rw [cosetIn_input_map, hw]
      exact hrun
    · rw [hw]
      exact hh

end GraphIsoPalomar
