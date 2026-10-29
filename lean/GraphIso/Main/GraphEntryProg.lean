module

public import GraphIso.Main.GraphEntry
public import GraphIso.Main.Full
public import GraphIso.Graph.Entry

/-!
# The graph-isomorphism entry: the programs

Stage 14j-6c-3, item 3 (`PLAN-14.md` §14.15). The programs computing the encoding and the
decoding of `GraphEntry.lean`, with their exact results and polynomial costs, and the entry.

* `offProg`: the pair offsets `offArr n` (`n + n u`, by `mulProg` and addition), at cost
  `offCost n`.
* `liftArrProg`, `liftDataProg`: the lift of vertex data (`liftArr`, `liftData`), at cost
  `liftArrCost n` per array.
* `strProg`: the string `gStr n X`, at cost at most `strCost n` on valid data.
* `gensProg`: the generators `gensData n`, at cost at most `gensCost n`.
* `decodeProg`: the decoded answer `decodeAns n a`, at cost at most `decCost n s` when the answer
  has at most `s` generators.
* **The entry** `giEntry D`: from `(n, X, Y)`, the encoding, then the mini procedure's entry
  `mainEntry` (one `generate`, then the recursion), then the decoding. It is well formed
  (`giEntry_wf`). `giEntry_runs`: if the main entry solves the encoded instance within `c` with
  at most `(2N)²` generators, the entry returns a `GICosetOK` result within
  `encCost n + c + decCost n (2N · 2N)`.
-/

@[expose] public section

namespace GraphIso.Main

open Equiv Cost GraphIso GraphIso.Programs GraphIso.Graph Sims

/-! ### Programs -/

section Programs

variable {S : Signature} {rec : Ty × Ty} {var : Ty → Type}

/-- One offset: `n + n u`. -/
def offElemProg (n u : var .nat) : Prog S rec var .nat :=
  .bind (Graph.mulProg n u) fun nu => .op2 .add n nu

/-- The offsets `n + n u` for `u < n`. -/
def offProg (n : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun rn => .bind (mapList rn fun u => offElemProg n u) fun l =>
  .op1 .arrayOfList l

/-- The write of the pair `(u, v)`: its point `ou + v` and its image `oau + a v`. -/
def liftElemProg (ou oau : var .nat) (a : var (.array .nat)) (v : var .nat) :
    Prog S rec var (.prod .nat .nat) :=
  .bind (.op2 .add ou v) fun i => .bind (.op2 .arrayGet a v) fun av =>
  .bind (.op2 .add oau av) fun x => .op2 .pair i x

/-- The block of writes of the vertex `u`, prepended to `acc`. -/
def liftStepProg (rn : var (.list .nat)) (o a : var (.array .nat))
    (acc : var (.list (.prod .nat .nat))) (u : var .nat) :
    Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op2 .arrayGet a u) fun au => .bind (.op2 .arrayGet o u) fun ou =>
  .bind (.op2 .arrayGet o au) fun oau =>
  .bind (mapList rn fun v => liftElemProg ou oau a v) fun row =>
  .bind (.op2 .pair u au) fun w₀ => .bind (.op2 .cons w₀ row) fun blk =>
  .op2 .append blk acc

/-- The lift of an array of vertex images `a`, with offsets `o`, on `N` points. -/
def liftArrProg (n N : var .nat) (o a : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun rn => .bind (.op0 .nil) fun nil =>
  .bind (.foldList rn nil fun acc u => liftStepProg rn o a acc u) fun ws =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk N z) fun base =>
  .prim .arrayUpdate (.cons base (.cons ws .nil))

/-- The lift of permutation data. -/
def liftDataProg (n N : var .nat) (o : var (.array .nat)) (g : var Ty.perm) :
    Prog S rec var Ty.perm :=
  .bind (.op1 .fst g) fun f => .bind (.op1 .snd g) fun b =>
  .bind (liftArrProg n N o f) fun f' => .bind (liftArrProg n N o b) fun b' => .op2 .pair f' b'

/-- The write of the pair `(u, v)` of an edge: its point `ou + v`, value `1`. -/
def strElemProg (ou one v : var .nat) : Prog S rec var (.prod .nat .nat) :=
  .bind (.op2 .add ou v) fun i => .op2 .pair i one

/-- The writes of the neighbours of `u`, prepended to `acc`. -/
def strStepProg (o : var (.array .nat)) (X : var Ty.graph) (acc : var (.list (.prod .nat .nat)))
    (u : var .nat) : Prog S rec var (.list (.prod .nat .nat)) :=
  .bind (.op2 .arrayGet X u) fun nb => .bind (.op2 .arrayGet o u) fun ou =>
  .bind (.op0 (.natLit 1)) fun one =>
  .bind (mapList nb fun v => strElemProg ou one v) fun blk =>
  .op2 .append blk acc

/-- The string of the graph `X`, with offsets `o`, on `N` points. -/
def strProg (n N : var .nat) (o : var (.array .nat)) (X : var Ty.graph) :
    Prog S rec var Ty.str :=
  .bind (.op1 .range n) fun rn => .bind (.op0 .nil) fun nil =>
  .bind (.foldList rn nil fun acc u => strStepProg o X acc u) fun ws =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .arrayMk N z) fun base =>
  .prim .arrayUpdate (.cons base (.cons ws .nil))

/-- `u + 1`. -/
def succProg (u : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 1)) fun one => .op2 .add u one

/-- `u − 1`. -/
def predProg (u : var .nat) : Prog S rec var .nat :=
  .bind (.op0 (.natLit 1)) fun one => .op2 .sub u one

/-- The array `(u + 1)_{u < n}` with the write `(n − 1, 0)`. -/
def rotFProg (n : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun rn =>
  .bind (mapList rn fun u => succProg u) fun l =>
  .bind (.op1 .arrayOfList l) fun arr =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub n one) fun last =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .pair last z) fun w =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .cons w nil) fun ws =>
  .prim .arrayUpdate (.cons arr (.cons ws .nil))

/-- The array `(u − 1)_{u < n}` with the write `(0, n − 1)`. -/
def rotIProg (n : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun rn =>
  .bind (mapList rn fun u => predProg u) fun l =>
  .bind (.op1 .arrayOfList l) fun arr =>
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .sub n one) fun last =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op2 .pair z last) fun w =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .cons w nil) fun ws =>
  .prim .arrayUpdate (.cons arr (.cons ws .nil))

/-- The array `(u)_{u < n}` with the writes `(0, 1)` and `(1, 0)`. -/
def swFProg (n : var .nat) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun rn => .bind (.op1 .arrayOfList rn) fun arr =>
  .bind (.op0 (.natLit 0)) fun z => .bind (.op0 (.natLit 1)) fun one =>
  .bind (.op2 .pair z one) fun w₁ => .bind (.op2 .pair one z) fun w₂ =>
  .bind (.op0 .nil) fun nil => .bind (.op2 .cons w₂ nil) fun l => .bind (.op2 .cons w₁ l) fun ws =>
  .prim .arrayUpdate (.cons arr (.cons ws .nil))

/-- The generators: the lifts of the `n`-cycle and of the transposition of `0` and `1`, none for
`n ≤ 1`. -/
def gensProg (n N : var .nat) (o : var (.array .nat)) : Prog S rec var Ty.gens :=
  .bind (.op0 (.natLit 1)) fun one => .bind (.op2 .natLt one n) fun big =>
  .ite big
    (.bind (rotFProg n) fun rf => .bind (rotIProg n) fun ri => .bind (.op2 .pair rf ri) fun r =>
     .bind (liftDataProg n N o r) fun lr =>
     .bind (swFProg n) fun sf => .bind (.op2 .pair sf sf) fun sw =>
     .bind (liftDataProg n N o sw) fun ls =>
     .bind (.op0 .nil) fun nil => .bind (.op2 .cons ls nil) fun l₁ => .op2 .cons lr l₁)
    (.op0 .nil)

/-- The first `n` entries of an array. -/
def restrictArrProg (n : var .nat) (a : var (.array .nat)) : Prog S rec var (.array .nat) :=
  .bind (.op1 .range n) fun rn => .bind (mapList rn fun u => .op2 .arrayGet a u) fun l =>
  .op1 .arrayOfList l

/-- The restriction of permutation data to the first `n` points. -/
def restrictProg (n : var .nat) (d : var Ty.perm) : Prog S rec var Ty.perm :=
  .bind (.op1 .fst d) fun f => .bind (.op1 .snd d) fun b =>
  .bind (restrictArrProg n f) fun f' => .bind (restrictArrProg n b) fun b' => .op2 .pair f' b'

/-- The output: a coset of permutations of the vertices, or `none`. -/
abbrev Ty.giCoset : Ty := .option (.prod Ty.perm Ty.gens)

/-- The decoded answer. -/
def decodeProg {D : Ty} (n : var .nat) (ans : var (Ty.answer D)) : Prog S rec var Ty.giCoset :=
  .caseOption ans (.op0 .none) fun c =>
    .bind (.op1 .fst c) fun τ => .bind (.op1 .snd c) fun H =>
    .bind (.op1 .snd H) fun r => .bind (.op1 .fst r) fun gs =>
    .bind (restrictProg n τ) fun τ' => .bind (mapList gs fun g => restrictProg n g) fun hs =>
    .bind (.op2 .pair τ' hs) fun p => .op1 .some p

end Programs

/-- **The graph-isomorphism entry.** From `(n, X, Y)`: the offsets, `N = n + n · n`, the strings,
the whole window, the identity and the generators; then the mini procedure's entry (one
`generate`, then the recursion on the instance without a hint); then the decoding. -/
def giEntry (D : Ty) : (var : Ty → Type) → var Ty.giInput →
    Prog (groupSig D) (hinstTy D, Ty.answer D) var Ty.giCoset := fun var inp =>
  .bind (.op1 .fst inp) fun n => .bind (.op1 .snd inp) fun XY =>
  .bind (.op1 .fst XY) fun X => .bind (.op1 .snd XY) fun Y =>
  .bind (offProg n) fun o =>
  .bind (Graph.mulProg n n) fun nn => .bind (.op2 .add n nn) fun N =>
  .bind (strProg n N o X) fun x => .bind (strProg n N o Y) fun y =>
  .bind (.op1 .range N) fun pts => .bind (mkWindow N pts) fun w =>
  .bind (permOne N) fun σ => .bind (gensProg n N o) fun gs =>
  .bind (.op2 .pair x y) fun xy => .bind (.op2 .pair N gs) fun ng =>
  .bind (.op2 .pair σ ng) fun r₂ => .bind (.op2 .pair w r₂) fun r₁ =>
  .bind (.op2 .pair xy r₁) fun inst =>
  .bind (miniEntry D var inst) fun ans =>
  decodeProg n ans

theorem giEntry_wf {D : Ty} {var₁ var₂ : Ty → Type} (x₁ : var₁ Ty.giInput)
    (x₂ : var₂ Ty.giInput) :
    Prog.Wf true [⟨Ty.giInput, x₁, x₂⟩] (giEntry D var₁ x₁) (giEntry D var₂ x₂) := by
  unfold giEntry offProg offElemProg Graph.mulProg strProg strStepProg strElemProg mkWindow
    permOne gensProg rotFProg rotIProg swFProg succProg predProg liftDataProg liftArrProg
    liftStepProg liftElemProg miniEntry decodeProg restrictProg restrictArrProg mapList
  prog_wf

/-! ### Specifications -/

section Specs

variable {S : Signature} {a b : Ty} {X : Ctx S} {body : a.denote → Prog S (a, b) Ty.denote b}

/-- The cost of the offsets. -/
def offCost (n : ℕ) : ℕ := 3 * n * n + 8 * n + 4

theorem RunsWithin.offElemProg (n u : ℕ) :
    RunsWithin X body (Main.offElemProg n u) (n + n * u) (3 * n + 3) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.mulProg n u)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

theorem RunsWithin.offProg (n : ℕ) :
    RunsWithin X body (Main.offProg n) (offArr n) (offCost n) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := List.range n) (c := 3 * n + 3) (F := fun u => n + n * u)
    (f := fun u => Main.offElemProg n u) fun u _ => RunsWithin.offElemProg n u
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_range, List.length_map, offCost]
    nlinarith

theorem length_foldl_prepend {α β : Type} (F : β → List α) :
    ∀ (xs : List β) (acc : List α),
      (xs.foldl (fun acc x => F x ++ acc) acc).length = acc.length + (xs.map (F · |>.length)).sum
  | [], acc => by simp
  | x :: xs, acc => by
    rw [List.foldl_cons, length_foldl_prepend F xs, List.length_append, List.map_cons,
      List.sum_cons]
    omega

/-- The cost of a lifted array. -/
def liftArrCost (n : ℕ) : ℕ := 9 * n * n + 12 * n + 5 + 2 * gN n

theorem RunsWithin.liftElemProg (ou oau : ℕ) (a : Array ℕ) (v : ℕ) :
    RunsWithin X body (Main.liftElemProg ou oau a v) (ou + v, oau + get a v) 4 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.liftStepProg (n : ℕ) (o a : Array ℕ) (acc : List (ℕ × ℕ)) (u : ℕ) :
    RunsWithin X body (Main.liftStepProg (List.range n) o a acc u) (liftRow n o a u ++ acc)
      (8 * n + 9) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .nat) (xs := List.range n) (c := 4)
    (F := fun v => (get o u + v, get o (get a u) + get a v))
    (f := fun v => Main.liftElemProg (get o u) (get o (get a u)) a v)
    fun v _ => RunsWithin.liftElemProg _ _ a v
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hm
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, Prim.eval, List.length_cons, List.length_map,
      List.length_range]
    omega

theorem RunsWithin.liftArrProg (n : ℕ) (o a : Array ℕ) :
    RunsWithin X body (Main.liftArrProg n (gN n) o a) (liftArr n o a) (liftArrCost n) := by
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.prod .nat .nat)) (cf := fun _ => 8 * n + 9)
    (F := fun acc u => liftRow n o a u ++ acc)
    (f := fun acc u => Main.liftStepProg (List.range n) o a acc u) (List.range n) []
    fun acc u _ => RunsWithin.liftStepProg n o a acc u
  rw [sum_map_const, List.length_range] at hfold
  have hlen : (liftWrites n o a).length = n * (n + 1) := by
    rw [liftWrites, length_foldl_prepend]
    simp [liftRow]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have hl : (List.foldl (fun acc u => liftRow n o a u ++ acc) [] (List.range n)).length =
        n * (n + 1) := hlen
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate, hl,
      liftArrCost]
    nlinarith

/-- The cost of lifted data. -/
def liftDataCost (n : ℕ) : ℕ := 2 * liftArrCost n + 3

theorem RunsWithin.liftDataProg (n : ℕ) (g : PermData) :
    RunsWithin X body (Main.liftDataProg n (gN n) (offArr n) g) (liftData n g)
      (liftDataCost n) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.liftArrProg n _ _)
    run_step (RunsWithin.liftArrProg n _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, liftDataCost]
    omega

/-- The cost of a string, on valid data. -/
def strCost (n : ℕ) : ℕ := 7 * n * n + 8 * n + 5 + 2 * gN n

theorem RunsWithin.strElemProg (ou v : ℕ) :
    RunsWithin X body (Main.strElemProg ou 1 v) (ou + v, 1) 2 := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc => simp [Prim.cost]

theorem RunsWithin.strStepProg (o : Array ℕ) (G : GraphData) (acc : List (ℕ × ℕ)) (u : ℕ) :
    RunsWithin X body (Main.strStepProg o G acc u)
      ((nbrs G u).map (fun v => (get o u + v, 1)) ++ acc) (6 * (nbrs G u).length + 6) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat)
    (b' := .prod .nat .nat) (xs := nbrs G u) (c := 2) (F := fun v => (get o u + v, 1))
    (f := fun v => Main.strElemProg (get o u) 1 v) fun v _ => RunsWithin.strElemProg _ v
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_map]
    change 1 + (1 + (1 + ((nbrs G u).length * (2 + 3) + 2 + ((nbrs G u).length + 1)))) ≤ _
    omega

theorem RunsWithin.strProg {Δ n : ℕ} {G : GraphData} (hG : G.ValidD Δ n) :
    RunsWithin X body (Main.strProg n (gN n) (offArr n) G) (gStr n G) (strCost n) := by
  have hdeg : ∀ u, (nbrs G u).length ≤ n := fun u =>
    mf_length_le_of_nodup (hG.nodup u) fun v hv => hG.lt u v hv
  have hfold := RunsWithin.foldList_of (X := X) (body := body) (a' := .nat)
    (b' := .list (.prod .nat .nat)) (cf := fun _ => 6 * n + 6)
    (F := fun acc u => (nbrs G u).map (fun v => (get (offArr n) u + v, 1)) ++ acc)
    (f := fun acc u => Main.strStepProg (offArr n) G acc u) (List.range n) []
    fun acc u _ => (RunsWithin.strStepProg (offArr n) G acc u).mono (by
      have := hdeg u
      omega)
  rw [sum_map_const, List.length_range] at hfold
  have hlen : (strWrites n (offArr n) G).length ≤ n * n := by
    rw [strWrites, length_foldl_prepend]
    simp only [List.length_nil, List.length_map, Nat.zero_add]
    calc ((List.range n).map fun u => (nbrs G u).length).sum
        ≤ ((List.range n).map fun _ => n).sum := List.sum_le_sum fun u _ => hdeg u
      _ = n * n := by rw [sum_map_const, List.length_range]
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hfold
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    have hl : (List.foldl (fun acc u => (nbrs G u).map (fun v => (get (offArr n) u + v, 1)) ++
        acc) [] (List.range n)).length ≤ n * n := hlen
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, Array.size_replicate,
      strCost]
    nlinarith

theorem RunsWithin.succProg (u : ℕ) : RunsWithin X body (Main.succProg u) (u + 1) 2 :=
  (RunsWithin.prim _ _).bind_le (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])

theorem RunsWithin.predProg (u : ℕ) : RunsWithin X body (Main.predProg u) (u - 1) 2 :=
  (RunsWithin.prim _ _).bind_le (RunsWithin.prim_le rfl le_rfl) (by simp [Prim.cost])

/-- The cost of a vertex array of the generators. -/
def vtxCost (n : ℕ) : ℕ := 8 * n + 12

theorem RunsWithin.rotFProg (n : ℕ) : RunsWithin X body (Main.rotFProg n) (rotF n) (vtxCost n) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := List.range n) (c := 2) (F := (· + 1)) (f := fun u => Main.succProg u)
    fun u _ => RunsWithin.succProg u
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hm
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, List.length_range,
      List.length_map, List.size_toArray, List.length_cons, List.length_nil, vtxCost]
    omega

theorem RunsWithin.rotIProg (n : ℕ) : RunsWithin X body (Main.rotIProg n) (rotI n) (vtxCost n) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := List.range n) (c := 2) (F := (· - 1)) (f := fun u => Main.predProg u)
    fun u _ => RunsWithin.predProg u
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hm
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, List.length_range,
      List.length_map, List.size_toArray, List.length_cons, List.length_nil, vtxCost]
    omega

theorem RunsWithin.swFProg (n : ℕ) : RunsWithin X body (Main.swFProg n) (swF n) (vtxCost n) := by
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
    run_step (RunsWithin.prim _ _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, Args.tail_cons, List.length_range,
      List.size_toArray, List.length_cons, List.length_nil, vtxCost]
    omega

/-- The cost of the generators. -/
def gensCost (n : ℕ) : ℕ := 3 * vtxCost n + 2 * liftDataCost n + 10

theorem RunsWithin.gensProg (n : ℕ) :
    RunsWithin X body (Main.gensProg n (gN n) (offArr n)) (gensData n) (gensCost n) := by
  by_cases h : 1 < n
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_pos (by simp [Prim.eval, h]) _
      run_step (RunsWithin.rotFProg n)
      run_step (RunsWithin.rotIProg n)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.liftDataProg n _)
      run_step (RunsWithin.swFProg n)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.liftDataProg n _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le (by simp [Prim.eval, gensData, h]) le_rfl
    case hc =>
      simp only [Prim.cost, gensCost]
      omega
  · apply RunsWithin.mono
    case h =>
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_with Sims.RunsWithin.ite_neg (by simp [Prim.eval, h]) _
      exact RunsWithin.prim_le (by simp [Prim.eval, gensData, h]) le_rfl
    case hc =>
      simp only [Prim.cost, gensCost]
      omega

theorem RunsWithin.restrictArrProg (n : ℕ) (a : Array ℕ) :
    RunsWithin X body (Main.restrictArrProg n a) (restrictArr n a) (6 * n + 4) := by
  have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := .nat) (b' := .nat)
    (xs := List.range n) (c := 1) (F := get a) (f := fun u => .op2 .arrayGet a u)
    fun u _ => RunsWithin.prim_le rfl le_rfl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step hm
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost, Args.head_cons, List.length_range, List.length_map]
    omega

theorem RunsWithin.restrictProg (n : ℕ) (d : PermData) :
    RunsWithin X body (Main.restrictProg n d) (restrictData n d) (12 * n + 11) := by
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.restrictArrProg n _)
    run_step (RunsWithin.restrictArrProg n _)
    exact RunsWithin.prim_le rfl le_rfl
  case hc =>
    simp only [Prim.cost]
    omega

/-- The cost of the decoding, for at most `s` generators. -/
def decCost (n s : ℕ) : ℕ := (s + 1) * (12 * n + 14) + 6

theorem RunsWithin.decodeProg {D : Ty} (n s : ℕ) (ans : AnswerData D)
    (hs : ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s) :
    RunsWithin X body (Main.decodeProg n ans) (decodeAns n ans) (decCost n s) := by
  rcases ans with _ | ⟨τ, H⟩
  · apply RunsWithin.mono
    case h => exact RunsWithin.caseOption_none (RunsWithin.prim_le rfl le_rfl)
    case hc =>
      simp only [Prim.cost, decCost]
      nlinarith
  · have hm := RunsWithin.mapList_le (X := X) (body := body) (a' := Ty.perm) (b' := Ty.perm)
      (xs := H.2.1) (c := 12 * n + 11) (F := restrictData n)
      (f := fun g => Main.restrictProg n g) fun g _ => RunsWithin.restrictProg n g
    have hl : H.2.1.length ≤ s := hs _ rfl
    apply RunsWithin.mono
    case h =>
      apply RunsWithin.caseOption_some
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.prim _ _)
      run_step (RunsWithin.restrictProg n _)
      run_step hm
      run_step (RunsWithin.prim _ _)
      exact RunsWithin.prim_le rfl le_rfl
    case hc =>
      simp only [Prim.cost, decCost]
      nlinarith

end Specs

/-! ### The entry -/

section Entry

/-- The encoded instance. -/
def giInst (n : ℕ) (X Y : GraphData) : Solver.Ty.input.denote :=
  ((gStr n X, gStr n Y), WinData.ofPoints (gN n) (List.range (gN n)), PermData.one (gN n), gN n,
    gensData n)

/-- The cost of the encoding, on valid data. -/
def encCost (n : ℕ) : ℕ :=
  offCost n + (3 * n + 3) + 2 * strCost n + (gN n + 1) + (2 * gN n + 5 * gN n + 7) +
    (2 * gN n + 3) + gensCost n + 11

variable {thr : ThrProg Ty.unit} {Δ n : ℕ} {X Y : GraphData}

/-- **The entry, given a run of the main entry on the encoded instance.** -/
theorem giEntry_runs (hX : X.ValidD Δ n) (hY : Y.ValidD Δ n) {c : ℕ}
    (hmain : ∃ ans : AnswerData Ty.unit,
      RunsWithin ssCtx (mainBody thr Ty.denote) (mainEntry Ty.unit Ty.denote (giInst n X Y)) ans
        c ∧
      AnsOK ssDV (gN n) ((WinData.ofPoints (gN n) (List.range (gN n))).denote (gN n))
        ((PermData.one (gN n)).denote (gN n)) ((gensData n).denote (gN n))
        ((gStr n X).denote (gN n)) ((gStr n Y).denote (gN n)) ans ∧
      ∀ c : CosetData Ty.unit, ans = some c → c.2.gens.length ≤ 2 * gN n * (2 * gN n)) :
    ∃ r, RunsWithin ssCtx (mainBody thr Ty.denote) (giEntry Ty.unit Ty.denote (n, X, Y)) r
        (encCost n + c + decCost n (2 * gN n * (2 * gN n))) ∧ GICosetOK n X Y r := by
  obtain ⟨ans, hrun, hok, hg⟩ := hmain
  rw [WinData.denote_univ, PermData.denote_one, gensData_denote] at hok
  refine ⟨decodeAns n ans, ?_, decode_ok hX hY hok hg⟩
  have hN : n + n * n = gN n := rfl
  apply RunsWithin.mono
  case h =>
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.offProg n)
    run_step (RunsWithin.mulProg n n)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.strProg hX)
    run_step (RunsWithin.strProg hY)
    run_step (RunsWithin.prim _ _)
    run_step (Programs.RunsWithin.mkWindow _ _)
    run_step (Programs.RunsWithin.permOne _)
    run_step (RunsWithin.gensProg n)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step (RunsWithin.prim _ _)
    run_step hrun
    exact RunsWithin.decodeProg n _ ans hg
  case hc =>
    simp only [Prim.cost, Prim.eval, Args.head_cons, List.length_range, encCost, gN]
    omega

end Entry

end GraphIso.Main
