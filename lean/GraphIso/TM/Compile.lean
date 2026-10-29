module

public import GraphIso.TM.Env
public import GraphIso.Cost.WellFormed

/-!
# The compiler

Stage 17e (`PLAN-17.md` §8). Programs of the cost language over the empty signature are
compiled to stack-program code, and the code is proved to simulate `eval`.

* **Levels.** A program is instantiated with de Bruijn levels, `Lv t = ℕ`. The compiled code
  keeps the pointers of the variables in scope on `env` (`GraphIso.TM.Env`): in a frame of
  depth `d`, the level `k < d` is the entry `d - 1 - k` from the top.
* **`comp pc pb d p`** pushes the pointer of the value of `p` onto `work`:
  - `ret x` copies the entry of `x`; `bind p k` runs `p`, moves its pointer onto `env`, runs
    `k d` at depth `d + 1` and drops the entry;
  - `prim p xs` copies the arguments' pointers onto `work` and runs `pc p`, the code of the
    primitive (a parameter, specified by `PrimSpec`);
  - `ite`, `caseOption` and `caseList` fetch the cell of the scrutinee, branch on its tag and
    bind its fields as new levels (`iteCode`, `optCode`, `listCode`);
  - `foldList xs i f` is a while loop (`foldCode`, `foldStep`): the remaining list is at level
    `d`, and each step binds the accumulator and the element at levels `d + 1` and `d + 2`;
  - `loop x f` is a while loop (`loopCode`, `loopStep`): the state is bound at level `d`;
  - `recur x` moves the argument's pointer onto `env`, a new frame of depth `1`, and calls the
    procedure `pb`, whose body is the compiled procedure body `comp pc pb 1 (Pr.proc Lv 0)`.
* **`psize d p`**: the size of the program; a primitive weighs `pw p + 1` (`pw` covers the bits
  of a literal and the cells of a default value), a loop or a fold `2` plus its body.
* **`HeapBnd B F h`**, the size invariant: the cell at index `i` has an address of at most
  `B + i` bits, at most `F` fields, and fields of at most `B + i` bits. Every heap satisfies it
  for `B` and `F` at least its length in symbols (`HeapBnd.of_length`), and then it has at most
  `h.length * (B + h.length + 4 + F * (B + h.length + 1))` symbols (`length_encHeap_le_bnd`).
  Pointers (entries of frames, arguments and results) have at most `B + h.length` bits.
* **`PrimSpec prog pc B F K Q`**, the specification of the primitives' code (written in stage
  17f): for every primitive `p` with `pw p ≤ K` and arguments `xs` with `p.cost xs ≤ F` whose
  pointers (of at most `B + h.length` bits) are on `work`, the last on top, from `HeapAt h` and
  `HeapBnd B F h` with empty registers, `pc p` appends at most `K * p.cost xs` cells keeping
  `HeapAt` and `HeapBnd B F`, replaces the arguments by a pointer (of at most `B` plus the new
  number of cells in bits) representing `p.eval xs`, leaves the registers empty and every stack
  but `heap` and `cnt` unchanged, within `p.cost xs * Q N` steps, `N` the final heap's length in
  symbols.
* **`comp_sat`**, the simulation theorem. The proof is by induction on the fuel (`sim_all`), one
  lemma per construct (`sim_ret`, …, `sim_recur`), and for the loops an inner induction on the
  remaining list (`foldLoop_sat`) or on the fuel (`loopLoop_sat`).

**Step bounds.** Besides its parts, each construct takes at most `Q N` steps
(`ctrlB D (B + N) ≤ Q N`, `D` a bound on the depth of frames), and each charged unit pays for at
most `K` times `Q N` steps, where `K` is at least the size of every loop body and of the
procedure body plus `1`. So the code of `p` runs within `(psize d p + K * cost) * Q N` steps.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost

variable {P : Type}

/-- Variables as de Bruijn levels. -/
abbrev Lv : Ty → Type := fun _ => ℕ

/-- Code for each primitive. -/
abbrev PrimCode (P : Type) : Type :=
  ∀ {args : List Ty} {t : Ty}, Prim args t → Code Stk Sym Rg P

/-- The number of cells of the default value of a type. -/
def tySize : Ty → ℕ
  | .prod a b => tySize a + tySize b + 1
  | _ => 1

/-- The weight of a primitive: the bits of a literal, the cells of a default value. -/
def pw : {args : List Ty} → {t : Ty} → Prim args t → ℕ
  | _, _, .natLit k => (toBits k).length + 2
  | _, a, .arrayGet => tySize a + 2
  | _, _, _ => 2

/-- The marker that keeps a compiled loop running. -/
abbrev goMark : Sym := .mk 3

/-- Move the number on top of `work` onto `env`. -/
def pushEnv : Code Stk Sym Rg P := moveNum2 .work .env .t0

/-- Drop the top entry of `env`. -/
def popEnv : Code Stk Sym Rg P := dropNum .env

/-- Copy the arguments' pointers onto `work`, the last on top. -/
def fetchArgs (d : ℕ) : {ts : List Ty} → Args Lv ts → Code Stk Sym Rg P
  | _, .nil => .skip
  | _, .cons x xs => .seq (fetchLv d x .work) (fetchArgs d xs)

/-- A branch on a Boolean at level `x`. -/
def iteCode (d x : ℕ) (cp cq : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (fetchLv d x .ptr) (.seq fetchCell (.seq closeCell
    (.ite (.is 1 (some (.tag .tt))) (.seq (.act (.set 1 none)) cp)
      (.seq (.act (.set 1 none)) cq))))

/-- Case analysis on an option at level `x`; the value of `some` is bound at level `d`. -/
def optCode (d x : ℕ) (cp cq : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (fetchLv d x .ptr) (.seq fetchCell
    (.ite (.is 1 (some (.tag .none))) (.seq (.act (.set 1 none)) (.seq closeCell cp))
      (.seq (.act (.set 1 none)) (.seq pushEnv (.seq closeCell (.seq cq popEnv))))))

/-- Case analysis on a list at level `x`; the head and the tail of `cons` are bound at levels
`d` and `d + 1`. -/
def listCode (d x : ℕ) (cp cq : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (fetchLv d x .ptr) (.seq fetchCell
    (.ite (.is 1 (some (.tag .nil))) (.seq (.act (.set 1 none)) (.seq closeCell cp))
      (.seq (.act (.set 1 none)) (.seq pushEnv (.seq pushEnv (.seq closeCell
        (.seq cq (.seq popEnv popEnv))))))))

/-- One step of a fold: the remaining list is at level `d`, the accumulator on `work`. On
`cons`, the tail replaces the list, the accumulator and the head are bound at levels `d + 1`
and `d + 2`, and the body runs. -/
def foldStep (cf : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (.act (.set 0 none)) (.seq (copyNum .env .ptr .t0) (.seq fetchCell
    (.ite (.is 1 (some (.tag .cons)))
      (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .t4 .t0) (.seq popEnv (.seq pushEnv
        (.seq closeCell (.seq pushEnv (.seq (moveNum2 .t4 .env .t0) (.seq cf
          (.seq popEnv (.seq popEnv (.act (.set 0 (some goMark)))))))))))))
      (.seq (.act (.set 1 none)) closeCell))))

/-- A fold over the list at level `xs` from the value at level `i`. -/
def foldCode (d xs i : ℕ) (cf : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (fetchLv d xs .work) (.seq pushEnv (.seq (fetchLv (d + 1) i .work)
    (.seq (.act (.set 0 (some goMark))) (.seq (.loop (.is 0 (some goMark)) (foldStep cf)) popEnv))))

/-- One step of a loop: the state, on `work`, is bound at level `d`, and the body runs; on
`some`, its value is the new state; on `none`, the state is the result. -/
def loopStep (cf : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (.act (.set 0 none)) (.seq pushEnv (.seq cf (.seq (moveNum2 .work .ptr .t0)
    (.seq fetchCell (.ite (.is 1 (some (.tag .some)))
      (.seq (.act (.set 1 none)) (.seq (moveNum2 .work .t4 .t0) (.seq closeCell
        (.seq (moveNum2 .t4 .work .t0) (.seq popEnv (.act (.set 0 (some goMark))))))))
      (.seq (.act (.set 1 none)) (.seq closeCell (moveNum2 .env .work .t0))))))))

/-- A loop from the state at level `x`. -/
def loopCode (d x : ℕ) (cf : Code Stk Sym Rg P) : Code Stk Sym Rg P :=
  .seq (fetchLv d x .work)
    (.seq (.act (.set 0 (some goMark))) (.loop (.is 0 (some goMark)) (loopStep cf)))

/-- **The compiler**: code that pushes the pointer of the program's value onto `work`, in a
frame of depth `d`. -/
def comp (pc : PrimCode P) (pb : P) {rec : Ty × Ty} :
    ℕ → {t : Ty} → Prog Signature.empty rec Lv t → Code Stk Sym Rg P
  | d, _, .ret x => fetchLv d x .work
  | d, _, .bind p k =>
    .seq (comp pc pb d p) (.seq pushEnv (.seq (comp pc pb (d + 1) (k d)) popEnv))
  | d, _, .prim p xs => .seq (fetchArgs d xs) (pc p)
  | d, _, .ite x p q => iteCode d x (comp pc pb d p) (comp pc pb d q)
  | d, _, .caseOption x p q => optCode d x (comp pc pb d p) (comp pc pb (d + 1) (q d))
  | d, _, .caseList x p q => listCode d x (comp pc pb d p) (comp pc pb (d + 2) (q d (d + 1)))
  | d, _, .foldList xs i f => foldCode d xs i (comp pc pb (d + 3) (f (d + 1) (d + 2)))
  | d, _, .loop x f => loopCode d x (comp pc pb (d + 1) (f d))
  | d, _, .recur x => .seq (fetchLv d x .work) (.seq pushEnv (.seq (.call pb) popEnv))
  | _, _, .call op _ => Empty.elim op

/-- The size of a program. -/
def psize {rec : Ty × Ty} : ℕ → {t : Ty} → Prog Signature.empty rec Lv t → ℕ
  | _, _, .ret _ => 1
  | d, _, .bind p k => psize d p + psize (d + 1) (k d) + 1
  | _, _, .prim p _ => pw p + 1
  | d, _, .ite _ p q => psize d p + psize d q + 1
  | d, _, .caseOption _ p q => psize d p + psize (d + 1) (q d) + 1
  | d, _, .caseList _ p q => psize d p + psize (d + 2) (q d (d + 1)) + 1
  | d, _, .foldList _ _ f => psize (d + 3) (f (d + 1) (d + 2)) + 2
  | d, _, .loop _ f => psize (d + 1) (f d) + 2
  | _, _, .recur _ => 1
  | _, _, .call op _ => Empty.elim op

/-- **The size invariant of the heap**: the cell at index `i` has an address of at most `B + i`
bits, at most `F` fields, and fields of at most `B + i` bits. Every heap satisfies it when `B`
and `F` are at least its length in symbols (`HeapBnd.of_length`). -/
def HeapBnd (B F : ℕ) (h : List Cell) : Prop :=
  ∀ i (hi : i < h.length), h[i].addr.length ≤ B + i ∧ h[i].fields.length ≤ F ∧
    ∀ f ∈ h[i].fields, f.length ≤ B + i

/-- The frame of depth `d` on `env` represents the context `Γ`: its entries are pointers of at
most `B + h.length` bits, and each `⟨t, x, k⟩ ∈ Γ` has `k < d` and its entry represents `x`. -/
def EnvAt (B : ℕ) (Γ : WfCtx Ty.denote Lv) (d : ℕ) (h : List Cell) (c : Cfg Stk Sym Rg) : Prop :=
  ∃ ls rest, ls.length = d ∧ c.stk .env = envEnc ls ++ rest ∧
    (∀ l ∈ ls, l.length ≤ B + h.length) ∧
    ∀ e ∈ Γ, ∃ hk : e.2.2 < ls.length, Rep h e.1 e.2.1 (ofBits ls[e.2.2])

/-- Pointers representing arguments. -/
inductive ArgsRep (h : List Cell) : {ts : List Ty} → Args Ty.denote ts → List (List Bool) → Prop
  | nil : ArgsRep h .nil []
  | cons {t : Ty} {ts : List Ty} {x : t.denote} {xs : Args Ty.denote ts} {l : List Bool}
      {ls : List (List Bool)} :
      Rep h t x (ofBits l) → ArgsRep h xs ls → ArgsRep h (.cons x xs) (l :: ls)

/-- The step bound of `fetchCell` for a heap of `N` symbols and a pointer of at most `E` bits. -/
def fcE (N E : ℕ) : ℕ := lookupBound N E + 2 * N + 12

/-- The control overhead of one construct, for a frame of depth at most `D`, a heap of at most
`M` symbols and pointers of at most `M` bits. -/
def ctrlB (D M : ℕ) : ℕ := 3 * fetchB D M + fcE M M + 100 * M + 200

/-- **The specification of the primitives' code**: from `HeapAt h` and `HeapBnd B F h`, empty
registers, and the pointers `ls` of the arguments (of at most `B + h.length` bits) on `work`
(the last on top), `pc p` appends at most `K * p.cost xs` cells, keeping `HeapAt` and
`HeapBnd B F`, and replaces the arguments by a pointer of at most `B + (h ++ h').length` bits
representing `p.eval xs`, within `p.cost xs * Q N` steps (`N` the final heap's length in
symbols). -/
def PrimSpec (prog : Program Stk Sym Rg P) (pc : PrimCode P) (B F K : ℕ) (Q : ℕ → ℕ) : Prop :=
  ∀ {args : List Ty} {t : Ty} (p : Prim args t) (xs : Args Ty.denote args) (h : List Cell)
    (c : Cfg Stk Sym Rg) (ls : List (List Bool)) (w : List Sym),
    pw p ≤ K → K ≤ B → p.cost xs ≤ F → HeapAt h c → HeapBnd B F h → c.regs = Regs.empty →
    ArgsRep h xs ls → (∀ l ∈ ls, l.length ≤ B + h.length) → c.stk .work = envEnc ls ++ w →
    ∃ c' n h' l, Exec prog (pc p) c c' n ∧ HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
      c'.regs = Regs.empty ∧ Rep (h ++ h') t (p.eval xs) (ofBits l) ∧
      l.length ≤ B + (h ++ h').length ∧ c'.stk .work = bits l ++ .nd :: w ∧
      (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c.stk j) ∧
      h'.length ≤ K * p.cost xs ∧ n ≤ p.cost xs * Q (encHeap (h ++ h')).length

/-- The code `x` pushes a pointer representing `v` onto `work`: it appends cells (at most
`K * C`) keeping `HeapAt` and `HeapBnd B F`, the pointer has at most `B` plus the new number of
cells in bits, the registers end empty, every stack but `heap`, `cnt` and `work` is unchanged,
within `(s + K * C) * Q N` steps (`N` the final heap's length in symbols). -/
def Pushes (prog : Program Stk Sym Rg P) (x : Code Stk Sym Rg P) (c : Cfg Stk Sym Rg)
    (h : List Cell) (t : Ty) (v : t.denote) (B F K : ℕ) (Q : ℕ → ℕ) (s C : ℕ) : Prop :=
  ∃ c' n h' l, Exec prog x c c' n ∧ HeapAt (h ++ h') c' ∧ HeapBnd B F (h ++ h') ∧
    c'.regs = Regs.empty ∧ Rep (h ++ h') t v (ofBits l) ∧ l.length ≤ B + (h ++ h').length ∧
    c'.stk .work = bits l ++ .nd :: c.stk .work ∧
    (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c.stk j) ∧
    h'.length ≤ K * C ∧ n ≤ (s + K * C) * Q (encHeap (h ++ h')).length

/-! ### Heaps and frames -/

theorem length_encHeap_append (h h' : List Cell) :
    (encHeap (h ++ h')).length = (encHeap h).length + (encHeap h').length := by
  simp [length_encHeap]

theorem length_encHeap_mono (h h' : List Cell) :
    (encHeap h).length ≤ (encHeap (h ++ h')).length := by
  rw [length_encHeap_append]; omega

theorem length_encFields (fs : List (List Bool)) :
    (encFields fs).length = (fs.map fun f => f.length + 1).sum := by
  induction fs with
  | nil => rfl
  | cons f fs ih => rw [length_encFields_cons, ih]; simp

/-- The fields of a cell have fewer than `B + h.length` bits. -/
theorem HeapBnd.field_lt {B F : ℕ} {h : List Cell} (hB : HeapBnd B F h) {p : ℕ} {t : Tag}
    {fs : List (List Bool)} (hc : CellAt h p t fs) : ∀ f ∈ fs, f.length < B + h.length := by
  obtain ⟨hp, _, hf⟩ := hc
  intro f hfs
  have := (hB p hp).2.2 f (hf ▸ hfs)
  omega

/-- **Every heap satisfies the size invariant** for `B` and `F` at least its length in symbols. -/
theorem HeapBnd.of_length {B F : ℕ} {h : List Cell} (hB : (encHeap h).length ≤ B)
    (hF : (encHeap h).length ≤ F) : HeapBnd B F h := by
  intro i hi
  have hc := length_encCell_le h i hi
  have ha := length_addr_lt h[i]
  have hfs : (encFields h[i].fields).length < (encCell h[i]).length := by
    simp [encCell, cellBody]; omega
  have hcnt := length_le_encFields h[i].fields
  refine ⟨by omega, by omega, fun f hf => ?_⟩
  have : f.length < (encFields h[i].fields).length := by
    rw [length_encFields]
    have := le_sum_of_mem_nat (List.mem_map.2 ⟨f, hf, rfl⟩ :
      f.length + 1 ∈ h[i].fields.map fun f => f.length + 1)
    omega
  omega

/-- **The length of a heap under the size invariant.** -/
theorem length_encHeap_le_bnd {B F : ℕ} {h : List Cell} (hB : HeapBnd B F h) :
    (encHeap h).length ≤ h.length * (B + h.length + 4 + F * (B + h.length + 1)) := by
  rw [length_encHeap]
  refine sum_map_le_mul _ _ h fun cl hcl => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hcl
  obtain ⟨ha, hF, hf⟩ := hB i hi
  have hfs : (encFields h[i].fields).length ≤ F * (B + h.length + 1) := by
    rw [length_encFields]
    refine (sum_map_le_mul _ (B + h.length + 1) _ fun f hf' => ?_).trans
      (Nat.mul_le_mul_right _ hF)
    have := hf f hf'
    omega
  simp only [encCell, cellBody, List.length_append, List.length_cons, length_bits,
    List.length_nil]
  omega

theorem EnvAt.mono {B : ℕ} {Γ : WfCtx Ty.denote Lv} {d : ℕ} {h : List Cell} {c c' : Cfg Stk Sym Rg}
    (hE : EnvAt B Γ d h c) (h' : List Cell) (he : c'.stk .env = c.stk .env) :
    EnvAt B Γ d (h ++ h') c' := by
  obtain ⟨ls, rest, hl, hc, hb, hΓ⟩ := hE
  refine ⟨ls, rest, hl, he.trans hc, fun l hl' => ?_, fun e he' => ?_⟩
  · have := hb l hl'; simp only [List.length_append]; omega
  · obtain ⟨hk, hr⟩ := hΓ e he'
    exact ⟨hk, hr.mono⟩

/-- Binding a new level. -/
theorem EnvAt.push {B : ℕ} {Γ : WfCtx Ty.denote Lv} {d : ℕ} {h h' : List Cell}
    {c c' : Cfg Stk Sym Rg}
    {t : Ty} {x : t.denote} {l : List Bool} (hE : EnvAt B Γ d h c)
    (he : c'.stk .env = bits l ++ .nd :: c.stk .env) (hr : Rep (h ++ h') t x (ofBits l))
    (hl : l.length ≤ B + (h ++ h').length) : EnvAt B (⟨t, x, d⟩ :: Γ) (d + 1) (h ++ h') c' := by
  obtain ⟨ls, rest, rfl, hc, hb, hΓ⟩ := hE
  refine ⟨ls ++ [l], rest, by simp, by rw [he, hc, envEnc_concat]; simp, fun m hm => ?_,
    fun e he' => ?_⟩
  · rcases List.mem_append.1 hm with hm | hm
    · have := hb m hm; simp only [List.length_append]; omega
    · rw [List.mem_singleton.1 hm]; exact hl
  · rcases List.mem_cons.1 he' with rfl | he'
    · exact ⟨by simp, by simpa using hr⟩
    · obtain ⟨hk, hr'⟩ := hΓ e he'
      exact ⟨by rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt hk,
        by rw [List.getElem_append_left hk]; exact hr'.mono⟩

theorem EnvAt.sub {B : ℕ} {Γ Γ' : WfCtx Ty.denote Lv} {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    (hE : EnvAt B Γ d h c) (hs : Γ' ⊆ Γ) : EnvAt B Γ' d h c := by
  obtain ⟨ls, rest, hl, hc, hb, hΓ⟩ := hE
  exact ⟨ls, rest, hl, hc, hb, fun e he => hΓ e (hs he)⟩

/-- The pointer of a variable. -/
theorem EnvAt.var {B : ℕ} {Γ : WfCtx Ty.denote Lv} {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    (hE : EnvAt B Γ d h c) {t : Ty} {x : t.denote} {k : ℕ} (hx : ⟨t, x, k⟩ ∈ Γ) :
    ∃ ls rest, ls.length = d ∧ c.stk .env = envEnc ls ++ rest ∧
      (∀ l ∈ ls, l.length ≤ B + h.length) ∧ ∃ hk : k < ls.length, Rep h t x (ofBits ls[k]) := by
  obtain ⟨ls, rest, hl, hc, hb, hΓ⟩ := hE
  exact ⟨ls, rest, hl, hc, hb, hΓ _ hx⟩

theorem fetchB_mono {j j' E E' : ℕ} (hj : j ≤ j') (hE : E ≤ E') : fetchB j E ≤ fetchB j' E' :=
  Nat.mul_le_mul (by omega) (by omega)

variable {prog : Program Stk Sym Rg P}

/-- `fetchCell` for a pointer of at most `E` bits. -/
theorem fetchCellE_sat {h : List Cell} {c : Cfg Stk Sym Rg} {p : List Bool} {rp : List Sym}
    {t : Tag} {fs : List (List Bool)} {E : ℕ} (hwf : HeapWF h) (hh : c.stk .heap = encHeap h)
    (hs : c.stk .scan = []) (hv : c.regs = Regs.empty) (hc : CellAt h (ofBits p) t fs)
    (hpE : p.length ≤ E) (hp : c.stk .ptr = bits p ++ .nd :: rp) :
    Sat prog fetchCell c (fcE (encHeap h).length E) fun c' =>
      c'.regs = rv none (some (.tag t)) none none ∧
        c'.stk .work = encFields fs ++ .mk 0 :: c.stk .work ∧ c'.stk .ptr = rp ∧
        ∀ j, j ≠ .work → j ≠ .ptr → c'.stk j = c.stk j := by
  obtain ⟨hi, ht, hf⟩ := hc
  have hl := lookupBound_mono (N := (encHeap h).length) hpE
  have ha := length_addr_lt h[ofBits p]
  have hN := length_encCell_le h _ hi
  unfold fetchCell fcE
  refine Sat.seq_le (lookup_sat hwf hv hh hs hp hi) (by omega) fun c₁ ⟨hr₁, hw₁, hp₁, hj₁⟩ => ?_
  refine (openCell_sat hr₁ hw₁).mono (by omega) fun c' ⟨hr', hw', hj'⟩ =>
    ⟨by rw [hr', ht], by rw [hw', hf], by rw [hj' .ptr (by decide), hp₁], fun j hjw hjp => ?_⟩
  rw [hj' j hjw, hj₁ j hjw hjp]

/-- Copy the pointer of a variable onto `dst`. -/
theorem fetchVar_sat {B : ℕ} {Γ : WfCtx Ty.denote Lv} {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    (hE : EnvAt B Γ d h c) (hv : c.regs = Regs.empty) {t : Ty} {x : t.denote} {k : ℕ}
    (hx : ⟨t, x, k⟩ ∈ Γ) {dst : Stk} (hd₁ : dst ≠ .env) (hd₂ : dst ≠ .t0) (hd₃ : dst ≠ .t1) :
    ∃ l, Rep h t x (ofBits l) ∧ l.length ≤ B + h.length ∧
      Sat prog (fetchLv d k dst) c (fetchB d (B + h.length)) fun c' =>
        c'.regs = Regs.empty ∧ c'.stk dst = bits l ++ .nd :: c.stk dst ∧
          ∀ j, j ≠ dst → c'.stk j = c.stk j := by
  obtain ⟨ls, rest, rfl, he, hb, hk, hr⟩ := hE.var hx
  exact ⟨ls[k], hr, hb _ (List.getElem_mem hk), (fetchLv_sat hd₁ hd₂ hd₃ hk hv he hb).mono
    (fetchB_mono (by omega) le_rfl) fun _ h => h⟩

/-- Copy the pointers of the arguments onto `work`. -/
theorem fetchArgs_sat {B : ℕ} {Γ : WfCtx Ty.denote Lv} {d : ℕ} {h : List Cell} :
    ∀ {ts : List Ty} {xs₁ : Args Ty.denote ts} {xs₂ : Args Lv ts}, Args.Wf Γ xs₁ xs₂ →
    ∀ {c : Cfg Stk Sym Rg}, EnvAt B Γ d h c → c.regs = Regs.empty →
    ∃ ls, ArgsRep h xs₁ ls ∧ (∀ l ∈ ls, l.length ≤ B + h.length) ∧
      Sat prog (fetchArgs d xs₂) c (ts.length * (fetchB d (B + h.length) + 1) + 1) fun c' =>
        c'.regs = Regs.empty ∧ c'.stk .work = envEnc ls ++ c.stk .work ∧
          ∀ j, j ≠ .work → c'.stk j = c.stk j
  | _, _, _, .nil, c, _, hv => ⟨[], .nil, by simp, (Sat.skip (Q := fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .work = envEnc [] ++ c.stk .work ∧
        ∀ j, j ≠ .work → c'.stk j = c.stk j) ⟨hv, by simp, fun _ _ => rfl⟩).mono (by simp)
      fun _ h => h⟩
  | _, _, _, .cons hx hxs, c, hE, hv => by
    obtain ⟨l, hr, hl, hs⟩ := fetchVar_sat (prog := prog) hE hv hx (dst := .work) (by decide)
      (by decide) (by decide)
    obtain ⟨c₁, n₁, e₁, hn₁, hr₁, hw₁, hj₁⟩ := hs
    have hE₁ : EnvAt B Γ d h c₁ := by
      simpa using hE.mono [] (hj₁ .env (by decide))
    obtain ⟨ls, hR, hb, hs'⟩ := fetchArgs_sat hxs hE₁ hr₁
    obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hw₂, hj₂⟩ := hs'
    refine ⟨l :: ls, .cons hr hR, fun m hm => ?_, c₂, _, .seq e₁ e₂, ?_, hr₂, ?_,
      fun j hj => ?_⟩
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact hl
      · exact hb m hm
    · simp only [List.length_cons, Nat.succ_mul]; omega
    · rw [hw₂, hw₁]; simp [envEnc, encNums_append]
    · rw [hj₂ j hj, hj₁ j hj]

/-! ### The simulation, case by case -/

theorem length_args_le {args : List Ty} {t : Ty} (p : Prim args t) : args.length ≤ 2 := by
  cases p <;> simp

theorem two_le_pw {args : List Ty} {t : Ty} (p : Prim args t) : 2 ≤ pw p := by
  cases p <;> simp [pw]

theorem fetchB_le_ctrlB {d D E N : ℕ} (hd : d ≤ D) (hE : E ≤ N) : fetchB d E ≤ ctrlB D N := by
  have := fetchB_mono hd hE
  unfold ctrlB; omega

theorem lin_le_ctrlB (D N : ℕ) : 100 * N + 200 ≤ ctrlB D N := by unfold ctrlB; omega

theorem fcE_le_ctrlB (D N : ℕ) : fcE N N + 100 * N + 200 ≤ ctrlB D N := by unfold ctrlB; omega

theorem fcE_mono {N N' E E' : ℕ} (hN : N ≤ N') (hE : E ≤ E') : fcE N E ≤ fcE N' E' := by
  unfold fcE lookupBound; gcongr

theorem length_le_encHeap_append (h h' : List Cell) : h.length ≤ (encHeap (h ++ h')).length :=
  (Nat.le_trans (by simp) (length_le_encHeap (h ++ h')))

/-- The control overhead at the heap `h` (pointers of at most `B + h.length` bits, frames of
depth `j ≤ D`) is paid by `Q` at any larger heap `h ++ g`. -/
theorem ctrl_le {B D j : ℕ} {Q : ℕ → ℕ} (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) (hj : j ≤ D)
    (h g : List Cell) :
    B + h.length ≤ B + (encHeap (h ++ g)).length ∧
    3 * fetchB j (B + h.length) + fcE (encHeap h).length (B + h.length) +
      100 * (B + (encHeap (h ++ g)).length) + 200 ≤ Q (encHeap (h ++ g)).length := by
  have hN := length_le_encHeap_append h g
  have hN' := length_encHeap_mono h g
  have h₁ := fetchB_mono hj (by omega : B + h.length ≤ B + (encHeap (h ++ g)).length)
  have h₂ := fcE_mono (by omega : (encHeap h).length ≤ B + (encHeap (h ++ g)).length)
    (by omega : B + h.length ≤ B + (encHeap (h ++ g)).length)
  have h₃ := hQc (encHeap (h ++ g)).length
  unfold ctrlB at h₃
  exact ⟨by omega, by omega⟩

theorem bnd_one {n o s K C q : ℕ} (hn : n ≤ o) (ho : o ≤ q) (hs : 1 ≤ s) :
    n ≤ (s + K * C) * q := by
  have : q ≤ (s + K * C) * q := Nat.le_mul_of_pos_left q (by omega)
  omega

theorem bnd_bind {n₁ n₃ o s₁ s₂ C₁ C₂ K q : ℕ} (h₁ : n₁ ≤ (s₁ + K * C₁) * q)
    (h₃ : n₃ ≤ (s₂ + K * C₂) * q) (ho : o ≤ q) :
    n₁ + n₃ + o ≤ (s₁ + s₂ + 1 + K * (C₁ + C₂)) * q := by
  have : (s₁ + s₂ + 1 + K * (C₁ + C₂)) * q = (s₁ + K * C₁) * q + (s₂ + K * C₂) * q + q := by
    ring
  omega

/-- Monotonicity of a bound in the heap. -/
theorem bnd_mono {n s K C : ℕ} {Q : ℕ → ℕ} (hQ : Monotone Q) {N N' : ℕ} (hn : n ≤ (s + K * C) * Q N)
    (hN : N ≤ N') : n ≤ (s + K * C) * Q N' :=
  hn.trans (Nat.mul_le_mul_left _ (hQ hN))

/-- Fetch the cell of a variable: its tag in register `1`, its fields and the marker `mk 0` on
`work`. -/
theorem fetchVarCell {B : ℕ} {Γ : WfCtx Ty.denote Lv} {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    (hH : HeapAt h c) (hE : EnvAt B Γ d h c) (hv : c.regs = Regs.empty) {t : Ty} {x : t.denote}
    {k : ℕ} (hx : ⟨t, x, k⟩ ∈ Γ) :
    ∃ l, Rep h t x (ofBits l) ∧ ∀ tg fs, CellAt h (ofBits l) tg fs →
      ∃ c₁ n₁ c₂ n₂, Exec prog (fetchLv d k .ptr) c c₁ n₁ ∧ Exec prog fetchCell c₁ c₂ n₂ ∧
        n₁ + n₂ ≤ fetchB d (B + h.length) + fcE (encHeap h).length (B + h.length) ∧
        c₂.regs = rv none (some (.tag tg)) none none ∧
        c₂.stk .work = encFields fs ++ .mk 0 :: c.stk .work ∧
        ∀ j, j ≠ .work → c₂.stk j = c.stk j := by
  obtain ⟨l, hr, hl, c₁, n₁, e₁, hn₁, hr₁, hp₁, hj₁⟩ :=
    fetchVar_sat (prog := prog) hE hv hx (dst := .ptr) (by decide) (by decide) (by decide)
  refine ⟨l, hr, fun tg fs hc => ?_⟩
  obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hw₂, hp₂, hj₂⟩ := fetchCellE_sat (prog := prog) hH.wf
    ((hj₁ .heap (by decide)).trans hH.heap) ((hj₁ .scan (by decide)).trans hH.scan) hr₁ hc hl hp₁
  refine ⟨c₁, n₁, c₂, n₂, e₁, e₂, by omega, hr₂, by rw [hw₂, hj₁ .work (by decide)],
    fun j hj => ?_⟩
  by_cases hjp : j = .ptr
  · subst hjp; rw [hp₂]
  · rw [hj₂ j hj hjp, hj₁ j hjp]

theorem exec_ite_cond {b : Cond Sym Rg} {x : Bool} {X Y : Code Stk Sym Rg P}
    {c c' : Cfg Stk Sym Rg} {n : ℕ} (hb : b.eval c.regs = x) (h : Exec prog (cond x X Y) c c' n) :
    Exec prog (.ite b X Y) c c' (n + 1) := by
  cases x
  · exact .ite_false hb h
  · exact .ite_true hb h

theorem bnd_branch {nb o s' S₀ C' K q : ℕ} (hb : nb ≤ (s' + K * C') * q) (hs : s' ≤ S₀)
    (ho : o ≤ q) : o + nb ≤ (S₀ + 1 + K * (1 + C')) * q := by
  have e : (S₀ + 1 + K * (1 + C')) * q = (S₀ + K * C') * q + q + K * q := by ring
  have : (s' + K * C') * q ≤ (S₀ + K * C') * q := Nat.mul_le_mul_right _ (by omega)
  omega

theorem bnd_recur {nb o sb C' K q : ℕ} (hb : nb ≤ (sb + K * C') * q) (hK : sb ≤ K)
    (ho : o ≤ q) : o + nb ≤ (1 + K * (1 + C')) * q := by
  have e : (1 + K * (1 + C')) * q = q + K * q + K * C' * q := by ring
  have e' : (sb + K * C') * q = sb * q + K * C' * q := by ring
  have : sb * q ≤ K * q := Nat.mul_le_mul_right _ hK
  omega

/-- The head of a fold step: copy the remaining list's pointer from `env` and fetch its cell. -/
theorem foldHead {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c)
    (hv : c.regs = rv (some goMark) none none none) {lH : List Bool} {rest : List Sym}
    (he : c.stk .env = bits lH ++ .nd :: rest) {E : ℕ} (hl : lH.length ≤ E) {tg : Tag}
    {fs : List (List Bool)} (hc : CellAt h (ofBits lH) tg fs) :
    ∃ c₂ n₂ c₃ n₃, Exec prog (copyNum .env .ptr .t0) (Act.run (.set 0 none) c) c₂ n₂ ∧
      Exec prog fetchCell c₂ c₃ n₃ ∧ n₂ + n₃ ≤ 14 * lH.length + 21 + fcE (encHeap h).length E ∧
      c₃.regs = rv none (some (.tag tg)) none none ∧
      c₃.stk .work = encFields fs ++ .mk 0 :: c.stk .work ∧
      ∀ j, j ≠ .work → c₃.stk j = c.stk j := by
  have hr₁ : (Act.run (.set 0 none) c).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hv]
  obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hp₂, hj₂⟩ := copyNum_sat (prog := prog) (a := .env) (b := .ptr)
    (t := .t0) (by decide) (by decide) (by decide) hr₁ (by simpa [Act.run] using he)
  have hj₂' : ∀ j, j ≠ .ptr → c₂.stk j = c.stk j := fun j hj => by
    rw [hj₂ j hj]; rfl
  obtain ⟨c₃, n₃, e₃, hn₃, hr₃, hw₃, hp₃, hj₃⟩ := fetchCellE_sat (prog := prog) hH.wf
    ((hj₂' .heap (by decide)).trans hH.heap) ((hj₂' .scan (by decide)).trans hH.scan) hr₂ hc
    hl hp₂
  refine ⟨c₂, n₂, c₃, n₃, e₂, e₃, by omega, hr₃, by rw [hw₃, hj₂' .work (by decide)],
    fun j hj => ?_⟩
  by_cases hjp : j = .ptr
  · subst hjp; rw [hp₃]; rfl
  · rw [hj₃ j hj hjp, hj₂' j hjp]

theorem bnd_iter {o nb nr sf C₁ C₂ K q : ℕ} (ho : o ≤ q) (hb : nb ≤ (sf + K * C₁) * q)
    (hr : nr ≤ (1 + K * C₂) * q) (hK : sf + 1 ≤ K) :
    o + nb + nr ≤ (1 + K * (1 + (C₁ + C₂))) * q := by
  have e : (1 + K * (1 + (C₁ + C₂))) * q = q + K * q + K * C₁ * q + K * C₂ * q := by ring
  have e₁ : (sf + K * C₁) * q = sf * q + K * C₁ * q := by ring
  have e₂ : (1 + K * C₂) * q = q + K * C₂ * q := by ring
  have : sf * q + q ≤ K * q := by
    have := Nat.mul_le_mul_right q hK
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  omega

section Sim

variable {a b : Ty}

/-- The simulation statement at a given fuel. -/
def Sim (prog : Program Stk Sym Rg P) (pc : PrimCode P) (pb : P) (Pr : WfProc Signature.empty a b)
    (O : Oracle Signature.empty) (B F K D : ℕ) (Q : ℕ → ℕ) (fuel : ℕ) : Prop :=
  ∀ {t : Ty} {Γ : WfCtx Ty.denote Lv} {p₁ : Prog Signature.empty (a, b) Ty.denote t}
    {p₂ : Prog Signature.empty (a, b) Lv t}, Prog.Wf true Γ p₁ p₂ →
    ∀ {v : t.denote} {tr : Trace Signature.empty},
    eval O (Pr.proc Ty.denote) fuel p₁ = some (v, tr) →
    ∀ {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}, HeapAt h c → HeapBnd B F h →
    c.regs = Regs.empty → EnvAt B Γ d h c → psize d p₂ ≤ K → d + 3 * psize d p₂ ≤ D →
    Trace.localCost tr ≤ F →
    Pushes prog (comp pc pb d p₂) c h t v B F K Q (psize d p₂) (Trace.localCost tr)

variable {pc : PrimCode P} {pb : P} {Pr : WfProc Signature.empty a b} {O : Oracle Signature.empty}
  {B F K D : ℕ} {Q : ℕ → ℕ}

theorem sim_ret (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {t : Ty} {Γ : WfCtx Ty.denote Lv}
    {x₁ : t.denote} {x₂ : ℕ} (hx : ⟨t, x₁, x₂⟩ ∈ Γ) {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}
    (hH : HeapAt h c) (hB : HeapBnd B F h) (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c)
    (hD : d ≤ D) :
    Pushes prog
      (comp pc pb d (Prog.ret (S := Signature.empty) (rec := (a, b)) (var := Lv) (t := t) x₂))
      c h t x₁ B F K Q 1 0 := by
  obtain ⟨l, hr, hl, c', n, e, hn, hr', hw', hj'⟩ :=
    fetchVar_sat (prog := prog) hE hv hx (dst := .work) (by decide) (by decide) (by decide)
  obtain ⟨-, hct⟩ := ctrl_le hQc hD h []
  refine ⟨c', n, [], l, e, ?_, by simpa using hB, hr', by simpa using hr, by simpa using hl, hw',
    fun j hj _ hjw => hj' j hjw, by simp, bnd_one hn (by omega) le_rfl⟩
  simpa using hH.frame (hj' .heap (by decide)) (hj' .scan (by decide)) (hj' .cnt (by decide))

theorem sim_bind (hQ : Monotone Q) (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s t : Ty} {Γ : WfCtx Ty.denote Lv}
    {p₁ : Prog Signature.empty (a, b) Ty.denote s} {p₂ : Prog Signature.empty (a, b) Lv s}
    {k₁ : s.denote → Prog Signature.empty (a, b) Ty.denote t}
    {k₂ : ℕ → Prog Signature.empty (a, b) Lv t} (hp : Prog.Wf true Γ p₁ p₂)
    (hk : ∀ v₁ v₂, Prog.Wf true (⟨s, v₁, v₂⟩ :: Γ) (k₁ v₁) (k₂ v₂)) {v : t.denote}
    {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.bind p₁ k₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c) (hK : psize d (.bind p₂ k₂) ≤ K)
    (hD : d + 3 * psize d (.bind p₂ k₂) ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (.bind p₂ k₂)) c h t v B F K Q (psize d (.bind p₂ k₂))
      (Trace.localCost tr) := by
  obtain ⟨v₁, t₁, t₂, h₁, h₂, rfl⟩ := seqT_eq_some.1 he
  simp only [Trace.localCost_append] at hF ⊢
  have hs : psize d (Prog.bind p₂ k₂) = psize d p₂ + psize (d + 1) (k₂ d) + 1 := rfl
  rw [hs] at hK hD ⊢
  obtain ⟨c₁, n₁, g₁, l₁, e₁, hH₁, hB₁, hr₁, hR₁, hl₁, hw₁, hj₁, hc₁, hn₁⟩ :=
    ih hp h₁ hH hB hv hE (by omega) (by omega) (by omega)
  obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hw₂, he₂, hj₂⟩ := moveNum2_sat (prog := prog) (a := .work)
    (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₁ hw₁
  have hH₂ : HeapAt (h ++ g₁) c₂ := hH₁.frame (hj₂ .heap (by decide) (by decide))
    (hj₂ .scan (by decide) (by decide)) (hj₂ .cnt (by decide) (by decide))
  have hE₂ : EnvAt B (⟨s, v₁, d⟩ :: Γ) (d + 1) (h ++ g₁) c₂ :=
    hE.push (by rw [he₂, hj₁ .env (by decide) (by decide) (by decide)]) hR₁ hl₁
  obtain ⟨c₃, n₃, g₃, l₃, e₃, hH₃, hB₃, hr₃, hR₃, hl₃, hw₃, hj₃, hc₃, hn₃⟩ :=
    ih (hk v₁ d) h₂ hH₂ hB₁ hr₂ hE₂ (by omega) (by omega) (by omega)
  have he₃ : c₃.stk .env = bits l₁ ++ .nd :: c.stk .env := by
    rw [hj₃ .env (by decide) (by decide) (by decide), he₂,
      hj₁ .env (by decide) (by decide) (by decide)]
  obtain ⟨c₄, n₄, e₄, hn₄, hr₄, he₄, hj₄⟩ := dropNum_sat (prog := prog) hr₃ he₃
  have hN₁ := length_encHeap_mono (h ++ g₁) g₃
  have hlN : l₁.length ≤ B + (encHeap (h ++ g₁ ++ g₃)).length :=
    hl₁.trans (by have := length_le_encHeap_append (h ++ g₁) g₃; omega)
  have ho := lin_le_ctrlB D (B + (encHeap (h ++ g₁ ++ g₃)).length)
  have hq := hQc (encHeap (h ++ g₁ ++ g₃)).length
  refine ⟨c₄, n₁ + (n₂ + (n₃ + n₄ + 1) + 1) + 1, g₁ ++ g₃, l₃, .seq e₁ (.seq e₂ (.seq e₃ e₄)),
    ?_, ?_, hr₄, ?_, ?_, ?_, fun j hjh hjc hjw => ?_, ?_, ?_⟩ <;>
    try simp only [← List.append_assoc]
  · exact hH₃.frame (hj₄ .heap (by decide)) (hj₄ .scan (by decide)) (hj₄ .cnt (by decide))
  · exact hB₃
  · exact hR₃
  · exact hl₃
  · rw [hj₄ .work (by decide), hw₃, hw₂]
  · by_cases hje : j = .env
    · subst hje; rw [he₄]
    · rw [hj₄ j hje, hj₃ j hjh hjc hjw, hj₂ j hjw hje, hj₁ j hjh hjc hjw]
  · rw [List.length_append, Nat.mul_add]; omega
  · have := bnd_bind (bnd_mono hQ hn₁ hN₁) hn₃ (o := n₂ + n₄ + 3) (by omega)
    omega

theorem sim_prim (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) (hKB : K ≤ B) (hpc : PrimSpec prog pc B F K Q)
    {fuel : ℕ} {args : List Ty} {t : Ty} {Γ : WfCtx Ty.denote Lv} (p : Prim args t)
    {xs₁ : Args Ty.denote args} {xs₂ : Args Lv args} (hxs : Args.Wf Γ xs₁ xs₂) {v : t.denote}
    {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.prim p xs₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c)
    (hK : psize d (Prog.prim (S := Signature.empty) (rec := (a, b)) p xs₂) ≤ K) (hD : d ≤ D)
    (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (Prog.prim (S := Signature.empty) (rec := (a, b)) p xs₂)) c h t v
      B F K Q (psize d (Prog.prim (S := Signature.empty) (rec := (a, b)) p xs₂))
      (Trace.localCost tr) := by
  simp only [eval, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hs : psize d (Prog.prim (S := Signature.empty) (rec := (a, b)) p xs₂) = pw p + 1 := rfl
  have hC : Trace.localCost [Event.local (S := Signature.empty) .prim (p.cost xs₁)] =
      p.cost xs₁ := by simp
  rw [hs] at hK ⊢
  rw [hC] at hF ⊢
  obtain ⟨ls, hR, hb, c₁, n₁, e₁, hn₁, hr₁, hw₁, hj₁⟩ := fetchArgs_sat (prog := prog) hxs hE hv
  have hH₁ : HeapAt h c₁ := hH.frame (hj₁ .heap (by decide)) (hj₁ .scan (by decide))
    (hj₁ .cnt (by decide))
  obtain ⟨c₂, n₂, g, l, e₂, hH₂, hB₂, hr₂, hR₂, hl₂, hw₂, hj₂, hc₂, hn₂⟩ :=
    hpc p xs₁ h c₁ ls (c.stk .work) (by omega) hKB hF hH₁ hB hr₁ hR hb hw₁
  obtain ⟨-, hct⟩ := ctrl_le hQc hD h g
  have h2 := length_args_le p
  have hpw := two_le_pw p
  have ha : args.length * (fetchB d (B + h.length) + 1) ≤ 2 * (fetchB d (B + h.length) + 1) :=
    Nat.mul_le_mul_right _ h2
  have hK1 : p.cost xs₁ ≤ K * p.cost xs₁ := Nat.le_mul_of_pos_left _ (by omega)
  have hmul : (pw p + 1 + K * p.cost xs₁) * Q (encHeap (h ++ g)).length =
      (pw p + 1) * Q (encHeap (h ++ g)).length + K * p.cost xs₁ * Q (encHeap (h ++ g)).length := by
    ring
  have hle : p.cost xs₁ * Q (encHeap (h ++ g)).length ≤
      K * p.cost xs₁ * Q (encHeap (h ++ g)).length := Nat.mul_le_mul_right _ hK1
  have hq2 : Q (encHeap (h ++ g)).length ≤ (pw p + 1) * Q (encHeap (h ++ g)).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨c₂, n₁ + n₂ + 1, g, l, .seq e₁ e₂, hH₂, hB₂, hr₂, hR₂, hl₂, hw₂,
    fun j hjh hjc hjw => by rw [hj₂ j hjh hjc hjw, hj₁ j hjw], hc₂, ?_⟩
  omega

theorem sim_ite (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {t : Ty} {Γ : WfCtx Ty.denote Lv}
    {x₁ : Bool} {x₂ : ℕ} (hx : ⟨.bool, x₁, x₂⟩ ∈ Γ)
    {p₁ q₁ : Prog Signature.empty (a, b) Ty.denote t} {p₂ q₂ : Prog Signature.empty (a, b) Lv t}
    (hp : Prog.Wf true Γ p₁ p₂) (hq : Prog.Wf true Γ q₁ q₂) {v : t.denote}
    {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.ite x₁ p₁ q₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c) (hK : psize d (.ite x₂ p₂ q₂) ≤ K)
    (hD : d + 3 * psize d (.ite x₂ p₂ q₂) ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (.ite x₂ p₂ q₂)) c h t v B F K Q (psize d (.ite x₂ p₂ q₂))
      (Trace.localCost tr) := by
  obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 he
  have hC : Trace.localCost (Event.local (S := Signature.empty) .branch 1 :: t') =
      1 + Trace.localCost t' := by simp
  rw [hC] at hF ⊢
  have hs : psize d (Prog.ite x₂ p₂ q₂) = psize d p₂ + psize d q₂ + 1 := rfl
  rw [hs] at hK hD ⊢
  have hw : Prog.Wf true Γ (cond x₁ p₁ q₁) (cond x₁ p₂ q₂) := by cases x₁ <;> assumption
  have hsz : psize d (cond x₁ p₂ q₂) ≤ psize d p₂ + psize d q₂ := by cases x₁ <;> simp
  have hcomp : cond x₁ (Code.seq (.act (.set 1 none)) (comp pc pb d p₂))
      (.seq (.act (.set 1 none)) (comp pc pb d q₂)) =
      .seq (.act (.set 1 none)) (comp pc pb d (cond x₁ p₂ q₂)) := by cases x₁ <;> rfl
  obtain ⟨l, hr, hcell⟩ := fetchVarCell (prog := prog) hH hE hv hx
  obtain ⟨c₁, n₁, c₂, n₂, e₁, e₂, hn₁₂, hr₂, hw₂, hj₂⟩ := hcell _ _ hr.bool_inv
  obtain ⟨c₃, n₃, e₃, hn₃, hr₃, hw₃, hj₃⟩ := closeCell_sat (prog := prog) hr₂ hw₂
  set c₄ := Act.run (.set 1 none) c₃ with hc₄
  have hr₄ : c₄.regs = Regs.empty := by rw [hc₄, empty_eq_rv]; simp [Act.run, hr₃]
  have hj₄ : ∀ j, c₄.stk j = c.stk j := fun j => by
    by_cases hjw : j = .work
    · subst hjw; simp [hc₄, Act.run, hw₃]
    · simp [hc₄, Act.run, hj₃ j hjw, hj₂ j hjw]
  have hH₄ : HeapAt h c₄ := hH.frame (hj₄ .heap) (hj₄ .scan) (hj₄ .cnt)
  have hE₄ : EnvAt B Γ d h c₄ := by simpa using hE.mono [] (hj₄ .env)
  obtain ⟨c₅, n₅, g, l₅, e₅, hH₅, hB₅, hr₅, hR₅, hl₅, hw₅, hj₅, hc₅, hn₅⟩ :=
    ih hw h₁ hH₄ hB hr₄ hE₄ (by omega) (by omega) (by omega)
  have hb : (Cond.is (1 : Fin Rg) (some (.tag .tt))).eval c₃.regs = x₁ := by
    rw [hr₃]; cases x₁ <;> rfl
  have e₆ : Exec prog (.ite (.is 1 (some (.tag .tt))) (.seq (.act (.set 1 none)) (comp pc pb d p₂))
      (.seq (.act (.set 1 none)) (comp pc pb d q₂))) c₃ c₅ (1 + n₅ + 1 + 1) :=
    exec_ite_cond hb (by rw [hcomp]; exact .seq (.act _ c₃) e₅)
  obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) h g
  refine ⟨c₅, n₁ + (n₂ + (n₃ + (1 + n₅ + 1 + 1) + 1) + 1) + 1, g, l₅,
    .seq e₁ (.seq e₂ (.seq e₃ e₆)), hH₅, hB₅, hr₅, hR₅, hl₅, by rw [hw₅, hj₄ .work],
    fun j hjh hjc hjw => by rw [hj₅ j hjh hjc hjw, hj₄ j],
    hc₅.trans (Nat.mul_le_mul_left _ (by omega)), ?_⟩
  have := bnd_branch hn₅ hsz (o := n₁ + n₂ + n₃ + 7) (by omega)
  omega

theorem sim_opt (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s t : Ty} {Γ : WfCtx Ty.denote Lv}
    {o₁ : Option s.denote} {o₂ : ℕ} (ho : ⟨.option s, o₁, o₂⟩ ∈ Γ)
    {p₁ : Prog Signature.empty (a, b) Ty.denote t} {p₂ : Prog Signature.empty (a, b) Lv t}
    {q₁ : s.denote → Prog Signature.empty (a, b) Ty.denote t}
    {q₂ : ℕ → Prog Signature.empty (a, b) Lv t} (hp : Prog.Wf true Γ p₁ p₂)
    (hq : ∀ v₁ v₂, Prog.Wf true (⟨s, v₁, v₂⟩ :: Γ) (q₁ v₁) (q₂ v₂)) {v : t.denote}
    {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.caseOption o₁ p₁ q₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c)
    (hK : psize d (Prog.caseOption (a := s) o₂ p₂ q₂) ≤ K)
    (hD : d + 3 * psize d (Prog.caseOption (a := s) o₂ p₂ q₂) ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (Prog.caseOption (a := s) o₂ p₂ q₂)) c h t v B F K Q
      (psize d (Prog.caseOption (a := s) o₂ p₂ q₂)) (Trace.localCost tr) := by
  obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 he
  have hC : Trace.localCost (Event.local (S := Signature.empty) .branch 1 :: t') =
      1 + Trace.localCost t' := by simp
  rw [hC] at hF ⊢
  have hs : psize d (Prog.caseOption (a := s) o₂ p₂ q₂) =
      psize d p₂ + psize (d + 1) (q₂ d) + 1 := rfl
  rw [hs] at hK hD ⊢
  obtain ⟨l, hr, hcell⟩ := fetchVarCell (prog := prog) hH hE hv ho
  cases o₁ with
  | none =>
    obtain ⟨c₁, n₁, c₂, n₂, e₁, e₂, hn₁₂, hr₂, hw₂, hj₂⟩ := hcell _ _ hr.none_inv
    set c₃ := Act.run (.set 1 none) c₂ with hc₃
    have hr₃ : c₃.regs = rv none none none none := by simp [hc₃, Act.run, hr₂]
    obtain ⟨c₄, n₄, e₄, hn₄, hr₄, hw₄, hj₄⟩ := closeCell_sat (prog := prog) (c := c₃) hr₃
      (by simpa [hc₃, Act.run, encFields] using hw₂)
    have hj₄' : ∀ j, c₄.stk j = c.stk j := fun j => by
      by_cases hjw : j = .work
      · subst hjw; rw [hw₄]
      · rw [hj₄ j hjw]; simp [hc₃, Act.run, hj₂ j hjw]
    rw [← empty_eq_rv] at hr₄
    obtain ⟨c₅, n₅, g, l₅, e₅, hH₅, hB₅, hr₅, hR₅, hl₅, hw₅, hj₅, hc₅, hn₅⟩ :=
      ih hp h₁ (hH.frame (hj₄' .heap) (hj₄' .scan) (hj₄' .cnt)) hB hr₄
        (by simpa using hE.mono [] (hj₄' .env)) (by omega) (by omega) (by omega)
    have hb : (Cond.is (1 : Fin Rg) (some (.tag .none))).eval c₂.regs = true := by
      rw [hr₂]; rfl
    obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) h g
    refine ⟨c₅, n₁ + (n₂ + (1 + (n₄ + n₅ + 1) + 1 + 1) + 1) + 1, g, l₅,
      .seq e₁ (.seq e₂ (.ite_true hb (.seq (.act _ c₂) (.seq e₄ e₅)))), hH₅, hB₅, hr₅, hR₅,
      hl₅, by rw [hw₅, hj₄' .work], fun j hjh hjc hjw => by rw [hj₅ j hjh hjc hjw, hj₄' j],
      hc₅.trans (Nat.mul_le_mul_left _ (by omega)), ?_⟩
    have := bnd_branch hn₅ (Nat.le_add_right (psize d p₂) (psize (d + 1) (q₂ d)))
      (o := n₁ + n₂ + n₄ + 6) (by omega)
    omega
  | some x =>
    obtain ⟨lf, hcl, hrf⟩ := hr.some_inv
    have hlf : lf.length ≤ B + h.length :=
      (hB.field_lt hcl lf (List.mem_singleton_self lf)).le
    obtain ⟨c₁, n₁, c₂, n₂, e₁, e₂, hn₁₂, hr₂, hw₂, hj₂⟩ := hcell _ _ hcl
    set c₃ := Act.run (.set 1 none) c₂ with hc₃
    have hr₃ : c₃.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₃, Act.run, hr₂]
    have hw₃ : c₃.stk .work = bits lf ++ .nd :: (.mk 0 :: c.stk .work) := by
      simp [hc₃, Act.run, hw₂, encFields]
    obtain ⟨c₄, n₄, e₄, hn₄, hr₄, hw₄, he₄, hj₄⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₃ hw₃
    rw [empty_eq_rv] at hr₄
    obtain ⟨c₅, n₅, e₅, hn₅, hr₅, hw₅, hj₅⟩ := closeCell_sat (prog := prog) hr₄ hw₄
    rw [← empty_eq_rv] at hr₅
    have hj₅' : ∀ j, j ≠ .env → c₅.stk j = c.stk j := fun j hje => by
      by_cases hjw : j = .work
      · subst hjw; rw [hw₅]
      · rw [hj₅ j hjw, hj₄ j hjw hje]; simp [hc₃, Act.run, hj₂ j hjw]
    have he₅ : c₅.stk .env = bits lf ++ .nd :: c.stk .env := by
      rw [hj₅ .env (by decide), he₄]; simp [hc₃, Act.run, hj₂ .env (by decide)]
    have hE₅ : EnvAt B (⟨s, x, d⟩ :: Γ) (d + 1) h c₅ := by
      simpa using hE.push (h' := []) he₅ (by simpa using hrf) (by simpa using hlf)
    obtain ⟨c₆, n₆, g, l₆, e₆, hH₆, hB₆, hr₆, hR₆, hl₆, hw₆, hj₆, hc₆, hn₆⟩ :=
      ih (hq x d) h₁ (hH.frame (hj₅' .heap (by decide)) (hj₅' .scan (by decide))
        (hj₅' .cnt (by decide))) hB hr₅ hE₅ (by omega) (by omega) (by omega)
    have he₆ : c₆.stk .env = bits lf ++ .nd :: c.stk .env := by
      rw [hj₆ .env (by decide) (by decide) (by decide), he₅]
    obtain ⟨c₇, n₇, e₇, hn₇, hr₇, he₇, hj₇⟩ := dropNum_sat (prog := prog) hr₆ he₆
    have hb : (Cond.is (1 : Fin Rg) (some (.tag .none))).eval c₂.regs = false := by
      rw [hr₂]; decide
    obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) h g
    refine ⟨c₇, n₁ + (n₂ + (1 + (n₄ + (n₅ + (n₆ + n₇ + 1) + 1) + 1) + 1 + 1) + 1) + 1, g, l₆,
      .seq e₁ (.seq e₂ (.ite_false hb (.seq (.act _ c₂) (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))),
      hH₆.frame (hj₇ .heap (by decide)) (hj₇ .scan (by decide)) (hj₇ .cnt (by decide)),
      hB₆, hr₇, hR₆, hl₆, ?_, fun j hjh hjc hjw => ?_,
      hc₆.trans (Nat.mul_le_mul_left _ (by omega)), ?_⟩
    · rw [hj₇ .work (by decide), hw₆, hj₅' .work (by decide)]
    · by_cases hje : j = .env
      · subst hje; rw [he₇]
      · rw [hj₇ j hje, hj₆ j hjh hjc hjw, hj₅' j hje]
    · have := bnd_branch hn₆ (Nat.le_add_left (psize (d + 1) (q₂ d)) (psize d p₂))
        (o := n₁ + n₂ + n₄ + n₅ + n₇ + 8) (by omega)
      omega

theorem sim_list (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s t : Ty} {Γ : WfCtx Ty.denote Lv}
    {o₁ : List s.denote} {o₂ : ℕ} (ho : ⟨.list s, o₁, o₂⟩ ∈ Γ)
    {p₁ : Prog Signature.empty (a, b) Ty.denote t} {p₂ : Prog Signature.empty (a, b) Lv t}
    {q₁ : s.denote → List s.denote → Prog Signature.empty (a, b) Ty.denote t}
    {q₂ : ℕ → ℕ → Prog Signature.empty (a, b) Lv t} (hp : Prog.Wf true Γ p₁ p₂)
    (hq : ∀ x₁ x₂ xs₁ xs₂,
      Prog.Wf true (⟨s, x₁, x₂⟩ :: ⟨.list s, xs₁, xs₂⟩ :: Γ) (q₁ x₁ xs₁) (q₂ x₂ xs₂))
    {v : t.denote} {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.caseList o₁ p₁ q₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c)
    (hK : psize d (Prog.caseList (a := s) o₂ p₂ q₂) ≤ K)
    (hD : d + 3 * psize d (Prog.caseList (a := s) o₂ p₂ q₂) ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (Prog.caseList (a := s) o₂ p₂ q₂)) c h t v B F K Q
      (psize d (Prog.caseList (a := s) o₂ p₂ q₂)) (Trace.localCost tr) := by
  obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 he
  have hC : Trace.localCost (Event.local (S := Signature.empty) .branch 1 :: t') =
      1 + Trace.localCost t' := by simp
  rw [hC] at hF ⊢
  have hs : psize d (Prog.caseList (a := s) o₂ p₂ q₂) =
      psize d p₂ + psize (d + 2) (q₂ d (d + 1)) + 1 := rfl
  rw [hs] at hK hD ⊢
  obtain ⟨l, hr, hcell⟩ := fetchVarCell (prog := prog) hH hE hv ho
  cases o₁ with
  | nil =>
    obtain ⟨c₁, n₁, c₂, n₂, e₁, e₂, hn₁₂, hr₂, hw₂, hj₂⟩ := hcell _ _ hr.nil_inv
    set c₃ := Act.run (.set 1 none) c₂ with hc₃
    have hr₃ : c₃.regs = rv none none none none := by simp [hc₃, Act.run, hr₂]
    obtain ⟨c₄, n₄, e₄, hn₄, hr₄, hw₄, hj₄⟩ := closeCell_sat (prog := prog) (c := c₃) hr₃
      (by simpa [hc₃, Act.run, encFields] using hw₂)
    have hj₄' : ∀ j, c₄.stk j = c.stk j := fun j => by
      by_cases hjw : j = .work
      · subst hjw; rw [hw₄]
      · rw [hj₄ j hjw]; simp [hc₃, Act.run, hj₂ j hjw]
    rw [← empty_eq_rv] at hr₄
    obtain ⟨c₅, n₅, g, l₅, e₅, hH₅, hB₅, hr₅, hR₅, hl₅, hw₅, hj₅, hc₅, hn₅⟩ :=
      ih hp h₁ (hH.frame (hj₄' .heap) (hj₄' .scan) (hj₄' .cnt)) hB hr₄
        (by simpa using hE.mono [] (hj₄' .env)) (by omega) (by omega) (by omega)
    have hb : (Cond.is (1 : Fin Rg) (some (.tag .nil))).eval c₂.regs = true := by
      rw [hr₂]; rfl
    obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) h g
    refine ⟨c₅, n₁ + (n₂ + (1 + (n₄ + n₅ + 1) + 1 + 1) + 1) + 1, g, l₅,
      .seq e₁ (.seq e₂ (.ite_true hb (.seq (.act _ c₂) (.seq e₄ e₅)))), hH₅, hB₅, hr₅, hR₅,
      hl₅, by rw [hw₅, hj₄' .work], fun j hjh hjc hjw => by rw [hj₅ j hjh hjc hjw, hj₄' j],
      hc₅.trans (Nat.mul_le_mul_left _ (by omega)), ?_⟩
    have := bnd_branch hn₅ (Nat.le_add_right (psize d p₂) (psize (d + 2) (q₂ d (d + 1))))
      (o := n₁ + n₂ + n₄ + 6) (by omega)
    omega
  | cons x xs =>
    obtain ⟨lf₁, lf₂, hcl, hrf₁, hrf₂⟩ := hr.cons_inv
    have hlf₁ : lf₁.length ≤ B + h.length := (hB.field_lt hcl lf₁ (by simp)).le
    have hlf₂ : lf₂.length ≤ B + h.length := (hB.field_lt hcl lf₂ (by simp)).le
    obtain ⟨c₁, n₁, c₂, n₂, e₁, e₂, hn₁₂, hr₂, hw₂, hj₂⟩ := hcell _ _ hcl
    set c₃ := Act.run (.set 1 none) c₂ with hc₃
    have hr₃ : c₃.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₃, Act.run, hr₂]
    have hw₃ : c₃.stk .work = bits lf₁ ++ .nd :: (bits lf₂ ++ .nd :: .mk 0 :: c.stk .work) := by
      simp [hc₃, Act.run, hw₂, encFields]
    obtain ⟨c₄, n₄, e₄, hn₄, hr₄, hw₄, he₄, hj₄⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₃ hw₃
    obtain ⟨c₅, n₅, e₅, hn₅, hr₅, hw₅, he₅, hj₅⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₄ hw₄
    rw [empty_eq_rv] at hr₅
    obtain ⟨c₆, n₆, e₆, hn₆, hr₆, hw₆, hj₆⟩ := closeCell_sat (prog := prog) hr₅ hw₅
    rw [← empty_eq_rv] at hr₆
    have hj₆' : ∀ j, j ≠ .env → c₆.stk j = c.stk j := fun j hje => by
      by_cases hjw : j = .work
      · subst hjw; rw [hw₆]
      · rw [hj₆ j hjw, hj₅ j hjw hje, hj₄ j hjw hje]; simp [hc₃, Act.run, hj₂ j hjw]
    have he₄' : c₄.stk .env = bits lf₁ ++ .nd :: c.stk .env := by
      rw [he₄]; simp [hc₃, Act.run, hj₂ .env (by decide)]
    have hE₄ : EnvAt B (⟨s, x, d⟩ :: Γ) (d + 1) h c₄ := by
      simpa using hE.push (h' := []) he₄' (by simpa using hrf₁) (by simpa using hlf₁)
    have hE₅ : EnvAt B (⟨.list s, xs, d + 1⟩ :: ⟨s, x, d⟩ :: Γ) (d + 1 + 1) h c₅ := by
      simpa using hE₄.push (h' := []) he₅ (by simpa using hrf₂) (by simpa using hlf₂)
    have hE₅' : EnvAt B (⟨.list s, xs, d + 1⟩ :: ⟨s, x, d⟩ :: Γ) (d + 2) h c₆ := by
      simpa using hE₅.mono [] (hj₆ .env (by decide))
    have hE₆ : EnvAt B (⟨s, x, d⟩ :: ⟨.list s, xs, d + 1⟩ :: Γ) (d + 2) h c₆ :=
      hE₅'.sub fun e he => by simp only [List.mem_cons] at he ⊢; tauto
    obtain ⟨c₇, n₇, g, l₇, e₇, hH₇, hB₇, hr₇, hR₇, hl₇, hw₇, hj₇, hc₇, hn₇⟩ :=
      ih (hq x d xs (d + 1)) h₁ (hH.frame (hj₆' .heap (by decide)) (hj₆' .scan (by decide))
        (hj₆' .cnt (by decide))) hB hr₆ hE₆ (by omega) (by omega) (by omega)
    have he₇ : c₇.stk .env = bits lf₂ ++ .nd :: (bits lf₁ ++ .nd :: c.stk .env) := by
      rw [hj₇ .env (by decide) (by decide) (by decide), hj₆ .env (by decide), he₅, he₄']
    obtain ⟨c₈, n₈, e₈, hn₈, hr₈, he₈, hj₈⟩ := dropNum_sat (prog := prog) hr₇ he₇
    obtain ⟨c₉, n₉, e₉, hn₉, hr₉, he₉, hj₉⟩ := dropNum_sat (prog := prog) hr₈ he₈
    have hb : (Cond.is (1 : Fin Rg) (some (.tag .nil))).eval c₂.regs = false := by
      rw [hr₂]; decide
    obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) h g
    have hj₉' : ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c₉.stk j = c.stk j := by
      intro j hjh hjc hjw
      by_cases hje : j = .env
      · subst hje; rw [he₉]
      · rw [hj₉ j hje, hj₈ j hje, hj₇ j hjh hjc hjw, hj₆' j hje]
    refine ⟨c₉, n₁ + (n₂ + (1 + (n₄ + (n₅ + (n₆ + (n₇ + (n₈ + n₉ + 1) + 1) + 1) + 1) + 1) +
      1 + 1) + 1) + 1, g, l₇, .seq e₁ (.seq e₂ (.ite_false hb (.seq (.act _ c₂)
        (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉)))))))),
      hH₇.frame ((hj₉ .heap (by decide)).trans (hj₈ .heap (by decide)))
        ((hj₉ .scan (by decide)).trans (hj₈ .scan (by decide)))
        ((hj₉ .cnt (by decide)).trans (hj₈ .cnt (by decide))),
      hB₇, hr₉, hR₇, hl₇, ?_, hj₉', hc₇.trans (Nat.mul_le_mul_left _ (by omega)), ?_⟩
    · rw [hj₉ .work (by decide), hj₈ .work (by decide), hw₇, hj₆' .work (by decide)]
    · have := bnd_branch hn₇ (Nat.le_add_left (psize (d + 2) (q₂ d (d + 1))) (psize d p₂))
        (o := n₁ + n₂ + n₄ + n₅ + n₆ + n₈ + n₉ + 10) (by omega)
      omega

theorem sim_recur (hQc : ∀ N, ctrlB D (B + N) ≤ Q N)
    (hprog : prog.body pb = comp pc pb 1 (Pr.proc Lv 0)) (hKb : psize 1 (Pr.proc Lv 0) + 1 ≤ K)
    (hDb : 1 + 3 * psize 1 (Pr.proc Lv 0) ≤ D) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {Γ : WfCtx Ty.denote Lv} {x₁ : a.denote}
    {x₂ : ℕ} (hx : ⟨a, x₁, x₂⟩ ∈ Γ) {v : b.denote} {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.recur x₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c) (hD : d ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (Prog.recur (S := Signature.empty) (rec := (a, b)) (var := Lv) x₂))
      c h b v B F K Q 1 (Trace.localCost tr) := by
  obtain ⟨t', h₁, rfl⟩ := consT_eq_some.1 he
  have hC : Trace.localCost (Event.local (S := Signature.empty) .recCall 1 :: t') =
      1 + Trace.localCost t' := by simp
  rw [hC] at hF ⊢
  obtain ⟨l, hr, hl, c₁, n₁, e₁, hn₁, hr₁, hw₁, hj₁⟩ :=
    fetchVar_sat (prog := prog) hE hv hx (dst := .work) (by decide) (by decide) (by decide)
  obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hw₂, he₂, hj₂⟩ := moveNum2_sat (prog := prog) (a := .work)
    (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₁ hw₁
  have hj₂' : ∀ j, j ≠ .env → c₂.stk j = c.stk j := fun j hje => by
    by_cases hjw : j = .work
    · subst hjw; rw [hw₂]
    · rw [hj₂ j hjw hje, hj₁ j hjw]
  have he₂' : c₂.stk .env = bits l ++ .nd :: c.stk .env := by
    rw [he₂, hj₁ .env (by decide)]
  have hE₂ : EnvAt B [⟨a, x₁, 0⟩] 1 h c₂ := by
    refine ⟨[l], c.stk .env, rfl, by rw [he₂']; simp [envEnc], by simpa using hl,
      fun e he => ?_⟩
    rw [List.mem_singleton.1 he]
    exact ⟨by simp, by simpa using hr⟩
  obtain ⟨c₃, n₃, g, l₃, e₃, hH₃, hB₃, hr₃, hR₃, hl₃, hw₃, hj₃, hc₃, hn₃⟩ :=
    ih (Pr.wf Ty.denote Lv x₁ 0) h₁ (hH.frame (hj₂' .heap (by decide))
      (hj₂' .scan (by decide)) (hj₂' .cnt (by decide))) hB hr₂ hE₂ (by omega) (by omega)
      (by omega)
  have e₃' : Exec prog (.call pb) c₂ c₃ (n₃ + 2) := .call (by rw [hprog]; exact e₃)
  have he₃ : c₃.stk .env = bits l ++ .nd :: c.stk .env := by
    rw [hj₃ .env (by decide) (by decide) (by decide), he₂']
  obtain ⟨c₄, n₄, e₄, hn₄, hr₄, he₄, hj₄⟩ := dropNum_sat (prog := prog) hr₃ he₃
  obtain ⟨hM, hct'⟩ := ctrl_le hQc hD h g
  refine ⟨c₄, n₁ + (n₂ + (n₃ + 2 + n₄ + 1) + 1) + 1, g, l₃, .seq e₁ (.seq e₂ (.seq e₃' e₄)),
    hH₃.frame (hj₄ .heap (by decide)) (hj₄ .scan (by decide)) (hj₄ .cnt (by decide)), hB₃, hr₄,
    hR₃, hl₃, by rw [hj₄ .work (by decide), hw₃, hj₂' .work (by decide)],
    fun j hjh hjc hjw => ?_, hc₃.trans (Nat.mul_le_mul_left _ (by omega)), ?_⟩
  · by_cases hje : j = .env
    · subst hje; rw [he₄]
    · rw [hj₄ j hje, hj₃ j hjh hjc hjw, hj₂' j hje]
  · have := bnd_recur hn₃ (by omega : psize 1 (Pr.proc Lv 0) ≤ K) (o := n₁ + n₂ + n₄ + 5)
      (by omega)
    omega

/-- **The loop of a compiled fold**, by induction on the remaining list: at the head of the
loop, the remaining list's pointer is on top of `env` and the accumulator's on top of `work`. -/
theorem foldLoop_sat (hQ : Monotone Q) (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s u : Ty} {Γ : WfCtx Ty.denote Lv}
    {f₁ : u.denote → s.denote → Prog Signature.empty (a, b) Ty.denote u}
    {f₂ : ℕ → ℕ → Prog Signature.empty (a, b) Lv u}
    (hf : ∀ acc₁ acc₂ x₁ x₂,
      Prog.Wf true (⟨u, acc₁, acc₂⟩ :: ⟨s, x₁, x₂⟩ :: Γ) (f₁ acc₁ x₁) (f₂ acc₂ x₂)) {d : ℕ}
    (hK : psize (d + 3) (f₂ (d + 1) (d + 2)) + 2 ≤ K)
    (hD : d + 3 + 3 * psize (d + 3) (f₂ (d + 1) (d + 2)) ≤ D) (c₀ : Cfg Stk Sym Rg) :
    ∀ (ys : List s.denote) (acc r : u.denote) (tr : Trace Signature.empty),
      foldRun (fun acc x => eval O (Pr.proc Ty.denote) fuel (f₁ acc x)) ys acc = some (r, tr) →
      Trace.localCost tr ≤ F →
      ∀ (h : List Cell) (c : Cfg Stk Sym Rg) (lH la : List Bool), HeapAt h c → HeapBnd B F h →
      c.regs = rv (some goMark) none none none → EnvAt B Γ d h c₀ →
      c.stk .env = bits lH ++ .nd :: c₀.stk .env → lH.length ≤ B + h.length →
      Rep h (.list s) ys (ofBits lH) → c.stk .work = bits la ++ .nd :: c₀.stk .work →
      la.length ≤ B + h.length → Rep h u acc (ofBits la) →
      (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → j ≠ .env → c.stk j = c₀.stk j) →
      ∃ c' n g l lH', Exec prog (.loop (.is 0 (some goMark))
          (foldStep (comp pc pb (d + 3) (f₂ (d + 1) (d + 2))))) c c' n ∧
        HeapAt (h ++ g) c' ∧ HeapBnd B F (h ++ g) ∧ c'.regs = Regs.empty ∧
        Rep (h ++ g) u r (ofBits l) ∧ l.length ≤ B + (h ++ g).length ∧
        c'.stk .work = bits l ++ .nd :: c₀.stk .work ∧
        c'.stk .env = bits lH' ++ .nd :: c₀.stk .env ∧ lH'.length ≤ B + (h ++ g).length ∧
        (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → j ≠ .env → c'.stk j = c₀.stk j) ∧
        g.length ≤ K * Trace.localCost tr ∧
        n ≤ (1 + K * Trace.localCost tr) * Q (encHeap (h ++ g)).length := by
  intro ys
  induction ys with
  | nil =>
    intro acc r tr hrun hF h c lH la hH hB hv hE₀ he hlH hR hw hla hRa hj
    simp only [foldRun, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    obtain ⟨c₂, n₂, c₃, n₃, e₂, e₃, hn₂₃, hr₃, hw₃, hj₃⟩ :=
      foldHead (prog := prog) hH hv he hlH hR.nil_inv
    set c₄ := Act.run (.set 1 none) c₃ with hc₄
    have hr₄ : c₄.regs = rv none none none none := by simp [hc₄, Act.run, hr₃]
    obtain ⟨c₅, n₅, e₅, hn₅, hr₅, hw₅, hj₅⟩ := closeCell_sat (prog := prog) (c := c₄) hr₄
      (by simpa [hc₄, Act.run, encFields] using hw₃)
    have hj₅' : ∀ j, c₅.stk j = c.stk j := fun j => by
      by_cases hjw : j = .work
      · subst hjw; rw [hw₅]
      · rw [hj₅ j hjw]; simp [hc₄, Act.run, hj₃ j hjw]
    have hb : (Cond.is (0 : Fin Rg) (some goMark)).eval c.regs = true := by rw [hv]; rfl
    have hb' : (Cond.is (0 : Fin Rg) (some goMark)).eval c₅.regs = false := by rw [hr₅]; decide
    have hb₃ : (Cond.is (1 : Fin Rg) (some (.tag .cons))).eval c₃.regs = false := by
      rw [hr₃]; decide
    have e : Exec prog (foldStep (comp pc pb (d + 3) (f₂ (d + 1) (d + 2)))) c c₅ _ :=
      .seq (.act _ c) (.seq e₂ (.seq e₃ (.ite_false hb₃ (.seq (.act _ c₃) e₅))))
    obtain ⟨hM, hct⟩ := ctrl_le hQc (j := d) (by omega) h []
    refine ⟨c₅, _, [], la, lH, .loop_true hb e (.loop_false hb'), ?_, by simpa using hB,
      by rw [hr₅, empty_eq_rv], by simpa using hRa, by simpa using hla,
      by rw [hw₅, hw], by rw [hj₅' .env, he], by simpa using hlH,
      fun j hjh hjc hjw hje => by rw [hj₅' j, hj j hjh hjc hjw hje], by simp, ?_⟩
    · simpa using hH.frame (hj₅' .heap) (hj₅' .scan) (hj₅' .cnt)
    · simp only [Trace.localCost_nil, Nat.mul_zero, Nat.add_zero, Nat.one_mul]
      omega
  | cons y ys ihy =>
    intro acc r tr hrun hF h c lH la hH hB hv hE₀ he hlH hR hw hla hRa hj
    obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 hrun
    obtain ⟨acc', t₁, t₂, hstep, hrest, rfl⟩ := seqT_eq_some.1 h₁
    have hC : Trace.localCost (Event.local (S := Signature.empty) .iter 1 :: (t₁ ++ t₂)) =
        1 + (Trace.localCost t₁ + Trace.localCost t₂) := by simp
    rw [hC] at hF ⊢
    obtain ⟨l₁, l₂, hcl, hr₁, hr₂⟩ := hR.cons_inv
    have hl₁ : l₁.length ≤ B + h.length := (hB.field_lt hcl l₁ (by simp)).le
    have hl₂ : l₂.length ≤ B + h.length := (hB.field_lt hcl l₂ (by simp)).le
    obtain ⟨c₂, n₂, c₃, n₃, e₂, e₃, hn₂₃, hr₃, hw₃, hj₃⟩ :=
      foldHead (prog := prog) hH hv he hlH hcl
    set c₄ := Act.run (.set 1 none) c₃ with hc₄
    have hr₄ : c₄.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₄, Act.run, hr₃]
    have hw₄ : c₄.stk .work = bits l₁ ++ .nd :: (bits l₂ ++ .nd :: .mk 0 :: c.stk .work) := by
      simp [hc₄, Act.run, hw₃, encFields]
    have hj₄ : ∀ j, j ≠ .work → c₄.stk j = c.stk j := fun j hj => by
      simp [hc₄, Act.run, hj₃ j hj]
    obtain ⟨c₅, n₅, e₅, hn₅, hr₅, hw₅, ht₅, hj₅⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .t4) (t := .t0) (by decide) (by decide) (by decide) hr₄ hw₄
    have he₅ : c₅.stk .env = bits lH ++ .nd :: c₀.stk .env := by
      rw [hj₅ .env (by decide) (by decide), hj₄ .env (by decide), he]
    obtain ⟨c₆, n₆, e₆, hn₆, hr₆, he₆, hj₆⟩ := dropNum_sat (prog := prog) hr₅ he₅
    have hw₆ : c₆.stk .work = bits l₂ ++ .nd :: (.mk 0 :: c.stk .work) := by
      rw [hj₆ .work (by decide), hw₅]
    obtain ⟨c₇, n₇, e₇, hn₇, hr₇, hw₇, he₇, hj₇⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₆ hw₆
    rw [empty_eq_rv] at hr₇
    obtain ⟨c₈, n₈, e₈, hn₈, hr₈, hw₈, hj₈⟩ := closeCell_sat (prog := prog) hr₇ hw₇
    rw [← empty_eq_rv] at hr₈
    have hw₈' : c₈.stk .work = bits la ++ .nd :: c₀.stk .work := by rw [hw₈, hw]
    obtain ⟨c₉, n₉, e₉, hn₉, hr₉, hw₉, he₉, hj₉⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₈ hw₈'
    have ht₉ : c₉.stk .t4 = bits l₁ ++ .nd :: c₀.stk .t4 := by
      rw [hj₉ .t4 (by decide) (by decide), hj₈ .t4 (by decide), hj₇ .t4 (by decide) (by decide),
        hj₆ .t4 (by decide), ht₅, hj₄ .t4 (by decide),
        hj .t4 (by decide) (by decide) (by decide) (by decide)]
    obtain ⟨c₁₀, n₁₀, e₁₀, hn₁₀, hr₁₀, ht₁₀, he₁₀, hj₁₀⟩ := moveNum2_sat (prog := prog)
      (a := .t4) (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₉ ht₉
    have hj₁₀' : ∀ j, j ≠ .work → j ≠ .env → j ≠ .t4 → c₁₀.stk j = c.stk j :=
      fun j hjw hje hj4 => by
        rw [hj₁₀ j hj4 hje, hj₉ j hjw hje, hj₈ j hjw, hj₇ j hjw hje, hj₆ j hje,
          hj₅ j hjw hj4, hj₄ j hjw]
    have hw₁₀ : c₁₀.stk .work = c₀.stk .work := by rw [hj₁₀ .work (by decide) (by decide), hw₉]
    have hH₁₀ : HeapAt h c₁₀ := hH.frame (hj₁₀' .heap (by decide) (by decide) (by decide))
      (hj₁₀' .scan (by decide) (by decide) (by decide)) (hj₁₀' .cnt (by decide) (by decide)
        (by decide))
    have hE₇ : EnvAt B (⟨.list s, ys, d⟩ :: Γ) (d + 1) h c₇ := by
      simpa using hE₀.push (h' := []) (c' := c₇) (by rw [he₇, he₆]) (by simpa using hr₂)
        (by simpa using hl₂)
    have hE₉ : EnvAt B (⟨u, acc, d + 1⟩ :: ⟨.list s, ys, d⟩ :: Γ) (d + 1 + 1) h c₉ := by
      simpa using hE₇.push (h' := []) (c' := c₉) (by rw [he₉, hj₈ .env (by decide)])
        (by simpa using hRa) (by simpa using hla)
    have hE₁₀ : EnvAt B (⟨s, y, d + 2⟩ :: ⟨u, acc, d + 1⟩ :: ⟨.list s, ys, d⟩ :: Γ) (d + 3) h
        c₁₀ := by
      simpa using hE₉.push (h' := []) (c' := c₁₀) he₁₀ (by simpa using hr₁) (by simpa using hl₁)
    have hEb : EnvAt B (⟨u, acc, d + 1⟩ :: ⟨s, y, d + 2⟩ :: Γ) (d + 3) h c₁₀ :=
      hE₁₀.sub fun e he => by
        rcases List.mem_cons.1 he with rfl | he
        · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
        rcases List.mem_cons.1 he with rfl | he
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inr he)))))
    obtain ⟨c₁₁, n₁₁, g₁, la', e₁₁, hH₁₁, hB₁₁, hr₁₁, hR₁₁, hla', hw₁₁, hj₁₁, hc₁₁, hn₁₁⟩ :=
      ih (hf acc (d + 1) y (d + 2)) hstep hH₁₀ hB hr₁₀ hEb (by omega) (by omega) (by omega)
    have he₁₁ : c₁₁.stk .env = bits l₁ ++ .nd :: (bits la ++ .nd ::
        (bits l₂ ++ .nd :: c₀.stk .env)) := by
      rw [hj₁₁ .env (by decide) (by decide) (by decide), he₁₀, he₉, hj₈ .env (by decide), he₇,
        he₆]
    obtain ⟨c₁₂, n₁₂, e₁₂, hn₁₂, hr₁₂, he₁₂, hj₁₂⟩ := dropNum_sat (prog := prog) hr₁₁ he₁₁
    obtain ⟨c₁₃, n₁₃, e₁₃, hn₁₃, hr₁₃, he₁₃, hj₁₃⟩ := dropNum_sat (prog := prog) hr₁₂ he₁₂
    set c₁₄ := Act.run (.set 0 (some goMark)) c₁₃ with hc₁₄
    have hr₁₄ : c₁₄.regs = rv (some goMark) none none none := by
      rw [empty_eq_rv] at hr₁₃; simp [hc₁₄, Act.run, hr₁₃]
    have hj₁₄ : ∀ j, j ≠ .env → c₁₄.stk j = c₁₁.stk j := fun j hje => by
      simp [hc₁₄, Act.run, hj₁₃ j hje, hj₁₂ j hje]
    have hE₀' : EnvAt B Γ d (h ++ g₁) c₀ := hE₀.mono g₁ rfl
    obtain ⟨c', n', g₂, l, lH', e', hH', hB', hr', hR', hl', hw', he', hlH', hj', hc', hn'⟩ :=
      ihy acc' r t₂ hrest (by omega) (h ++ g₁) c₁₄ l₂ la'
        (hH₁₁.frame (hj₁₄ .heap (by decide)) (hj₁₄ .scan (by decide)) (hj₁₄ .cnt (by decide)))
        hB₁₁ hr₁₄ hE₀' (by simp [hc₁₄, Act.run, he₁₃])
        (by simp only [List.length_append]; omega) hr₂.mono
        (by rw [hj₁₄ .work (by decide), hw₁₁, hw₁₀]) hla' hR₁₁
        (fun j hjh hjc hjw hje => by
          rw [hj₁₄ j hje, hj₁₁ j hjh hjc hjw]
          by_cases hj4 : j = .t4
          · subst hj4; rw [ht₁₀]
          · rw [hj₁₀' j hjw hje hj4, hj j hjh hjc hjw hje])
    have hb : (Cond.is (0 : Fin Rg) (some goMark)).eval c.regs = true := by rw [hv]; rfl
    have hb₃ : (Cond.is (1 : Fin Rg) (some (.tag .cons))).eval c₃.regs = true := by
      rw [hr₃]; rfl
    have e : Exec prog (foldStep (comp pc pb (d + 3) (f₂ (d + 1) (d + 2)))) c c₁₄ _ :=
      .seq (.act _ c) (.seq e₂ (.seq e₃ (.ite_true hb₃ (.seq (.act _ c₃) (.seq e₅ (.seq e₆
        (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀ (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ (.act _ c₁₃))))))))))))))
    have hN₁ : (encHeap (h ++ g₁)).length ≤ (encHeap (h ++ g₁ ++ g₂)).length :=
      length_encHeap_mono _ _
    obtain ⟨hM, hct⟩ := ctrl_le hQc (j := d) (by omega) h (g₁ ++ g₂)
    rw [← List.append_assoc] at hM hct
    refine ⟨c', _, g₁ ++ g₂, l, lH', .loop_true hb e e', ?_, ?_, hr', ?_, ?_, hw', he', ?_, hj',
      ?_, ?_⟩ <;> try simp only [← List.append_assoc]
    · exact hH'
    · exact hB'
    · exact hR'
    · exact hl'
    · exact hlH'
    · rw [List.length_append, Nat.mul_add, Nat.mul_add]; omega
    · have := bnd_iter (o := n₂ + n₃ + n₅ + n₆ + n₇ + n₈ + n₉ + n₁₀ + n₁₂ + n₁₃ + 30)
        (nb := n₁₁) (nr := n') (by omega) (bnd_mono hQ hn₁₁ hN₁) hn' (by omega)
      omega

theorem sim_fold (hQ : Monotone Q) (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s u : Ty} {Γ : WfCtx Ty.denote Lv}
    {xs₁ : List s.denote} {xs₂ : ℕ} (hxs : ⟨.list s, xs₁, xs₂⟩ ∈ Γ) {i₁ : u.denote} {i₂ : ℕ}
    (hi : ⟨u, i₁, i₂⟩ ∈ Γ) {f₁ : u.denote → s.denote → Prog Signature.empty (a, b) Ty.denote u}
    {f₂ : ℕ → ℕ → Prog Signature.empty (a, b) Lv u}
    (hf : ∀ acc₁ acc₂ x₁ x₂,
      Prog.Wf true (⟨u, acc₁, acc₂⟩ :: ⟨s, x₁, x₂⟩ :: Γ) (f₁ acc₁ x₁) (f₂ acc₂ x₂))
    {v : u.denote} {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.foldList xs₁ i₁ f₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c)
    (hK : psize d (Prog.foldList (a := s) xs₂ i₂ f₂) ≤ K)
    (hD : d + 3 * psize d (Prog.foldList (a := s) xs₂ i₂ f₂) ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (Prog.foldList (a := s) xs₂ i₂ f₂)) c h u v B F K Q
      (psize d (Prog.foldList (a := s) xs₂ i₂ f₂)) (Trace.localCost tr) := by
  have hs : psize d (Prog.foldList (a := s) xs₂ i₂ f₂) = psize (d + 3) (f₂ (d + 1) (d + 2)) + 2 :=
    rfl
  rw [hs] at hK hD ⊢
  obtain ⟨lx, hrx, hlx, c₁, n₁, e₁, hn₁, hr₁, hw₁, hj₁⟩ :=
    fetchVar_sat (prog := prog) hE hv hxs (dst := .work) (by decide) (by decide) (by decide)
  obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hw₂, he₂, hj₂⟩ := moveNum2_sat (prog := prog) (a := .work)
    (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₁ hw₁
  have he₂' : c₂.stk .env = bits lx ++ .nd :: c.stk .env := by rw [he₂, hj₁ .env (by decide)]
  have hE₂ : EnvAt B (⟨.list s, xs₁, d⟩ :: Γ) (d + 1) h c₂ := by
    simpa using hE.push (h' := []) he₂' (by simpa using hrx) (by simpa using hlx)
  obtain ⟨li, hri, hli, c₃, n₃, e₃, hn₃, hr₃, hw₃, hj₃⟩ := fetchVar_sat (prog := prog) hE₂ hr₂
    (List.mem_cons_of_mem _ hi) (dst := .work) (by decide) (by decide) (by decide)
  set c₄ := Act.run (.set 0 (some goMark)) c₃ with hc₄
  have hr₄ : c₄.regs = rv (some goMark) none none none := by
    rw [empty_eq_rv] at hr₃; simp [hc₄, Act.run, hr₃]
  have hj₄ : ∀ j, j ≠ .work → j ≠ .env → c₄.stk j = c.stk j := fun j hjw hje => by
    simp [hc₄, Act.run, hj₃ j hjw, hj₂ j hjw hje, hj₁ j hjw]
  obtain ⟨c₅, n₅, g, l, lH', e₅, hH₅, hB₅, hr₅, hR₅, hl₅, hw₅, he₅, hlH', hj₅, hc₅, hn₅⟩ :=
    foldLoop_sat hQ hQc ih hf (by omega) (by omega) c xs₁ i₁ v tr he hF h c₄ lx li
      (hH.frame (hj₄ .heap (by decide) (by decide)) (hj₄ .scan (by decide) (by decide))
        (hj₄ .cnt (by decide) (by decide))) hB hr₄ hE
      (by simp [hc₄, Act.run, hj₃ .env (by decide), he₂']) hlx hrx
      (by simp [hc₄, Act.run, hw₃, hw₂]) hli hri
      (fun j hjh hjc hjw hje => hj₄ j hjw hje)
  obtain ⟨c₆, n₆, e₆, hn₆, hr₆, he₆, hj₆⟩ := dropNum_sat (prog := prog) hr₅ he₅
  obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d + 1) (by omega) h g
  have hfe := fetchB_mono (j := d) (j' := d + 1) (E := B + h.length) (E' := B + h.length)
    (by omega) le_rfl
  have hlH'N : lH'.length ≤ B + (encHeap (h ++ g)).length :=
    hlH'.trans (by have := length_le_encHeap (h ++ g); omega)
  refine ⟨c₆, _, g, l, .seq e₁ (.seq e₂ (.seq e₃ (.seq (.act _ c₃) (.seq e₅ e₆)))),
    hH₅.frame (hj₆ .heap (by decide)) (hj₆ .scan (by decide)) (hj₆ .cnt (by decide)), hB₅, hr₆,
    hR₅, hl₅, by rw [hj₆ .work (by decide), hw₅], fun j hjh hjc hjw => ?_, hc₅, ?_⟩
  · by_cases hje : j = .env
    · subst hje; rw [he₆]
    · rw [hj₆ j hje, hj₅ j hjh hjc hjw hje]
  · have e : (psize (d + 3) (f₂ (d + 1) (d + 2)) + 2 + K * Trace.localCost tr) *
        Q (encHeap (h ++ g)).length = (psize (d + 3) (f₂ (d + 1) (d + 2)) + 1) *
          Q (encHeap (h ++ g)).length + (1 + K * Trace.localCost tr) *
          Q (encHeap (h ++ g)).length := by ring
    have : Q (encHeap (h ++ g)).length ≤ (psize (d + 3) (f₂ (d + 1) (d + 2)) + 1) *
        Q (encHeap (h ++ g)).length := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- **The loop of a compiled `loop`**, by induction on the fuel: at the head of the loop, the
state's pointer is on top of `work`. -/
theorem loopLoop_sat (hQ : Monotone Q) (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s : Ty} {Γ : WfCtx Ty.denote Lv}
    {f₁ : s.denote → Prog Signature.empty (a, b) Ty.denote (.option s)}
    {f₂ : ℕ → Prog Signature.empty (a, b) Lv (.option s)}
    (hf : ∀ v₁ v₂, Prog.Wf true (⟨s, v₁, v₂⟩ :: Γ) (f₁ v₁) (f₂ v₂)) {d : ℕ}
    (hK : psize (d + 1) (f₂ d) + 2 ≤ K) (hD : d + 1 + 3 * psize (d + 1) (f₂ d) ≤ D)
    (c₀ : Cfg Stk Sym Rg) :
    ∀ m, m ≤ fuel + 1 → ∀ (st r : s.denote) (tr : Trace Signature.empty),
      eval O (Pr.proc Ty.denote) m (.loop st f₁) = some (r, tr) → Trace.localCost tr ≤ F →
      ∀ (h : List Cell) (c : Cfg Stk Sym Rg) (ls : List Bool), HeapAt h c → HeapBnd B F h →
      c.regs = rv (some goMark) none none none → EnvAt B Γ d h c₀ →
      c.stk .work = bits ls ++ .nd :: c₀.stk .work → ls.length ≤ B + h.length →
      Rep h s st (ofBits ls) → (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c.stk j = c₀.stk j) →
      ∃ c' n g l, Exec prog (.loop (.is 0 (some goMark)) (loopStep (comp pc pb (d + 1) (f₂ d))))
          c c' n ∧
        HeapAt (h ++ g) c' ∧ HeapBnd B F (h ++ g) ∧ c'.regs = Regs.empty ∧
        Rep (h ++ g) s r (ofBits l) ∧ l.length ≤ B + (h ++ g).length ∧
        c'.stk .work = bits l ++ .nd :: c₀.stk .work ∧
        (∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → c'.stk j = c₀.stk j) ∧
        g.length ≤ K * Trace.localCost tr ∧
        n ≤ (1 + K * Trace.localCost tr) * Q (encHeap (h ++ g)).length := by
  intro m
  induction m with
  | zero => intro _ st r tr he; simp [eval] at he
  | succ m ihm =>
    intro hm st r tr he hF h c ls hH hB hv hE₀ hw hls hR hj
    obtain ⟨t, h₁, rfl⟩ := consT_eq_some.1 he
    obtain ⟨o, t₁, t₂, hbody, hcont, rfl⟩ := seqT_eq_some.1 h₁
    have hC : Trace.localCost (Event.local (S := Signature.empty) .iter 1 :: (t₁ ++ t₂)) =
        1 + (Trace.localCost t₁ + Trace.localCost t₂) := by simp
    rw [hC] at hF ⊢
    have hbody' := eval_mono (by omega : m ≤ fuel) hbody
    set c₁ := Act.run (.set 0 none) c with hc₁
    have hr₁ : c₁.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₁, Act.run, hv]
    obtain ⟨c₂, n₂, e₂, hn₂, hr₂, hw₂, he₂, hj₂⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .env) (t := .t0) (by decide) (by decide) (by decide) hr₁
      (by simpa [hc₁, Act.run] using hw)
    have he₂' : c₂.stk .env = bits ls ++ .nd :: c₀.stk .env := by
      rw [he₂]; simp [hc₁, Act.run, hj .env (by decide) (by decide) (by decide)]
    have hj₂' : ∀ j, j ≠ .work → j ≠ .env → c₂.stk j = c.stk j := fun j hjw hje => by
      rw [hj₂ j hjw hje]; rfl
    have hE₂ : EnvAt B (⟨s, st, d⟩ :: Γ) (d + 1) h c₂ := by
      simpa using hE₀.push (h' := []) he₂' (by simpa using hR) (by simpa using hls)
    obtain ⟨c₃, n₃, g₁, lo, e₃, hH₃, hB₃, hr₃, hR₃, hlo, hw₃, hj₃, hc₃, hn₃⟩ :=
      ih (hf st d) hbody' (hH.frame (hj₂' .heap (by decide) (by decide))
        (hj₂' .scan (by decide) (by decide)) (hj₂' .cnt (by decide) (by decide))) hB hr₂ hE₂
        (by omega) (by omega) (by omega)
    obtain ⟨c₄, n₄, e₄, hn₄, hr₄, hw₄, hp₄, hj₄⟩ := moveNum2_sat (prog := prog) (a := .work)
      (b := .ptr) (t := .t0) (by decide) (by decide) (by decide) hr₃ hw₃
    have hb : (Cond.is (0 : Fin Rg) (some goMark)).eval c.regs = true := by rw [hv]; rfl
    -- the frame so far: every stack but `heap`, `cnt`, `work`, `env` and `ptr` is `c₀`'s
    have hj₄' : ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .work → j ≠ .env → j ≠ .ptr →
        c₄.stk j = c₀.stk j := fun j hjh hjc hjw hje hjp => by
      rw [hj₄ j hjw hjp, hj₃ j hjh hjc hjw, hj₂' j hjw hje, hj j hjh hjc hjw]
    have hH₄ : HeapAt (h ++ g₁) c₄ := hH₃.frame (hj₄ .heap (by decide) (by decide))
      (hj₄ .scan (by decide) (by decide)) (hj₄ .cnt (by decide) (by decide))
    have hp₄' : c₄.stk .ptr = bits lo ++ .nd :: c₀.stk .ptr := by
      rw [hp₄, hj₃ .ptr (by decide) (by decide) (by decide), hj₂' .ptr (by decide) (by decide),
        hj .ptr (by decide) (by decide) (by decide)]
    have he₄ : c₄.stk .env = bits ls ++ .nd :: c₀.stk .env := by
      rw [hj₄ .env (by decide) (by decide), hj₃ .env (by decide) (by decide) (by decide), he₂']
    have hw₄' : c₄.stk .work = c₀.stk .work := by rw [hw₄, hw₂]
    have hlen : h.length ≤ (h ++ g₁).length := by simp
    cases o with
    | none =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hcont
      obtain ⟨rfl, rfl⟩ := hcont
      obtain ⟨c₅, n₅, e₅, hn₅, hr₅, hw₅, hp₅, hj₅⟩ := fetchCellE_sat (prog := prog) hH₄.wf
        hH₄.heap hH₄.scan hr₄ hR₃.none_inv hlo hp₄'
      set c₆ := Act.run (.set 1 none) c₅ with hc₆
      have hr₆ : c₆.regs = rv none none none none := by simp [hc₆, Act.run, hr₅]
      obtain ⟨c₇, n₇, e₇, hn₇, hr₇, hw₇, hj₇⟩ := closeCell_sat (prog := prog) (c := c₆) hr₆
        (by simpa [hc₆, Act.run, encFields] using hw₅)
      rw [← empty_eq_rv] at hr₇
      have he₇ : c₇.stk .env = bits ls ++ .nd :: c₀.stk .env := by
        rw [hj₇ .env (by decide)]; simp [hc₆, Act.run, hj₅ .env (by decide) (by decide), he₄]
      obtain ⟨c₈, n₈, e₈, hn₈, hr₈, he₈, hw₈, hj₈⟩ := moveNum2_sat (prog := prog) (a := .env)
        (b := .work) (t := .t0) (by decide) (by decide) (by decide) hr₇ he₇
      have hbs : (Cond.is (1 : Fin Rg) (some (.tag .some))).eval c₅.regs = false := by
        rw [hr₅]; decide
      have hb' : (Cond.is (0 : Fin Rg) (some goMark)).eval c₈.regs = false := by
        rw [hr₈, empty_eq_rv]; decide
      have hj₈' : ∀ j, j ≠ .work → j ≠ .env → c₈.stk j = c₅.stk j := fun j hjw hje => by
        rw [hj₈ j hje hjw, hj₇ j hjw]; rfl
      have e : Exec prog (loopStep (comp pc pb (d + 1) (f₂ d))) c c₈ _ :=
        .seq (.act _ c) (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ite_false hbs
          (.seq (.act _ c₅) (.seq e₇ e₈)))))))
      obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) (h ++ g₁) []
      simp only [List.append_nil] at hM hct'
      refine ⟨c₈, _, g₁, ls, .loop_true hb e (.loop_false hb'),
        hH₄.frame (by rw [hj₈' .heap (by decide) (by decide), hj₅ .heap (by decide) (by decide)])
          (by rw [hj₈' .scan (by decide) (by decide), hj₅ .scan (by decide) (by decide)])
          (by rw [hj₈' .cnt (by decide) (by decide), hj₅ .cnt (by decide) (by decide)]),
        hB₃, hr₈, hR.mono, by simp only [List.length_append]; omega, ?_,
        fun j hjh hjc hjw => ?_, ?_, ?_⟩
      · rw [hw₈, hw₇, hw₄']
      · by_cases hje : j = .env
        · subst hje; rw [he₈]
        by_cases hjp : j = .ptr
        · subst hjp; rw [hj₈' .ptr (by decide) (by decide), hp₅]
        · rw [hj₈' j hjw hje, hj₅ j hjw hjp, hj₄' j hjh hjc hjw hje hjp]
      · simp only [Trace.localCost_nil, Nat.add_zero]
        exact hc₃.trans (Nat.mul_le_mul_left _ (by omega))
      · have := bnd_iter (o := n₂ + n₄ + n₅ + n₇ + n₈ + 30) (nb := n₃) (nr := 0)
          (C₂ := Trace.localCost ([] : Trace Signature.empty)) (by omega) hn₃ (Nat.zero_le _)
          (by omega)
        omega
    | some st' =>
      obtain ⟨lf, hcl, hRf⟩ := hR₃.some_inv
      have hlf : lf.length < B + (h ++ g₁).length :=
        hB₃.field_lt hcl lf (List.mem_singleton_self lf)
      obtain ⟨c₅, n₅, e₅, hn₅, hr₅, hw₅, hp₅, hj₅⟩ := fetchCellE_sat (prog := prog) hH₄.wf
        hH₄.heap hH₄.scan hr₄ hcl hlo hp₄'
      set c₆ := Act.run (.set 1 none) c₅ with hc₆
      have hr₆ : c₆.regs = Regs.empty := by rw [empty_eq_rv]; simp [hc₆, Act.run, hr₅]
      have hw₆ : c₆.stk .work = bits lf ++ .nd :: (.mk 0 :: c₄.stk .work) := by
        simp [hc₆, Act.run, hw₅, encFields]
      obtain ⟨c₇, n₇, e₇, hn₇, hr₇, hw₇, ht₇, hj₇⟩ := moveNum2_sat (prog := prog) (a := .work)
        (b := .t4) (t := .t0) (by decide) (by decide) (by decide) hr₆ hw₆
      rw [empty_eq_rv] at hr₇
      obtain ⟨c₈, n₈, e₈, hn₈, hr₈, hw₈, hj₈⟩ := closeCell_sat (prog := prog) hr₇ hw₇
      rw [← empty_eq_rv] at hr₈
      have ht₈ : c₈.stk .t4 = bits lf ++ .nd :: c₆.stk .t4 := by rw [hj₈ .t4 (by decide), ht₇]
      obtain ⟨c₉, n₉, e₉, hn₉, hr₉, ht₉, hw₉, hj₉⟩ := moveNum2_sat (prog := prog) (a := .t4)
        (b := .work) (t := .t0) (by decide) (by decide) (by decide) hr₈ ht₈
      have he₉ : c₉.stk .env = bits ls ++ .nd :: c₀.stk .env := by
        rw [hj₉ .env (by decide) (by decide), hj₈ .env (by decide),
          hj₇ .env (by decide) (by decide)]
        simp [hc₆, Act.run, hj₅ .env (by decide) (by decide), he₄]
      obtain ⟨c₁₀, n₁₀, e₁₀, hn₁₀, hr₁₀, he₁₀, hj₁₀⟩ := dropNum_sat (prog := prog) hr₉ he₉
      set c₁₁ := Act.run (.set 0 (some goMark)) c₁₀ with hc₁₁
      have hr₁₁ : c₁₁.regs = rv (some goMark) none none none := by
        rw [empty_eq_rv] at hr₁₀; simp [hc₁₁, Act.run, hr₁₀]
      -- every stack but `heap`, `cnt`, `work`, `env`, `ptr` and `t4` is `c₄`'s
      have hj₁₁ : ∀ j, j ≠ .work → j ≠ .env → j ≠ .ptr → j ≠ .t4 → c₁₁.stk j = c₄.stk j :=
        fun j hjw hje hjp hj4 => by
          simp only [hc₁₁, Act.run]
          rw [hj₁₀ j hje, hj₉ j hj4 hjw, hj₈ j hjw, hj₇ j hjw hj4]
          simp [hc₆, Act.run, hj₅ j hjw hjp]
      have hw₁₁ : c₁₁.stk .work = bits lf ++ .nd :: c₀.stk .work := by
        simp only [hc₁₁, Act.run]
        rw [hj₁₀ .work (by decide), hw₉, hw₈, hw₄']
      have ht₁₁ : c₁₁.stk .t4 = c₀.stk .t4 := by
        simp only [hc₁₁, Act.run]
        rw [hj₁₀ .t4 (by decide), ht₉]
        simp [hc₆, Act.run, hj₅ .t4 (by decide) (by decide), hj₄' .t4 (by decide) (by decide)
          (by decide) (by decide) (by decide)]
      have hp₁₁ : c₁₁.stk .ptr = c₀.stk .ptr := by
        simp only [hc₁₁, Act.run]
        rw [hj₁₀ .ptr (by decide), hj₉ .ptr (by decide) (by decide), hj₈ .ptr (by decide),
          hj₇ .ptr (by decide) (by decide)]
        simp [hc₆, Act.run, hp₅]
      have hE₀' : EnvAt B Γ d (h ++ g₁) c₀ := hE₀.mono g₁ rfl
      obtain ⟨c', n', g₂, l, e', hH', hB', hr', hR', hl', hw', hj', hc', hn'⟩ :=
        ihm (by omega) st' r t₂ hcont (by omega) (h ++ g₁) c₁₁ lf
          (hH₄.frame (hj₁₁ .heap (by decide) (by decide) (by decide) (by decide))
            (hj₁₁ .scan (by decide) (by decide) (by decide) (by decide))
            (hj₁₁ .cnt (by decide) (by decide) (by decide) (by decide)))
          hB₃ hr₁₁ hE₀' hw₁₁ hlf.le hRf (fun j hjh hjc hjw => by
            by_cases hje : j = .env
            · subst hje; simp only [hc₁₁, Act.run]; rw [he₁₀]
            by_cases hjp : j = .ptr
            · subst hjp; exact hp₁₁
            by_cases hj4 : j = .t4
            · subst hj4; exact ht₁₁
            rw [hj₁₁ j hjw hje hjp hj4, hj₄' j hjh hjc hjw hje hjp])
      have hbs : (Cond.is (1 : Fin Rg) (some (.tag .some))).eval c₅.regs = true := by
        rw [hr₅]; rfl
      have e : Exec prog (loopStep (comp pc pb (d + 1) (f₂ d))) c c₁₁ _ :=
        .seq (.act _ c) (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.ite_true hbs
          (.seq (.act _ c₅) (.seq e₇ (.seq e₈ (.seq e₉ (.seq e₁₀ (.act _ c₁₀)))))))))))
      have hN₁ : (encHeap (h ++ g₁)).length ≤ (encHeap (h ++ g₁ ++ g₂)).length :=
        length_encHeap_mono _ _
      obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) (h ++ g₁) g₂
      refine ⟨c', _, g₁ ++ g₂, l, .loop_true hb e e', ?_, ?_, hr', ?_, ?_, hw', hj', ?_, ?_⟩ <;>
        try simp only [← List.append_assoc]
      · exact hH'
      · exact hB'
      · exact hR'
      · exact hl'
      · rw [List.length_append, Nat.mul_add, Nat.mul_add]; omega
      · have := bnd_iter (o := n₂ + n₄ + n₅ + n₇ + n₈ + n₉ + n₁₀ + 30) (nb := n₃) (nr := n')
          (by omega) (bnd_mono hQ hn₃ hN₁) hn' (by omega)
        omega
theorem sim_loop (hQ : Monotone Q) (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) {fuel : ℕ}
    (ih : Sim prog pc pb Pr O B F K D Q fuel) {s : Ty} {Γ : WfCtx Ty.denote Lv}
    {x₁ : s.denote} {x₂ : ℕ} (hx : ⟨s, x₁, x₂⟩ ∈ Γ)
    {f₁ : s.denote → Prog Signature.empty (a, b) Ty.denote (.option s)}
    {f₂ : ℕ → Prog Signature.empty (a, b) Lv (.option s)}
    (hf : ∀ v₁ v₂, Prog.Wf true (⟨s, v₁, v₂⟩ :: Γ) (f₁ v₁) (f₂ v₂)) {v : s.denote}
    {tr : Trace Signature.empty}
    (he : eval O (Pr.proc Ty.denote) (fuel + 1) (.loop x₁ f₁) = some (v, tr)) {d : ℕ}
    {h : List Cell} {c : Cfg Stk Sym Rg} (hH : HeapAt h c) (hB : HeapBnd B F h)
    (hv : c.regs = Regs.empty) (hE : EnvAt B Γ d h c) (hK : psize d (Prog.loop x₂ f₂) ≤ K)
    (hD : d + 3 * psize d (Prog.loop x₂ f₂) ≤ D) (hF : Trace.localCost tr ≤ F) :
    Pushes prog (comp pc pb d (Prog.loop x₂ f₂)) c h s v B F K Q (psize d (Prog.loop x₂ f₂))
      (Trace.localCost tr) := by
  have hs : psize d (Prog.loop x₂ f₂) = psize (d + 1) (f₂ d) + 2 := rfl
  rw [hs] at hK hD ⊢
  obtain ⟨ls, hrs, hls, c₁, n₁, e₁, hn₁, hr₁, hw₁, hj₁⟩ :=
    fetchVar_sat (prog := prog) hE hv hx (dst := .work) (by decide) (by decide) (by decide)
  set c₂ := Act.run (.set 0 (some goMark)) c₁ with hc₂
  have hr₂ : c₂.regs = rv (some goMark) none none none := by
    rw [empty_eq_rv] at hr₁; simp [hc₂, Act.run, hr₁]
  have hj₂ : ∀ j, j ≠ .work → c₂.stk j = c.stk j := fun j hjw => by
    simp [hc₂, Act.run, hj₁ j hjw]
  obtain ⟨c₃, n₃, g, l, e₃, hH₃, hB₃, hr₃, hR₃, hl₃, hw₃, hj₃, hc₃, hn₃⟩ :=
    loopLoop_sat hQ hQc ih hf (by omega) (by omega) c (fuel + 1) le_rfl x₁ v tr he hF h c₂ ls
      (hH.frame (hj₂ .heap (by decide)) (hj₂ .scan (by decide)) (hj₂ .cnt (by decide))) hB hr₂
      hE (by simp [hc₂, Act.run, hw₁]) hls hrs (fun j _ _ hjw => hj₂ j hjw)
  obtain ⟨hM, hct'⟩ := ctrl_le hQc (j := d) (by omega) h g
  refine ⟨c₃, _, g, l, .seq e₁ (.seq (.act _ c₁) e₃), hH₃, hB₃, hr₃, hR₃, hl₃, hw₃, hj₃, hc₃, ?_⟩
  have e : (psize (d + 1) (f₂ d) + 2 + K * Trace.localCost tr) * Q (encHeap (h ++ g)).length =
      (psize (d + 1) (f₂ d) + 1) * Q (encHeap (h ++ g)).length +
        (1 + K * Trace.localCost tr) * Q (encHeap (h ++ g)).length := by ring
  have : Q (encHeap (h ++ g)).length ≤ (psize (d + 1) (f₂ d) + 1) * Q (encHeap (h ++ g)).length :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- The simulation at every fuel, by induction. -/
theorem sim_all (hprog : prog.body pb = comp pc pb 1 (Pr.proc Lv 0)) (hQ : Monotone Q)
    (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) (hKB : K ≤ B) (hpc : PrimSpec prog pc B F K Q)
    (hKb : psize 1 (Pr.proc Lv 0) + 1 ≤ K) (hDb : 1 + 3 * psize 1 (Pr.proc Lv 0) ≤ D) :
    ∀ fuel, Sim prog pc pb Pr O B F K D Q fuel := by
  intro fuel
  induction fuel with
  | zero => intro t Γ p₁ p₂ _ v tr he; simp [eval] at he
  | succ fuel ih =>
    intro t Γ p₁ p₂ hwf v tr he d h c hH hB hv hE hK hD hF
    cases hwf with
    | ret hx =>
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact sim_ret hQc hx hH hB hv hE (by simp [psize] at hD; omega)
    | bind hp hk => exact sim_bind hQ hQc ih hp hk he hH hB hv hE hK hD hF
    | prim p hxs =>
      exact sim_prim hQc hKB hpc p hxs he hH hB hv hE hK (by omega) hF
    | ite hx hp hq => exact sim_ite hQc ih hx hp hq he hH hB hv hE hK hD hF
    | caseOption ho hp hq => exact sim_opt hQc ih ho hp hq he hH hB hv hE hK hD hF
    | caseList ho hp hq => exact sim_list hQc ih ho hp hq he hH hB hv hE hK hD hF
    | foldList hxs hi hf => exact sim_fold hQ hQc ih hxs hi hf he hH hB hv hE hK hD hF
    | loop hx hf => exact sim_loop hQ hQc ih hx hf he hH hB hv hE hK hD hF
    | recur _ hx =>
      exact sim_recur hQc hprog hKb hDb ih hx he hH hB hv hE (by simp [psize] at hD; omega) hF
    | call op _ => exact op.elim

end Sim

/-- **The simulation theorem.** Let `Pr` be a well-formed procedure over the empty signature,
run by the procedure `pb` whose body is `comp pc pb 1 (Pr.proc Lv 0)`. Assume that the
primitives' code meets `PrimSpec` for `B F K Q`, that `Q` is monotone with
`ctrlB D (B + N) ≤ Q N` (the control overhead), that `K ≤ B`, and that `K` and `D` are large
enough for the procedure body. If a program `p₁` at `Ty.denote` and a program `p₂` at levels
are related by `Prog.Wf true Γ`, `p₁` evaluates to `v` with a trace `tr` of local cost at most
`F`, the machine holds a heap `h` (`HeapAt`, `HeapBnd B F`) with empty registers and a frame of
depth `d` representing `Γ` (`EnvAt B`), and `psize d p₂ ≤ K`, `d + 3 * psize d p₂ ≤ D`, then the
code `comp pc pb d p₂` pushes a pointer representing `v` onto `work` (`Pushes`): it appends at
most `K * cost` cells, keeps `HeapAt` and `HeapBnd B F`, leaves the registers empty and every
stack but `heap`, `cnt` and `work` unchanged, within `(psize d p₂ + K * cost) * Q N` steps, `N`
the final heap's length in symbols. -/
theorem comp_sat {a b : Ty} (pc : PrimCode P) (pb : P) (Pr : WfProc Signature.empty a b)
    (O : Oracle Signature.empty) {prog : Program Stk Sym Rg P}
    (hprog : prog.body pb = comp pc pb 1 (Pr.proc Lv 0))
    {B F K D : ℕ} {Q : ℕ → ℕ} (hQ : Monotone Q) (hQc : ∀ N, ctrlB D (B + N) ≤ Q N) (hKB : K ≤ B)
    (hpc : PrimSpec prog pc B F K Q) (hKb : psize 1 (Pr.proc Lv 0) + 1 ≤ K)
    (hDb : 1 + 3 * psize 1 (Pr.proc Lv 0) ≤ D) :
    ∀ (fuel : ℕ) {t : Ty} {Γ : WfCtx Ty.denote Lv} {p₁ : Prog Signature.empty (a, b) Ty.denote t}
      {p₂ : Prog Signature.empty (a, b) Lv t}, Prog.Wf true Γ p₁ p₂ →
      ∀ {v : t.denote} {tr : Trace Signature.empty},
      eval O (Pr.proc Ty.denote) fuel p₁ = some (v, tr) →
      ∀ {d : ℕ} {h : List Cell} {c : Cfg Stk Sym Rg}, HeapAt h c → HeapBnd B F h →
      c.regs = Regs.empty → EnvAt B Γ d h c → psize d p₂ ≤ K → d + 3 * psize d p₂ ≤ D →
      Trace.localCost tr ≤ F →
      Pushes prog (comp pc pb d p₂) c h t v B F K Q (psize d p₂) (Trace.localCost tr) :=
  sim_all hprog hQ hQc hKB hpc hKb hDb

end GraphIso.TM
