module

public import GraphIso.TM.Prims
public import GraphIso.TM.Machine

/-!
# The simulation on Turing machines

Stage 17g (`PLAN-17.md` §10).

* **Stack growth** (`Exec.length_le`): a run of `n` steps adds at most `n` symbols to each
  stack. So the heap loaded from an input has at most as many symbols as the loading took steps.
* **`canonPtr`** makes the number on `ptr` canonical (drops its high zero bits): the pointer the
  compiled code leaves is at most `B` plus the number of cells long, and `write` needs a pointer
  at most as long as the heap.
* **The main program** `mainProg Pr E`: the procedure `true` runs the compiled body of `Pr`, and
  `main` (`false`) initializes the allocation counter, loads the input, binds it at level `0`,
  runs the compiled entry `E`, drops the level, makes the result's pointer canonical, writes the
  result and erases `heap` and `cnt`.
* **The run** (`main_sat`, `main_exec`): for an entry `E` well formed against its level
  instantiation and every run of `E` on `x` with value `v` and trace `tr`, `main` runs from the
  input configuration of `ser a' x` to the output configuration of `ser c v` (every other stack
  empty, registers empty) within `mainT` steps, and so within
  `mainPoly = (κ (C + L + L' + 1)) ^ 120` (`mainT_le`). Here `C` is the local cost of `tr`, `L`
  and `L'` are the lengths of the input and of the output, and
  `κ = 4096 (wt a' + wt c + K + D + |E| + 1)`, with `K`, `D` the size constants of `Pr` and `E`
  (`kP`, `dP`) and `|E| = psize 1 (E Lv 0)`.
* **On Turing machines** (`main_tm`): the machine `toFinTM2 (mainProg Pr E) .inp .out` outputs
  `ser c v` on input `ser a' x` within `mainPoly + 1` steps (`TM2OutputsInTime`).

The output's length is in the bound because values share cells: at a cost of about `m`, a
program can build a list of `m` copies of one list of `m` numbers, which the machine writes out
in at least `m²` symbols (lists nested `d` deep: `m ^ d`). So no bound
`C_P (C + L + 1) ^ d` with `d` independent of the program holds.
-/

@[expose] public section

namespace GraphIso.TM

open GraphIso.Cost Function

section Growth

variable {K Γ : Type} {R : ℕ} {P : Type} [DecidableEq K] [DecidableEq Γ] [Inhabited Γ]

/-- **Stack growth**: each step pushes at most one symbol. -/
theorem Exec.length_le {prog : Program K Γ R P} {x : Code K Γ R P} {c c' : Cfg K Γ R} {n : ℕ}
    (h : Exec prog x c c' n) : ∀ k, (c'.stk k).length ≤ (c.stk k).length + n := by
  induction h with
  | skip c => intro k; omega
  | act a c =>
    intro k
    cases a with
    | push j s =>
      simp only [Act.run]
      by_cases e : k = j
      · subst e; simp
      · simp [update_of_ne e]
    | pushReg j r =>
      simp only [Act.run]
      by_cases e : k = j
      · subst e; simp
      · simp [update_of_ne e]
    | pop j r =>
      simp only [Act.run]
      by_cases e : k = j
      · subst e; simp; omega
      · simp [update_of_ne e]
    | peek j r => simp [Act.run]
    | set r o => simp [Act.run]
  | seq _ _ ih₁ ih₂ => intro k; have := ih₁ k; have := ih₂ k; omega
  | ite_true _ _ ih => intro k; have := ih k; omega
  | ite_false _ _ ih => intro k; have := ih k; omega
  | loop_false _ => intro k; omega
  | loop_true _ _ _ ih₁ ih₂ => intro k; have := ih₁ k; have := ih₂ k; omega
  | call _ ih => intro k; have := ih k; omega

end Growth

variable {P : Type} {prog : Program Stk Sym Rg P}

/-! ### Canonical pointers -/

/-- Make the number on `ptr` canonical (drop its high zero bits), through `t0`. -/
def canonPtr : Code Stk Sym Rg P :=
  .seq (moveBits .ptr .t0) (.seq (.act (.peek .t0 0)) (.seq (.loop (.is 0 (some (.bit false)))
      (.seq (.act (.set 0 none)) (.seq (.act (.pop .t0 0)) (.seq (.act (.set 0 none))
        (.act (.peek .t0 0))))))
    (.seq (.act (.set 0 none)) (moveBits .t0 .ptr))))

theorem canonPtr_sat {c : Cfg Stk Sym Rg} {l : List Bool} {rp : List Sym}
    (hv : c.regs = Regs.empty) (hp : c.stk .ptr = bits l ++ .nd :: rp) :
    Sat prog canonPtr c (20 * l.length + 30) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk .ptr = bits (toBits (ofBits l)) ++ .nd :: rp ∧
        Fr [.ptr] c c' := by
  unfold canonPtr
  refine Sat.seq_le (moveBits_sat (by decide) hv hp) (by omega)
    fun c₁ ⟨hr₁, hp₁, ht₁, hj₁⟩ => Sat.act_seq (by omega) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = l.reverse := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = L.dropWhile (· == false) := ⟨_, rfl⟩
  have hsplit : L = L.takeWhile (· == false) ++ D := by
    rw [hD]; exact List.takeWhile_append_dropWhile.symm
  have ht₁' : c₁.stk .t0 = bits (L.takeWhile (· == false) ++ D) ++ .nd :: c.stk .t0 := by
    rw [ht₁, ← hsplit, hL]
  have hloop := Sat.loop (prog := prog) (b := .is 0 (some (.bit false)))
    (x := .seq (.act (.set 0 none)) (.seq (.act (.pop .t0 0)) (.seq (.act (.set 0 none))
      (.act (.peek .t0 0))))) (t := 7)
    (I := fun m c₅ => ∃ pre, pre.length = m ∧ (∀ y ∈ pre, y = false) ∧
      c₅.stk .t0 = bits (pre ++ D) ++ .nd :: c.stk .t0 ∧
      c₅.regs = rv (c₅.stk .t0).head? none none none ∧ ∀ j, j ≠ .t0 → c₅.stk j = c₁.stk j)
    (Q := fun c₅ => c₅.stk .t0 = bits D ++ .nd :: c.stk .t0 ∧
      c₅.regs = rv (c₅.stk .t0).head? none none none ∧ ∀ j, j ≠ .t0 → c₅.stk j = c₁.stk j)
    (fun m c₅ ⟨pre, hlen, hpre, ht₅, hr₅, hj₅⟩ => by
      obtain ⟨y, pre, rfl⟩ : ∃ y pre', pre = y :: pre' := by
        cases pre with
        | nil => simp at hlen
        | cons y pre' => exact ⟨y, pre', rfl⟩
      have hy : y = false := hpre y (by simp)
      subst hy
      refine ⟨by simp [Cond.eval, hr₅, ht₅, bits], ?_⟩
      refine Sat.act_seq (by omega) (Sat.act_seq (by omega) (Sat.act_seq (by omega)
        (Sat.act_le (by omega) ⟨pre, by simpa using hlen, fun z hz => hpre z (by simp [hz]),
          ?_, ?_, ?_⟩)))
      · simp [Act.run, ht₅, bits]
      · simp [Act.run, hr₅]
      · intro j hj; simp [Act.run, update_of_ne hj, hj₅ j hj])
    (fun c₅ ⟨pre, hlen, hpre, ht₅, hr₅, hj₅⟩ => by
      obtain rfl : pre = [] := List.eq_nil_of_length_eq_zero hlen
      simp only [List.nil_append] at ht₅
      refine ⟨?_, ht₅, hr₅, hj₅⟩
      have := head_dropWhile_false L
      rw [← hD] at this
      simp only [Cond.eval, hr₅, ht₅, rv_zero, decide_eq_false_iff_not]
      simpa [bits] using this)
  have hk : (L.takeWhile (· == false)).length ≤ l.length := by
    have := List.takeWhile_prefix (p := (· == false)) (l := L) |>.length_le
    simpa [hL] using this
  have hDl : D.length ≤ l.length := by
    have := List.dropWhile_suffix (p := (· == false)) (l := L) |>.length_le
    simpa [hL, hD] using this
  refine Sat.seq_le (hloop _ _ ⟨L.takeWhile (· == false), rfl,
    fun y hy => by simpa using List.mem_takeWhile_imp hy,
    by simpa [Act.run] using ht₁', ?_, ?_⟩) (by omega)
    fun c₅ ⟨ht₅, hr₅, hj₅⟩ => ?_
  · rw [empty_eq_rv] at hr₁; simp [Act.run, hr₁]
  · intro j hj; simp [Act.run]
  refine Sat.act_seq (by omega) ?_
  have hv₆ : (Act.run (.set 0 none) c₅).regs = Regs.empty := by
    rw [empty_eq_rv]; simp [Act.run, hr₅]
  refine (moveBits_sat (l := D) (rest := c.stk .t0) (by decide) hv₆
    (by simpa [Act.run] using ht₅)).mono (by omega)
    fun c' ⟨hr', ht', hp', hj'⟩ => ⟨hr', ?_, ?_⟩
  · rw [hp']
    simp only [Act.run]
    rw [hj₅ .ptr (by decide), hp₁]
    have hs : D.reverse = toBits (ofBits l) := by
      rw [← strip_eq_toBits, hD, hL]; rfl
    rw [hs]
  · intro j hj
    simp only [List.mem_singleton] at hj
    by_cases hj0 : j = .t0
    · subst hj0; rw [ht']
    rw [hj' j hj0 hj]
    simp only [Act.run]
    rw [hj₅ j hj0, hj₁ j hj hj0]

/-! ### The main program -/

section Main

variable {a b a' c : Ty}

/-- The body of `main`: initialize the allocation counter, load the input, bind it at level `0`,
run `code`, drop the level, make the result's pointer canonical, write the result, and erase
the heap and the counter. -/
def mainBody (a' c : Ty) (code : Code Stk Sym Rg Bool) : Code Stk Sym Rg Bool :=
  .seq (.act (.push .cnt .nd)) (.seq (load a') (.seq pushEnv (.seq code (.seq popEnv
    (.seq (moveNum2 .work .ptr .t0) (.seq canonPtr (.seq (write c) (.seq (erase .heap)
      (erase .cnt)))))))))

/-- **The main program** for a procedure `Pr` and an entry `E`: the procedure `true` runs the
compiled body of `Pr`, and `main` (`false`) runs `mainBody` with the compiled entry. -/
def mainProg (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c) :
    Program Stk Sym Rg Bool :=
  ⟨fun q => if q then comp primCode true 1 (Pr.proc Lv 0) else
    mainBody a' c (comp primCode true 1 (E Lv 0)), false⟩

/-! ### The step bound of a run -/

/-- Cells and pointers of the loaded input (`L` its length, `wa` the weight of its type). -/
def uB (wa L : ℕ) : ℕ := wa * (L + 1)

/-- Steps of loading, and so symbols of the loaded heap. -/
def heapB (wa L : ℕ) : ℕ := wa * (L + 1) * PL (uB wa L)

/-- The field bound `F` of the run (`C` its local cost). -/
def fB (wa C L : ℕ) : ℕ := C + heapB wa L + 2

/-- The bit bound `B` of the run (`K` the size constant). -/
def bB (wa K C L : ℕ) : ℕ := fB wa C L + K + uB wa L + 1

/-- Cells of the final heap, at most. -/
def nCells (wa K C L : ℕ) : ℕ := uB wa L + K * C

/-- Symbols of the final heap, at most. -/
def nSym (wa K C L : ℕ) : ℕ :=
  nCells wa K C L * (bB wa K C L + nCells wa K C L + 4 +
    fB wa C L * (bB wa K C L + nCells wa K C L + 1))

/-- The step bound of one unit of the compiled code, at a heap of `N` symbols. -/
def qB (D B N : ℕ) : ℕ := ctrlB D (B + N) + primB (B + N)

/-- **The step bound of `main`**, for weights `wa`, `wc` of the input and output types, size
constants `K`, `D`, the entry's size `sE`, the local cost `C`, and the input and output lengths
`L`, `L'`. -/
def mainT (wa wc K D sE C L L' : ℕ) : ℕ :=
  heapB wa L + 14 * uB wa L + (sE + K * C) * qB D (bB wa K C L) (nSym wa K C L) +
    32 * (bB wa K C L + nCells wa K C L) + wc * (L' + 1) * visB (nSym wa K C L) +
    2 * nSym wa K C L + 2 * nCells wa K C L + 120

end Main

/-! ### The run of `main` -/

/-- A run as a `Sat` with its final configuration. -/
theorem Sat.of_exec {K Γ : Type} {R : ℕ} {P : Type} [DecidableEq K] [DecidableEq Γ] [Inhabited Γ]
    {prog : Program K Γ R P} {x : Code K Γ R P} {c c' : Cfg K Γ R} {n t : ℕ}
    (e : Exec prog x c c' n) (hn : n ≤ t) : Sat prog x c t (· = c') := ⟨c', n, e, hn, rfl⟩

theorem visB_mono {N N' : ℕ} (h : N ≤ N') : visB N ≤ visB N' := by
  unfold visB lookupBound; gcongr

theorem heapLen_mono {n n' B B' F F' : ℕ} (hn : n ≤ n') (hB : B ≤ B') (hF : F ≤ F') :
    n * (B + n + 4 + F * (B + n + 1)) ≤ n' * (B' + n' + 4 + F' * (B' + n' + 1)) := by
  gcongr

section Consts

variable {a b a' c : Ty}

/-- The size constant `K` of a procedure and an entry: their sizes plus one. -/
def kP (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c) : ℕ :=
  psize 1 (Pr.proc Lv 0) + psize 1 (E Lv 0) + 1

/-- The depth constant `D` of a procedure and an entry (frames and nested levels). -/
def dP (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c) : ℕ :=
  1 + 3 * (psize 1 (Pr.proc Lv 0) + psize 1 (E Lv 0))

end Consts

section Run

variable {a b a' c : Ty}

/-- **The run of `main`** within the bound `mainT`, as a `Sat`. -/
theorem main_sat (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c)
    (hE : ∀ x₁ x₂, Prog.Wf true [⟨a', x₁, x₂⟩] (E Ty.denote x₁) (E Lv x₂))
    (O : Oracle Signature.empty) {x : a'.denote} {v : c.denote} {tr : Trace Signature.empty}
    {fuel : ℕ} (he : eval O (Pr.proc Ty.denote) fuel (E Ty.denote x) = some (v, tr)) :
    Sat (mainProg Pr E) (mainBody a' c (comp primCode true 1 (E Lv 0))) (inCfg .inp (ser a' x))
      (mainT (wt a') (wt c) (kP Pr E) (dP Pr E) (psize 1 (E Lv 0)) (Trace.localCost tr)
        (ser a' x).length (ser c v).length) (· = inCfg .out (ser c v)) := by
  obtain ⟨L, hL⟩ : ∃ L, L = (ser a' x).length := ⟨_, rfl⟩
  obtain ⟨L', hL'⟩ : ∃ L', L' = (ser c v).length := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = Trace.localCost tr := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = kP Pr E := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = dP Pr E := ⟨_, rfl⟩
  obtain ⟨sE, hsE⟩ : ∃ sE, sE = psize 1 (E Lv 0) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = uB (wt a') L := ⟨_, rfl⟩
  obtain ⟨HB, hHB⟩ : ∃ HB, HB = heapB (wt a') L := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = fB (wt a') C L := ⟨_, rfl⟩
  obtain ⟨B, hBB⟩ : ∃ B, B = bB (wt a') K C L := ⟨_, rfl⟩
  obtain ⟨NC, hNC⟩ : ∃ NC, NC = nCells (wt a') K C L := ⟨_, rfl⟩
  obtain ⟨NS, hNS⟩ : ∃ NS, NS = nSym (wt a') K C L := ⟨_, rfl⟩
  have hFdef : F = C + HB + 2 := by rw [hF, hHB]; rfl
  have hBdef : B = F + K + U + 1 := by rw [hBB, hF, hU]; rfl
  have hNCdef : NC = U + K * C := by rw [hNC, hU]; rfl
  have hNSdef : NS = NC * (B + NC + 4 + F * (B + NC + 1)) := by rw [hNS, hNC, hBB, hF]; rfl
  have hHBdef : HB = wt a' * (L + 1) * PL U := by rw [hHB, hU]; rfl
  have hUdef : U = wt a' * (L + 1) := by rw [hU]; rfl
  have hKdef : K = psize 1 (Pr.proc Lv 0) + psize 1 (E Lv 0) + 1 := by rw [hK]; rfl
  have hDdef : D = 1 + 3 * (psize 1 (Pr.proc Lv 0) + psize 1 (E Lv 0)) := by rw [hD]; rfl
  have hwa := one_le_wt a'
  have hLU : L ≤ U := by rw [hUdef]; nlinarith
  unfold mainT
  rw [← hL, ← hL', ← hC, ← hK, ← hD, ← hsE, ← hU, ← hHB, ← hBB, ← hNC, ← hNS]
  unfold mainBody
  -- the counter
  refine Sat.act_seq (by omega) ?_
  have hH₁ : HeapAt [] (Act.run (.push .cnt .nd) (inCfg .inp (ser a' x))) :=
    ⟨fun i hi => by simp at hi, by simp [Act.run, inCfg, inStk, encHeap],
      by simp [Act.run, inCfg, inStk], [], by simp [Act.run, inCfg, inStk], rfl, by simp⟩
  -- loading
  have hcB := cellsB_le a' x
  rw [← hL] at hcB
  have hld := ldB_le a' x U (by omega)
  rw [← hL] at hld
  have hload := load_sat (P := Bool) a' (mainProg Pr E) x [] _ [] U hH₁
    (by simp [Act.run, inCfg]) (by simp [Act.run, inCfg, inStk]) (by simp; omega)
  obtain ⟨c₂, n₂, e₂, hn₂, hr₂, h₀, l, hH₂, hcell, hlU, hR, hinp₂, hw₂, hj₂⟩ := hload.exec
  simp only [List.nil_append] at hH₂ hR
  have hgrow := e₂.length_le .heap
  rw [hH₂.heap] at hgrow
  have hN₀ : (encHeap h₀).length ≤ HB := by
    simp [Act.run, inCfg, inStk] at hgrow; rw [hHBdef]; omega
  refine Sat.seq_le (Sat.of_exec e₂ (t := HB) (by rw [hHBdef]; omega)) (by omega)
    fun c₂' hc₂ => ?_
  subst c₂'
  -- the stacks of the start
  have hs₀ : ∀ j : Stk, j ≠ .inp → (inCfg (Γ := Sym) (R := Rg) Stk.inp (ser a' x)).stk j = [] :=
    fun j hj => by
    simp [inCfg, inStk, hj]
  have hj₂' : ∀ j, j ≠ .heap → j ≠ .cnt → j ≠ .inp → j ≠ .work → c₂.stk j = [] := by
    intro j h1 h2 h3 h4
    rw [hj₂ j h1 h2 h3 h4]
    simp [Act.run, update_of_ne h2, hs₀ j h3]
  have hw₂' : c₂.stk .work = bits l ++ .nd :: [] := by
    rw [hw₂]; simp [Act.run, inCfg, inStk]
  -- binding the input at level `0`
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₂ hw₂')
    (t₁ := 12 * l.length + 19) (by omega) fun c₃ ⟨hr₃, hw₃, he₃, hj₃⟩ => ?_
  have hH₃ : HeapAt h₀ c₃ := hH₂.fr (fr2 hj₃) (by decide) (by decide) (by decide)
  have he₃' : c₃.stk .env = envEnc [l] ++ [] := by
    rw [he₃, hj₂' .env (by decide) (by decide) (by decide) (by decide)]; simp [envEnc]
  -- the compiled entry
  have hB₀ : HeapBnd B F h₀ := HeapBnd.of_length (by omega) (by omega)
  have hEnv : EnvAt B [⟨a', x, 0⟩] 1 h₀ c₃ :=
    ⟨[l], [], rfl, he₃', fun l' hl' => by simp at hl'; subst hl'; omega, fun e he => by
      simp only [List.mem_singleton] at he; subst he; exact ⟨by simp, by simpa using hR⟩⟩
  have hQm : Monotone (fun N => qB D B N) := fun _ _ hN =>
    Nat.add_le_add (ctrlB_mono (by omega)) (primB_mono (by omega))
  have hps : PrimSpec (mainProg Pr E) primCode B F K (fun N => qB D B N) :=
    primCode_spec (Q := fun N => qB D B N) _ (by omega) (by omega)
      fun N => Nat.le_add_left (primB (B + N)) (ctrlB D (B + N))
  have hpush := comp_sat (prog := mainProg Pr E) primCode true Pr O rfl hQm
    (fun N => Nat.le_add_right (ctrlB D (B + N)) (primB (B + N))) (by omega) hps
    (by omega) (by omega) fuel (hE x 0) he hH₃ hB₀ hr₃ hEnv (by omega) (by omega) (by omega)
  obtain ⟨c₄, n₄, g, l', e₄, hH₄, hB₄, hr₄, hR₄, hl'B, hw₄, hj₄, hg, hn₄⟩ := hpush
  rw [← hC] at hg hn₄
  have hcells : (h₀ ++ g).length ≤ NC := by simp; omega
  have hNf : (encHeap (h₀ ++ g)).length ≤ NS := by
    rw [hNSdef]
    exact (length_encHeap_le_bnd hB₄).trans (heapLen_mono hcells le_rfl le_rfl)
  have hn₄' : n₄ ≤ (sE + K * C) * qB D B NS := by
    rw [hsE]
    exact hn₄.trans (Nat.mul_le_mul_left _ (hQm hNf))
  refine Sat.seq_le (Sat.of_exec e₄ hn₄') (by omega) fun c₄' hc₄ => ?_
  subst c₄'
  -- dropping the level
  have he₄ : c₄.stk .env = bits l ++ .nd :: [] := by
    rw [hj₄ .env (by decide) (by decide) (by decide), he₃']; simp [envEnc]
  refine Sat.seq_le (dropNum_sat hr₄ he₄) (t₁ := 2 * l.length + 5) (by omega)
    fun c₅ ⟨hr₅, he₅, hj₅⟩ => ?_
  -- the result's pointer onto `ptr`
  have hw₅ : c₅.stk .work = bits l' ++ .nd :: [] := by
    rw [hj₅ .work (by decide), hw₄, hw₃]
  have hl'NC : l'.length ≤ B + NC := by omega
  refine Sat.seq_le (moveNum2_sat (by decide) (by decide) (by decide) hr₅ hw₅)
    (t₁ := 12 * l'.length + 19) (by omega) fun c₆ ⟨hr₆, hw₆, hp₆, hj₆⟩ => ?_
  have hp₆' : c₆.stk .ptr = bits l' ++ .nd :: [] := by
    rw [hp₆, hj₅ .ptr (by decide), hj₄ .ptr (by decide) (by decide) (by decide),
      hj₃ .ptr (by decide) (by decide),
      hj₂' .ptr (by decide) (by decide) (by decide) (by decide)]
  refine Sat.seq_le (canonPtr_sat hr₆ hp₆') (by omega) fun c₇ ⟨hr₇, hp₇, F7⟩ => ?_
  -- writing the result
  have hH₇ : HeapAt (h₀ ++ g) c₇ := by
    refine hH₄.frame ?_ ?_ ?_ <;>
      rw [F7 _ (by decide), hj₆ _ (by decide) (by decide), hj₅ _ (by decide)]
  have hlt := hR₄.lt
  have hpN : (toBits (ofBits l')).length ≤ (encHeap (h₀ ++ g)).length :=
    (length_toBits_le _).trans (by have := length_le_encHeap (h₀ ++ g); omega)
  have hwr := write_sat c (mainProg Pr E) v (h₀ ++ g) c₇ (toBits (ofBits l')) [] hH₇.wf
    hH₇.heap hH₇.scan hr₇ (by rw [ofBits_toBits]; exact hR₄) hpN hp₇
  have hwB : wrB c v (encHeap (h₀ ++ g)).length ≤ wt c * (L' + 1) * visB NS := by
    have := wrB_le c v (encHeap (h₀ ++ g)).length
    rw [← hL'] at this
    exact this.trans (Nat.mul_le_mul_left _ (visB_mono hNf))
  refine Sat.seq_le hwr (by omega) fun c₈ ⟨hr₈, ho₈, hp₈, hj₈⟩ => ?_
  -- erasing the heap and the counter
  have hh₈ : c₈.stk .heap = encHeap (h₀ ++ g) := by
    rw [hj₈ .heap (by decide) (by decide), F7 .heap (by decide), hj₆ .heap (by decide) (by decide),
      hj₅ .heap (by decide), hH₄.heap]
  refine Sat.seq_le (erase_sat hr₈) (by rw [hh₈]; omega) fun c₉ ⟨hr₉, hh₉, hj₉⟩ => ?_
  obtain ⟨lc, hcnt, -, hlc⟩ := hH₄.cnt
  have hc₉ : c₉.stk .cnt = bits lc ++ [.nd] := by
    rw [hj₉ .cnt (by decide), hj₈ .cnt (by decide) (by decide), F7 .cnt (by decide),
      hj₆ .cnt (by decide) (by decide), hj₅ .cnt (by decide), hcnt]
  refine (erase_sat hr₉).mono (by rw [hc₉, hh₈]; simp; omega) fun c' ⟨hr', hc', hj'⟩ => ?_
  -- the final configuration
  have hstk : c'.stk = inStk .out (ser c v) := by
    funext j
    by_cases hjc : j = .cnt
    · subst hjc; rw [hc']; simp [inStk]
    rw [hj' j hjc]
    by_cases hjh : j = .heap
    · subst hjh; rw [hh₉]; simp [inStk]
    rw [hj₉ j hjh]
    by_cases hjo : j = .out
    · subst hjo
      rw [ho₈, F7 .out (by decide), hj₆ .out (by decide) (by decide), hj₅ .out (by decide),
        hj₄ .out (by decide) (by decide) (by decide), hj₃ .out (by decide) (by decide),
        hj₂' .out (by decide) (by decide) (by decide) (by decide)]
      simp [inStk]
    by_cases hjp : j = .ptr
    · subst hjp; rw [hp₈]; simp [inStk]
    rw [hj₈ j hjo hjp, F7 j (by simpa using hjp)]
    by_cases hjw : j = .work
    · subst hjw; rw [hw₆]; simp [inStk]
    rw [hj₆ j hjw hjp]
    by_cases hje : j = .env
    · subst hje; rw [he₅]; simp [inStk]
    rw [hj₅ j hje, hj₄ j hjh hjc hjw, hj₃ j hjw hje]
    by_cases hji : j = .inp
    · subst hji; rw [hinp₂]; simp [inStk]
    rw [hj₂' j hjh hjc hji hjw]
    simp [inStk, hjo]
  show c' = ⟨Regs.empty, inStk .out (ser c v)⟩
  cases c'
  simp only at hr' hstk
  rw [hr', hstk]

end Run

/-! ### Powers of a large base -/

section PowBound

variable {Y : ℕ}

/-- `4096 * Y ^ k ≤ Y ^ (k + 1)` for `Y ≥ 4096`. -/
theorem pow_step (hY : 4096 ≤ Y) (k : ℕ) : 4096 * Y ^ k ≤ Y ^ (k + 1) := by
  rw [pow_succ, mul_comm 4096]; exact Nat.mul_le_mul_left _ hY

theorem pow_mono_le (hY : 4096 ≤ Y) {i j : ℕ} (h : i ≤ j) : Y ^ i ≤ Y ^ j :=
  Nat.pow_le_pow_right (by omega) h

theorem one_le_pow' (hY : 4096 ≤ Y) (k : ℕ) : 1 ≤ Y ^ k := Nat.one_le_pow k Y (by omega)

theorem le_pow_mul {a b i j : ℕ} (ha : a ≤ Y ^ i) (hb : b ≤ Y ^ j) : a * b ≤ Y ^ (i + j) := by
  rw [pow_add]; exact Nat.mul_le_mul ha hb

theorem le_pow_one {a : ℕ} (ha : a ≤ Y) : a ≤ Y ^ 1 := by rwa [pow_one]

end PowBound

/-! ### The polynomial bound of `main` -/

/-- The constant of the polynomial bound. -/
def kappa (wa wc K D sE : ℕ) : ℕ := 4096 * (wa + wc + K + D + sE + 1)

section MainPoly

variable {Y : ℕ}

theorem PL_le (hY : 4096 ≤ Y) {U : ℕ} (hU : U ≤ Y) : PL U ≤ Y ^ 5 := by
  unfold PL allocBound
  have h1 : (U + 1) * (U + 2) ≤ Y ^ 2 * 2 := by
    have : (U + 1) * (U + 2) ≤ (Y + 1) * (Y + 2) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have h2 : 6 * ((U + 1) * (U + 2)) + 14 ≤ Y ^ 2 * 13 := by nlinarith
  have h3 : (U + 1) * (U + 2) * (6 * ((U + 1) * (U + 2)) + 14) ≤ Y ^ 2 * 2 * (Y ^ 2 * 13) :=
    Nat.mul_le_mul h1 h2
  have h4 : Y ^ 2 * 2 * (Y ^ 2 * 13) = 26 * Y ^ 4 := by ring
  have h5 : 4096 * Y ^ 4 ≤ Y ^ 5 := pow_step hY 4
  have h6 : Y ^ 1 ≤ Y ^ 4 := pow_mono_le hY (by omega)
  have h7 := le_pow_one hU
  have h8 := le_pow_one (le_refl Y)
  omega

theorem lookupBound_le_pow (hY : 4096 ≤ Y) {N lp k : ℕ} (hN : N ≤ Y ^ k) (hl : lp ≤ Y ^ k) :
    lookupBound N lp ≤ Y ^ (2 * k + 3) := by
  have h₁ := lookupBound_le N lp
  have hs := pow_step hY k
  have h1 := one_le_pow' hY k
  have h₂ : N + lp + 3 ≤ Y ^ (k + 1) := by omega
  have h₃ : (N + lp + 3) ^ 2 ≤ Y ^ (2 * k + 2) := by
    calc (N + lp + 3) ^ 2 ≤ (Y ^ (k + 1)) ^ 2 := Nat.pow_le_pow_left h₂ 2
      _ = Y ^ (2 * k + 2) := by ring
  have : 4096 * Y ^ (2 * k + 2) ≤ Y ^ (2 * k + 3) := pow_step hY _
  omega

theorem fcE_le_pow (hY : 4096 ≤ Y) {M k : ℕ} (hM : M ≤ Y ^ k) : fcE M M ≤ Y ^ (2 * k + 4) := by
  unfold fcE
  have h₁ := lookupBound_le_pow hY hM hM
  have h₂ : Y ^ k ≤ Y ^ (2 * k + 3) := pow_mono_le hY (by omega)
  have : 4096 * Y ^ (2 * k + 3) ≤ Y ^ (2 * k + 4) := pow_step hY _
  have := one_le_pow' hY (2 * k + 3)
  omega

theorem allocBound_le_pow (hY : 4096 ≤ Y) {A M k : ℕ} (hA : A ≤ Y ^ k) (hM : M ≤ Y ^ k) :
    allocBound A M ≤ Y ^ (2 * k + 3) := by
  unfold allocBound
  have hs := pow_step hY k
  have h1 := one_le_pow' hY k
  have h₂ : 6 * A + 14 ≤ Y ^ (k + 1) := by omega
  have h₃ : A * (6 * A + 14) ≤ Y ^ (k + (k + 1)) := le_pow_mul hA h₂
  rw [show k + (k + 1) = 2 * k + 1 by ring] at h₃
  have : 4096 * Y ^ (2 * k + 1) ≤ Y ^ (2 * k + 2) := pow_step hY _
  have : 4096 * Y ^ (2 * k + 2) ≤ Y ^ (2 * k + 3) := pow_step hY _
  have : Y ^ k ≤ Y ^ (2 * k + 1) := pow_mono_le hY (by omega)
  have := one_le_pow' hY (2 * k + 1)
  omega

/-- **The polynomial bound of `main`**: `mainT ≤ (κ (C + L + L' + 1)) ^ 120`, `κ` the constant
`kappa` of the weights and the size constants. -/
theorem mainT_le {wa wc K D sE C L L' : ℕ} :
    mainT wa wc K D sE C L L' ≤ (kappa wa wc K D sE * (C + L + L' + 1)) ^ 120 := by
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = kappa wa wc K D sE := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = κ * (C + L + L' + 1) := ⟨_, rfl⟩
  rw [← hκ, ← hYdef]
  have hκ' : κ = 4096 * (wa + wc + K + D + sE + 1) := hκ
  have hX : 1 ≤ C + L + L' + 1 := by omega
  have hκY : κ ≤ Y := by rw [hYdef]; exact Nat.le_mul_of_pos_right _ hX
  have hXY : C + L + L' + 1 ≤ Y := by rw [hYdef]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hY : 4096 ≤ Y := by omega
  have hwc : wc ≤ Y := by omega
  have hK : K ≤ Y := by omega
  have hD : D ≤ Y := by omega
  have hsE : sE ≤ Y := by omega
  have hC : C ≤ Y := by omega
  have hU : uB wa L ≤ Y := by
    unfold uB; rw [hYdef]; exact Nat.mul_le_mul (by omega) (by omega)
  have hY1 : Y ≤ Y ^ 1 := le_pow_one le_rfl
  have p : ∀ k, 4096 * Y ^ k ≤ Y ^ (k + 1) := pow_step hY
  have m : ∀ i j, i ≤ j → Y ^ i ≤ Y ^ j := fun i j h => pow_mono_le hY h
  have o : ∀ k, 1 ≤ Y ^ k := one_le_pow' hY
  -- the parameters of the run
  have hHB : heapB wa L ≤ Y ^ 6 := le_pow_mul (le_pow_one hU) (PL_le hY hU)
  have hF : fB wa C L ≤ Y ^ 7 := by
    unfold fB
    have : 4096 * Y ^ 6 ≤ Y ^ 7 := p 6
    have := m 1 6 (by omega)
    omega
  have hB : bB wa K C L ≤ Y ^ 8 := by
    unfold bB
    have : 4096 * Y ^ 7 ≤ Y ^ 8 := p 7
    have := m 1 7 (by omega)
    omega
  have hKC : K * C ≤ Y ^ 2 := le_pow_mul (le_pow_one hK) (le_pow_one hC)
  have hNC : nCells wa K C L ≤ Y ^ 3 := by
    unfold nCells
    have : 4096 * Y ^ 2 ≤ Y ^ 3 := p 2
    have := m 1 2 (by omega)
    omega
  have hNS : nSym wa K C L ≤ Y ^ 20 := by
    unfold nSym
    have i1 : bB wa K C L + nCells wa K C L + 1 ≤ Y ^ 9 := by
      have : 4096 * Y ^ 8 ≤ Y ^ 9 := p 8
      have := m 3 8 (by omega)
      have := o 8
      omega
    have i2 : fB wa C L * (bB wa K C L + nCells wa K C L + 1) ≤ Y ^ 16 := le_pow_mul hF i1
    have i3 : bB wa K C L + nCells wa K C L + 4 +
        fB wa C L * (bB wa K C L + nCells wa K C L + 1) ≤ Y ^ 17 := by
      have : 4096 * Y ^ 16 ≤ Y ^ 17 := p 16
      have := m 8 16 (by omega)
      have := m 3 16 (by omega)
      have := o 16
      omega
    exact le_pow_mul hNC i3
  have hM : bB wa K C L + nSym wa K C L ≤ Y ^ 21 := by
    have : 4096 * Y ^ 20 ≤ Y ^ 21 := p 20
    have := m 8 20 (by omega)
    omega
  -- one unit of the compiled code
  have hctrl : ctrlB D (bB wa K C L + nSym wa K C L) ≤ Y ^ 47 := by
    unfold ctrlB fetchB
    have h1 : 2 * D + 1 ≤ Y ^ 2 := by
      have : 4096 * Y ^ 1 ≤ Y ^ 2 := p 1
      omega
    have h2 : 14 * (bB wa K C L + nSym wa K C L) + 25 ≤ Y ^ 22 := by
      have : 4096 * Y ^ 21 ≤ Y ^ 22 := p 21
      have := o 21
      omega
    have h3 : (2 * D + 1) * (14 * (bB wa K C L + nSym wa K C L) + 25) ≤ Y ^ 24 :=
      le_pow_mul h1 h2
    have h4 : fcE (bB wa K C L + nSym wa K C L) (bB wa K C L + nSym wa K C L) ≤ Y ^ 46 :=
      fcE_le_pow hY hM
    have : 4096 * Y ^ 46 ≤ Y ^ 47 := p 46
    have := m 24 46 (by omega)
    have := m 21 46 (by omega)
    have := o 46
    omega
  have hprim : primB (bB wa K C L + nSym wa K C L) ≤ Y ^ 112 := by
    unfold primB
    obtain ⟨M, hMdef⟩ : ∃ M, M = bB wa K C L + nSym wa K C L := ⟨_, rfl⟩
    rw [← hMdef] at hM ⊢
    have hMM : M * M ≤ Y ^ 42 := le_pow_mul hM hM
    have hA : M * M + 3 * M + 2 ≤ Y ^ 43 := by
      have : 4096 * Y ^ 42 ≤ Y ^ 43 := p 42
      have := m 21 42 (by omega)
      have := o 42
      omega
    have hA2 : allocBound (M * M + 3 * M + 2) M ≤ Y ^ 89 :=
      allocBound_le_pow hY hA (hM.trans (m 21 43 (by omega)))
    have hf : fcE M M ≤ Y ^ 46 := fcE_le_pow hY hM
    have h5 : fcE M M + allocBound (M * M + 3 * M + 2) M + 100 * M + 100 ≤ Y ^ 90 := by
      have : 4096 * Y ^ 89 ≤ Y ^ 90 := p 89
      have := m 46 89 (by omega)
      have := m 21 89 (by omega)
      have := o 89
      omega
    have h6 : 2 * M + 10 ≤ Y ^ 22 := by
      have : 4096 * Y ^ 21 ≤ Y ^ 22 := p 21
      have := o 21
      omega
    exact le_pow_mul h6 h5
  have hq : qB D (bB wa K C L) (nSym wa K C L) ≤ Y ^ 113 := by
    unfold qB
    have : 4096 * Y ^ 112 ≤ Y ^ 113 := p 112
    have := m 47 112 (by omega)
    omega
  have hsK : sE + K * C ≤ Y ^ 3 := by
    have : 4096 * Y ^ 2 ≤ Y ^ 3 := p 2
    have := m 1 2 (by omega)
    omega
  have hcomp : (sE + K * C) * qB D (bB wa K C L) (nSym wa K C L) ≤ Y ^ 116 :=
    le_pow_mul hsK hq
  -- writing
  have hvis : visB (nSym wa K C L) ≤ Y ^ 44 := by
    unfold visB
    have h1 : lookupBound (nSym wa K C L) (nSym wa K C L) ≤ Y ^ 43 :=
      lookupBound_le_pow hY hNS hNS
    have h2 : 6 * nSym wa K C L + 14 ≤ Y ^ 21 := by
      have : 4096 * Y ^ 20 ≤ Y ^ 21 := p 20
      have := o 20
      omega
    have h3 : nSym wa K C L * (6 * nSym wa K C L + 14) ≤ Y ^ 41 := le_pow_mul hNS h2
    have : 4096 * Y ^ 43 ≤ Y ^ 44 := p 43
    have := m 41 43 (by omega)
    have := m 20 43 (by omega)
    have := o 43
    omega
  have hwL : wc * (L' + 1) ≤ Y ^ 2 := le_pow_mul (le_pow_one hwc) (le_pow_one (by omega))
  have hwr : wc * (L' + 1) * visB (nSym wa K C L) ≤ Y ^ 46 := le_pow_mul hwL hvis
  -- the sum
  unfold mainT
  have : 4096 * Y ^ 116 ≤ Y ^ 117 := p 116
  have := m 117 120 (by omega)
  have := m 6 116 (by omega)
  have := m 1 116 (by omega)
  have := m 8 116 (by omega)
  have := m 3 116 (by omega)
  have := m 46 116 (by omega)
  have := m 20 116 (by omega)
  have := o 116
  omega

end MainPoly

section Machine

variable {a b a' c : Ty}

/-- The step bound of `main` in closed form: `(κ (C + L + L' + 1)) ^ 120`. -/
def mainPoly (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c) (C L L' : ℕ) : ℕ :=
  (kappa (wt a') (wt c) (kP Pr E) (dP Pr E) (psize 1 (E Lv 0)) * (C + L + L' + 1)) ^ 120

/-- **The run of `main`**: from the input `ser a' x` alone on `inp` to the output `ser c v`
alone on `out` (registers empty), within `mainPoly` steps. -/
theorem main_exec (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c)
    (hE : ∀ x₁ x₂, Prog.Wf true [⟨a', x₁, x₂⟩] (E Ty.denote x₁) (E Lv x₂))
    (O : Oracle Signature.empty) {x : a'.denote} {v : c.denote} {tr : Trace Signature.empty}
    (hr : Runs O (Pr.proc Ty.denote) (E Ty.denote x) v tr) :
    ∃ n, Exec (mainProg Pr E) ((mainProg Pr E).body (mainProg Pr E).main)
        (inCfg .inp (ser a' x)) (inCfg .out (ser c v)) n ∧
      n ≤ mainPoly Pr E (Trace.localCost tr) (ser a' x).length (ser c v).length := by
  obtain ⟨fuel, he⟩ := hr
  obtain ⟨c', n, e, hn, rfl⟩ := (main_sat Pr E hE O he).exec
  exact ⟨n, e, hn.trans mainT_le⟩

/-- **On Turing machines**: the machine `toFinTM2 (mainProg Pr E) .inp .out` outputs `ser c v`
on input `ser a' x` within `mainPoly + 1` steps. The step count is computed by the interpreter
(`stepsOf`). -/
def main_tm (Pr : WfProc Signature.empty a b)
    (E : (var : Ty → Type) → var a' → Prog Signature.empty (a, b) var c)
    (hE : ∀ x₁ x₂, Prog.Wf true [⟨a', x₁, x₂⟩] (E Ty.denote x₁) (E Lv x₂))
    (O : Oracle Signature.empty) {x : a'.denote} {v : c.denote} {tr : Trace Signature.empty}
    (hr : Runs O (Pr.proc Ty.denote) (E Ty.denote x) v tr) :
    Turing.TM2OutputsInTime (toFinTM2 (mainProg Pr E) .inp .out) (ser a' x) (some (ser c v))
      (mainPoly Pr E (Trace.localCost tr) (ser a' x).length (ser c v).length + 1) where
  steps := stepsOf (mainProg Pr E)
    (mainPoly Pr E (Trace.localCost tr) (ser a' x).length (ser c v).length)
    (inCfg .inp (ser a' x)) + 1
  evals_in_steps := by
    obtain ⟨n, e, hn⟩ := main_exec Pr E hE O hr
    rw [stepsOf_eq _ e hn]
    exact (outputsInTime _ _ _ e).evals_in_steps
  steps_le_m := by
    obtain ⟨n, e, hn⟩ := main_exec Pr E hE O hr
    rw [stepsOf_eq _ e hn]
    exact Nat.add_le_add_right hn 1

end Machine

end GraphIso.TM
