module

public import GraphIso.TM.Write

/-!
# Environments

Stage 17e (`PLAN-17.md` §8). The compiled code keeps the pointers of the variables in scope on
the stack `env`, newest on top.

* **`encNums ns`**: the numbers `ns` on a stack, the first on top; `envEnc ls = encNums
  ls.reverse` is a frame whose level `k` is `ls[k]` (the last level on top).
* **`moveN j a b`**: moves `j` numbers from `a` onto `b`, one by one, so they end in reverse
  order (`moveN_sat`).
* **`fetchTo j dst`**: copies the number at offset `j` of `env` (`0` is the top) onto `dst`,
  restoring `env` (`fetchTo_sat`, within `fetchB j E` steps for numbers of at most `E` bits).
* **`fetchLv d k dst`**: copies the level `k` of a frame of depth `d` (`fetchLv_sat`).
-/

@[expose] public section

namespace GraphIso.TM

variable {P : Type} {prog : Program Stk Sym Rg P}

/-- The numbers `ns` on a stack, the first on top. -/
def encNums (ns : List (List Bool)) : List Sym := (ns.map fun l => bits l ++ [.nd]).flatten

@[simp] theorem encNums_nil : encNums [] = [] := rfl

@[simp] theorem encNums_cons (l : List Bool) (ns : List (List Bool)) :
    encNums (l :: ns) = bits l ++ .nd :: encNums ns := by
  simp [encNums]

theorem encNums_append (ns ms : List (List Bool)) :
    encNums (ns ++ ms) = encNums ns ++ encNums ms := by
  simp [encNums]

/-- A frame: level `k` is `ls[k]`, the last level on top. -/
def envEnc (ls : List (List Bool)) : List Sym := encNums ls.reverse

@[simp] theorem envEnc_nil : envEnc [] = [] := rfl

theorem envEnc_concat (ls : List (List Bool)) (l : List Bool) :
    envEnc (ls ++ [l]) = bits l ++ .nd :: envEnc ls := by
  simp [envEnc]

/-- Move `j` numbers from `a` onto `b` through `t0`, one by one. -/
def moveN : ℕ → Stk → Stk → Code Stk Sym Rg P
  | 0, _, _ => .skip
  | j + 1, a, b => .seq (moveNum2 a b .t0) (moveN j a b)

theorem moveN_sat {a b : Stk} (hab : a ≠ b) (ha : a ≠ .t0) (hb : b ≠ .t0) :
    ∀ (ns : List (List Bool)) (c : Cfg Stk Sym Rg) (rest : List Sym), c.regs = Regs.empty →
      c.stk a = encNums ns ++ rest →
      Sat prog (moveN ns.length a b) c ((ns.map fun l => 12 * l.length + 20).sum + 1)
        fun c' => c'.regs = Regs.empty ∧ c'.stk a = rest ∧
          c'.stk b = encNums ns.reverse ++ c.stk b ∧ ∀ j, j ≠ a → j ≠ b → c'.stk j = c.stk j
  | [], c, rest, hv, hc => (Sat.skip ⟨hv, by simpa using hc, by simp, fun _ _ _ => rfl⟩).mono
      (by simp) fun _ h => h
  | l :: ns, c, rest, hv, hc => by
    have hc' : c.stk a = bits l ++ .nd :: (encNums ns ++ rest) := by rw [hc]; simp
    refine Sat.seq_le (moveNum2_sat hab ha hb hv hc') (by simp; omega)
      fun c₁ ⟨hr₁, ha₁, hb₁, hj₁⟩ => ?_
    refine (moveN_sat hab ha hb ns c₁ rest hr₁ ha₁).mono (by simp; omega)
      fun c' ⟨hr', ha', hb', hj'⟩ => ⟨hr', ha', ?_, fun j hja hjb => ?_⟩
    · rw [hb', hb₁]; simp [encNums_append]
    · rw [hj' j hja hjb, hj₁ j hja hjb]

theorem sum_map_le_mul {α : Type} (f : α → ℕ) (k : ℕ) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ k) → (l.map f).sum ≤ l.length * k
  | [], _ => by simp
  | x :: l, h => by
    have h₁ := h x (by simp)
    have h₂ := sum_map_le_mul f k l fun y hy => h y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Copy the number at offset `j` of `env` onto `dst`, through `t1` and `t0`. -/
def fetchTo (j : ℕ) (dst : Stk) : Code Stk Sym Rg P :=
  .seq (moveN j .env .t1) (.seq (copyNum .env dst .t0) (moveN j .t1 .env))

/-- The step bound of `fetchTo j` for numbers of at most `E` bits. -/
def fetchB (j E : ℕ) : ℕ := (2 * j + 1) * (14 * E + 25)

theorem fetchTo_sat {dst : Stk} (hd₁ : dst ≠ .env) (hd₂ : dst ≠ .t0) (hd₃ : dst ≠ .t1)
    {c : Cfg Stk Sym Rg} {ns : List (List Bool)} {l : List Bool} {rest : List Sym} {E : ℕ}
    (hv : c.regs = Regs.empty) (he : c.stk .env = encNums ns ++ bits l ++ .nd :: rest)
    (hE : ∀ m ∈ ns, m.length ≤ E) (hl : l.length ≤ E) :
    Sat prog (fetchTo ns.length dst) c (fetchB ns.length E) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk dst = bits l ++ .nd :: c.stk dst ∧
        ∀ j, j ≠ dst → c'.stk j = c.stk j := by
  have hS := sum_map_le_mul (fun m : List Bool => 12 * m.length + 20) (12 * E + 20) ns
    fun m hm => by have := hE m hm; omega
  have hS' := sum_map_le_mul (fun m : List Bool => 12 * m.length + 20) (12 * E + 20) ns.reverse
    fun m hm => by have := hE m (List.mem_reverse.1 hm); omega
  rw [List.length_reverse] at hS'
  have hj : ns.length * (12 * E + 20) ≤ ns.length * (14 * E + 25) :=
    Nat.mul_le_mul_left _ (by omega)
  have hB : fetchB ns.length E = 2 * (ns.length * (14 * E + 25)) + (14 * E + 25) := by
    unfold fetchB; ring
  unfold fetchTo
  refine Sat.seq_le (moveN_sat (by decide) (by decide) (by decide) ns c (bits l ++ .nd :: rest)
    hv (by rw [he, List.append_assoc])) (by omega) fun c₁ ⟨hr₁, he₁, ht₁, hj₁⟩ => ?_
  refine Sat.seq_le (copyNum_sat (Ne.symm hd₁) (by decide) hd₂ hr₁ he₁) (by omega)
    fun c₂ ⟨hr₂, hd₂', hj₂⟩ => ?_
  have ht₂ : c₂.stk .t1 = encNums ns.reverse ++ c.stk .t1 := by
    rw [hj₂ .t1 (Ne.symm hd₃), ht₁]
  have e := moveN_sat (prog := prog) (a := .t1) (b := .env) (by decide) (by decide) (by decide)
    ns.reverse c₂
    (c.stk .t1) hr₂ ht₂
  rw [List.length_reverse] at e
  refine e.mono (by omega) fun c' ⟨hr', ht', he', hj'⟩ => ⟨hr', ?_, fun j hjd => ?_⟩
  · rw [hj' dst hd₃ hd₁, hd₂', hj₁ dst hd₁ hd₃]
  · by_cases hje : j = .env
    · subst hje
      rw [he', List.reverse_reverse, hj₂ .env (Ne.symm hd₁), he₁, he, List.append_assoc]
    by_cases hjt : j = .t1
    · subst hjt; rw [ht']
    rw [hj' j hjt hje, hj₂ j hjd, hj₁ j hje hjt]

/-- Copy the level `k` of a frame of depth `d` onto `dst`. -/
def fetchLv (d k : ℕ) (dst : Stk) : Code Stk Sym Rg P := fetchTo (d - 1 - k) dst

theorem fetchLv_sat {dst : Stk} (hd₁ : dst ≠ .env) (hd₂ : dst ≠ .t0) (hd₃ : dst ≠ .t1)
    {c : Cfg Stk Sym Rg} {ls : List (List Bool)} {k : ℕ} (hk : k < ls.length) {rest : List Sym}
    {E : ℕ} (hv : c.regs = Regs.empty) (he : c.stk .env = envEnc ls ++ rest)
    (hE : ∀ m ∈ ls, m.length ≤ E) :
    Sat prog (fetchLv ls.length k dst) c (fetchB (ls.length - 1 - k) E) fun c' =>
      c'.regs = Regs.empty ∧ c'.stk dst = bits ls[k] ++ .nd :: c.stk dst ∧
        ∀ j, j ≠ dst → c'.stk j = c.stk j := by
  have key : envEnc ls = encNums (ls.drop (k + 1)).reverse ++ bits ls[k] ++
      .nd :: encNums (ls.take k).reverse := by
    have e := List.take_append_drop k ls
    rw [List.drop_eq_getElem_cons hk] at e
    have e' : envEnc ls = envEnc (ls.take k ++ ls[k] :: ls.drop (k + 1)) := by rw [e]
    rw [e', envEnc, List.reverse_append, List.reverse_cons, encNums_append, encNums_append]
    simp only [encNums_cons, encNums_nil, List.append_assoc, List.cons_append, List.nil_append]
  have hlen : (ls.drop (k + 1)).reverse.length = ls.length - 1 - k := by simp; omega
  have he' : c.stk .env = encNums (ls.drop (k + 1)).reverse ++ bits ls[k] ++
      .nd :: (encNums (ls.take k).reverse ++ rest) := by
    rw [he, key]; simp
  unfold fetchLv
  rw [← hlen]
  exact fetchTo_sat hd₁ hd₂ hd₃ hv he'
    (fun m hm => hE m (List.mem_of_mem_drop (List.mem_reverse.1 hm)))
    (hE _ (List.getElem_mem hk))

end GraphIso.TM
