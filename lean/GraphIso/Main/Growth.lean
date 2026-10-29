module

public import GraphIso.Main.SimsSteps
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Growth classes

Stage 14j-6c-2 (`PLAN-14.md` §14.14, item 1). For an index type `ι` and a size `L : ι → ℕ`,
write `X i = L i + 1`.

* `PLB L e v` (**polylogarithmic**): `v i ≤ c · X i ^ e` for some `c` and every `i`.
* `QPB L d v` (**quasi-polynomial**): `v i ≤ 2 ^ (c · X i ^ d)` for some `c` and every `i`.

The closure lemmas:

* Both classes contain the constants and are closed under `+`, `max`, `min`, truncated `-` and
  `/` (bounded by the first argument).
* `QPB L d` is closed under `·` and constant powers. `PLB` adds the degrees under products and
  multiplies them under constant powers.
* Degrees can be raised (`lift`). `PLB L e ⊆ QPB L 1` (`PLB.qpb`). `Nat.log 2` and `Nat.clog 2`
  map `QPB L d` into `PLB L d`.
* The growth steps, for `x ∈ QPB L 1` and `y ∈ PLB L e`:
  - `x ^ y`, `y !` and `x.choose y` are in `QPB L (e + 1)`;
  - `2 ^ y` is in `QPB L e`.
* Re-indexing (`comp`). `supTo g b` and `∑_{j < b} g j` are bounded over the pairs `(i, j)` with
  `j ≤ b i` (respectively `j < b i`), where the bound variable is in `PLB` when `b` is
  (`bvar_le`, `bvar_lt`).
-/

@[expose] public section

namespace GraphIso.Growth

open GraphIso.Main

variable {ι κ : Type} {L : ι → ℕ}

/-- **Polylogarithmic growth**: `v i ≤ c (L i + 1)^e`. -/
def PLB (L : ι → ℕ) (e : ℕ) (v : ι → ℕ) : Prop := ∃ c, ∀ i, v i ≤ c * (L i + 1) ^ e

/-- **Quasi-polynomial growth**: `v i ≤ 2^(c (L i + 1)^d)`. -/
def QPB (L : ι → ℕ) (d : ℕ) (v : ι → ℕ) : Prop := ∃ c, ∀ i, v i ≤ 2 ^ (c * (L i + 1) ^ d)

theorem one_le_X (L : ι → ℕ) (e : ℕ) (i : ι) : 1 ≤ (L i + 1) ^ e := Nat.one_le_pow _ _ (by omega)

theorem self_le_two_pow (a : ℕ) : a ≤ 2 ^ a := (Nat.lt_two_pow_self).le

/-! ### Quasi-polynomial growth -/

namespace QPB

variable {d : ℕ} {f g : ι → ℕ}

theorem mono (h : QPB L d f) (hle : ∀ i, g i ≤ f i) : QPB L d g :=
  let ⟨c, hc⟩ := h; ⟨c, fun i => (hle i).trans (hc i)⟩

theorem const (a : ℕ) : QPB L d (fun _ => a) :=
  ⟨a, fun i => (self_le_two_pow a).trans
    (Nat.pow_le_pow_right (by omega) (Nat.le_mul_of_pos_right _ (one_le_X L d i)))⟩

theorem lift {d' : ℕ} (h : QPB L d f) (hd : d ≤ d') : QPB L d' f :=
  let ⟨c, hc⟩ := h
  ⟨c, fun i => (hc i).trans (Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hd)))⟩

theorem add (hf : QPB L d f) (hg : QPB L d g) : QPB L d (fun i => f i + g i) := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  refine ⟨c₁ + c₂ + 1, fun i => ?_⟩
  have hX := one_le_X L d i
  have e₁ : 2 ^ (c₁ * (L i + 1) ^ d) ≤ 2 ^ ((c₁ + c₂) * (L i + 1) ^ d) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))
  have e₂ : 2 ^ (c₂ * (L i + 1) ^ d) ≤ 2 ^ ((c₁ + c₂) * (L i + 1) ^ d) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))
  have e₃ : 2 ^ ((c₁ + c₂) * (L i + 1) ^ d) * 2 ≤ 2 ^ ((c₁ + c₂ + 1) * (L i + 1) ^ d) := by
    rw [← pow_succ]
    exact Nat.pow_le_pow_right (by omega) (by rw [add_one_mul]; omega)
  have := h₁ i
  have := h₂ i
  show f i + g i ≤ _
  omega

theorem mul (hf : QPB L d f) (hg : QPB L d g) : QPB L d (fun i => f i * g i) := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, fun i => ?_⟩
  rw [Nat.add_mul, pow_add]
  exact Nat.mul_le_mul (h₁ i) (h₂ i)

theorem max (hf : QPB L d f) (hg : QPB L d g) : QPB L d (fun i => Max.max (f i) (g i)) :=
  (hf.add hg).mono fun i => by simp only [Nat.max_def]; split <;> omega

theorem min_left (hf : QPB L d f) : QPB L d (fun i => Min.min (f i) (g i)) :=
  hf.mono fun _ => Nat.min_le_left _ _

theorem sub (hf : QPB L d f) : QPB L d (fun i => f i - g i) := hf.mono fun _ => Nat.sub_le _ _

theorem div (hf : QPB L d f) : QPB L d (fun i => f i / g i) := hf.mono fun _ => Nat.div_le_self _ _

theorem pow_const (n : ℕ) (hf : QPB L d f) : QPB L d (fun i => f i ^ n) := by
  obtain ⟨c, h⟩ := hf
  refine ⟨c * n, fun i => ?_⟩
  calc f i ^ n ≤ (2 ^ (c * (L i + 1) ^ d)) ^ n := Nat.pow_le_pow_left (h i) n
    _ = 2 ^ (c * n * (L i + 1) ^ d) := by rw [← pow_mul]; ring_nf

theorem clog (hf : QPB L d f) : QPB L d (fun i => Nat.clog 2 (f i)) :=
  hf.mono fun i => (Nat.clog_le_of_le_pow (self_le_two_pow (f i))).trans le_rfl

theorem log (hf : QPB L d f) : QPB L d (fun i => Nat.log 2 (f i)) :=
  hf.mono fun _ => Nat.log_le_self _ _

theorem comp (h : QPB L d f) (π : κ → ι) : QPB (fun x => L (π x)) d (fun x => f (π x)) :=
  let ⟨c, hc⟩ := h; ⟨c, fun x => hc (π x)⟩

end QPB

/-! ### Polylogarithmic growth -/

namespace PLB

variable {e : ℕ} {f g : ι → ℕ}

theorem mono (h : PLB L e f) (hle : ∀ i, g i ≤ f i) : PLB L e g :=
  let ⟨c, hc⟩ := h; ⟨c, fun i => (hle i).trans (hc i)⟩

theorem const (a : ℕ) : PLB L e (fun _ => a) :=
  ⟨a, fun i => Nat.le_mul_of_pos_right _ (one_le_X L e i)⟩

theorem lift {e' : ℕ} (h : PLB L e f) (he : e ≤ e') : PLB L e' f :=
  let ⟨c, hc⟩ := h
  ⟨c, fun i => (hc i).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) he))⟩

theorem add (hf : PLB L e f) (hg : PLB L e g) : PLB L e (fun i => f i + g i) := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  exact ⟨c₁ + c₂, fun i => by rw [Nat.add_mul]; exact Nat.add_le_add (h₁ i) (h₂ i)⟩

theorem mul {e' : ℕ} (hf : PLB L e f) (hg : PLB L e' g) : PLB L (e + e') (fun i => f i * g i) := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, fun i => ?_⟩
  calc f i * g i ≤ (c₁ * (L i + 1) ^ e) * (c₂ * (L i + 1) ^ e') := Nat.mul_le_mul (h₁ i) (h₂ i)
    _ = c₁ * c₂ * (L i + 1) ^ (e + e') := by rw [pow_add]; ring

theorem const_mul (a : ℕ) (hf : PLB L e f) : PLB L e (fun i => a * f i) :=
  let ⟨c, hc⟩ := hf
  ⟨a * c, fun i => by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hc i)⟩

theorem mul_const (a : ℕ) (hf : PLB L e f) : PLB L e (fun i => f i * a) :=
  (hf.const_mul a).mono fun _ => (Nat.mul_comm _ _).le

theorem max (hf : PLB L e f) (hg : PLB L e g) : PLB L e (fun i => Max.max (f i) (g i)) :=
  (hf.add hg).mono fun i => by simp only [Nat.max_def]; split <;> omega

theorem min_left (hf : PLB L e f) : PLB L e (fun i => Min.min (f i) (g i)) :=
  hf.mono fun _ => Nat.min_le_left _ _

theorem sub (hf : PLB L e f) : PLB L e (fun i => f i - g i) := hf.mono fun _ => Nat.sub_le _ _

theorem div (hf : PLB L e f) : PLB L e (fun i => f i / g i) := hf.mono fun _ => Nat.div_le_self _ _

theorem pow_const (n : ℕ) (hf : PLB L e f) : PLB L (e * n) (fun i => f i ^ n) := by
  obtain ⟨c, h⟩ := hf
  refine ⟨c ^ n, fun i => ?_⟩
  calc f i ^ n ≤ (c * (L i + 1) ^ e) ^ n := Nat.pow_le_pow_left (h i) n
    _ = c ^ n * (L i + 1) ^ (e * n) := by rw [mul_pow, ← pow_mul]

/-- `Nat.clog 2` maps quasi-polynomial into polylogarithmic growth. -/
theorem clog {d : ℕ} (hf : QPB L d f) : PLB L d (fun i => Nat.clog 2 (f i)) :=
  let ⟨c, hc⟩ := hf; ⟨c, fun i => Nat.clog_le_of_le_pow (hc i)⟩

/-- `Nat.log 2` maps quasi-polynomial into polylogarithmic growth. -/
theorem log {d : ℕ} (hf : QPB L d f) : PLB L d (fun i => Nat.log 2 (f i)) :=
  (clog hf).mono fun _ => Nat.log_le_clog _ _

theorem comp (h : PLB L e f) (π : κ → ι) : PLB (fun x => L (π x)) e (fun x => f (π x)) :=
  let ⟨c, hc⟩ := h; ⟨c, fun x => hc (π x)⟩

/-- **Polylogarithmic is quasi-polynomial of degree one**: `c X^e ≤ 2^{(c + e) X}`. -/
theorem qpb (h : PLB L e f) : QPB L 1 f := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c + e, fun i => (hc i).trans ?_⟩
  have h1 : c ≤ 2 ^ c := self_le_two_pow c
  have h2 : (L i + 1) ^ e ≤ 2 ^ (e * (L i + 1)) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (self_le_two_pow _) e
  calc c * (L i + 1) ^ e ≤ 2 ^ c * 2 ^ (e * (L i + 1)) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (c + e * (L i + 1)) := (pow_add _ _ _).symm
    _ ≤ 2 ^ ((c + e) * (L i + 1) ^ 1) :=
      Nat.pow_le_pow_right (by omega) (by rw [pow_one, Nat.add_mul]; nlinarith)

/-- `PLB L e ⊆ QPB L d` for `d ≥ 1`. -/
theorem qpb' {d : ℕ} (h : PLB L e f) (hd : 1 ≤ d) : QPB L d f := h.qpb.lift hd

/-- **The bound variable of `supTo`** is polylogarithmic when its bound is. -/
theorem bvar_le {b : ι → ℕ} (hb : PLB L e b) :
    PLB (fun p : {p : ι × ℕ // p.2 ≤ b p.1} => L p.1.1) e (fun p => p.1.2) :=
  let ⟨c, hc⟩ := hb; ⟨c, fun p => p.2.trans (hc p.1.1)⟩

/-- **The bound variable of a sum over `List.range`** is polylogarithmic when its length is. -/
theorem bvar_lt {b : ι → ℕ} (hb : PLB L e b) :
    PLB (fun p : {p : ι × ℕ // p.2 < b p.1} => L p.1.1) e (fun p => p.1.2) :=
  let ⟨c, hc⟩ := hb; ⟨c, fun p => p.2.le.trans (hc p.1.1)⟩

end PLB

/-! ### The growth steps -/

namespace QPB

variable {e : ℕ} {f g : ι → ℕ}

/-- **A quasi-polynomial base to a polylogarithmic power**: `2^{c₁ X}` to the `c₂ X^e`. -/
theorem pow (hf : QPB L 1 f) (hg : PLB L e g) : QPB L (e + 1) (fun i => f i ^ g i) := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  refine ⟨c₁ * c₂, fun i => ?_⟩
  calc f i ^ g i ≤ (2 ^ (c₁ * (L i + 1) ^ 1)) ^ (c₂ * (L i + 1) ^ e) :=
        (Nat.pow_le_pow_left (h₁ i) _).trans (Nat.pow_le_pow_right
          (Nat.one_le_two_pow) (h₂ i))
    _ = 2 ^ (c₁ * c₂ * (L i + 1) ^ (e + 1)) := by rw [← pow_mul]; ring_nf

/-- **The factorial of a polylogarithmic value**, through `y! ≤ y^y`. -/
theorem factorial (hg : PLB L e g) : QPB L (e + 1) (fun i => (g i).factorial) :=
  (pow hg.qpb hg).mono fun _ => Nat.factorial_le_pow _

/-- **A binomial with a polylogarithmic lower index**, through `x.choose y ≤ x^y`. -/
theorem choose (hf : QPB L 1 f) (hg : PLB L e g) : QPB L (e + 1) (fun i => (f i).choose (g i)) :=
  (pow hf hg).mono fun _ => Nat.choose_le_pow _ _

/-- **Two to a polylogarithmic power.** -/
theorem two_pow (hg : PLB L e g) : QPB L e (fun i => 2 ^ g i) :=
  let ⟨c, hc⟩ := hg; ⟨c, fun i => Nat.pow_le_pow_right (by omega) (hc i)⟩

/-- **`supTo`**, bounded over the pairs `(i, j)` with `j ≤ b i`. -/
theorem supTo {d : ℕ} {g : ι → ℕ → ℕ} {b : ι → ℕ}
    (h : QPB (fun p : {p : ι × ℕ // p.2 ≤ b p.1} => L p.1.1) d (fun p => g p.1.1 p.1.2)) :
    QPB L d (fun i => Main.supTo (g i) (b i)) :=
  let ⟨c, hc⟩ := h
  ⟨c, fun i => supTo_le fun j hj => hc ⟨(i, j), hj⟩⟩

theorem sum_range_le {g : ℕ → ℕ} {B : ℕ} :
    ∀ n, (∀ j < n, g j ≤ B) → ((List.range n).map g).sum ≤ n * B
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    have := sum_range_le n fun j hj => h j (by omega)
    have := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [Nat.succ_mul]
    omega

/-- **A sum over `List.range`**, bounded over the pairs `(i, j)` with `j < b i`. -/
theorem sum_range {d : ℕ} {g : ι → ℕ → ℕ} {b : ι → ℕ} (hb : QPB L d b)
    (h : QPB (fun p : {p : ι × ℕ // p.2 < b p.1} => L p.1.1) d (fun p => g p.1.1 p.1.2)) :
    QPB L d (fun i => ((List.range (b i)).map (g i)).sum) := by
  obtain ⟨c, hc⟩ := h
  refine (hb.mul (⟨c, fun i => le_rfl⟩ : QPB L d fun i => 2 ^ (c * (L i + 1) ^ d))).mono
    fun i => sum_range_le _ fun j hj => hc ⟨(i, j), hj⟩

end QPB

end GraphIso.Growth
