module

public import GraphIso.Programs.Window
public import GraphIso.Reductions.Subgroup

/-!
# Represented instances and answers of the reduction programs

The reduction programs pass whole instances to a sub-solver and receive represented answers.

* `CosetData D`: a representative and a group with backend data in `D`.
* `InstData D`: the two strings, the window and the coset. Strings are never copied by the
  reductions; only the coset changes from one call to the next.
* `AnsOK DV n W σ G x y a`: the represented answer `a` is valid data of degree `n` (with
  backend data satisfying `DV`) and denotes exactly `iso W σ G x y`.
* `SubSolves X body DV sub P C s`: on every instance satisfying `P`, the sub-solver `sub`
  returns an `AnsOK` answer at cost at most `C I`, and its output groups have at most `s`
  generators. The reduction theorems take this as a hypothesis; the solver discharges it for
  its recursive call.
-/

@[expose] public section

namespace GraphIso

open Equiv Pointwise Cost

namespace Cost.Ty

/-- Represented cosets `σ • G`. -/
abbrev coset (D : Ty) : Ty := .prod perm (group D)
/-- Represented answers: `none` or a coset. -/
abbrev answer (D : Ty) : Ty := .option (coset D)
/-- The pair of strings `(x, y)`. -/
abbrev strs : Ty := .prod str str
/-- Represented instances. -/
abbrev inst (D : Ty) : Ty := .prod strs (.prod win (coset D))

end Cost.Ty

variable {D : Ty}

/-- A represented coset. -/
abbrev CosetData (D : Ty) := PermData × GroupData D.denote
/-- A represented answer. -/
abbrev AnswerData (D : Ty) := Option (CosetData D)
/-- A represented instance: strings, window, coset. -/
abbrev InstData (D : Ty) := (StrData × StrData) × WinData × CosetData D

/-- The positions listed in `pts`, as a window of `Fin n`. -/
def ptsSet (n : ℕ) (pts : List ℕ) : Set (Fin n) := {u | u.val ∈ pts}

theorem ptsSet_eq_denote (n : ℕ) (w : WinData) : ptsSet n w.1 = w.denote n := rfl

/-- The represented answer is valid and denotes exactly the solution set. -/
def AnsOK (DV : ℕ → GensData → D.denote → Prop) (n : ℕ) (W : Set (Fin n)) (σ : Perm (Fin n))
    (G : Subgroup (Perm (Fin n))) (x y : Fin n → ℕ) : AnswerData D → Prop
  | none => iso W σ G x y = ∅
  | some (τ, H) => τ.Valid n ∧ H.degree = n ∧ GroupValid DV n H.gens H.data ∧
      PermData.denote n τ • (GensData.denote n H.gens : Set (Perm (Fin n))) = iso W σ G x y

/-- The semantic answer denoted by a represented answer. -/
def AnswerData.denote (n : ℕ) (a : AnswerData D) : Answer (Fin n) :=
  a.map fun c => (PermData.denote n c.1, GensData.denote n c.2.gens)

section AnsOK

variable {DV : ℕ → GensData → D.denote → Prop} {n : ℕ} {W W₁ W₂ : Set (Fin n)}
  {σ : Perm (Fin n)} {G : Subgroup (Perm (Fin n))} {x y : Fin n → ℕ}

theorem AnsOK.isCorrect {a : AnswerData D} (h : AnsOK DV n W σ G x y a) :
    Answer.IsCorrect (a.denote n) W σ G x y := by
  rcases a with _ | ⟨τ, H⟩
  · exact h.symm
  · exact h.2.2.2

/-- A successful answer's group is the automorphism subgroup. -/
theorem AnsOK.eq_aut {τ : PermData} {H : GroupData D.denote} (hW : IsInvariant G W)
    (h : AnsOK DV n W σ G x y (some (τ, H))) : GensData.denote n H.gens = aut hW x :=
  eq_aut_of_iso_eq_smul hW h.2.2.2.symm

theorem AnsOK.union_none (h : AnsOK DV n W₁ σ G x y (none : AnswerData D)) :
    AnsOK DV n (W₁ ∪ W₂) σ G x y (none : AnswerData D) :=
  iso_union_of_eq_empty h

/-- Sequential composition of represented answers. -/
theorem AnsOK.union_some {τ : PermData} {H : GroupData D.denote} {a : AnswerData D}
    (h₁ : AnsOK DV n W₁ σ G x y (some (τ, H)))
    (h₂ : AnsOK DV n W₂ (PermData.denote n τ) (GensData.denote n H.gens) x y a) :
    AnsOK DV n (W₁ ∪ W₂) σ G x y a := by
  have e : iso (W₁ ∪ W₂) σ G x y = iso W₂ (PermData.denote n τ) (GensData.denote n H.gens) x y :=
    iso_union_of_eq_smul h₁.2.2.2.symm
  rcases a with _ | ⟨τ', H'⟩
  · exact e.trans h₂
  · exact ⟨h₂.1, h₂.2.1, h₂.2.2.1, h₂.2.2.2.trans e.symm⟩

/-- The input coset is the answer for the empty window. -/
theorem AnsOK.empty_window {σd : PermData} {Gd : GroupData D.denote} (hσ : σd.Valid n)
    (hG : Gd.degree = n) (hGv : GroupValid DV n Gd.gens Gd.data) :
    AnsOK DV n ∅ (PermData.denote n σd) (GensData.denote n Gd.gens) x y (some (σd, Gd)) :=
  ⟨hσ, hG, hGv, (iso_empty_window).symm⟩

end AnsOK

namespace InstData

variable (I : InstData D)

/-- The degree, read from the group. -/
def degree : ℕ := I.2.2.2.degree
/-- The decoded window. -/
def W : Set (Fin I.degree) := WinData.denote I.degree I.2.1
/-- The decoded representative. -/
def σ : Perm (Fin I.degree) := PermData.denote I.degree I.2.2.1
/-- The decoded group. -/
def G : Subgroup (Perm (Fin I.degree)) := GensData.denote I.degree I.2.2.2.gens
/-- The decoded source string. -/
def xs : Fin I.degree → ℕ := StrData.denote I.degree I.1.1
/-- The decoded target string. -/
def ys : Fin I.degree → ℕ := StrData.denote I.degree I.1.2

/-- Representation invariants of an instance, including invariance of the window. -/
structure Valid (DV : ℕ → GensData → D.denote → Prop) : Prop where
  win : WinData.Valid I.degree I.2.1
  rep : PermData.Valid I.degree I.2.2.1
  group : GroupValid DV I.degree I.2.2.2.gens I.2.2.2.data
  invariant : IsInvariant I.G I.W

/-- The answer is correct for the instance. -/
def OK (DV : ℕ → GensData → D.denote → Prop) (a : AnswerData D) : Prop :=
  AnsOK DV I.degree I.W I.σ I.G I.xs I.ys a

end InstData

/-- The sub-solver `sub` solves every instance satisfying `P` at cost at most `C I`, with output
groups of at most `s` generators. -/
def SubSolves {S : Signature} {a b : Ty} (X : Ctx S) (body : a.denote → Prog S (a, b) Ty.denote b)
    (DV : ℕ → GensData → D.denote → Prop)
    (sub : InstData D → Prog S (a, b) Ty.denote (Ty.answer D)) (P : InstData D → Prop)
    (C : InstData D → ℕ) (s : ℕ) : Prop :=
  ∀ I, P I → ∃ ans : AnswerData D, RunsWithin X body (sub I) ans (C I) ∧ I.OK DV ans ∧
    ∀ c : CosetData D, ans = some c → c.2.gens.length ≤ s

end GraphIso
