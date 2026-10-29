module

public import GraphIso.Graph.Domain
public import GraphIso.Reductions.BlockAction

/-!
# Permutation data from functions

`PermData.ofFun D f f'` lists `f` and `f'` on `0, …, D − 1`. When `f` and `f'` are mutually
inverse maps of `{0, …, D − 1}` it is valid, and its permutation acts by `f`
(`act_denote_ofFun`). The data the algorithm builds are of this form:

* `indData`: the induced action of `g` on the domain of a layer step;
* `liftData`: the canonical lift;
* `swapData`: a transposition;
* `isoData`: the isomorphism read off a swapping element.
-/

@[expose] public section

namespace GraphIso.Graph

open Equiv Sims

/-- The data listing `f` and `f'` on `0, …, D − 1`. -/
def PermData.ofFun (D : ℕ) (f f' : ℕ → ℕ) : PermData :=
  (((List.range D).map f).toArray, ((List.range D).map f').toArray)

theorem get_ofFun_fst {D : ℕ} {f f' : ℕ → ℕ} {i : ℕ} (hi : i < D) :
    get (PermData.ofFun D f f').1 i = f i := by
  simp [PermData.ofFun, get, hi]

theorem get_ofFun_snd {D : ℕ} {f f' : ℕ → ℕ} {i : ℕ} (hi : i < D) :
    get (PermData.ofFun D f f').2 i = f' i := by
  simp [PermData.ofFun, get, hi]

/-- Mutually inverse maps of `{0, …, D − 1}`. -/
structure InvPair (D : ℕ) (f f' : ℕ → ℕ) : Prop where
  lt : ∀ i < D, f i < D
  lt' : ∀ i < D, f' i < D
  left : ∀ i < D, f' (f i) = i
  right : ∀ i < D, f (f' i) = i

theorem valid_ofFun {D : ℕ} {f f' : ℕ → ℕ} (h : InvPair D f f') :
    (PermData.ofFun D f f').Valid D := by
  refine ⟨by simp [PermData.ofFun], by simp [PermData.ofFun], fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · rw [get_ofFun_fst hi]; exact h.lt i hi
  · rw [get_ofFun_snd hi]; exact h.lt' i hi
  · rw [get_ofFun_fst hi, get_ofFun_snd (h.lt i hi)]; exact h.left i hi
  · rw [get_ofFun_snd hi, get_ofFun_fst (h.lt' i hi)]; exact h.right i hi

theorem act_denote_ofFun {D : ℕ} {f f' : ℕ → ℕ} (h : InvPair D f f') {i : ℕ} (hi : i < D) :
    act (PermData.denote D (PermData.ofFun D f f')) i = f i := by
  rw [act_of_lt _ hi, PermData.val_denote_apply (valid_ofFun h), get_ofFun_fst hi]

/-- Two permutations agreeing as maps on `{0, …, D − 1}` are equal. -/
theorem perm_eq_of_act {D : ℕ} {g h : Perm (Fin D)} (e : ∀ i < D, act g i = act h i) : g = h := by
  ext x
  have := e x x.2
  rwa [act_of_lt _ x.2, act_of_lt _ x.2] at this

theorem denote_ofFun_eq {D : ℕ} {f f' : ℕ → ℕ} (h : InvPair D f f') {g : Perm (Fin D)}
    (e : ∀ i < D, act g i = f i) : PermData.denote D (PermData.ofFun D f f') = g :=
  perm_eq_of_act fun i hi => by rw [act_denote_ofFun h hi, e i hi]

/-- The maps of a permutation and its inverse form an inverse pair. -/
theorem invPair_act {D : ℕ} (g : Perm (Fin D)) : InvPair D (act g) (act g⁻¹) :=
  ⟨fun _ hi => act_lt g hi, fun _ hi => act_lt g⁻¹ hi, fun i _ => act_inv_act g i,
    fun i _ => act_act_inv g i⟩

/-- The data of a valid permutation give the maps of its permutation. -/
theorem get_fst_of_valid {D : ℕ} {d : PermData} (hd : d.Valid D) {i : ℕ} (hi : i < D) :
    get d.1 i = act (PermData.denote D d) i := by
  rw [act_of_lt _ hi, PermData.val_denote_apply hd]

theorem get_snd_of_valid {D : ℕ} {d : PermData} (hd : d.Valid D) {i : ℕ} (hi : i < D) :
    get d.2 i = act (PermData.denote D d)⁻¹ i := by
  rw [act_of_lt _ hi, PermData.val_denote_inv_apply hd]

end GraphIso.Graph
