module

public import GraphIso.Reductions.SequentialProg
public import GraphIso.GroupOps.Interface

/-!
# Block systems

A block list `bs` for the window `w` lists nonempty blocks that together list the window's
points exactly once (`IsBlockList`). The group `G` permutes the blocks when every element maps
each block into a block (`PermutesBlocks`); this is the certificate the block reduction
accepts, and the induced action on blocks is built from it.

* `blockKernel G bs`: the elements of `G` mapping every block into itself, a subgroup of `G`
  (`blockKernel_le`). It is the kernel of the action on the blocks.
* `seqInputs_of_blocks`: every block is invariant under any subgroup of the block kernel, and
  the blocks cover the window; these are the hypotheses of the sequential reduction.

Correctness of the block reduction needs only these facts; `PermutesBlocks` is what makes the
action on blocks a homomorphism, and hence what makes `K` computable by an induced action.
-/

@[expose] public section

namespace GraphIso

open Equiv

variable {n : ℕ}

/-- `bs` partitions the window into nonempty blocks, listing every point exactly once. -/
def IsBlockList (w : WinData) (bs : List (List ℕ)) : Prop :=
  bs.flatten.Perm w.1 ∧ ∀ b ∈ bs, b ≠ []

/-- `G` permutes the blocks: every element maps each block into a block. -/
def PermutesBlocks (G : Subgroup (Perm (Fin n))) (bs : List (List ℕ)) : Prop :=
  ∀ g ∈ G, ∀ b ∈ bs, ∃ b' ∈ bs, ∀ u : Fin n, u.val ∈ b → (g u).val ∈ b'

/-- The kernel of the action on the blocks: the elements of `G` mapping every block into
itself. -/
def blockKernel (G : Subgroup (Perm (Fin n))) (bs : List (List ℕ)) : Subgroup (Perm (Fin n)) where
  carrier := {g | g ∈ G ∧ ∀ b ∈ bs, ∀ u : Fin n, u.val ∈ b → (g u).val ∈ b}
  one_mem' := ⟨G.one_mem, fun _ _ _ hu => hu⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    exact ⟨mul_mem hg hh, fun b hb u hu => hg' b hb _ (hh' b hb u hu)⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨inv_mem hg, fun b hb u hu => ?_⟩
    have himg := image_eq_of_mapsTo_of_finite (W := ptsSet n b) (Set.toFinite _)
      (g := g) fun v hv => hg' b hb v hv
    have hu' : u ∈ g '' ptsSet n b := by rw [himg]; exact hu
    obtain ⟨v, hv, rfl⟩ := hu'
    have hgv : g⁻¹ (g v) = v := by simp
    rw [hgv]
    exact hv

theorem mem_blockKernel {G : Subgroup (Perm (Fin n))} {bs : List (List ℕ)} {g : Perm (Fin n)} :
    g ∈ blockKernel G bs ↔ g ∈ G ∧ ∀ b ∈ bs, ∀ u : Fin n, u.val ∈ b → (g u).val ∈ b := Iff.rfl

theorem blockKernel_le (G : Subgroup (Perm (Fin n))) (bs : List (List ℕ)) :
    blockKernel G bs ≤ G := fun _ h => h.1

/-- The blocks supply the hypotheses of the sequential reduction, for any subgroup of the
block kernel, and cover the window. -/
theorem seqInputs_of_blocks {G H : Subgroup (Perm (Fin n))} {w : WinData} (hw : w.Valid n)
    {bs : List (List ℕ)} (hbs : IsBlockList w bs) (hH : H ≤ blockKernel G bs) :
    (∀ b ∈ bs, b.Nodup ∧ (∀ i ∈ b, i < n) ∧ IsInvariant H (ptsSet n b)) ∧
      seqUnion (bs.map (ptsSet n)) = w.denote n := by
  obtain ⟨hperm, -⟩ := hbs
  have hnd : bs.flatten.Nodup := hperm.nodup_iff.2 hw.nodup
  have hmem : ∀ i, i ∈ bs.flatten ↔ i ∈ w.1 := fun i => hperm.mem_iff
  refine ⟨fun b hb => ⟨?_, ?_, ?_⟩, ?_⟩
  · exact (List.nodup_flatten.1 hnd).1 b hb
  · intro i hi
    exact hw.lt i ((hmem i).1 (List.mem_flatten.2 ⟨b, hb, hi⟩))
  · intro g hg u hu
    exact ((hH hg).2 b hb u hu)
  · ext u
    simp only [mem_seqUnion, List.mem_map, ptsSet]
    constructor
    · rintro ⟨_, ⟨b, hb, rfl⟩, hu⟩
      exact (hmem u.val).1 (List.mem_flatten.2 ⟨b, hb, hu⟩)
    · intro hu
      obtain ⟨b, hb, hu⟩ := List.mem_flatten.1 ((hmem u.val).2 hu)
      exact ⟨_, ⟨b, hb, rfl⟩, hu⟩

end GraphIso
