import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ZInQ.Manuscript.RC.HCMV21

/-- Piece (iii), the conclusion to be proved for geometric reduction at the chosen
place. Instantiate `C` by the ideal class group, `X` by CM points with the chosen
level orientations, and `Y` by optimal embeddings with those level orientations
and the one residue-field orientation. This is a glue interface, not a printed input. -/
def OrientedCorrespondence {C X Y : Type*} [Group C] [MulAction C X] [MulAction C Y]
    (red : X → Y) : Prop :=
  Function.Bijective red ∧ ∀ (c : C) (x : X), red (c • x) = c • red x

/-- The formal torsor step. The two orbit maps are bijective at the reference
points; this is a property of the actions independently of the reduction map. -/
theorem orientedCorrespondence_of_orbit_maps {C X Y : Type*} [Group C]
    [MulAction C X] [MulAction C Y] (red : X → Y) (x₀ : X)
    (hx : Function.Bijective (fun c : C => c • x₀))
    (hy : Function.Bijective (fun c : C => c • red x₀))
    (he : ∀ (c : C) (x : X), red (c • x) = c • red x) : OrientedCorrespondence (C := C) red := by
  refine ⟨⟨?_, ?_⟩, he⟩
  · intro x y hxy
    obtain ⟨c, rfl⟩ := hx.2 x
    obtain ⟨d, rfl⟩ := hx.2 y
    have h := hy.1 ((he c x₀).symm.trans (hxy.trans (he d x₀)))
    rw [h]
  · intro y
    obtain ⟨c, rfl⟩ := hy.2 y
    exact ⟨c • x₀, he c x₀⟩

open scoped BigOperators in
/-- The reindexing used for the reference orientation in Appendix F (tex
9279–9295). The additivity of evaluation and reduction is a separate step. -/
theorem weighted_sum_of_equivariant_reduction {C X Y A : Type*} [Group C] [Fintype C]
    [MulAction C X] [MulAction C Y] [AddCommGroup A] (red : X → Y) (x₀ : X)
    (he : ∀ c : C, red (c • x₀) = c • red x₀) (P : Y → A) (χ : C → ℤ) :
    ∑ c : C, χ c • P (red (c • x₀)) = ∑ c : C, χ c • P (c • red x₀) := by
  exact Finset.sum_congr rfl fun c _ => congrArg (fun y => χ c • P y) (he c)

end ZInQ.Manuscript.RC.HCMV21
