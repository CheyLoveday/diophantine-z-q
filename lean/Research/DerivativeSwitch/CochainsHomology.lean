import Research.DerivativeSwitch.ContinuousSelmer
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Homology comparison for the continuous cochains used by the cones

Forgetting the topology of the cochain modules preserves kernels and
cokernels. Extension to integer degrees preserves homology in each
nonnegative degree. This identifies the local term of the Selmer diagram
with the continuous cohomology used by the local invariant.
-/

namespace Research.DerivativeSwitch.ContinuousSelmer

open CategoryTheory HomologicalComplex

universe u

variable {R G : Type u} [CommRing R] [TopologicalSpace R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The homology of the integer-indexed cochain model is Mathlib's
continuous cohomology with the topology on its carrier forgotten. -/
noncomputable def cochainsHomologyIso (X : TopRep.{u} R G) (n : ℕ) :
    (cochains X).homology (n : ℤ) ≅
      (forget₂ (TopModuleCat R) (ModuleCat R)).obj (continuousCohomology n X) := by
  let F := forget₂ (TopModuleCat R) (ModuleCat R)
  let A := TopRep.homogeneousCochains X
  let B := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj A
  have inherited : F.PreservesHomology := by infer_instance
  exact (B.extendHomologyIso ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) rfl) ≪≫
    (A.sc n).mapHomologyIso F

end Research.DerivativeSwitch.ContinuousSelmer
