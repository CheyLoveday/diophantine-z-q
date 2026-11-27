import ZInQKernel.Contrib.OneProof.Y3RelLemmaPSeesaw

/-!
Import check for the exact frozen comparison and its proved partial results.
The theorem statements for the outstanding glue remain explicit hypotheses.
-/

open Y3LemmaP

#check exists_open_pairClass_eq_of_geometricPairClass_eq
#check pairClass_eq_over_field_of_geometricPairClass_eq
#check canonicalPolarizationPullback_iff_fibreComparison

example (hRig : NormalizedPairFibreRigidity)
    (hFib : CanonicalPolarizationFibreComparison) (hExists : CanonicalPolarizationExists) :
    Y3FullThreeRepZ30Pol ↔ Y3RouteA.Y3FullThreeRepZ30 :=
  y3FullThreeRepZ30Pol_iff_of_relativePieces hRig hFib hExists
