import ZInQKernel.Contrib.OneProof.SGRDirectNVLocal
open IsLocalRing HDec
example (R L K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field L] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L] : Module.Flat R (integralClosure R L) := by
  infer_instance
#check @Submodule.torsion_eq_bot
#check @CharP.charP_to_charZero
