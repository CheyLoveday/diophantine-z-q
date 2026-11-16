import ZInQKernel.Contrib.OneProof.SGRDirectNV
open Polynomial CategoryTheory AlgebraicGeometry
open GlueDescent.B2Q NumberField
open HDec HDec.G0ModField HDec.PropTSRed HDec.PropTSGlue HDec.HeckeRestNV HDec.TSHecke LeafQM LeafQM.AV
#check @UnramifiedAt
#print UnramifiedAt
#check @intPolyAlg
example (E : Type) [Field E] [Algebra ℚ[X] E] : letI := intPolyAlg E; Algebra.IsIntegral ℤ[X] (integralClosure ℤ[X] E) := by
  letI := intPolyAlg E
  infer_instance
example : IsAlgClosed Qbar := inferInstance
example (K : Type) [Field K] (L : IntermediateField ℚ K) [CharZero K] : CharZero L := inferInstance
