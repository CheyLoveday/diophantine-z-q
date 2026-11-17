import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.DegHomogPolyFLT
import ZInQKernel.Contrib.OneProof.CharPolyCharP

/-- Composition with charpoly-p's assembly (scratch only): the open field, with no hypothesis. -/
theorem charPolyIndepOfEllAlgClosed_proof : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'
    ZInQ.Contrib.OneProof.DegPolyFLT.degHomogPoly

#print axioms charPolyIndepOfEllAlgClosed_proof

#discharges
