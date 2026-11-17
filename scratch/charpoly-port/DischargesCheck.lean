import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.DegHomogPolyFLT
import ZInQKernel.Contrib.OneProof.CharPolyCharP

/-- Composition with charpoly-p's assembly (scratch only). -/
theorem charPolyIndepOfEllAlgClosed_of_finrankGeneric
    (h : ZInQ.Contrib.OneProof.DegPolyFLT.FinrankGenericEqDegEnd) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  ZInQ.Contrib.OneProof.CharPolyCharP.charPolyIndepOfEllAlgClosed_of_degHomogPoly'
    (ZInQ.Contrib.OneProof.DegPolyFLT.degHomogPoly_of_finrankGeneric h)

#discharges
