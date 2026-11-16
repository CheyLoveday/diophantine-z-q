import ZInQKernel.Contrib.OneProof.DegEqDetTate

open ZInQ.Contrib.OneProof

#print axioms DegDet.degEqDetTate_of_degHomogPoly
#print axioms DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly
#print axioms DegDet.degEnd_mul_of_isIsogeny
#print axioms DegDet.det_eq_deg_abstract
-- the statement discharged is exactly the open field
example : (DegDet.DegHomogPoly → DegDet.DegLadicIsogeny → ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed →
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) := DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly
example : (DegDet.DegHomogPoly → DegDet.DegLadicIsogeny → ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed →
    CharPolyEll.DegEqDetTate) := DegDet.degEqDetTate_of_degHomogPoly
#print axioms DegDet.degLadicIsogeny_of_sepDegKernel
#print axioms DegDet.charPolyIndepOfEllAlgClosed_of_printed
#print axioms DegDet.TateIndex.norm_det_map_eq
example : (DegDet.DegHomogPoly → DegDet.SepDegKernel → AvSplit.MumfordTorsionAlgClosed →
    ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed → ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) :=
  DegDet.charPolyIndepOfEllAlgClosed_of_printed
