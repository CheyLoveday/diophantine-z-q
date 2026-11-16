import ZInQKernel.Contrib.OneProof.DegEqDetTate

open ZInQ.Contrib.OneProof

#print axioms DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford
#print axioms DegDet.degEqDetTate_of_degHomogPoly_mumford
#print axioms DegDet.KerDvd.kerDvdDeg
#print axioms DegDet.TateIndex.norm_det_map_eq
#print axioms DegDet.det_eq_deg_abstract_le
#print axioms DegDet.degEqDetTate_of_degHomogPoly
#print axioms DegDet.charPolyIndepOfEllAlgClosed_of_printed
#print axioms DegDet.degLadicIsogeny_of_sepDegKernel
-- exact types
example : (DegDet.DegHomogPoly → AvSplit.MumfordTorsionAlgClosed →
    ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed → ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) :=
  DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford
example : (DegDet.DegHomogPoly → AvSplit.MumfordTorsionAlgClosed →
    ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed → CharPolyEll.DegEqDetTate) :=
  DegDet.degEqDetTate_of_degHomogPoly_mumford
