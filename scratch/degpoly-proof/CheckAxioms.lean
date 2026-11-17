import ZInQKernel.Contrib.OneProof.CharPolyLattice
import ZInQKernel.Contrib.OneProof.DegHomogPolyC

open ZInQ.Contrib.OneProof

-- exact types of the discharges
example : BPAnalytic.Uniformization.UniformizationLeafAll → AvSplit.MumfordTorsionAlgClosed →
    CharPolyLattice.CharPolyIndepOfEllAlgClosedNoEmb → ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  CharPolyLattice.charPolyIndepOfEllAlgClosed_of_noEmb
example : BPAnalytic.Uniformization.UniformizationLeafAll → AvSplit.MumfordTorsionAlgClosed →
    DegPolyC.DegHomogPolyNoEmb → DegDet.DegHomogPoly :=
  DegPolyC.degHomogPoly_of_noEmb

#print axioms CharPolyLattice.charpoly_V_eq
#print axioms CharPolyLattice.charPolyIndepOfEllC
#print axioms CharPolyLattice.charPolyIndepOfEllAlgClosedC
#print axioms CharPolyLattice.charPolyIndepOfEllAlgQ
#print axioms CharPolyLattice.charPolyIndepOfEllAlgClosed_of_noEmb
#print axioms DegPolyC.card_ker_eq
#print axioms DegPolyC.degEnd_le_card_fibre
#print axioms DegPolyC.degEnd_ne_zero
#print axioms DegPolyC.degEnd_eq_card_fibre
#print axioms DegPolyC.card_ker_eq_det
#print axioms DegPolyC.latRep_injective
#print axioms DegPolyC.isIsogeny_of_det_ne_zero
#print axioms DegPolyC.degEnd_eq_det
#print axioms DegPolyC.degHomogPolyC
#print axioms DegPolyC.degHomogPoly_of_noEmb
#print axioms DegPolyC.charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb
#print axioms DegPolyC.degEqDetTateC
