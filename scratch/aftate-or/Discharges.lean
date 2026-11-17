import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.AfTateOr

#discharges

#print axioms AfTateOr.r16CoreY_of_dsOr_igusaDS
#print axioms AfTateOr.weakOdd_of_dsOr
#print axioms AfTateOr.isX1AlgDS_of_isX1Model
#print axioms AfTateOr.isX1Model_of_isX1AlgDS
#print axioms AfTateOr.weakOddAt_of_orAt
#print axioms AfTateOr.not_isNewform_one
#print axioms AfTateOr.dsOr_of_picZero
#print axioms AfTateOr.dsOr_of_weakPicZero
#print axioms AfTateOr.weakPicZero_of_dsOr
#print axioms AfTateOr.nonempty_ringEquiv_of_rel
#check (AfTateOr.r16CoreY_of_dsOr_igusaDS :
  AfTateOr.AfTateDSOr → X1Igusa.IgusaGL2DS → AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY)
