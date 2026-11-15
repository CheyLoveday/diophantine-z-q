import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.BLRLocalizes

#discharges

#print axioms GapBLR.blr_1_2_4_mp
#print axioms GapBLR.neronLocalizesDVR_proved
example : GapBLR.BLR_1_2_4_MP := GapBLR.blr_1_2_4_mp
example : ReductGlue.NeronLocalizesDVR := GapBLR.neronLocalizesDVR_proved
