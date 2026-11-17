import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.R16CoreYSatDet

#discharges

#print axioms AfTateLam.r16CoreY_of_sat_det
#print axioms AfTateLam.r16CoreY_of_printed
#print axioms AfTateLam.dsLambda_of_sat_det
#check (AfTateLam.r16CoreY_of_sat_det :
  AfTateLam.HeckeJ1DS → AfTateLam.AfShimura → AfTateLam.AfTateDSLambdaSat → AfTateLam.AfDetLambda →
    X1Igusa.IgusaGL2DS → AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY)
