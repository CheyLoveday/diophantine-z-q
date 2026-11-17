import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.AfTateLambda

#discharges

#print axioms AfTateLam.r16CoreY_of_printed
#print axioms AfTateLam.component
#print axioms AfTateLam.trace_det_precomp
#print axioms AfTateLam.finrank_E
#print axioms AfTateLam.liesOver_place
#print axioms AfTateLam.τhat_algQl
#print axioms AfTateLam.lin_trace_det
#print axioms AfTateLam.exists_frob
#print axioms AfTateLam.dsLambda_of_tensor
#print axioms AfTateLam.dsLambda_of_sat_det
#check (AfTateLam.r16CoreY_of_printed :
  AfTateLam.HeckeJ1DS → AfTateLam.AfShimura → AfTateLam.AfTateDSLambda → X1Igusa.IgusaGL2DS →
    AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY)
