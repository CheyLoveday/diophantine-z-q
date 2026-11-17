import ZInQKernel.OneProof.Main
import ZInQKernel.OneProof.Discharges
import ZInQKernel.Contrib.OneProof.R16CoreYDS965

#discharges

#print axioms AfTateLam.r16CoreY_of_ds965
#print axioms AfTateLam.afDetLambda_of_ds965
#print axioms AfTateLam.afCharpolyDS965_iff
#check (AfTateLam.r16CoreY_of_ds965 :
  AfTateLam.HeckeJ1DS → AfTateLam.AfShimura → AfTateLam.AfCharpolyDS965 →
    X1Igusa.IgusaGL2DS → AvSplit.MumfordTorsionAlgClosed → R16Split.R16CoreY)
#check (AfTateLam.afDetLambda_of_ds965 :
  AvSplit.MumfordTorsionAlgClosed → AfTateLam.AfCharpolyDS965 → AfTateLam.AfDetLambda)
