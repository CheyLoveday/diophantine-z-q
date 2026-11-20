import ZInQKernel.Contrib.RC53Assist.BCDTPrint.Literal
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.ModularNewformPrinted

/-!
# The printed Theorem A in its two consumers

`bcdtThmA_of_printed` (`Descent.lean`) has the type `PoleS12.BCDTThmA` of the main row's leaf
hB, so every consumer of that leaf can cite the printed statement instead. Two of them:

* `PoleS12.kolyvaginRankOne_of_printed` (Lemma 5.5, the rank half at `r = 1`);
* `PrintsAnalytic.modularNewform_of_printed` (modularity in newform form, with Shimura 1973,
  Li 1975, Carayol 1986 and Faltings 1983), used unchanged.
-/

namespace ZInQ.Contrib.RC53Assist.BCDTPrint

open ZInQ.Contrib.RC53Assist.NewformGlueG0 (Li1975StrongMultiplicityOneWeightTwo)
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
  (Shimura1973ConjugateEigenforms Carayol1986RationalNewformEulerFactors
    Faltings1983EulerFactorRigidityQ)

/-- **PROVED**, by `bcdtThmA_of_printed` and `PoleS12.kolyvaginRankOne_of_printed`: Lemma 5.5,
rank half at `r = 1`, from the printed Theorem A and Kolyvagin's Theorem 1. -/
theorem kolyvaginRankOne_of_bcdtPrinted (hB : BCDTThmAPrinted)
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) : ZInQ.Manuscript.PoleRC.KolyvaginRankOne :=
  ZInQ.Manuscript.PoleS12.kolyvaginRankOne_of_printed (bcdtThmA_of_printed hB) hK

/-- **PROVED**, by `bcdtThmA_of_printed` and the unchanged
`PrintsAnalytic.modularNewform_of_printed`: modularity in newform form from the printed
Theorem A and the four printed corollaries of Shimura 1973 (Theorem 1), Li 1975 (Theorem 5),
Carayol 1986 (§0.8, Corollaire) and Faltings 1983 (§5, Korollar 2). -/
theorem modularNewform_of_bcdtPrinted (hB : BCDTThmAPrinted)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    ZInQ.Manuscript.RC.PrintsAnalytic.ModularNewform :=
  ZInQ.Manuscript.RC.PrintsAnalytic.modularNewform_of_printed (bcdtThmA_of_printed hB)
    hS hL hC hF

end ZInQ.Contrib.RC53Assist.BCDTPrint
