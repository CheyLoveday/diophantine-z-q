import ZInQKernel.Contrib.RC53Assist.NewformGlues.G1G2
import ZInQKernel.Contrib.RC53Assist.NewformGlueG0.GaloisCompletion

/-!
# The rational newform periods and the weak Weil parametrization from printed theorems

`NewformPeriodsRational` follows from Shimura 1973, Theorem 1, and Faltings 1983, Korollar 2, with
the newform glue G0 (`newformPeriodsRational_of_prints_G0`, the period glues G1 and G2 being
proved), and G0 follows from four printed corollaries
(`newformOfModularCurveGlue_of_printed_corollaries`: Shimura 1973, Theorem 1; Li 1975, Theorem 5;
Carayol 1986, section 0.8, Corollaire; Faltings 1983, section 5, Korollar 2). Hence
`NewformPeriodsRational` and `ModularToWeakWeil` hold given those printed statements alone. -/

namespace ZInQ.Contrib.RC53Assist.NewformGlues

open ZInQ.Contrib.CloudB3RC53.ModularWeil ZInQ.Contrib.RC53Assist.NewformPeriods
  ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent

/-- PROVED from printed theorems. `NewformPeriodsRational` from Shimura 1973, Theorem 1, Faltings
1983, Korollar 2, and the four printed corollaries of the newform glue G0. -/
theorem newformPeriodsRational_of_printed
    (hS1 : Shimura1973Thm1RationalGamma0) (hF1 : Faltings1983Kor2EllipticQ)
    (hS : Shimura1973ConjugateEigenforms)
    (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    NewformPeriodsRational :=
  newformPeriodsRational_of_prints_G0 hS1 hF1
    (newformOfModularCurveGlue_of_printed_corollaries hS hL hC hF)

/-- PROVED from printed theorems. The weak Weil parametrization input `ModularToWeakWeil` of the
Kolyvagin print from the same printed statements. -/
theorem modularToWeakWeil_of_printed
    (hS1 : Shimura1973Thm1RationalGamma0) (hF1 : Faltings1983Kor2EllipticQ)
    (hS : Shimura1973ConjugateEigenforms)
    (hL : ZInQ.Contrib.RC53Assist.NewformGlueG0.Li1975StrongMultiplicityOneWeightTwo)
    (hC : Carayol1986RationalNewformEulerFactors) (hF : Faltings1983EulerFactorRigidityQ) :
    ZInQ.Contrib.CloudB3RC53.ModularToWeakWeil :=
  modularToWeakWeil_of_newformPeriodsRational
    (newformPeriodsRational_of_printed hS1 hF1 hS hL hC hF)

end ZInQ.Contrib.RC53Assist.NewformGlues
