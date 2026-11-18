import ZInQKernel.Contrib.RC53Assist.NewformPeriodsG1.ParametrizationPeriods
import ZInQKernel.Contrib.RC53Assist.IsogenyLatticeAnalytic.AnalyticTransport
import ZInQKernel.Contrib.RC53Assist.PullbackScalar.ResidueComparisonProof

/-!
# The period glues G1 and G2 of the newform period package, proved

`ParametrizationPeriodsGlue` (G1) is `parametrizationPeriodsGlue_holds`
(`ZInQKernel/Contrib/RC53Assist/NewformPeriodsG1/ParametrizationPeriods.lean`). The isogeny-lattice glue
(G2) follows from its analytic part `isogenyLatticeAnalyticGlue_holds`
(`ZInQKernel/Contrib/RC53Assist/IsogenyLatticeAnalytic/AnalyticTransport.lean`) and its algebraic part
`isogenyScalarRationalGlue_proof`
(`ZInQKernel/Contrib/RC53Assist/PullbackScalar/ResidueComparisonProof.lean`) through
`isogenyLatticeGlue_of_glues`. So the rational period statement `NewformPeriodsRational` rests only on the
two printed theorems (Shimura 1973, Theorem 1; Faltings 1983, Korollar 2) and the newform glue G0.
-/

namespace ZInQ.Contrib.RC53Assist.NewformGlues

open ZInQ.Contrib.CloudB3RC53.ModularWeil ZInQ.Contrib.RC53Assist.NewformPeriods

/-- PROVED. The isogeny-lattice glue G2: the rational pull-back scalar of a rational isogeny carries the
first period lattice into the second. -/
theorem isogenyLatticeGlue_proved : ZInQ.Contrib.RC53Assist.NewformPeriods.IsogenyLatticeGlue :=
  isogenyLatticeGlue_of_glues
    ZInQ.Contrib.RC53Assist.IsogenyLatticeAnalytic.isogenyLatticeAnalyticGlue_holds
    ZInQ.Contrib.RC53Assist.PullbackScalar.ResidueComparison.isogenyScalarRationalGlue_proof

/-- PROVED. `NewformPeriodsRational` from the two printed theorems and the newform glue G0, the period
glues G1 and G2 being proved. -/
theorem newformPeriodsRational_of_prints_G0
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) : NewformPeriodsRational :=
  ZInQ.Contrib.RC53Assist.NewformPeriodsG1.newformPeriodsRational_of_prints_G0_G2 hS hF h0
    isogenyLatticeGlue_proved

end ZInQ.Contrib.RC53Assist.NewformGlues
