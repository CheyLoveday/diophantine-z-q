import ZInQKernel.Contrib.RC53Assist.TateCurve.LiteralTate
import ZInQKernel.Contrib.RC53Assist.TateCurve.AdditiveOneInput
import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.Main

/-!
# The coinvariant-route readings from two printed theorems

With the two local-field statements proved (`LocalReadings/`) and the Weil-pairing input proved
(`AdditiveOneInput.lean`), the Tate-module reading at multiplicative primes needs only the printed
form of Tate's theorem and the multiplicative direction of the semistable reduction criterion, and
the additive reading needs only the semistable reduction criterion.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.GlobalTrace

open ZInQ.Contrib.RC53Assist.TateCurve

/-- **PROVED FROM TWO PRINTED THEOREMS**: the Tate-module reading at multiplicative primes from
Silverman, Theorem 14.1 (C.14.1), page 445, in its printed existence form, and the
multiplicative direction of the semistable reduction criterion (Silverberg-Zarhin, *Reduction of
Abelian Varieties*, Theorem 4.1). -/
theorem tateCurveTateModulePrint_of_two_prints (hT : SilvermanC141TateUniformizationLiteral)
    (hS : LocalSemistableTatePrint) : TateCurveTateModulePrint :=
  tateCurveTateModulePrint_of_literal hT hS localUnramifiedValueGroupPrint
    localFrobeniusGenerationPrint

end ZInQ.Contrib.RC53Assist.GlobalTrace
