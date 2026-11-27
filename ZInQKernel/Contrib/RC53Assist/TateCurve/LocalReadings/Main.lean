import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.UnramifiedValueGroup
import ZInQKernel.Contrib.RC53Assist.TateCurve.LocalReadings.Nonvacuity

/-!
# The two local arithmetic readings

Both original local-field propositions are proved without additional hypotheses.
The accompanying examples realize their extending-valuation and Frobenius inputs.

Kind: proved. Locators: Serre, *Local Fields*, I, §8 and III, §5.
The references are to the book, not the chapter in Cassels--Fröhlich.
-/

namespace ZInQ.Contrib.RC53Assist.TateCurve

/-- **PROVED**: the exact two original local arithmetic propositions together.
Locator: Serre, *Local Fields*, I, §8 and III, §5. -/
theorem localArithmeticReadings :
    LocalUnramifiedValueGroupPrint ∧ LocalFrobeniusGenerationPrint :=
  ⟨localUnramifiedValueGroupPrint, localFrobeniusGenerationPrint⟩

end ZInQ.Contrib.RC53Assist.TateCurve
