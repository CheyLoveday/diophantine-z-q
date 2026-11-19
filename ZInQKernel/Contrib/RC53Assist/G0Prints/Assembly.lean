import ZInQKernel.Contrib.RC53Assist.G0Prints.Carayol

/-!
# The unchanged G0 fields from printed and geometric inputs

This module only instantiates the existing assembly. The two field types
are the original definitions: neither their premises nor their conclusions
are weakened. The local-factor readings are proved steps. Shimura's
complexified algebraic differential interface remains a named geometric
source reading, not a literal print.

Locators: Shimura 1973, §1, pp. 524–526; Carayol 1986, §0.8, p. 411;
Faltings 1983, §5, Korollar 2, p. 361; Li 1975, Theorem 5, p. 298.
Bibliography keys `shimura-factors`, `carayol`, `faltings1983`, `li-newforms`.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option autoImplicit false

namespace ZInQ.Contrib.RC53Assist.G0Prints

open ZInQ.Contrib.RC53Assist.NewformGlueG0
open ZInQ.Contrib.RC53Assist.NewformGlueG0.Descent
open ZInQ.Contrib.RC53Assist.GlobalTrace

/-- **PROVED ASSEMBLY**, the two unchanged local-factor fields from the
Faltings and Carayol prints, Shimura's named geometric source reading,
and the three previously named bad-prime hypotheses.
The first component uses the actual quotient and complete analytic
L-functions. The second uses Tate local factors and coinvariant dictionaries.
Locators: Shimura pp. 524–526; Carayol p. 411; Faltings p. 361. -/
theorem g0_local_factor_fields_of_prints_of_geometricReading
    (hS : Shimura1973RationalGeometricReading) (hC : Carayol1986CorollaireRational)
    (hF : Faltings1983Korollar2iiiivPrint)
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    Carayol1986RationalNewformEulerFactors ∧ Faltings1983EulerFactorRigidityQ :=
  ⟨Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading hT hLG hA hS hC,
    Faltings1983EulerFactorRigidityQ_of_print hT hLG hA hF⟩

/-- **PROVED ASSEMBLY**, the existing full-coefficient newform consequence
uses the two proved field readings, at exactly its original type.
Coefficient-field descent and the final coefficient assembly are reused
without edits. No existence of a newform for the input elliptic curve is
assumed as a substitute for this conclusion.
Locators: Shimura p. 526; Li p. 298; Carayol p. 411; Faltings p. 361. -/
theorem liCarayolNewformOfModular_of_prints_of_geometricReading
    (hSg : Shimura1973RationalGeometricReading) (hC : Carayol1986CorollaireRational)
    (hF : Faltings1983Korollar2iiiivPrint)
    (hS : Shimura1973ConjugateEigenforms) (hL : Li1975StrongMultiplicityOneWeightTwo)
    (hT : TateCurveTateModulePrint) (hLG : DecompositionGroupLocalGlobalGlue)
    (hA : AdditiveReductionCoinvariantsVanish) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.LiCarayolNewformOfModular :=
  liCarayolNewformOfModular_of_printed_corollaries hS hL
    (Carayol1986RationalNewformEulerFactors_of_print_of_geometricReading hT hLG hA hSg hC)
    (Faltings1983EulerFactorRigidityQ_of_print hT hLG hA hF)

end ZInQ.Contrib.RC53Assist.G0Prints
