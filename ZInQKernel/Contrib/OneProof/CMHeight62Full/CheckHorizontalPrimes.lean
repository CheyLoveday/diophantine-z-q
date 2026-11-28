import ZInQKernel.Contrib.OneProof.CMHeight62Full.HorizontalPrimes

/-!
# Axiom check for `HorizontalPrimes`

Every theorem of `HorizontalPrimes` depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

namespace ZInQ.Contrib.CMHeight62Full

#print axioms comap_ker_localSection
#print axioms isPrime_span_sectionParam
#print axioms comap_span_sectionParam
#print axioms isLocalization_localization_span_sectionParam
#print axioms localizationAtSectionKer_equiv
#print axioms maximalIdeal_localization_span_sectionParam
#print axioms maximalIdeal_localizationAtSectionKer
#print axioms maximalIdeal_eq_span_of_ringEquiv
#print axioms finrank_cotangentSpace_le_of_basis
#print axioms residue_algebraMap_ne_zero_of_not_mem
#print axioms isDiscreteValuationRing_localization_horizontal
#print axioms isDiscreteValuationRing_localization_horizontal_sectionLocal

end ZInQ.Contrib.CMHeight62Full
