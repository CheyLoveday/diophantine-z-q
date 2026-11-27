import ZInQKernel.Contrib.OneProof.ShimuraOrbits
import ZInQKernel.Contrib.OneProof.ShimuraPointDict

/-!
# The Shimura Hecke relations, closed

The orbit counts reduce `ShimuraSteps.ShimuraHeckeRelations` to the analytic point
dictionary (`ShimuraSteps.shimuraHeckeRelations_of_pointDictionary`), and the
existence and uniqueness of the `AtTau` points (`ShimuraPointDict.existsUnique_atTau`)
supply that dictionary. Together they give the relations with no hypothesis.
-/

namespace ShimuraSteps

/-- The analytic point dictionary: every parameter has exactly one `AtTau` point. -/
theorem pointDictionary : PointDictionary :=
  fun _ hN _ _ _ _ hC hG τ => ShimuraPointDict.existsUnique_atTau hN hC hG τ

/-- The composite Hecke operators with their divisor-class action and relations,
with no hypothesis. -/
theorem shimuraHeckeRelations : ShimuraHeckeRelations :=
  shimuraHeckeRelations_of_pointDictionary pointDictionary

/-- Shimura 1973 Theorem 1 for `A_f` from the printed form alone. -/
theorem shimuraThm1Af_of_printed_closed (hPrint : ShimuraThm1AsPrinted) :
    R16Thm1b.ShimuraThm1Af :=
  shimuraThm1Af_of_printed_pointDictionary hPrint pointDictionary

#print axioms pointDictionary
#print axioms shimuraHeckeRelations
#print axioms shimuraThm1Af_of_printed_closed

end ShimuraSteps
