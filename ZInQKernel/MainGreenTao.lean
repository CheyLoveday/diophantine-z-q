import ZInQKernel.Main
import ZInQKernel.External.GreenTaoDense
import ZInQKernel.Density.PropDFinal

/-!
# The manuscript-faithful conditional headline

Szemerédi's theorem in the primes and the density proposition are proved in
Lean. Together they supply route AP's progression input, leaving precisely
`SixContactMin` and the manuscript's `PoleCompleteness` as hypotheses.
-/

namespace ZInQ

/-- Theorem 1.1 from H and manuscript PC (Theorem 5.2).
The polynomial and all frozen numerical bounds are those of `FrozenTarget`. -/
theorem exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
    (hH : SixContactMin) (hPC : PoleCompleteness) : FrozenTarget :=
  exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness_goodPrimeAP hH hPC
    (goodPrimeAP_of_greenTaoDense greenTaoDense Density.goodPrimeDensity)

end ZInQ
