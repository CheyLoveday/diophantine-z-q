# Berger comparison

**Scoped stop; the Berger row remains GLUE.** Lean proves the same-extension
representation transport once supplied with an equivariant map from
`B_max[log[p̃]]` to the embedded Fontaine ring and the normalization
of Berger's logarithm. Base change of a fixed basis avoids a fixed-field
calculation or a proof of injectivity of the map. The journal theorem
locator is **UNVERIFIED**; the earlier audit records different numbers
in arXiv v3 and the later author copy. No new manuscript error was found.
The untilt in the reported logarithm formula is a residue, so using it
as a denominator requires a lift or an equivalent construction.

All three new Lean modules compile. `ResidueLog` lifts a near-one
denominator to a Witt unit, constructs its p-adic logarithm and the
kernel-adic logarithm of the quotient, and proves the correction lies
in `A_max`. `FrobeniusGenerator` proves the crystalline range of
`φ(ξ)/p` and the resulting finite polynomial evaluations.
`Transport` proves the conditional basis equivalence and the exact
comparison from the two ring inputs. The conditional route through
`BergerThm06Print` to `bergerSurveyF` typechecks. The axiom audit
found only `propext`, `Classical.choice` and `Quot.sound`.

The remaining ring input is `FrobeniusTransport`: extend the finite
calculation to the two actual semistable images and check equivariance.
The remaining logarithm input is the cyclotomic unit calculation and
compatibility of the constructed near-one logarithm with Berger's
branch. `FontainePolynomialEmbedding` is separately open.
No new discharge or printed theorem; delta **0 GLUE / 0 LEAF**.
The full report is in `docs/research/berger-comparison.md`.
