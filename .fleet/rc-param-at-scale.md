# rc-param-at-scale

Scoped stop: `AlgebraicParametrizationAtScale` for `Ecurve ℓ` at the fixed scale is still open. The first missing proposition puts the two convergent analytic Laurent expansions at the width-one cusp in the specified field `modularFunctionField (newformLevel (Ecurve ℓ))`, with the same coefficients as the analytic x- and y-coordinates. The [report](../docs/research/rc-param-at-scale.md) states it exactly. The analytic route still needs rational coordinate coefficients and a converse q-expansion theorem for the prescribed field; the geometric route needs the Jacobian quotient, based Abel–Jacobi map and differential comparison. The existing Milne audit notes that the two cited statements do not give the Hecke equality and gives a separate newform locator; its two unused Conjecture 11.17 misprints are recorded in the report.

All six Lean files under `ZInQKernel/Contrib/OneProof/RC/ParamAtScale/` compile and the 23 theorem audits use only the standard three axioms. The generic map extends to a dominant ℚ-morphism; matching Laurent expansions determine its affine coordinate germs. The remaining chart check identifies the full projective value, including at the identity.

- Prepared and Stage Kummer: one theorem supplies both selector inputs given the existing at-scale proposition and `CMFieldOfDefinition`.
- Elkik: a single nonzero rational scalar gives the analytic limit at every rational cusp. Full `hAJ` still needs specialization at the genuine cusp and identification of its based Abel–Jacobi image. No numerical Manin constant is assumed.
- Heegner values: one rational map gives the prescribed analytic values after the chosen class-field embeddings, conditional on at-scale and the oriented CM representatives. The CCL trace step remains with the sibling.

Final proof/report SHA (parent of this handoff): `4eb3bb83c2624d052466bb5ba61b0737a51313d6`. The handoff's own SHA is given by `git log -1 --format=%H -- .fleet/rc-param-at-scale.md`.
