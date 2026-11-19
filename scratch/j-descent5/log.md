# CM period descent results log

## Sizing before any build

- **VERIFIED (source):** `JDescent3FunctionField.lean` attaches the actual generic stalk, the rational identity place matching its stalk, and all positive pole-space dimensions and exact poles conditional on genus one. Tau Ceti's `RiemannRoch/Basic.lean` and `Place/Basic.lean` give order tests for pole spaces, strict valuation inequalities, and uniformizers. Its `EllipticCurve/Affine/FunctionField/Genus.lean` computes those spaces for an existing Weierstrass equation, so it cannot construct the equation here. The new algebra is distinct-order independence, a relation at order six, coordinate changes, and the exclusion of a simple pole via order one. This looks like a self-contained function-field proof.
- **VERIFIED (source):** The vendor `AlgebraicCurve.exists_place_range_stalk_eq` attaches a valuation subring to each closed point. Mathlib's generic-stalk construction embeds sections on nonempty opens into the function field. Sections need a local-to-global gluing lemma, and a place attached to a closed point other than the identity must be shown distinct from the identity place. Inversion requires transporting stalk orders or obtaining evenness directly from the analytic double pole and cubic. These are separate from the cubic relation.
- **VERIFIED (source):** `JDescent.lean` recovers an algebraic modular invariant from the matched short coefficients; `JDescent2Analytic.lean` identifies the lattice coordinates from a nonsingular cubic, an even abscissa and an exact double pole, and `hasDoublePoleAtZero_of_localParameter` handles the analytic identity with a numerator and local parameter. The same-period holomorphy and openness clauses are in `HDecomp/LeafPush2/R22.lean`; the stronger `HDecomp/Analytic/Uniformization.lean` supplies a coordinate derivative for a different witness. `IsPeriodAt` does not assume a derivative for its witness.
- **SPECULATIVE (size):** Realize a parameter and a unit numerator as sections on a neighborhood of the identity. Their value and unit identities are algebraic; showing a nonzero derivative needs actual first-order information on the given period map, or a proof that an analytic parameter evaluation on it is locally injective. That comparison can be isolated without invoking a general comparison of algebraic and analytic meromorphic functions.

## Cubic

- **VERIFIED (Lean):** `abVar_shortCubic_of_genusOne` constructs the normalized short equation in the actual generic stalk, with pole orders −2 and −3 and no other poles. Distinct-order independence makes six monomials a basis of the sixth pole space. A zero cubic coefficient would place the square of the ordinate in the fifth pole space. The singular case is excluded by a quotient with sole pole of order one.
- **VERIFIED (Lean):** `JDescent5Cubic.lean` compiled under `lake env lean`; all five theorem checks report only the standard three axioms.

## Sections

- **VERIFIED (Lean):** `abVar_shortSections_of_genusOne` realizes the normalized coordinates as regular sections on the complement of the identity. The proof uses the injectivity of the correspondence from closed points to stalk images in the generic field. The sections on a cover agree in the generic stalk and therefore glue; the cubic equation also lifts by injectivity there.
- **VERIFIED (Lean):** `JDescent5Sections.lean` compiled under `lake env lean`; all six theorem checks report only the standard three axioms.

## Pole-space action of an involution

- **VERIFIED (Lean):** `shortCubic_parity_of_place_involution` proves that any ground-field involution preserving the marked place fixes the short abscissa and sends the ordinate to itself or its negative. The proof expands the transformed coordinates in pole spaces of dimensions two and three. The involution forces both leading coefficients to square to one, while the cubic relates their cube and square. This fixes the abscissa coefficient and makes its translation zero.
- **VERIFIED (Lean):** Both theorem checks in `JDescent5Parity.lean` list only the three standard axioms.
