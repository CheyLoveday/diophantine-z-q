# Complex modular functions and the rational parametrization at the fixed scale

For every positive level $N$, `complexCuspClassification` proves the exact `ModFnField.ComplexCuspClassification N`: the specified complex Laurent series of a `Γ₀(N)`-invariant meromorphic function, meromorphic in every cusp parameter, belongs to the embedded field ℂ(j(q), j(q^N)). `projective_value_of_expansions` proves equality with the specified analytic point at every upper half-plane parameter, including the identity. Together they give `AlgebraicParametrizationAtScale` for the actual curve `Ecurve ℓ`, with the modular chart supplied as a parameter and a rational representative of the already fixed scale. The three consumers use this map. No new print was used as an input or added.

The manuscript constructs the map by the quotient and isogeny in tex 1781–1787. The function field route below, including the comparison with the analytic points, is on-the-spot, provenance (c). The degree bound uses an injection of the cosets into the projective line over ℤ/Nℤ, so it does not require a separate coset surjectivity proof. For coefficients at infinity, eventual holomorphy and exponential bounds in a common width-one scale pass to finite sums and products. Level-one invariance then makes the coefficients periodic with period one, so the bounded regularization descends to the punctured disk and extends across zero. This gives integral Laurent exponents without constructing fractional expansions for the individual factors. Interior poles of the orbit coefficients are allowed, so the coefficients are rational functions of $j$. For the comparison of projective points, the regular function $Z/Y$ vanishes at the identity and equals $1/y$ at the generic point. Conversely the actual $x$-coordinate has a pole at every interior lattice value of the scaled primitive, including higher order zeros of the primitive minus a lattice element.

## Checked statements

The file column is relative to `ZInQKernel/Contrib/OneProof/RC/ModFnClassify/`. The namespace is `ZInQ.Manuscript.RC.ModFnClassify`. All 11 files compile with serial `lake env lean -j1 -DautoImplicit=false`. The 67 theorem audits list only `propext`, `Classical.choice` and `Quot.sound`. The statements below describe their conclusions and roles; the source contains the full binders.

| File and theorem | Statement and step supplied |
| --- | --- |
| `Interior.isCompact_truncatedFundamentalDomain` | The complex image of the standard modular fundamental domain below any height is compact. Interior pole clearing. |
| `Interior.finite_bad_in_fd` | A meromorphic function analytic above a height is nonanalytic at only finitely many points in that domain. Interior pole clearing. |
| `Interior.jFunction_invariant` | The analytic $j$ is level-one invariant. Interior pole clearing and generator growth. |
| `Interior.invariant_order` | Meromorphic order of a level-one invariant function is constant along an SL₂(ℤ) orbit. Interior pole clearing. |
| `Interior.pole_killing_power` (private) | At a zero of an analytic factor, multiplying a meromorphic function by some power of it gives order at least zero. Interior pole clearing. |
| `Interior.clear_interior_poles` | A level-one invariant meromorphic function analytic high in the half-plane admits a monic denominator polynomial in $j$, whose product has a globally analytic, invariant representative equal as punctured germs. Level-one converse. |
| `LevelOne.cuspGerm_analytic_tail` | A meromorphic realization in a positive-width cusp parameter makes the original function analytic above some height. Level-one and orbit coefficients. |
| `LevelOne.levelOne_const` (private) | An invariant analytic function bounded at infinity is constant, via the weight-zero modular form theorem. Level-one converse. |
| `LevelOne.j_cusp_unit` | There is an analytic germ $U$ with $U(0)=1$ and $U(q)=qj$ on the width-one chart. Principal part cancellation and growth. |
| `LevelOne.levelOne_polynomial_of_cleared_cusp` | An analytic level-one invariant function whose cusp germ becomes analytic after multiplication by $q^d$ is a polynomial in $j$. Level-one converse. |
| `LevelOne.levelOne_rational_in_j` | An invariant meromorphic function with a meromorphic width-one cusp germ admits polynomials $P,D$, $D$ monic, with $gD(j)=P(j)$ in every punctured interior germ. Level-one converse with poles. |
| `CuspGrowth.cuspGerm_growth` | A meromorphic cusp germ gives a bound after multiplication by a power of the cusp parameter. Cusp regularity of orbit coefficients. |
| `CuspGrowth.cuspGrowth_changeWidth` | The growth bound at one positive width implies such a bound at any positive width. Common growth scale. |
| `CuspGrowth.cuspGrowth_const`, `cuspGrowth_mul`, `cuspGrowth_sub` | Constants, products, and differences have the same type of bound (positive width for the difference). Closure under orbit coefficient operations. |
| `CuspGrowth.qParam_add_period` (private) | The cusp parameter is unchanged by addition of its nonzero width. Descent to the punctured disk. |
| `CuspGrowth.cuspGerm_of_periodic_growth` | On a positive-width cusp, periodicity, eventual holomorphy, and the growth bound imply existence of a meromorphic cusp germ with the prescribed tail values. Descent of periodic orbit coefficients. |
| `Cosets.lowerRow_rel_iff` (private) | Two bottom rows modulo $N$ define the same projective class exactly when the integral matrices represent the same right coset. Coset count. |
| `Cosets.card_levelCosets_le` | The right cosets of Γ₀(N) have cardinality at most `dedekindPsi N`, by the bottom row embedding. Degree bound. |
| `Orbit.orbitValue_permute`, `orbitPoly_invariant` | Translation on the right permutes orbit values; the resulting polynomial is level-one invariant. Orbit polynomial. |
| `Orbit.orbitPoly_root`, `orbitPoly_monic_degree` | The invariant function is a root; the polynomial is monic of degree the coset count. Orbit equation. |
| `Orbit.coeff_orbitProduct_closed` (private) | A property of functions stable under constants, subtraction and multiplication passes to each coefficient of the product of their linear factors. Orbit coefficient regularity. |
| `Orbit.orbitCoefficient_cusp_of_growth` | Meromorphy, invariance, eventual holomorphy and exponential growth of the translates give interior meromorphy, level-one invariance and a width-one cusp germ for every coefficient. Orbit equation. |
| `Orbit.cuspGerm_translates_analytic_growth` | Meromorphic germs of all translates at any positive widths give eventual holomorphy and width-one growth of the translates. Bridge from the exact converse hypotheses. |
| `Orbit.orbitCoefficient_cusp`, `orbitCoefficient_rational_in_j` | With meromorphic cusp germs of the translates, each coefficient has a width-one meromorphic cusp germ and is rational in $j$ as a meromorphic germ. Orbit equation over the level-one field. |
| `FormalOrbit.cuspGerm_realizes` | Existence of a meromorphic width-one cusp germ gives a complex Laurent series realizing its tail. Orbit coefficients in the Laurent field. |
| `FormalOrbit.realizes_j` | `jqModC ℂ` realizes the analytic $j$. Identification of the base field. |
| `FormalOrbit.realizes_finsetSum`, `realizes_complexPolynomial` | Finite sums and complex polynomial evaluation commute with Laurent realization. Transport of equations to Laurent series. |
| `FormalOrbit.realizes_mem_complexJField` | A Laurent realization of a level-one invariant meromorphic function with a cusp germ belongs to ℂ(j(q)). Formal level-one classification. |
| `FormalOrbit.formal_degree_bound_of_growth`, `formal_degree_bound`, `complexCusp_degree_bound` | The Laurent realization is integral over ℂ(j(q)) and has minimum polynomial degree at most `dedekindPsi N`, respectively from translate growth and tail holomorphy, arbitrary positive cusp widths, and the exact widths in the converse. Formal orbit equation. |
| `Compositum.mem_adjoin_of_linear_degree_bound` | For integral $x,y$ over a field of characteristic zero, if the degree of `x + c*y` is at most the degree of `x` for every $c$ in an infinite field of constants contained in the base, then $y$ belongs to the field generated by $x$. Two choices of $c$ generate the same subfield of the finite separable compositum and hence jointly generate $x,y$. Field comparison. |
| `Classification.dilate_smul_level` (private), `jNFunction_invariant` | Conjugating a Γ₀(N) matrix by dilation by $N$ gives an integral determinant-one matrix; therefore $j(Nτ)$ is Γ₀(N)-invariant. Generator comparison. |
| `Classification.jN_translate_analytic` | Every SL₂(ℤ) translate of $j(Nτ)$ is holomorphic in the upper half-plane. Generator comparison. |
| `Classification.cuspGrowth_add_one`, `j_polynomial_growth` (private) | The width-one bound is closed under addition, and polynomials in $j$ have the bound. Generator growth. |
| `Classification.cuspGrowth_root_of_monic` | Roots of a monic polynomial whose coefficients are polynomials in $j$ have an exponential bound, by Cauchy's root bound. Generator growth. |
| `Classification.jN_translate_growth` | The modular polynomial gives exponential growth of every translate of $j(Nτ)$. Application of the degree bound to $j(q^N)+cs$. |
| `Classification.qParam_width_one_zpow` (private), `realizes_jN` | A width-one Laurent monomial equals the matching exponential, and `jqNModC ℂ N` realizes $j(Nτ)$. Generator comparison. |
| `Classification.complex_jN_minpoly_degree` | The second generator is integral over ℂ(j(q)) and has degree exactly `dedekindPsi N` by the vendored finite-rank theorem. Field comparison. |
| `Classification.complexCuspClassification` | `∀ (N : ℕ) [NeZero N], ComplexCuspClassification N`. Together with existing rational descent, supplies the exact bilateral `HasSum` coordinate theorem and the generic and dominant maps of the preceding work. |
| `PrimitivePole.scaledPrimitive_not_constant` | A scaled primitive with nonzero rational scale and the prescribed coefficients is nonconstant on the half-plane. Identity comparison. |
| `PrimitivePole.xCoordinate_no_analytic_germ_at_lattice` | At an interior lattice value the analytic $x$-coordinate has no punctured germ represented by an analytic function, given the coefficient and lattice data and a nonzero rational scale. Identity comparison. |
| `ProjectiveIdentity.qParam_one_zpow`, `eq_germ_of_eq_tail` (private), `same_series_same_germ` (private) | Match the two width-one monomials, and extend tail equality (in particular from a shared Laurent series) to punctured germs on the upper half-plane. Projective comparison. |
| `ProjectiveIdentity.evalSection_eq_stalk` (private), `evalSection_ZOverY_at_identity` | Evaluation is the stalk map to the field at the image of the closed point; $Z/Y$ evaluates to zero at the identity. Identity comparison. |
| `ProjectiveIdentity.pullback_expansion` | A regular section on a target open has a meromorphic pullback whose series is the given generic image, with an analytic representative giving the evaluation at every chart point mapping to the open. Projective comparison. |
| `ProjectiveIdentity.projective_identity_iff_lattice` | For the prescribed generic map and Laurent realizations, the underlying image is the projective identity exactly when the scaled primitive belongs to the period lattice. Identity comparison. |
| `ProjectiveIdentity.appLE_of_lift`, `evalSection_on_zChart` (private) | Pullback along the lift through an open equals the open-section pullback; on $Z\ne0$ the affine coordinate-ring evaluation equals regular section evaluation. Affine chart comparison. |
| `ProjectiveIdentity.projectiveValue_on_affine` | Away from the identity, `projectiveValue` is the nonsingular point with coordinates the evaluations of $X/Z,Y/Z$. Affine chart comparison. |
| `ProjectiveIdentity.projective_value_of_expansions` | For the given generic map with both exact coordinate expansions, `projectiveValue ((X.complexPoint τ).comp π hQ).val = phiAn E f L κ τ` for all `τ : ℍ`. Full projective comparison in the at-scale interface. |
| `AtScale.algebraicParametrizationAtScale` | The existing normalized coefficient, lattice and period-inclusion data, a parameter `X0Model`, and `∃ c : ℚ, (c : ℂ) = κ` give `AlgebraicParametrizationAtScale E X f Lat κ`. |
| `AtScale.curve_algebraicParametrizationAtScale` | For `I : GenusOddInstance W`, at the supplied `X` and `∃ c : ℚ, (c : ℂ) = I.κ`, gives `AlgebraicParametrizationAtScale (Ecurve ℓ) X I.f I.Lat I.κ`. Actual curve and unchanged scale. |
| `AtScale.prepared_values`, `missing_values` | With the scale representative and `CMFieldOfDefinition X`, gives respectively `∀ h hp, StageSelector.PreparedParamValue … hp` and `StageKummer.MissingParamValues s` for the actual setup. The two selector consumers. |
| `AtScale.oriented_cm_values` | With the scale representative and the stated chart equalities for prescribed class-field points, a single dominant rational morphism for the actual curve agrees with every prescribed embedded analytic value. The oriented CM consumer. |

`LevelInvariant` and `LevelOneInvariant` are the respective group-action identities, already hypotheses of the converse (tex 1781–1787, via the analytic route). `CuspGerm h f` is the existence of a meromorphic germ at zero realizing only a single cusp tail, again just a converse hypothesis. `CuspGrowth h f` asks only for boundedness after multiplying by a power of the local parameter: it imposes no invariance, germ, or field membership. These conditions describe local regularity or symmetry and individually do not give the target's global field conclusion. There are no new structure hypotheses. The comparison uses the existing `X0Model.sectionExpansion`, which only describes regular source sections, and a generic map and tail realizations, which say nothing about equality at interior points (tex 1785–1787).

## Remaining hypotheses and ownership

| Exact input still used | Tex and owner |
| --- | --- |
| `X : X0Model (newformLevel (Ecurve ℓ))`, including its `sectionExpansion` and orbit chart. | 1781–1787, 2836–2838; sibling modular curve chart lane. The map is proved for this parameter. |
| `[NeZero (newformLevel (Ecurve ℓ))]`, `I.hE`, `I.hf`, `I.hLat`, `I.hκ` (ellipticity, positive level, matching Fourier coefficients, `IsLatticeOf`, and `IsParamScale`). | 1765–1784, 1825–1828; existing actual-curve and setup data. The positive level is also available from the existing stage setup where that setup is supplied. |
| `∃ c : ℚ, (c : ℂ) = I.κ` (nonzero follows from `I.hκ`). This represents the fixed scale, which is not inferred from choosing a new scale. | 1785–1787, 1825–1828; ELLIOT input for the chosen normalization. Identifying this normalization with the differential of the chosen rational quotient map is separate geometric theory. |
| `CMFieldOfDefinition X` for the prepared and missing selectors, using the existing `StageKummer.Setup I L`. | 2411–2416, 2839–2844, 2915–2917, 8213–8217; existing setup and ELLIOT input for field of definition, outside this lane. |
| For specified `O, ι, x, A, B`, `∀ m, (x m).map (ι m) = X.complexPoint (cmPoint (A m) (B m) (O m).discr)`. | 2915–2919; sibling Heegner-values lane for the oriented family. Trace relations are separate. |

The interior at-scale proposition has no algebraic cusp equality. Establishing the manuscript's based map as stated would also require a source algebraic cusp at infinity, a specialization comparison there, and, to identify the manuscript's construction and its Hecke relation, the genuine Jacobian quotient and Hecke theory (large; tex 1785–1788, 2836–2838). A good reduction comparison for the actual morphism is separate (tex 9347–9350). None of these is a hypothesis of the three delivered consumer theorems.

## Known issues

- The existing source audit in `RC/PrintsAnalytic/Milne.lean` reports that the cited Theorem 11.19 and Remark 11.18 cover the rational map and quotient; normalized newforms are in Proposition 11.21, and the cited pair does not supply the Hecke equality at tex 1788. The same audit records two unused discrepancies in Conjecture 11.17 (the coprimality wording and a duplicate conductor factor). These locators are from the existing audit; no new locator is supplied from memory. No new mathematical error in the manuscript was found.
- Orbit coefficients can have interior poles. Treating them as polynomials in $j$ would invalidate the degree proof. The descent uses the rational level-one theorem and a monic denominator.
- The identity comparison concerns interior chart points. It also covers ramification above the identity. The separate analytic cusp limit does not give the specialization of an algebraic cusp within `X0Model`.

## Manuscript check

| Tex and step | Verdict |
| --- | --- |
| 1765–1767, 1779–1780: use the stated twist curve and modular level. | OK — specialize the existing actual curve and its modularity interface. |
| 1781–1784: use a rational weight-two newform and the elliptic quotient. | Unverified — the normalized coefficients are provided by the existing interface; the Jacobian quotient is outside this route, and the citation is imprecise as recorded above. |
| 1785–1786: the rational map to the given elliptic curve. | Gap filled — prove the interior at-scale rational map by the complex classification, rational descent and projective value comparison. |
| 1787: image of the algebraic cusp at infinity. | Unverified — matching the value at every interior chart point does not identify the source algebraic cusp. |
| 1787–1788: Hecke equivariance. | Unverified — the existing audit does not find it in the cited pair and the field route does not use it. |
| 1825–1828: retain one normalization throughout. | OK — equality with the given normalization is required rather than selecting a substitute. |
| 2411–2416: values of the two distinct point selectors. | Gap filled — both consume the fixed-scale morphism through the existing field-of-definition interface. |
| 2836–2838: use the same rational parametrization for descent. | Gap filled — the supplied chart has a dominant rational morphism with the prescribed interior values; algebraic cusp normalization is separate. |
| 2839–2844: class fields and Heegner conductors. | OK — the consumers retain the specified fields and embeddings. |
| 2915–2919: choose compatible CM representatives and apply the map. | Gap filled — given these representatives with their chart comparison, the theorem supplies one rational map whose values match after each embedding. |
| 2917–2936: CCL relations with the stated specialization and trace. | Unverified — the oriented values theorem does not give the trace or Hecke comparison. |
| 8213–8217: apply the map to the points in the conductor-one sum. | Gap filled — the prepared values consumer gets the map at the fixed scale, with the existing CM source input. |
| 9347–9350: use rationality in the Frobenius comparison. | Unverified — rationality of the interior map is proved; the reduction compatibility is separate. |
