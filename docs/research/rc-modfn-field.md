# Modular parametrization coordinates in the rational function field

**Scoped stop: the complex converse at level `N`.** At the specified nonzero rational scale, both coordinates have convergent rational Laurent series at infinity, with pole bounds two and three; the coefficient of `q⁻²` in `x` is `κ⁻²`. The series satisfy the formal affine Weierstrass equation. Both coordinates also have meromorphic germs and convergent Laurent series in the local parameter at every cusp. Rational descent from the specified complex Laurent subfield is proved. `coordinates_in_modularFunctionField` gives the exact bilateral `HasSum` proposition of [the at-scale report](rc-param-at-scale.md) assuming only the complex converse below in addition to the existing curve and scale data. Field membership and the downstream at-scale proposition are still open unconditionally. No print was added. The work here is on-the-spot (c): the manuscript supplies the map by a quotient and isogeny, and does not cite the analytic classification used in this route.

## Exact remaining proposition

This is `ZInQ.Manuscript.RC.ModFnField.ComplexCuspClassification N` in `FieldMembership.lean`. Fix `N : ℕ` with `[NeZero N]`, and let `translatedLevel N σ = σ⁻¹ Γ₀(N) σ` in the real matrix group. With the namespace openings of that file, the assertion is:

```lean
∀ (g : ℂ → ℂ) (s : LaurentSeries ℂ),
  MeromorphicOn g {z : ℂ | 0 < z.im} →
  (∀ σ : SL(2, ℤ), σ ∈ CongruenceSubgroup.Gamma0 N →
    ∀ τ : ℍ, g (σ • τ : ℍ) = g τ) →
  (∀ σ : SL(2, ℤ), ∃ (G : ℂ → ℂ) (T : ℝ), MeromorphicAt G 0 ∧
    ∀ τ : ℍ, T < τ.im →
      G (Function.Periodic.qParam (translatedLevel N σ).strictWidthInfty τ) =
        g (σ • τ : ℍ)) →
  (∃ T : ℝ, ∀ τ : ℍ, T < τ.im →
    HasSum (fun m : ℤ => s.coeff m * Function.Periodic.qParam 1 τ ^ m) (g τ)) →
  s ∈ modularFunctionFieldC ℂ N
```

The conclusion only classifies an already supplied complex Laurent series. It says nothing about constructing a rational series, descending it, elliptic periods, an `X0Model`, or compatibility with the analytic parametrization. In particular it is strictly less data than the two rational series and their analytic realizations in the target; the proof supplies those local realizations separately and uses `modularFunctionField_descent` to infer rational membership. This isolates the analytic field classification of step 3 independently of the elliptic curve. `RationalTaylor f z` only says that each derivative at one center belongs to the image of ℚ in ℂ. It gives neither convergence nor a modular function; it is local input for computing rational coefficients in step 1. `Realizes a g` supplies a convergent tail for one complex Laurent series. It supplies neither field membership nor an equation relating two series; it is used for the equation comparison and as the analytic interface for the map. No other new definition is a structure or a packaged hypothesis.

To prove the converse by the proposed route, first prove the level-one statement for complex coefficients with interior poles. The vendored `mem_adjoin_jq_of_hasSum_of_slash_invariant` handles the rational series converging on the whole upper half-plane and gives polynomial membership; it does not treat poles in the upper half-plane. A level-one proof can clear the finitely many interior pole orbits by multiplying by factors `(j - j(p))` to sufficient orders. Finiteness uses a truncated fundamental domain and meromorphy in the cusp chart. Cancel the remaining principal part using the simple pole of `j`, then use the weight-zero constancy theorem. For level `N`, form the coset orbit polynomial. Its coefficients are invariant at level one and meromorphic at infinity: form them in a common multiple of the cusp widths, then translation by one forces only the integer powers. Use the identification of the coset count with `dedekindPsi N`, and build the field of these functions modulo equality of meromorphic germs to accommodate isolated point values. Pass through its Laurent expansion at infinity and identify the two generators as the vendored `j(q)` and `j(q^N)`. The vendored `finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi` and the checked degree lemmas then finish the equality. The compositum argument is needed so that the uniform degree bound applies to sums and products, through a primitive element, as well as to each original function.

## Checked statements

All theorem names below are in `ZInQ.Manuscript.RC.ModFnField`, in the indicated file under `ZInQKernel/Contrib/OneProof/RC/ModFnField/`.

| File and theorem | Statement and use |
| --- | --- |
| `Cusps.scaledPrimitive_cusp` | For every integral determinant-one `σ`, the strict width of the conjugated group is positive and an analytic germ at zero realizes `scaledPrimitive f κ (σ • τ)` in its local parameter. This is the cusp extension of the primitive, step 2. |
| `Cusps.coordinates_cusp_meromorphic` | Both affine coordinates have meromorphic representatives at zero in the same parameter. This includes a lattice value of the limiting primitive. Step 2 and input to the complex converse. |
| `Laurent.hasSum_laurent_shift` | For nonzero `q`, shift the coefficients of a power series by `-d` to turn its sum `q^d * g` into the Laurent sum `g`, through any coefficient ring map to ℂ. Steps 1 and 2. |
| `Laurent.meromorphicAt_hasSum_laurent` | A function meromorphic at zero admits a complex bilateral `HasSum` on a punctured disk, with all coefficients below `-d` zero for some natural `d`. Step 2. |
| `Laurent.coordinates_cusp_hasSum` | At each `σ∞`, both complex bilateral series converge to the translated coordinates on a common tail, with finite principal parts. Step 2. |
| `Weierstrass.weierstrassP_split` | ℘ is `z⁻² + regularPart L z`. Step 1. |
| `Weierstrass.derivWeierstrassP_split` | The lattice ℘′ is `-2 z⁻³ + deriv (regularPart L) z`. Step 1. |
| `Weierstrass.deriv_weierstrass_second` (private) | Away from the lattice the derivative of ℘′ is `6 ℘² - g₂/2`. Step 1 recurrence. |
| `Weierstrass.regularPart_ode` (private) | Near zero, writing `u = regularPart L`, `z² u″ = 12 u + z² (6 u² - g₂/2)`. Step 1 recurrence. |
| `Weierstrass.iteratedDeriv_mul_sq` (private) | The order-`n+2` derivative of `z² u` at zero is `(n+2)(n+1) u⁽ⁿ⁾(0)` for analytic `u`. Step 1 recurrence. |
| `Weierstrass.regularPart_derivatives_rational` | With `IsLatticeOf E L`, all derivatives of the regular part at zero are in the image of ℚ. The recurrence determines all except the order-four term, fixed directly by `g₃`, and starts with the constant and linear terms zero. Step 1. |
| `RationalTaylor.const`, `id_zero` | A rational constant at any center and the identity at zero have rational Taylor coefficients. Step 1. |
| `RationalTaylor.add`, `sub`, `mul`, `pow` | For analytic functions at the same center, rational Taylor coefficients are preserved by sum, difference, product and natural powers. Step 1. |
| `RationalTaylor.comp`, `inv`, `deriv` | Rational Taylor coefficients are preserved by analytic composition at the matching centers, analytic reciprocal at a nonzero value, and differentiation. Step 1. |
| `RationalTaylor.factor_at_zero` | For analytic `f` with rational Taylor coefficients and `f(0)=0`, locally `f(q)=q u(q)` with analytic rational Taylor series for `u` and `u(0)=f′(0)`. Step 1. |
| `Infinity.primitive_rationalTaylor` | At rational scale, the primitive is represented by an analytic function of `q` with rational Taylor coefficients, value zero and derivative `κ` at zero, given the elliptic Dirichlet coefficients of the cusp form. Step 1. |
| `Infinity.coordinates_rationalTaylor` | After multiplying by `q²` and `q³`, respectively, the coordinate germs at infinity are analytic with rational Taylor coefficients. The cleared x-coordinate has value `κ⁻²` at zero. Step 1. |
| `RationalExpansion.rationalLaurent_of_cleared` | An analytic pole-cleared germ with rational Taylor coefficients gives a rational Laurent series realizing the original tail, supported in degrees at least `-d`, with coefficient at `-d` equal to the cleared value at zero. Step 1. |
| `RationalExpansion.coordinates_rationalLaurent` | Two rational Laurent series realize the analytic coordinates on one tail. The pole bounds are two and three, and the x-coordinate has coefficient `κ⁻²` at degree `-2`. Step 1 and the later nonconstancy check. |
| `Descent.complexify_coeff` | Extending coefficients from ℚ to ℂ casts each coefficient. Step 3 descent. |
| `Descent.project_zero`, `project_add` (private) | Applying a rational linear functional coefficient by coefficient preserves zero and addition. Step 3 descent. |
| `Descent.project_scalar` (private) | Projecting a complex scalar times a rational series replaces that scalar by its projected rational value. Step 3 descent. |
| `Descent.project_mul` (private) | Projecting a complex linear combination of rational field elements commutes with multiplication by a rational series. Step 3 descent. |
| `Descent.project_mem` (private) | Those projections belong to the original rational field. Step 3 descent. |
| `Descent.mem_rat_adjoin_of_complexify_mem` | For any set of rational Laurent series, a rational Laurent series belonging after complexification to the complex generated field already belongs to the rational generated field. Clear denominators and project using a rational linear functional detecting a nonzero denominator coefficient. Step 3 descent. |
| `Descent.modularFunctionField_descent` | Specializes the preceding result to the vendored generators `j(q)`, `j(q^N)` at every nonzero level. Step 3 descent. |
| `Degree.integral_degree_of_orbit_product` | If the product of linear factors over a finite index set is the image of a base-field polynomial, each listed root is integral, with minimal polynomial degree at most the number of factors. Step 3 degree bound. |
| `Degree.intermediateField_eq_top_of_degree_bound` | In characteristic zero, a finite intermediate field equals the entire field if every element is integral and has degree at most that intermediate field's degree. Step 3 degree comparison. |
| `Tail.support_rescale`, `rescale_mul` (private) | Rescaling a Laurent series by multiplying its degree-`n` coefficient by `c^n` for nonzero `c` preserves support and commutes with multiplication. Step 3 operations on the expansion field; step 4 equation. |
| `Tail.lt_im_raise`, `qParam_raise`, `hasSum_rescale` (private) | Translation by `i T` for `T ≥ 0` raises height above `T`, multiplies `q` by `q(i T)`, and gives the rescaled series the same sum as evaluating the original series at the rescaled parameter. Steps 3 and 4. |
| `Tail.laurent_unique_of_tail`, `hasSum_mul_of_tail` | Equality of analytic sums on a common tail implies equality of formal coefficients; multiplication of formal series realizes the product on that tail above height zero. Steps 3 and 4. |
| `Equation.Realizes.const`, `add`, `mul`, `pow` | Tail convergence respects constants, addition, multiplication and natural powers. Step 4 equation. |
| `Equation.Realizes.eq_of_eventuallyEq` | Two series realizing eventually equal functions at infinity are equal. Step 4 equation. |
| `Equation.scaledPrimitive_off_lattice_on_tail` (private) | The primitive avoids its period lattice on a tail at infinity, using the simple zero of the primitive and discreteness of the lattice. Step 4 equation. |
| `Equation.coordinates_laurent_equation` | Rational Laurent realizations of the two coordinates satisfy the affine Weierstrass equation in ℚ((q)). Step 4 equation. |
| `FieldMembership.qParam_zpow_widthOne` (private) | `q^m` equals the width-one exponential monomial used by the at-scale proposition. Step 4 interface. |
| `FieldMembership.coordinates_in_modularFunctionField_with_equation` | Under the same inputs, gives rational field elements realizing the coordinates, with the formal equation and leading x-coefficient. Step 4 field map. |
| `FieldMembership.coordinates_in_modularFunctionField` | Given the complex converse, a rational scale with `IsParamScale`, `IsLatticeOf`, and the Fourier normalization, produces two elements of the exact rational modular function field and a common height with the exact bilateral exponential sums. Discharges the at-scale report's proposition conditional on the converse. |

## Remaining hypotheses and owners

| Input or comparison | Tex and owner |
| --- | --- |
| Complex converse stated above. Remaining analytic ingredients: complex level-one classification allowing interior poles, orbit-polynomial coefficients at level one with their cusp compatibility, identification of analytic cosets with the finite index count, and the map from meromorphic functions to the embedded Laurent field. | 1781–1787, 2836–2838; missing theory (large). |
| Matching fixed scale: for the originally fixed complex `κ₀`, a nonzero `κ : ℚ` with `(κ : ℂ) = κ₀`; also the existing `IsParamScale` for that lattice. Changing to another scale would not prove agreement with the fixed map. `IsLatticeOf`, the elliptic Dirichlet coefficients, and the period inclusion are the existing curve/analytic setup hypotheses. | 1779–1787, 1825–1828; ELLIOT input for the fixed normalization, existing tree for the supplied curve data and period interfaces. |
| Transfer the affine equation to the two Laurent series by convergence and uniqueness; use the nonzero leading coefficient to obtain a field embedding, then compare projective chart values including the identity. Identify the analytic basepoint with the specialization at the algebraic cusp for the manuscript's normalization. | 1785–1787, 2836–2838; missing theory (local to medium after the converse). |
| A source `X0Model N` with its interior chart and section expansions; the algebraic cusp used for normalization is additional. | 1781–1787, 2836–2838; sibling `rc-x0-model-2` for the source model. |
| `CMFieldOfDefinition X` for the prepared-param and Stage Kummer consumers. | 2839–2844, 2915–2917; ELLIOT input isolated in `RC/PreparedParam/`. |
| Elkik's genuine cusp class comparison: the image of `[c(r)] − [∞]` under `α q_f` is the specialization of the based map, identified with the analytic cusp torus limit. The earlier cusp limit already gives a single rational scalar at every cusp. | 1785–1788, 2937–2946; missing Jacobian and cusp specialization theory (large, excluded here). |
| Oriented CM representatives and embeddings with the specified chart equalities. For the CCL trace conclusion there are also Hecke compatibility, `T_q[∞]=(q+1)[∞]` and trace-to-Galois comparisons. | 2839–2846, 2915–2936; sibling `rc-heegner-values` for the CCL route, missing geometric comparison (large). |

The at-scale consumers therefore keep their existing conditions. The prepared-param chain would get its common dominant morphism at the fixed scale, the Heegner-values chain would get the specified values after each chosen embedding, and the Elkik chain would have the analytic germ comparison on the rational map. The comparison with genuine cusp classes for Elkik remains separate.

## Known issues

- The proposed orbit argument in the brief calls the symmetric coefficients polynomials in `j`. With interior poles, only rational functions of `j` are warranted: already at level one `1/(j-a)` has an interior pole for any attained value `a`. This is a correction to the proposed proof, not to the manuscript.
- The existing audit in `RC/PrintsAnalytic/Milne.lean` records that Theorem 11.19 and Remark 11.18 cover the map and quotient; the separate normalized-newform locator is Proposition 11.21, and the cited pair does not give the Hecke equality in tex 1788. The audit records two unused issues in Conjecture 11.17, “prime” versus “prime to `N`” and a duplicate conductor factor. These locators and issues are reported from that audit; no new source verification or print is claimed.

## Manuscript check

| Tex lines and step | Verdict |
| --- | --- |
| 1779–1780: modularity at the conductor. | OK — the existing modularity interface supplies the coefficient normalization for the actual curve. |
| 1781–1784: the rational newform and elliptic quotient. | Unverified — the rational Fourier data are used; the Jacobian quotient is outside this proof and the existing source audit gives the more precise newform locator. |
| 1785–1786: choose the isogeny and form the based rational map. | Gap filled — for the alternative analytic route the coordinate series are rational and have the required cusp germs, and descent from the complex field is proved; the complex converse and projective comparison are still open. |
| 1787: `π(∞)=0`. | Unverified — the primitive has value zero in the analytic cusp parameter; comparison to the algebraic cusp is open. |
| 1787–1788: Hecke equivariance. | Unverified — the cited pair does not supply this identity and it is unused here. |
| 1825–1828: use the fixed period normalization. | OK — the statements keep the specified scale as a parameter and use only its rationality, nonvanishing and period condition. |
| 2836–2838: fix one based parametrization over ℚ. | Gap filled — the exact Laurent-series handoff is now conditional only on the complex converse for the existing rational-scale data. |
| 2839–2846: specify the CM conductors and class fields. | Unverified — unchanged; no class-field realization is used in the coordinate proof. |
| 2915–2936: evaluate and compare the oriented CM points. | Unverified — the earlier conditional consumer is unchanged; the CCL comparisons are separate. |
| 2937–2946: cusp differences and Manin–Drinfeld. | Unverified — local analytic cusp germs are now proved, but their identification with the image of algebraic cusp classes is still required. |
