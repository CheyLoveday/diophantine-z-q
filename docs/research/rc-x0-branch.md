# Normalized branches of X₀(N)

For every nonzero level, `X0Branch.exists_stabilizer_germ_match` proves the
comparison of the inherited valuative lifts, `X0Branch.complexPoint_eq_iff`
identifies their fibers with Γ₀(N)-orbits, and `X0Branch.model N` constructs
`PreparedParam.X0Model N`. The model uses the same normalization, Laurent
function field, valuative points, and section expansions as the base.
There is no added print or manuscript hypothesis. The new proofs are on
the spot, provenance (c). All four files compile with serial
`lake env lean -j1 -DautoImplicit=false`. The 31 axiom checks report only
`propext`, `Classical.choice` and `Quot.sound`.

The chart's generic lift is the field embedding determined by the two
analytic j-germs, and its special point is evaluation at the center.
The inherited section comparison connects those two maps: near a chart
point the evaluators of regular functions are holomorphic and have exactly
the field-embedding germs. An affine neighborhood of the common point
has one étale coordinate by smoothness of relative dimension one. For
two nearby evaluations with the same coordinate, evaluate the complement
of the idempotent that generates the diagonal ideal in the relative tensor
square. Its value at the shared center is one and stays nonzero nearby.
It annihilates the differences between the two copies of every section,
so the nearby evaluations coincide.

Each pullback of the étale coordinate is nonconstant near its center:
otherwise local uniqueness would force the j-value to be constant there,
contrary to the local modular orbit theorem. The local holomorphic open
mapping theorem then matches nearby punctured parameters in the two
coordinate images. They have equal points on the normalization. Their
first plane coordinates agree by projection, and the second coordinates
agree by evaluating a common ratio of regular sections, whose denominator
is nonzero on sufficiently small punctured neighborhoods. The inherited
local orbit and identity principle argument gives a stabilizer element
matching the punctured sheet germs. This also covers the elliptic points.

## Statements and fields

The declarations are in `ZInQ.Manuscript.RC.X0Branch`.

| File | Statement | Field supplied |
| --- | --- | --- |
| `Unramified.lean` | `pairEval_tmul` evaluates a pure tensor as the product of its two evaluations when the maps agree on the base; `pairEval_self` gives evaluation after multiplication for two copies of one map. `continuousPairTest` represents any tensor by a continuous function of the parameters near the two centers, agreeing with tensor evaluation whenever the base evaluations agree. `eventually_eq_of_unramified` gives product neighborhoods of a common evaluation on an essentially finite type formally unramified algebra, in which agreeing on the base implies equality. | Local injectivity used for `complexPoint_eq_iff`. |
| `AffineEval.lean` | `affineEval_factor` reconstructs a complex point in an affine open from its section evaluations; `affineEval_congr` transports evaluations along equality of points; `affineEval_injective` gives the converse. `mem_basicOpen_iff_eval_ne_zero` identifies membership in a basic open with nonzero evaluation. `finiteChart_affine` asserts that the inverse image of the finite j-chart is affine; `chart_mem_finiteChart` puts every chart point in it. `eventually_chart_mem` keeps the lift in any open containing its center on a small complex neighborhood. `chartEval_center` and `chartEval_at_mem` compute the evaluation at the center and wherever the chart lies in the open. `chartEval_local` identifies the punctured germ with the valuative field realization and proves holomorphy; `chartEval_analyticAt` gives its holomorphic clause. `finitePointEval_eq` equates finite chart evaluations of equal scheme points. `exists_analyticJN_ratio` realizes the second coordinate by a fixed ratio of sections with nonzero denominator eventually at every punctured center. | Local evaluation of `complexPoint`, used for `complexPoint_eq_iff`. |
| `Overlap.lean` | `smooth_one` gives relative dimension one; `exists_etale_affine` gives an affine neighborhood carrying an étale map from a polynomial ring in one variable. `etaleCoordinate_agree` identifies two base evaluations with the same coordinate. `j_not_eventually_constant` rules out a locally constant first projection. `holomorphic_match` matches two nonconstant analytic germs at the same center value, with the second parameter in any prescribed neighborhood and distinct from its center. `eventually_overlap_of_complexPoint_eq` gives punctured overlap of the actual normalized chart points from equality at the center. | Local overlap needed for `complexPoint_eq_iff`. |
| `Model.lean` | `exists_stabilizer_germ_match`: if `complexPoint N (γ₁ • τ) = complexPoint N (γ₂ • τ)`, some `s : SL(2, ℤ)` fixes `τ` and the functions `z ↦ analyticJN N (γ₁ • ofComplex z)` and `z ↦ analyticJN N ((γ₂ * s) • ofComplex z)` are eventually equal at `𝓝[≠] (τ : ℂ)`. `complexPoint_eq_iff`: equality of two complex chart points is equivalent to one parameter being a Γ₀(N)-translate of the other. `model` bundles these with the inherited fields. | Full `complexPoint_eq_iff` and hence all fields of `X0Model N`. |

`pairEval`, `affineEval`, `finiteChart`, `chartEval`, and
`finitePointEval` are definitions used in these statements. The comparison
introduces no structures or propositions as hypotheses. The local
algebraic lemma uses the existing formal unramifiedness and finite
generation conditions on an arbitrary algebra; the analytic lemma uses
ordinary holomorphy and nonconstancy. These are separate inputs with no
modular sheet, normalized point, or orbit comparison in their statements.

## Remaining hypotheses

There are no remaining hypotheses for `PreparedParam.X0Model N` at
nonzero `N`; the level condition is exactly the one in the model
construction. For the downstream uses of this model:

| Input | Tex lines | Owner and size |
| --- | --- | --- |
| `AlgebraicParametrizationAtScale` | 2836–2838, 2916–2917 | Sibling lane `rc-param-at-scale`; substantial algebraic realization and comparison at the fixed analytic scale. |
| `CMFieldOfDefinition` and identification with the CM point chosen in the trace relation | 2915–2919 | Sibling CM work and its existing printed input; the chosen point and its descent are separate from this model. |
| Modular function field comparison needed by the downstream parametrization | 2836–2838 | Sibling lane `rc-modfn-field`; separate theory using the present model. |

## Known issues

- The manuscript does not cite Shimura 1971 for this model. The references
  at tex 770–771 and 11053–11057 are to the 1973 paper for a different step.
  The possible typo on conjugates recorded in the base report (reported
  p. 526, UNVERIFIED) is unused.
- The branch comparison uses the full complex point (including the residue
  embedding). Its underlying point on the rational scheme may be generic,
  for example over a transcendental j-value. The discrete place at a
  complex point is a statement over the complex base; one should not
  assume a nontrivial discrete valuation on the rational function field
  at every parameter. The affine étale proof does not require that
  assumption or a general analytification theorem.
- Coincident plane values at the center can occur for distinct normalized
  points. The argument uses the diagonal of the smooth model and
  punctured overlap. No manuscript error was found in the model steps used.

## Manuscript check

- Tex 1781–1788 — **gap filled**: the inherited rational model and formal cusp provide the source curve and the cusp used in the divisor. The elliptic quotient remains separate.
- Tex 2836–2838 — **gap filled**: the rational source model used with the stipulated modular parametrization is available at every nonzero level. The parametrization itself remains a sibling input.
- Tex 2839–2844 — **OK**: the additional hypotheses on the field and order concern the Heegner points and are not needed for the curve.
- Tex 2915–2916 — **gap filled**: the complex chart on the rational normalization has exactly the Γ₀(N)-equivalence of the level-oriented lattice parameters.
- Tex 2915–2919 — **unverified**: the CM field-of-definition and the cited trace relation are outside this comparison; they were not used.
- Tex 770–771 and 11053–11057 — **OK**: the Shimura citation is for a separate result and does not supply the model.
