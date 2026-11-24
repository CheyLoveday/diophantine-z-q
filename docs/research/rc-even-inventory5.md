# Placed Whittaker evaluations and the intrinsic ramified line

The retained cuspidal columns give the required finite Whittaker evaluations on the placed row. The ramified step stops at `PlacedCuspLists.RamifiedLocalModelAt` on the attached source representations. Once those local models give the individual translated newvector values, the comparison of the line scalar with the classical coefficient follows in Lean.

## Known issues

Tex 8162–8167 omits a base factor. The inherited proofs use the exact expansion at tex 8168–8182. The base still spells the existing old/new independence premise `Li1975OldNewIndependenceWeightTwo`. The integrator's corrected name and citation are recorded in [the preceding report](rc-even-inventory4.md#known-issues).

## Finite evaluations of the actual columns

For tex 9841–9856, take the finite matrices with $p$-component
$\left(\begin{smallmatrix}n&t\\0&1\end{smallmatrix}\right)$, where $t=0$ or $n=p$, and away components $a(np^j)$ for $j\in\mathbb Z$. This includes all positive diagonals, all $p$ translates at one, and their right-away translates. With $b$ the representative of $-t\bmod n$ in $[0,n)$, reduce using the rational matrix $\left(\begin{smallmatrix}n&-b\\0&1\end{smallmatrix}\right)$. Its inverse gives the slash representative $\left(\begin{smallmatrix}1&b\\0&n\end{smallmatrix}\right)$ up to a positive central scalar. The finite right corrections after translating by $n\widehat{\mathbb Z}$ are all upper triangular in the level group with lower-right entry one. At $p$ their upper-right entry is integral because $n\mid t+b$. Away from $p$, $p^j$ is a unit, and $b/n$ is integral since $b=0$ or $n=p$.

The elementary adelic integral reduction uses $[0,n)\times n\widehat{\mathbb Z}$ as a domain for $\mathbb Q\backslash\mathbb A_{\mathbb Q}$. For existence of a representative, clear the finitely many denominators and use the Chinese remainder theorem to subtract a rational number and land in $n\widehat{\mathbb Z}$ at all finite places. For uniqueness, the residual rational translates lie in $\mathbb Q\cap n\widehat{\mathbb Z}=n\mathbb Z$. The finite character is trivial on $n\widehat{\mathbb Z}$ and the finite measure contributes $1/n$. At real height one the reciprocal of the width-$n$ Fourier parameter to the $n$-th power supplies the real additive character and removes the archimedean Whittaker value. Lean proves the local matrix reductions and evaluates the resulting horizontal integral. The identification with the full adelic Haar integral uses the fundamental-domain argument above.

- `whittakerLocalReduction` checks the local level correction for each prime and each finite unipotent variable in the stated domain. `whittakerOffset_zero` and `whittakerOffset_add` handle the chosen representative, and `upper_level_of_norm` checks the upper triangular level matrices.
- `whittakerIntegral_eq` computes the individual integral as $a_n/n$. The private lemmas `whittakerSlash_hasSum`, `whittakerSlash_periodic`, `whittakerSlash_holo` and `whittakerSlash_bounded` use the individual Tau Ceti slash formula, the width-$n$ expansion and Mathlib's Fourier integral theorem. The integral translation has phase one in its $n$-th coefficient.
- `whittakerColumnsOfForms` lifts each integral through the given embedding. The private lemmas `isWhittakerTest_index`, `isWhittakerTest_away`, `whittakerIntegral_lifts`, `finiteWhittaker_eq` and `finiteWhittaker_away` establish uniqueness of the index, the away orbit and the lift. The inherited interface takes arbitrary matrices over the receiving field. Its function is extended by zero off the test locus, which is stable under the right-away multiplier.
- `PlacedCuspLists.whittakerColumnValues` uses the genuine `CuspDilation.form` of every retained column and its placed coefficient identity, including the undilated newforms. `PlacedCuspLists.dilationWhittakerAt_of_forms` supplies the exact inherited premise at each tested prime. The receiving field already contains the required values.
- `PlacedCuspLists.placedGaloisInput_of_carayol_of_ramified` inserts this supplier into the existing coefficient-one construction. The inherited path uses `WhittakerColumnValues.comparison` for the column sum and `WhittakerComparison.coeff_shift` via `cuspidal_upAtOne`.

## Ramified sources

| Input | What the tree supplies | Remaining |
| --- | --- | --- |
| Local action of the actual newform | Tau Ceti proves `Newform.heckeUCuspNat_eq_qExpansion_coeff_smul` on the classical form. The intrinsic source-level and old-degree tests are in `PlacedLocalLevels`. | Realize the genuine local component with its $K_1(p)$-fixed vector. |
| Central character and reciprocity | The block character is computed on the tested global units. Tau Ceti gives `artinMap` in the arithmetic convention, its unit/inertia formula, cyclotomic formulas, and a local-to-global comparison on finite layers. | Read the central character on this local action and identify its inertia restriction with `bitChar p` via geometric reciprocity on the Weil subgroup at the chosen absolute prime. |
| Casselman and normalized induction | `CasselmanCases`, `CasselmanOldspace` and `PrincipalInterchange` express the respective inputs. `conductor_one`, `ordered_principal`, `newspace_one` and `RamifiedFactor.line` derive the scalar given those inputs. | Supply the cases, fixed-space dimension and normalized induced realization on the actual local component. Casselman, *On some results of Atkin and Lehner*, Math. Ann. 201 (1973), newvector theorem, locator UNVERIFIED. |
| Local Carayol comparison | `CarayolThmAFrob` attaches the matrices using good-prime values and a conductor identity. `CarayolPrincipal` expresses the principal-series comparison and proves the two-dual normalization consequences when supplied. | Identify the attached matrices with the two local characters in the given normalization. The existing good-prime hypothesis supplies no ramified Frobenius comparison. |
| Classical newvector compatibility | The finite integrals and the classical bad-prime equation are available. | On the actual local vector identify its normalized Whittaker functional on the individual translates at one. |

`PlacedCuspLists.exists_with_local_square_roots` adjoins all the real square roots for a tested set at once and chooses a receiving place over the original fixed place. The row is rebuilt at that choice. `halfModulusOfRoot`, `halfModulusOfRoot_units` and `halfModulusOfRoot_uniformizer` give the unramified half-modulus and its normalization. The character and representation data still have to be supplied at the chosen field.

`ramified_scalar_complex_eq_sum` uses the dimension-one calculation to read the computed scalar on any level-one vector with functional value one. `whittaker_translate_sum_eq_classical` simplifies the sum of the individual integrals to the coefficient at one of the classical upper-triangular slash sum using Tau Ceti's coefficient formula. `ramified_scalar_complex_eq` applies that comparison to the newvector to obtain $a_p$. `PlacedCuspLists.ramifiedNewvectorAt_of_whittakerTests` descends this equality through the row embedding. `PlacedCuspLists.old_degree_endpoint_coefficients` proves that both endpoint coefficients vanish for every retained degree greater than one. `PlacedCuspLists.placedGaloisInput_of_carayol_of_localModels` then gives the precise input of `budgetRealization_of_placed` and `rules_and_seed_of_placed_joint`.

### Remaining hypotheses

- **`PlacedCuspLists.RamifiedLocalModelAt` (GLUE, tex 9754–9756, 9773–9840, 9855–9861 and 9866–9873).** For each `LocalPair p` and normalized source of intrinsic level divisible by $p$, supply the existing `RamifiedFactor` on that source's exact attached matrices. If the undilated column is retained, supply `NormalizedCuspSource.LocalWhittakerTest` for that factor. This input is on individual local representations, with no row operator, lattice, output coefficient or budget assertion. **Owners: local modular models and modular Galois.**
- **`NormalizedCuspSource.LocalWhittakerTest` (GLUE, tex 9841–9856).** On a supplied local action, choose its level-one vector and a complex Whittaker functional semilinear through the row embedding. Read value one on the vector and read the classical horizontal integral on each individually translated vector. This asks for the normalization and equivariance on a single source vector. The eigenvalue calculation, field descent, old-degree vanishing and row comparison are derived. **Owner: adelic modular forms.**

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited missing base factor. |
| 8168–8182 | OK | Exact expansion used by the inherited moving and unary laws. |
| 9638–9651 | OK | The original valuation is fixed and the coefficient field is chosen separately for a tested set. |
| 9652–9668 | OK | Use the inherited actual columns and integral orbit construction. |
| 9754–9760 | gap filled | Exact level and tame degrees are inherited. Both endpoint coefficients at every other retained degree now have a standalone calculation. |
| 9762–9771 | OK | All copies use the same attached representation of the normalized source. |
| 9773–9797 | unverified | The good polynomial is inherited. The ramified comparison on the attached representation is open. |
| 9799–9811 | unverified | The conductor-one logic is available. The actual local action, central-character identification, reciprocity and Casselman inputs still need suppliers. |
| 9813–9840 | OK | The normalized induced-line calculation is inherited. The half-modulus is realized after a finite field enlargement. |
| 9841–9848 | gap filled | The local reduction and individual translate integrals supply the finite sum used at one. |
| 9850–9854 | gap filled | The actual column integral gives $a_n/n$ over the row field. |
| 9855–9861 | unverified | The scalar is computed from the single-source compatibility, which remains an input for the genuine local action. |
| 9862–9864 | OK | The inherited row uses the empty Eisenstein sector. |
| 9866–9887 | OK | The inherited characteristic-zero calculation consumes the ramified line and the unramified old part. |
| 9919–9932 | OK | The joint consumer reads independently placed rows. |

## Verification and count

VERIFIED in Lean 4.35.0. The inherited `PlacedLocal` target built, and all three new modules passed individual `lake env lean` checks and module builds. The audit covers all 37 new declarations, including the private helpers. It reports only `propext`, `Classical.choice` and `Quot.sound`. [Check file](../../scratch/rc-even-inventory5/Audit.lean) · [Axioms output](../../scratch/rc-even-inventory5/axioms.txt)

Three Lean modules were added. The two inherited local premises on the row reduce to one named GLUE premise with its per-source compatibility predicate. The count delta for printed leaves, registered providers, axioms and edits to existing Lean modules is zero.
