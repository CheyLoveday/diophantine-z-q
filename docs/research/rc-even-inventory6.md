# Ramified factors on the placed cuspidal inventory

Scoped stop. The placed ramified factor and the individual Whittaker translates follow from `PlacedCuspLists.RamifiedPrincipalInputsAt` on the actual newform and its exact attached representation. The remaining construction is the local principal-series realization of that newform, the Carayol comparison for its ordered character pair, and the diagonal normalization of the Whittaker functional when its undilated column is retained.

## Known issues

Tex 8162–8167 has the inherited missing base factor. The upstream even-row construction uses tex 8168–8182. The base spells the old/new independence premise `Li1975OldNewIndependenceWeightTwo`. The corrected citation and integration name are recorded in the inventory4 report. [Prior report](rc-even-inventory4.md#known-issues)

The locators for the inherited Casselman inputs remain UNVERIFIED against the print. The manuscript cites Casselman, *On some results of Atkin and Lehner*, Math. Ann. 201 (1973), Theorem 1 and the corollary on p. 306 and Theorem 4 on p. 313. The Lean proof below uses the inherited fixed-space predicate and an ordered normalized model in the remaining GLUE.

## Intrinsic character and reciprocity

- `tested_sourceLevel_exponent_one` gives the exact exponent of a tested prime in a ramified source's intrinsic level. `tested_sourceChar_at_tested_unit` pulls the computed block character back to the actual normalized newform using one retained column and the equality of its lifted nebentypus.
- `localUnitResidue_eq_one` reads the principal units in the first residue layer. The private `localUnitResidue_natCast` lifts each nonzero residue. Given `SourceCentralCharacterAt`, `sourceCentralCharacter_of_tested` uses the Chinese remainder theorem and quadratic reciprocity to identify the actual central character on norm-one scalars. `charConductor_of_localUnitResidue` proves conductor one.
- `quadraticChar_of_cyclotomic_action` uses the quadratic Gauss sum associated with a primitive $p$-th root. Its square is $p^*=(-1)^{(p-1)/2}p$, and changing the root to its $a$-th power changes the sum by the quadratic character of $a$. `reciprocity_quadratic_of_residue` translates this into the precise `bitChar p` condition on the inertia of the chosen prime.
- `localWeilReciprocity` uses the decomposition group's action on the quotient of the absolute integers by that prime. Its private helpers `residueFrob_infinite`, `residueAction_inertia`, `residueExponent_spec`, `residueExponent_inertia` and `residueExponent_frob` show that the restricted action has an integer exponent, zero on inertia and one on the selected arithmetic Frobenius. The map is $w\\mapsto p^{-n(w)}\\chi_{\\mathrm{cyc},p}(w)$. These are the valuation and unit coordinates of the inverse of arithmetic Artin reciprocity over $\\mathbb Q_p$. The first coordinate uses arithmetic Frobenius on the residue field. The second uses the inverse of the unit in the arithmetic cyclotomic action, as in Tau Ceti's `abelianizedLocalCyclotomicCharacter_artinMap_padic`. Lean defines the map on the existing global Weil subgroup and proves the two required coordinates. An identification via an isomorphism to Tau Ceti's local absolute Galois group is outside this construction.
- `localWeilReciprocity_residue` proves directly that its unit on inertia reads the action on $p$-th roots of unity. The auxiliary predicate `ReciprocityAt.ResidueCyclotomic` is a first-layer reciprocity equation, with no newform, representation, or sign in it. This proof discharges it for the map used by the row.

## Factor and row

- `induced_finrank_level_one` uses evaluation at the identity to prove directly that the fixed space of the ordered induced model is a line. The private `fixed_eq_zero_of_induced_eval` gives injectivity on that fixed space. The inherited factor still asks for the Casselman formula at every level.
- `orderedInducingCharacters_unique` applies the inherited local Hecke calculation to a single nonzero fixed vector in the two ordered induced realizations. Their values agree at the uniformizer. The private `unramified_eq_of_uniformizer` extends this to every element of $\\mathbb Q_p^\\times$, and `induced_central_eq` recovers the second character from the center.
- `ramifiedFactorOfPrincipal` builds `RamifiedFactor` on the given action and exact Galois matrices. Conductor one comes from the nonzero fixed vector and the central character. The supplied ordered induction gives the principal case of the inherited classification, and uniqueness extends the single Carayol comparison to the comparisons required by the factor's interface.
- `halfModulusOfRoot_complex` identifies the chosen character with the positive square root of the local norm after the complex embedding. `PlacedCuspLists.exists_placed_local_root` realizes that branch in the receiving completion from the square root in the enlarged field.
- `NormalizedCuspSource.localWhittakerTest_of_diagonal` factors each representative as an integral unipotent times $a(p)$. The single diagonal reading and integral-unipotent invariance give the individual classical integrals of the newform. The inherited proof gives the line scalar $a_p$ and the separate endpoint vanishings for the other retained degrees.
- `PlacedCuspLists.ramifiedLocalModelAt_of_principalInputs` assembles the exact inherited premise. `PlacedCuspLists.ramifiedLocalModelAt_of_localWeil` supplies its reciprocity and square root. `PlacedCuspLists.placedGaloisInput_of_carayol_of_principalInputs` feeds the inherited budget and rules-and-seed consumers on the same source attachments.

## Remaining hypotheses

The per-set input `PlacedCuspLists.RamifiedPrincipalInputsAt` (GLUE) is quantified over sources with intrinsic level divisible by the tested prime. It has the following parts.

| Input | Manuscript | Owner and scope |
| --- | --- | --- |
| `LocalPrincipalAction` on the actual source and `SourceCentralCharacterAt` | 9754–9756, 9799–9827, 9859–9861 | Adelic modular forms. Realize the local right-translation action and its fixed newvector over the placed field. Identify the center on units with the source nebentypus. Supply the ordered normalized model, the inherited Casselman dimension formula and the principal-series interchange. These data concern the local action and one character at a time. The Galois comparison and all translated Fourier values are separate. |
| `Nonempty (CarayolPrincipal Q (H s).ρ C J.μ₁ J.μ₂ half)` | 9773–9797, 9810–9811, 9866–9873 | Modular Galois. Establish local comparison in the two-dual convention for the one chosen pair and the homomorphism already attached by `attachmentOfCarayol`. This is a comparison of character lines. The characteristic-zero Hecke scalar and the Whittaker values are derived in Lean. The inherited good-prime attachment supplies its own Frobenius and conductor clauses. |
| `NormalizedCuspSource.LocalWhittakerDiagonal` on that same newvector, conditional on a retained degree-one column | 9841–9856 | Adelic modular forms. Give the normalized functional with integral-unipotent invariance and its reading $a_p/p$ at the one diagonal matrix. The finite translate identities and the row calculation are then theorems. |

These are GLUE suppliers. No new print is invoked. The work to realize the genuine local action and its functional requires an adelization and local-component interface for Tau Ceti's classical newform. The Galois supplier requires a compatible local comparison for the attached representation over the selected completion.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 8162–8167 | error | Inherited missing base factor. |
| 8168–8182 | OK | Exact expansion used by the inherited even laws. |
| 9638–9654 | OK | Per-set receiving field over the fixed valuation. The positive square roots can be adjoined once for that set. |
| 9655–9668 | OK | The inherited row uses the integral orbit construction. |
| 9754–9760 | gap filled | Exact intrinsic exponent and the unit computation are proved on each ramified source. Tame dilation is inherited. |
| 9762–9771 | OK | All old copies still refer to the attached representation of the same normalized source. |
| 9773–9779, 9786–9797 | unverified | The exact local Carayol comparison remains an input for one ordered pair. The normalization calculation and the inherited good polynomial are available. |
| 9784–9785 | gap filled | The integer Frobenius exponent gives the inverse uniformizer and the cyclotomic unit gives the geometric convention on inertia. |
| 9799–9801 | gap filled | Conductor one follows from the central character on the first residue layer and the supplied fixed vector. |
| 9802–9809 | unverified | The ordered normalized principal-series realization of the actual local newform is still needed. |
| 9810–9811 | gap filled | The quadratic Gauss sum reads the inertia sign from the residual cyclotomic action. |
| 9813–9827 | unverified | The previous function-space and level calculations apply. Interchange and the actual normalized induced realization are still inputs. |
| 9828–9840 | OK | The inherited finite $H_p$ sum and its scalar apply to the constructed factor. The complex half-modulus branch is checked. |
| 9841–9856 | gap filled | Individual translation values follow from the one diagonal reading. The latter still needs the genuine functional. |
| 9857–9861 | unverified | The inherited line scalar follows from those values and the dimension formula, which remains an input on the genuine action. |
| 9862–9864 | OK | The inherited row uses the empty Eisenstein sector. |
| 9866–9887 | OK | The inherited local calculation consumes the ramified factor and the unramified old contribution on the exact attachments. |
| 9919–9932 | OK | The inherited joint consumer reads each placed row. |

## Verification and count delta

VERIFIED in Lean 4.35.0. The inherited `PlacedRamifiedNewvector` and the added imports built. Each of the four new modules passed its own `lake env lean` check and module build. The independent `#print axioms` check covers all 38 new declarations, including the private helpers. It reports only `propext`, `Classical.choice` and `Quot.sound`. [Audit](../../scratch/rc-even-inventory6/Audit.lean) · [Axioms output](../../scratch/rc-even-inventory6/axioms.txt)

The one open per-set GLUE premise now reduces to `RamifiedPrincipalInputsAt` over the explicit geometric reciprocity coordinates and the positive half-modulus. Delta is four Lean modules and zero printed leaves, registered providers, additional axioms, or edits to existing modules.
