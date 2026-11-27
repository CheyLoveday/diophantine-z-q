# Retained full local conditions: partial all-degree continuation

## Status

Route B is still partial. The primitive-place operator hypotheses and displayed tame-model contractions are now proved for the actual coefficient fibres. An all-degree contraction is also constructed for a genuine primitive quadratic/unramified quotient model with the actual lattice topology. The retained absolute-local-cochain comparison is not proved, so this continuation does not assemble StrictSymm or StrictSymmTrunc for the actual reduced switch.

No symmetry condition is an input to the new results. No new printed fact packet is introduced. The existing module hypotheses, including full two-power torsion over the smaller coefficient support and continuity of the coefficient character where needed, remain explicit.

## Verified results

### All-degree continuous prism

The central-scalar criterion is proved in the actual continuous cochain model, not only in degrees zero and one. If a central element a acts on the coefficient module by c and c - 1 is a unit, the homogeneous prism divided by c - 1 gives dH + Hd = 1 in every positive degree and the correct degree-zero identity. The contraction is transported through the homogeneous/inhomogeneous continuous-cochain dictionary and extended by zero to negative integer degrees.

The main constructions are homogeneousContraction, continuousContraction, extendContraction, fullContinuousContraction and fullContinuousConstContraction. The last one requires only continuous constant scalar maps. Its auxiliary discrete scalar topology does not change the coefficient topology, group action or continuous cochains. In particular, the coefficient module is not replaced by a discrete module.

Centrality is essential to the proved criterion. Centrality in a quotient is not asserted for a lift in the absolute local Galois group.

### Actual old primitive primes

The local square root is the image of the actual global square root s in K_S through the retained embedding. localRoot_square and localRoot_localization prove the square and action compatibilities. At an actual prime where the localized radicand has normalized valuation one and odd residue characteristic, exists_actual_primitive_inertia constructs an inertia element with actual quadratic-character value -1.

The Tate-inertia premise is discharged from the smaller coefficient support. Under HasFullTwoTorsion K S_0 W, the inclusion of the actual torsion into geometric torsion shows that every torsion level over K_S is fixed by inertia outside S_0. tate_fixed_outside_coefficient_support then proves the same for the whole Tate inverse limit. inflated_character_inertia_one proves that the moving character inflated from S_0 is trivial on that inertia.

Consequently, exists_actual_old_primitive_unit proves, for every permitted odd height-one test prime P and every actual old primitive place covered by these support and valuation hypotheses, the existence of an actual inertia element acting by -1 on

    VP K S W P (lambdaChar (quadChar s) (xi_0 composed with inflation)).

Its inertia-minus-one operator is -2 and is a unit. Neither a Tate-action identity nor a unit operator is assumed in this final primitive-place theorem.

primitive_fibre_tame_relation proves the displayed tame matrix relation using the actual retained fibre operators. primitiveFibreTameComplex uses those operators in the manuscript's three-term model. exists_actual_old_primitive_tame_contraction constructs its contracting homotopy for every actual local Frobenius choice and every parameter r of the existing q = 2r + 1 norm interface. This is a contraction of the displayed tame model, not yet of the retained full absolute-local-cochain condition.

### Primitive quadratic/unramified quotient

PrimitiveQuotientModel uses the actual unramified quotient Gal(K_v^ur/K_v), the canonical factor urFactor, and the actual smaller-support fibre VP K S_0 W P alpha_0. The product with the quadratic sign group acts jointly continuously for the retained lattice topology.

quadraticQuotientMap is the actual local restriction paired with the actual quadratic character. quadraticQuotientMap_primitive sends a primitive inertia element to the central sign (1,-1). quadraticQuotientMap_surjective proves surjectivity using that actual sign and surjectivity of the unramified restriction. pullback_action identifies the pulled-back quotient action with the actual quadratic twist of the smaller-support fibre's local action.

PrimitiveQuotientModel.contraction contracts all continuous cochains of this quotient in every integer degree. The group is the primitive quadratic/unramified quotient; it is not claimed to be the whole tame quotient or a procyclic replacement of the entire absolute local group. A surjective group map and a contracted quotient do not by themselves provide a retained inflation homotopy equivalence.

### Moving scalar calculation

fibre_moving_inertia proves the conditional formula sigma - 1 = X on the actual lambdaChar fibre when the stated Tate and character values hold. fibre_moving_inertia_unit proves that this operator is a unit away from P = (X).

No inertia witness for every actual finite moving stage is constructed. No identification of every finite moving-stage character with this lambdaChar interface is asserted. At P = (X), the required actual Frobenius unit hypotheses are not proved by this calculation.

## Precise remaining inputs

1. For each retained full place to be removed, construct the all-degree homotopy comparison from the actual full continuous cochains of the local absolute Galois group on the actual switch coefficient fibre to the appropriate tame model. The comparison must retain the specified local maps and homotopies. Neither the central-scalar criterion nor the contracted primitive quotient constructs this comparison.
2. Where the smaller-support quotient model is used, construct the continuous coefficient identification with the actual switch's larger-support fibre. The proved inertia-fixing result is not a continuous Tate-module or fibre isomorphism. No such coefficient isomorphism is included in this continuation.
3. Supply the wild/tame inflation and procyclic-inertia comparisons for the actual lattice-topologized fibres in all degrees. The existing UnramifiedQIso and UnramifiedCondition interfaces use finite discrete coefficients and cannot simply be applied to these fibres. A two-term finite-discrete calculation is not an all-degree comparison for the actual fibre.
4. Bind the moving-stage character data and the remaining Frobenius operators to the actual old primes, especially at the central moving test P = (X). The displayed moving operator unit alone also does not prove the tame matrix relation. For commuting Phi and g, the existing tameCommutingCriterion requires r(g^2 - 1) = 0 in the current normQ interface. The primitive sign supplies this relation; it is not established here for a generic moving fibre. This model-compatibility obligation must be checked against the actual finite-stage norm before using that comparison.
5. Select precisely the retained full places with genuine full-cochain contractions. Unused or unramified retained full conditions are not erased merely because the primitive-place theorem applies elsewhere. The nonremoved old conditions still have to satisfy the degree-two bound required by RetainedFullReduction.

With these actual comparisons, the prior full_contraction_of_tame_comparison or full_contraction_of_primitive_tame_comparison constructs the full contractions. They can populate RetainedFullReduction. The prior reduced_strictSymmetry then proves the RC26 StrictSymm and both Hsw symmetry conventions for the actual reduced switch, with the pullback of the original genuine isotropy datum. The prior retained-arrow, isotropy and traced-pairing preservation theorems remain unchanged. This implication is the intended route B; its actual comparison inputs are not supplied here.

There is also an independent import obstruction: ZInQKernel.Contrib.RC53Assist.StrictSymmFull.FullReduction has no built .olean in the supplied import environment. No build or import generation was run. The existing source and its earlier audit are unchanged.

Route A, literal strict symmetry of the original chosen forward homotopy on retained full absolute cochains, remains unproved.

## Verification and audit

LocalContractions.lean compiles with the supplied single-file command, six threads, the supplied CPU affinity, and maxHeartbeats 600000. It contains 34 theorems and 76 named declarations including definitions and instances. ContinuationAudit.txt contains 76 complete, unabridged type/axiom report pairs, including every theorem's exact statement. The only reported axioms are propext, Classical.choice and Quot.sound. The audit has zero errors, zero warnings and no elisions. Its temporary source was removed after the log was captured.

The earlier FullReduction.lean, Findings.md and Audit.txt editions retain their previous byte lengths and SHA-256 hashes. Only the new continuation source and its new supporting files were written. No commit, checkout, repository-history operation or project build was performed.
