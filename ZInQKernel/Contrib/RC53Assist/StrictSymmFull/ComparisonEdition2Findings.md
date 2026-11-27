# Source-corrected retained cochain comparison: edition 2

## Outcome

CoefficientComparisonEdition2.lean is a new alternative edition; the reviewed CoefficientComparison.lean, its audit and its findings are unchanged. Route B still supplies the actual primitive full-condition contractions and reduced-switch symmetry conditionally. The source correction makes two formerly implicit external facts independent named GLUE inputs and weakens the used wild pro-order requirement to prime to two.

This edition exports the same namespaces as the reviewed one. Select one edition as an import; do not import both simultaneously. No frozen source, published history or previous audit was changed.

## Source classification

The complete bibliography of the supplied manuscript contains neither Neukirch–Schmidt–Wingberg nor Serre's Local Fields / Corps Locaux. The bibitem serrelocal is Serre's Local class field theory chapter in Cassels–Fröhlich, not Local Fields. The two external facts below are therefore marked GLUE, not manuscript-cited, and are not presented as printed assertions of Nekovář.

### Separate external kernel identification

NSWWildKernelIdentification is the explicit named GLUE input, with locator Neukirch–Schmidt–Wingberg, Cohomology of Number Fields, electronic second edition 2.3, p. 410, footnote to (7.5.2), together with normality of the maximal tame extension.

The maximal tame field is defined independently as the compositum of all finite tame local subextensions, using their fixed spectral valuations. The input identifies the existing unramified/uniformizer-radical compositum with this field and identifies its normal fixing core wildKernel with the fixer of the maximal tame field, Gal(K̄_v/K_v^t). This translation is no longer hidden inside either the tame-frame or small-complex premise.

### Only the needed odd pro-order

NSWOddWildProOrder is separate named GLUE, not manuscript-cited, with locator Neukirch–Schmidt–Wingberg (7.5.1), electronic second edition 2.3, p. 409. Its statement uses only the consequence needed here: at an odd residue-characteristic place, every finite open-normal quotient of the maximal-tame wild kernel has cardinality coprime to two. It does not assume the stronger pro-residue-characteristic assertion.

actual_wild_primeToTwo transfers this weaker fact through NSWWildKernelIdentification and combines it with the already proved closedness of the actual radical kernel. Nekovar721Structure now contains only the sourced tame-frame consequence, conditional on the named identification. RetainedTameStructure records the weakened conjunction, prime-to-two kernel plus actual frame; retainedTameStructure_of_sources constructs it from the two GLUE inputs and the frame consequence.

### Nekovar414Fibre: CONSEQUENCE

Source: Nekovář, Selmer complexes, Lemma 4.1.4, Astérisque p. 96. The proposition body is unchanged; its docstring now states the actual translation:

- Take R = Λ/P, complete Noetherian local with residue field F₂, not R = k(P).
- The stable finite-type lattice L = Λ · (1 ⊗ T₂E) and its dilates 2^(-m)L exhaust V = k(P) ⊗ T₂E. Thus V is ind-admissible by 3.3.4, p. 79, and 3.7.2, p. 94.
- Compactness of the actual local group or closed-normal quotient puts every continuous cochain's image in one lattice dilate. Conversely every finite-type admissible submodule fits in a dilate. The complex is therefore exactly 3.4.1.1 with differential 3.4.1.2, p. 82.
- Kernel triviality gives M^H = V and the retained inflation is the specified source map. Scalar restriction does not change cohomology.

The docstring labels the result CONSEQUENCE. It records that 3.7.4(ii), p. 94, is correct but unused in this direct ind-admissible route. Neither a discrete topology on V nor residue characteristic zero is substituted.

### Nekovar721Structure: CONSEQUENCE

Source: Nekovář 7.2.1, Astérisque p. 156, with the notation of 7.1.1, p. 155. After the separate kernel identification, the tame generator and geometric Frobenius lift lift to the actual local absolute group. Their images have dense inertia and satisfy t f = f t^L. No odd pro-order assertion is attributed to Nekovář.

### Nekovar723Fibre: CONSEQUENCE

Source: Nekovář Proposition 7.2.3, Astérisque p. 158, proof pp. 158–160; its C(M) is in 7.2.1, pp. 156–157, and its procyclic input in 7.2.2, pp. 157–158. The same R = Λ/P, lattice-union and compact-image translations are stated in the docstring with 3.3.4, p. 79; 3.7.2, p. 94; and 3.4.1.1–3.4.1.2, p. 82.

The proposition now takes NSWWildKernelIdentification explicitly. It uses the actual lifted tame generator and geometric Frobenius, not an unrelated quotient. The full geometric norm, C(M), and frameLambdaTwo are unchanged. The summation range, argument order and signs of the degree-two formula remain exactly those checked against 7.2.3. The unused 3.7.4(ii) clause is identified as unused rather than being used to justify the wrong coefficient ring.

## Downstream interface and proof preservation

The final actual_old_primitive_absolute_contraction, actual_old_primitive_full_condition_contraction, actualRetainedReduction, actual_reduced_switch_symmetry and actual_reduced_switch_rc26 explicitly take the named kernel-identification and odd-pro-order GLUE inputs in addition to the three CONSEQUENCE inputs. other_place_contraction does not require the frame-existence premise, because its arithmetic packet already specifies the actual frame.

The pure coefficient-identification proofs and the entire ContinuousReduction namespace are textually unchanged. The full norm, tame small complex and degree-two comparison formula are textually unchanged. The changed proof terms only transport the weaker pro-order fact, assemble the separated source inputs, and pass those inputs to the existing comparison and contraction constructors. The exact unified change is ComparisonEdition2.diff.

The conditional route B statement is unchanged in mathematical target: the actual reduced continuous switch satisfies Hsw StrictSymmTrunc and StrictSymm and the exact RC26 place-wise formula with the original genuine isotropy pulled back through the prescribed inclusions. The coefficient topology, retained local maps, traced cup pairing and contraction formulas are not replaced.

## Precisely remaining

1. Supply or authorize the two separate external GLUE values. They are not manuscript-cited printed facts and are not proved by this edition.
2. Supply or approve the three corrected CONSEQUENCE values with their explicit source-to-object translations. The translation text is documentation of these premises, not a new Lean proof of ind-admissibility or the cited quasi-isomorphisms.
3. At nonprimitive full places selected for erasure, provide OtherPlaceInputs: actual kernel triviality, the actual tame frame and the displayed operator-unit tests. Moving-stage witness/character binding and central-test Frobenius determinant/unit binding remain open.
4. Retain the erasure-set conditions: the new derivative place is not removed, each removed old condition is full, and the nonremoved old strict conditions have the required literal degree-two bound.
5. If a consumer needs the older quadratic normQ presentation literally, its norm/Frobenius identification with the full geometric-norm presentation is still separate. Route A for the original unerased forward homotopy remains unproved.

## Verification

The supplied single-file command compiled the new edition cleanly with six threads, the supplied CPU affinity and maxHeartbeats 600000. ComparisonEdition2Audit.txt contains 144 complete type/axiom report pairs covering all 77 theorems, plus the full bodies of the three CONSEQUENCE inputs, two GLUE inputs, the weaker aggregate and the maximal-tame definitions. The only reported axioms are propext, Classical.choice and Quot.sound. There are zero errors, zero warnings and no elisions. The temporary audit source was removed after verification.

All previously delivered editions remain byte-for-byte unchanged. No commits, project builds, generated imports, subagents, human outreach or memory writes were made.
