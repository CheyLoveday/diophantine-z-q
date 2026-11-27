# Bound endpoint readbacks and independent cone determinants

## Status

This continuation repairs the statement-strength classification identified in the independent review and supplies stronger fixed-data endpoint interfaces and independent determinant calculations. It is a verified partial construction, not a proof of the manuscript's remaining arithmetic `OrigCoordLink3` identification.

The new endpoint types retain the selected step, matrix and representative readbacks. The preferred `FibreBinding` uses the actual native finite clearing-field fibre, the class lifted through `M.ψf`, and the fixed `pairedRow`. It retains the functional homotopy and permits arbitrary common coefficient carriers, including Laurent carriers. It contains no coordinate-equality or cone-normalization field. The optional direct integral two-term binding is kept conditional and its H3-torsion obstruction is proved explicitly.

The cone determinant is calculated independently for the fixed graded isomorphism, the stored original-to-triangular two-term basis change, and the actual native full-condition singular cancellation. The actual native cancellation factor is `det(B)⁻¹`, not an assumed factor one. The comparison from the native remaining model to the selected stored endpoint still needs to be constructed and independently normalized from the actual diagrams.

All earlier committed source editions are preserved. No new printed proposition, power-series-unit lift of the correction, or casewise coordinate-identity premise is introduced.

## 1. Review correction: earlier exports are conditional

`ConditionalEndpoints.md` is the classification addendum for the earlier endpoint exports.

- `Scalar.existing_relaxation_endpoint`, `existing_endpoint_on_carrier`, their Laurent/relabelled consequences and their reproduced versions are conditional algebraic extractions. Their exported existential forgets the selected step's matrix/vector readbacks and must not be credited as bound actual provenance.
- `Endpoint.original_coordinate_eq_existing_relaxed`, `ExistingRelaxationRealizationG.retained_basis` and the final realization-based clearing consumers are conditional algebraic reductions with an open determinant-normalization leaf. At fixed nonzero target coordinate and nonzero cone torsion, that uncomputed normalization is equivalent to coordinate equality. Syntactic absence of a coordinate-equality field is not independent arithmetic evidence.
- This correction is to the claimed statement strength, not to the kernel validity of the algebraic proofs. The concrete coefficient realizations, fixed-data comparison formula and field-level inverse-disk calculation remain valid partial results.

`EndpointObstructions.lean` records twelve theorems found in independent reviews: the round-3 free/zero endpoint and normalization obstructions, the same-disk/integral-inverse obstructions, and the additional exact four-dimensional fixed regular-matrix/adjugate/closure probes for the round-4 `StoredRegularity` exports. The integral pole obstruction uses the actual power-series/Laurent realization at `X`. The two deprecated conditional simplification names in the new probe are replaced by their current equivalent names.

At zero coordinates the old normalization field is stronger than coordinate equality. No equivalence of the entire realization record with the whole `OrigCoordLink` proposition is claimed.

## 2. BoundEndpoint.lean: selected fields are retained

Namespace: `ZInQ.Contrib.RC53Assist.CoordProvenance.BoundEndpoint`.

### Selection is not erased

`StepData` retains the complete matrix datum of one stored `ActualStep`: both original matrices, the four basis comparisons, the off-diagonal block, both class vectors and functional rows, the existing coordinate identities, primitive adjugate regularity and the step-unit expression. `selected_data_exists` and `selected` return this complete datum. `StepData.toActualStep` reads it back to the original step proposition.

This selection alone is not an actual Selmer model binding. It is explicitly classified as selected matrix data, rather than advertised as an actual class/functional producer.

`StepData.adjugate_ne_zero` proves regularity of the same fixed `s.DR` from its actual local block and primitive adjugate. It does not choose a different matrix carrying the scalar.

### Common realization keeps all readbacks

`CommonLift s f` is indexed by that fixed selected step. Its matrix and two vectors have explicit readbacks

`D.map f = s.DR`, `f ∘ z = s.zR`, `f ∘ w = s.wR`.

`CommonLift.stored_coordinate` has those exact fixed lifted fields in its conclusion. `relabel_readback` preserves the same relationships through relabelling. `common_fraction` transports a numerator and denominator without existentially replacing the matrix or either representative.

The native integral/sign specialization gives exact Laurent matrix/vector readbacks and exact clearing readbacks through the previously proved coefficient maps. `fixed_laurent_coordinate` preserves the existing scalar in the actual Laurent inclusion, on those same fixed fields.

The whole group-algebra sign evaluation is not asserted to be injective. The generic `common_fraction` theorem is used only with its displayed injectivity hypotheses; the concrete common-field component maps from `CoefficientRealization.lean` are the appropriate injective maps for fractional transport. The native specialization currently requires the displayed integral group-algebra lift of the stored power-series step. Generic `StepData`/`CommonLift` support other commutative carriers, but existence of the corresponding matched arithmetic Laurent-model lift is not proved here.

### Optional direct integral two-term binding

The direct `SelmerBinding` variant in this file is conditional and deliberately **not** the preferred generic arithmetic interface. A two-term complex over the completed integral coefficient ring would force integral H3 to vanish. `integral_h3_cycles_are_boundaries` and `no_integral_twoTerm_binding_of_nonzero_h3` record that obstruction. When actual integral H3 torsion is present, do not impose this variant; use the clearing-field `FibreBinding` below.

`coreCx` is the fixed two-term complex defined from `E.D`, not from the scalar.

`SelmerBinding s χ E M zActual hzActual P tr htr zc hzc` contains:

- a quasi-isomorphism from the completed fixed endpoint model to the same genuine family Selmer complex of `M`;
- the same fixed endpoint class representing the supplied actual family class, with an explicit actual boundary;
- values of the same fixed endpoint row equal to the actual `PD(-, conjugate class)` functional on this model map.

The actual functional is `ActualFull.rightFunctional P tr zc`. In the genuine specialization, `P` is the actual global/local continuous-cochain pairing with the retained isotropy data; it is not a freely chosen scalar trace or row.

`bindingOfNativeComparison` composes a supplied verified finite comparison `J` to the native `modelCx M` with `M.ψf`. The row comparison is with the already constructed `ActualFull.pairedRow M P tr zc`. Thus the exported binding is anchored in the same actual finite model and pairing as the earlier class lifts.

Constructing the arithmetic `J` and the integral/common coefficient lift is still a structural obligation. A bare weak step proposition does not construct either. No existence hypothesis for this binding is claimed to discharge those obligations.

### Zero witnesses are no longer discretionary

`readback` exports the selected-step equalities together with the actual class and pairing equations. `class_not_zero` excludes all-zero lifted class vectors when the fixed actual class is nonzero in cohomology.

`zero_row_kills_actual_cycles` proves that a zero bound row forces the same actual functional to vanish on every actual cohomology two-cycle. `functional_not_zero` therefore excludes a zero row on a nonzero actual functional class. These conditions concern the actual cochains and functional, not a replacement scalar definition.

`completed_row_closed` derives row closure from the actual endpoint chain map and traced cup product. The injectivity of the actual integral completion map reflects the class and row closure before completion. `stored_closed` then derives closure of the same selected stored vectors through their readbacks.

`actual_boundary_forces_class_zero` uses the fixed two-term model's zero degree-zero differential and the actual quasi-isomorphism: an actual boundary class forces the bound endpoint vector itself to be zero. `stored_scalar_zero_of_actual_boundary` combines this with regularity of the fixed stored matrix and its existing adjugate identity to prove that the existing scalar is zero. This zero-class result does not take a determinant-normalization leaf. It is a sufficient actual cochain-boundary result, not a uniform assertion that every arithmetic acyclic constituent has already been matched.

## 2A. FibreEndpoint.lean: preferred actual field-fibre binding

Namespace: `ZInQ.Contrib.RC53Assist.CoordProvenance.FibreEndpoint`.

This is the preferred binding for determinant clearing. It does not demand a two-term model over the integral completed ring. Its common ring and scalar carrier are arbitrary commutative rings, so the scalar carrier can be a Laurent field; its clearing realization maps into `FractionRing OO`.

`actualClassRepresentative` is chosen from the actual class lift through the native `M.ψf`. Its closure and actual boundary readback are proved. The source complex is exactly the finite native `Cev3 (M.C.map (φO b)) x`, the source class is the evaluated actual class representative, and the source row is the evaluated fixed `ActualFull.pairedRow M P tr zc`.

The target matrix, class and row are the images of the same fixed `CommonLift` fields under the clearing realization. `FibreBinding` retains both coefficient-map injections, the actual field comparison and quasi-isomorphism, the fixed target cycles, and the class/functional readbacks. The source class and paired row cannot be independently chosen to encode the scalar.

The functional equation retains an explicit degree-three primitive:

`targetRow * f2 = sourceRow + primitive * source.d2`.

`comparison` constructs the homotopy-aware augmented comparison from these exact fields. A nonzero source coboundary functional is not required to be the zero cochain. No cone-torsion equality or coordinate equality is a record field.

`readback` exports the original selected matrix/vector readbacks together with the actual native class and functional equations. `fixed_fractional_coordinate` retains those same target fields while transporting the existing selected scalar under the two injective coefficient realizations.

`zero_class_forces_native_boundary` and `class_not_zero` prove that a zero bound endpoint vector forces the fixed actual native field class to be a boundary. `zero_row_kills_native_cycles` proves that a zero bound row kills the same actual paired functional on native fibre cycles. `scalar_zero_of_native_boundary` derives the existing regular scalar's zero value from an actual native class boundary, the fixed comparison, coefficient injections and the stored adjugate identity, without a determinant-normalization leaf.

Constructing the actual field comparison and common coefficient realization remains an arithmetic finite-model obligation. The record is a faithful conditional binding contract, not an unconditional supplier. The native identification, original class, canonical arithmetic coefficient pairing/trace and conjugate-orthogonal data are still the given actual inputs; the weak family identification record does not choose those arithmetic objects for us.

## 3. ConeDeterminant.lean: determinant calculations, not renamed conclusions

Namespace: `ZInQ.Contrib.RC53Assist.CoordProvenance.ConeDeterminant`.

### Explicit degreewise isomorphism

`BasedIso` contains the actual forward and reverse chain maps and their degreewise inverse matrix identities. `coneContraction` gives the explicit contraction of that same cone, without assuming source or target acyclicity.

`coneMatrix_det` uses two displayed unitriangular operations to reduce the cone matrix to its cross-block form. `det_block_swap` and `det_oriented_cross` compute the parity sign. The resulting exact formula is

`torsion(cone f) = (-1)^card(odd source basis) * det(fO) * det(gE)`.

The proof uses no source/target coordinate, nonzero-coordinate premise, or assumed cone torsion. `basis_cone_torsion` specializes it to the displayed graded basis matrices.

### Stored two-term original bases

`twoTermForward` and `twoTermBackward` are the fixed maps for

`D ↔ P * D * Q`,

carrying the original cycle and row to `Q⁻¹ z` and `w P⁻¹`. `twoTermAugIso` retains the two augmentation lines as well.

`twoTerm_basis_cone_torsion` proves

`torsion(cone comparison) = parity sign * (det(P)det(Q))⁻¹`.

`twoTerm_basis_factor` independently computes the coordinate transport factor as `det(P)det(Q)`. For the selected step these are its actual `s.PR`, `s.QR` or primitive comparisons after the same finite relabelling. This does not assume that the transport factor is one, or infer its value by cancellation from coordinate equality.

### Singular-disk projection

`splitProjection` is the fixed projection from a retained based complex plus the degree-one-to-two disk `B`. Its cone is regrouped into the identity cone of the retained complex plus the degree-zero-to-one disk `-B`. The fixed orientation is regrouped explicitly.

The independently proved projection formula is

`torsion(cone projection) = parity sign * det(B)`.

This applies even when the retained augmented complex is nonacyclic. `source_basis_cone_torsion` and `rebasedProjection_cone_torsion` track the actual source-basis matrices, rather than adding a desired cone-torsion equality as an input.

### Actual native full-condition cancellation

`oddCancelBasis` is constructed from the actual cancellation matrices. Its relevant determinants are proved one from their unitriangular block forms. `oddCancelBasis_split` derives the split from the actual differential blocks and `d² = 0`.

For the native full-condition matrix complex, `full_actual_split` uses the actual `Xf` relabelling and the native `schurO_Xf` identity. Its target is exactly the augmented native remaining complex with the restricted class and paired row.

`actualFullProjection` is the corresponding fixed chain map. The even and odd projection matrices have literal readback theorems. `actualFullProjection_cone_torsion` computes

`torsion(actual native projection cone) = parity sign * C.B.det`.

`actualFullProjection_factor` computes its transport factor as `C.B.det⁻¹`. There is no cone-normalization parameter, coordinate-equality parameter, or nonzero-coordinate branch in either theorem.

To specialize this calculation at a native constituent, use

`C = Cev3 (M.C.map (φO b)) x`,

with the actual evaluated class lift and evaluated `ActualFull.pairedRow`, and `isUnit_Bev3 (M.C.map (φO b)) M.isUnit_B x`. This is the actual native singular cancellation. The fixed `eEp`/`eOf` relabelling and `σFull` define its retained orientation; no orientation is selected to force scalar equality.

This determinant calculation is an actual component of the desired normalization. It is not a claim that the additional comparison to the stored endpoint has been constructed or that its factor equals one.

## Exact remaining arithmetic work

1. Construct the common/integral lift of the actual selected step matrices and original-basis representatives, with the displayed readbacks. If the arithmetic endpoint is genuinely Laurent rather than the image of a power-series step, construct the appropriate bounded/common coefficient model rather than imposing a power-series-unit lift.
2. Construct the finite-model comparison `J` to the native `Identification3` model, from the actual support, local orthogonal and conjugation diagrams, with the actual class boundary and fixed paired-row values. The weak stored functional samples alone are not a chain map or quasi-isomorphism.
3. Match the actual correction and existing corrected representative in this same coefficient diagram. The previously proved coefficient maps and corrected fractional expression remain available, but the arithmetic matching is not inferred from their existence.
4. Compute the remaining comparison determinant from those actual fixed maps and retained unit disks. Combine it with the independently proved native singular factor `det(B)⁻¹` and actual stored basis determinants. Do not assume an unknown cone torsion is the parity sign or rename nonzero coordinate equality as a basis condition.
5. Feed that actual matched scalar and total computed factor to the native `OrigCoordLink3`/clearing interface. No new unconditional `OrigCoordLink3` theorem is claimed here.

## Verification and preservation

The final delivery contains 72 theorems: 12 recorded independent-review obstructions and 60 repair, scope and normalization results. Every one of the 122 explicitly named declarations and five additional record constructors has an individual axiom report. All axiom sets are subsets of `propext`, `Classical.choice`, `Quot.sound`; every theorem uses the standard three except `splitProjection_orientation`, which uses `propext` and `Quot.sound`.

`EndpointObstructions.lean`, `BoundEndpoint.lean` and `ConeDeterminant.lean` compile directly under the prescribed single-file command without diagnostics. `FibreEndpoint.lean` imports the new `BoundEndpoint` module, whose compiled cache is not written by this continuation. Its unchanged proof body is therefore verified in the delivered `ReviewRepairAllCheck.lean` fixture, together with the other three unchanged source bodies and their original prerequisite imports. That combined source check and all four declaration/constructor audits finish without diagnostics. Direct import-based compilation of `FibreEndpoint.lean` requires building its new dependency first during integration.

`ReviewRepairStatements.md` gives every exact written theorem header, proof-explicit elaborated type and individual axiom report. The type rendering retains full names, universes, binder types and proofs; implicit typeclass/argument parameters remain implicit as in the source. No printer ellipses occur in the audited types. The manifest records each source size/hash and the exact combined-source assembly. A nonempty compiler receipt records successful exits and the hashes of the unchanged empty compiler logs, which cannot themselves be uploaded as file payloads.

The twelve inherited source files present in the working copy are checked against their input fingerprints and left unchanged. The review obstructions are credited as found in independent reviews. Temporary audit directives are not present in production sources or in the delivered combined-source check. No memory write, repository-history operation, target build, compiled-cache write or outgoing message is part of this continuation.
