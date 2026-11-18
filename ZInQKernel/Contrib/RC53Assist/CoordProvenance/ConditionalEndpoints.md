# Conditional classification of the earlier endpoint exports

## Correction to the advertised provenance strength

An independent review found two statement-strength obstructions in the earlier endpoint exports. Both objections are valid. The algebraic proofs compile, but their types do not establish actual arithmetic endpoint provenance.

The earlier committed sources and reports are preserved. This addendum corrects how the exports are to be used and credited; it does not claim that historical source text was rewritten.

## C-R1: unbound endpoint existentials

`Scalar.existing_relaxation_endpoint`, `existing_endpoint_on_carrier`, their Laurent and finite-relabelled consequences, and the corresponding copies in `EndpointScalarSupport` are conditional algebraic extractions. Their conclusions forget the readback to the selected step's matrices and representatives. They must not be described as bound actual-endpoint producers.

The proof body selects witnesses from a step, but that fact is not a statement-level binding. The exact four-dimensional endpoint existential has zero-matrix and zero-vector witnesses for every supplied scalar. Even nonzero adjugate and closed representatives do not repair a freely chosen existential: the one-dimensional core `[0]` with class `[u]` and row `[1]` carries any prescribed scalar `u`.

A repaired endpoint must retain the selected step datum and its matrix/vector readbacks under every relabelling and coefficient realization, and must connect that fixed datum to the same actual Selmer model, class and paired functional. No unrestricted existence of replacement matrices/vectors is an actual provenance claim.

## C-R2: uncomputed determinant normalization

`Endpoint.original_coordinate_eq_existing_relaxed`, `ExistingRelaxationRealizationG.retained_basis`, `relIsKMG_of_existing_realizations` and `origCoordLink_of_existing_realizations` are conditional algebraic reductions with an open determinant-normalization input. They are not independent arithmetic provenance producers.

For a fixed comparison and fixed bases with nonzero cone torsion and nonzero target coordinate, the retained cone torsion being the prescribed parity sign is equivalent to equality of source and target coordinates. Therefore syntactically omitting a coordinate-identity premise is not evidence that the normalization was independently proved.

At zero target coordinates, the basis condition is stronger than coordinate equality; no equivalence of the entire realization record with the full coordinate-link proposition is asserted. A genuine repair computes the cone determinant from the fixed local/model maps and graded basis changes, without obtaining it by cancellation from the desired coordinate equality.

## C4-1: the free regular endpoint is still unbound

The same correction applies to `StoredRegularity.actualStep_regular_endpoint` and `existing_support_regular_endpoint`. Their free existential does not retain a readback to the selected step or the actual family model.

The additional independent review compiled the exact original index type with one fixed diagonal matrix `(0,1,1,1)`, class `(u,0,0,0)` and row `(1,0,0,0)`. Its adjugate is nonzero and both vectors are closed, for every prescribed scalar `u` over a nontrivial commutative ring. Thus adding regularity and closure does not repair the exported binding.

These two exports are conditional, unbound algebraic extractions, not actual arithmetic endpoint suppliers. `EndpointObstructions.lean` also records the exact four-dimensional fixed-matrix probe and its adjugate/closure calculations, credited as found in an independent review. The fixed-matrix regularity lemmas are retained and used on the new selected `s.DR` directly.

The native class-lift and representative-independence helpers remain conditional fixed-data results. Their original class, canonical arithmetic pairing/trace and conjugate data are not selected merely by the family identification record.

## Sound partial results retained

The concrete `Frac Λ` coefficient realizations, fixed-data model comparison with computed nonzero factor, homotopy-aware off-diagonal functional term, and field-level inverse-disk coordinate calculation remain sound. The inverse-disk calculation is not an integral identification-record cast.

`EndpointObstructions.lean` records the compiled counterexamples, credited as found in an independent review: universal free endpoints, universal all-zero endpoint witnesses, universal free regular endpoints, fixed zero-cycle exclusion, the normalization equivalence, and the same-disk/integral-inverse obstructions.

## Scope of the current repair

The new selected-step interfaces must retain concrete fields and readbacks. The actual model binding is to native `Identification3`, its `M.ψf`, the actual family class and the genuine paired row constructed in `ActualFullModel.lean`. Any actual model map or coefficient diagram not constructed from the current data remains an explicitly named structural obligation.

Normalization results must display their explicit matrix or graded-basis inputs and prove the determinant independently. A conditional model-binding record or a new name for the old cone-torsion equality is not counted as completion of the manuscript's scalar identification.
