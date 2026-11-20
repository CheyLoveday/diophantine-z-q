# Modular arithmetic inputs for prescribed-class detection

## Integration form

`ZInQKernel.Contrib.RC53Assist.Detection.Inputs` imports the existing built producer:

```lean
import ZInQKernel.Contrib.RC53Assist.Detection.Producer
```

It contains only the new declarations in `ZInQ.Contrib.RC53Assist.Detection.Inputs`: 74 named declarations, including 42 theorems and two input records with 14 fields. It contains no copied producer declarations. The extension body is byte-identical to the previously verified extension; only its independent module preamble was added.

The module was checked against integration base `3b0ffbb9c83eaccb0f82808d806a4939205665b1`. The imported producer's source SHA-256 is `8542fb31e04f4b26c8d864c66db653d27e3a2ce0bb891810f827811ec396b0ae`, matching the preserved earlier producer. Its built dependency was present.

The new module compiles directly with the requested single-file command, six threads, processor affinity 80–95, and priority ten. No producer or stage-step source file was edited, and no version-control operation, package update, or whole-project build was used. The existing stage-step assembly still imports the producer; the new module extends that import rather than redeclaring its contents. No all-modules build is claimed.

## Constructed declarations

### Genuine coefficient dictionary

`coindPairEquiv` realizes the genuine two-coset coinduced representation in its actual transversal coordinates. Actual complex conjugation exchanges the coordinates. Restriction in the first coordinate is the original coefficient action.

`rationalInducedRepresentation` uses the actual quadratic fixing subgroup and the action in `tlamBasis`. Coinduction is performed on each original rational Galois group. Integral matrices are limited before specialization, yielding `inducedSequenceRepresentation` and the two proved fields of `genuineCoefficientDictionary`.

The product of quadratic fixing subgroups is not assumed to have index two in the product of rational Galois groups. No continuous pointwise limiting action on one original Galois group is asserted.

### Rank-two and rank-four coefficient spans

`serre_small_matrices` produces genuine rational Galois preimages using the existing non-CM Serre theorem. The identity and the squares of preimages of three small elementary matrices span the full rank-two matrix algebra on a characteristic-zero fibre away from two. These squares fix the genuine quadratic base.

`exists_four_quadratic_tate_span`, `exists_four_twisted_span`, and `baseSequenceRepresentation_span` transport this span through the genuine Tate-basis change and unit scalar character twist.

`full_span_of_scalar_separation` isolates the two block projections from a single element acting by distinct scalars. Multiplication and actual coordinate exchange generate all four endomorphism blocks. `genuineCoefficientSpanWitness` combines this theorem with the actual rank-two span and the precise moving-inertia input below, then extracts finitely many actual rational sequences. No cohomology class evaluation or detecting determinant is supplied to this construction.

### Norm scalar and commutators

`exists_arithmetic_scalar_element` begins with Serre's scalar preimage, acting by `u = 1 + 2ⁿ` for fixed `n ≥ 2`. The genuine norm `g² τ g² τ⁻¹` is proved to act on the full Tate module by `u⁴`.

Under the explicit inversion condition on the chosen arithmetic fields, this norm fixes them. Normality implies that its commutators fix those fields. Scalar Tate action separately makes its commutators trivial on the full Tate module; this is proved to fix every required finite torsion field. `arithmeticCommonScalar_of_dihedral` then proves the exact earlier scalar record on both induced summands after integral matrix limits.

### Retained evaluation and first cohomology

`retainedEvaluation_of_embedding` constructs the earlier retained evaluation record from a sufficient cochain embedding. `exists_injective_actual_h1_map` constructs a well-defined injective linear map from retained first cohomology to the ordinary first cohomology of the genuine induced sequence representation, with the exact represented-cycle formula.

The degree-zero identity is explicitly used to preserve boundaries. Principal-boundary reflection alone does not define this quotient map. The alternative `RetainedBoundaryReflection` is named only as reflection and is not claimed to be a complete first-cohomology comparison.

### Combined prescribed-cycle producer

`detection_with_constructed_inputs` constructs the coefficient dictionary, scalar, finite coefficient span, and retained evaluation, and passes them to the existing `makeArithmeticDetection`. The nonzero input cycle is prescribed. Its partner, kernel representative sequence, compatible arithmetic label, and detecting determinant are outputs of the existing producer. There is no `hdet` input.

## Exact remaining inputs

The full Lean types, including all ordinary arithmetic and fibre hypotheses, are printed in `INPUTS_AUDIT.txt`. In addition to the existing Serre/non-CM, quadratic-base, nonprincipal-filter, and characteristic-zero fibre setup, the following three bindings remain.

### 1. Actual moving inertia: `NonquadraticInertiaInput`

It supplies `element : ℕ → rationalBaseGroup e` with:

1. every component fixing `torsField E i` at the required finite precision;
2. scalar character values inverted by actual conjugation `baseConjugate`;
3. the specialized integral limit of those character values having square different from one.

The first property makes the limiting twisted matrix a character scalar. The second supplies the inverse scalar in the conjugate coordinate. The third separates the two summands.

Connect actual moving-prime inertia to these fields; abstract moving-character data and a bare continuous character do not themselves export this precise rational Galois sequence. The arithmetic ingredients are good-prime unramified Tate action, the moving-inertia character generator, and actual character inversion. This is the characteristic-zero matrix-span argument of manuscript lines 4779–4785 and the finite construction of lines 2902–2912, not residual irreducibility.

### 2. Chosen kernel fields: `DihedralKernelFields`

For every component and every actual quadratic-subgroup automorphism, actual conjugation must invert its restriction to the exact field `characterField i ⊔ B i`.

This is a field-automorphism identity; it contains no cohomology class or determinant. Finite-dimensionality, normality, and character continuity do not imply it. The generic character field is chosen from an existence theorem and need not carry containment in the intended dihedral ring-class compositum. Prove that containment/inversion for the chosen fields, or export an appropriately bound character-field comparison.

The standard ring-class inversion fact used here is manuscript (H1), lines 2882–2892, and the norm scalar/common-kernel argument of lines 4766–4774. Arbitrary supplied fields are not claimed to satisfy the additional property.

### 3. Actual retained model: `RetainedCochainEmbedding`

The sufficient export consists of original integral degree-one cochain columns, localized coordinates, degree-zero through degree-two evaluation maps, both differential identities, degree-zero surjectivity, degree-one cochain injectivity, and the original-basis projection identity.

The first differential identity is essential:

```text
one(d₀y)(g) = g · zero(y) − zero(y).
```

Bind these exports to the actual retained stage Selmer/global model through coefficient change. The current `exists_retained_of_stageInputs` output retains differential, localization, pairing, duality, and homotopy matrices, but not the original cochain/model comparison maps or degree-zero evaluation. The intended fibre complex must be identified with that retained actual model, preserving its original columns and applicable first-cohomology injection or cone contraction.

If the actual comparison is not a cochain embedding, use a weaker verified first-cohomology comparison instead, still preserving boundaries through degree zero, reflecting principal cycles to model boundaries, and carrying original-basis normalization. The manuscript comparison for primitive and derivative models is lines 4651–4704; arbitrary orthogonal zero/full models require the extra contraction of lines 4706–4717.

## Scope preserved under the port

Output representatives fix the required finite stages and act trivially on the exact limiting coefficient module. They are not asserted to fix the full Tate module pointwise at each component. The scalar's commutators do have proved full-Tate triviality, but this does not strengthen arbitrary output representatives.

Fixed-decomposition normalization is a fibre-cycle identity with one common invertible conjugation transport. Original cochain columns are matched at rational-square representatives before normalization. No untransported identity on arbitrary original cochains or whole-complex version of (5.4) is asserted.

The remaining arithmetic and retained-model exports are substantive. This is not an unconditional completion of Theorem 5.3.

## Fresh declaration audit

Both `Inputs.lean` and the scratch audit compile with exit code zero on the specified integration base. The source has 84,400 bytes and SHA-256 `a88907ecab59ef140035ffcc6489046505bec1e5d04a900548786ab290d89f16`.

The new audit contains every exact statement and axiom receipt for all 74 declarations and 14 record fields: 88 entries, no missing or extra entries, and no errors. Every axiom set is contained in `{propext, Classical.choice, Quot.sound}`. The coefficient dictionary, finite coefficient-span witness, common-scalar constructor, injective first-cohomology comparison, and combined detection constructor each use exactly those three standard axioms.

The imported producer and the extension body remained unchanged throughout the port and audit. Temporary diagnostic source is removed from the delivered module set. The final module contains no diagnostic command, executable command, placeholder, additional axiom, or new notation/syntax declaration.
