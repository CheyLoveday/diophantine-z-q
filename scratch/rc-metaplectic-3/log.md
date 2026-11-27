# rc-metaplectic-3 results

- Base: `6d96810ba80d38cfb1ffdd0e608a61d71d054d07`.
- Actual diagonal, Weyl-square and Weyl–upper defects: `diagonal_defect_sign`, `weyl_square_defect_sign`, `weyl_upper_defect_sign` = the explicit local Hilbert signs `(s,t)`, `(-1,-1)`, `(-b,-1)`.
- `localProjection_kernel`: two-element central kernel on the paired local cover. `commonSection_first`, `commonSection_second`: the same section fixes both spherical vectors at good primes.
- `finiteProjection_surjective`, `commonProjection_kernel`: restricted product surjects; quotient by product-one finite sign tuples has exactly two elements over the identity. `commonFirst_sign`, `commonSecond_sign`: the remaining sign acts as minus the identity.
- `integerLiftStep_projection`, `integerLiftStep_first`, `integerLiftStep_second`: a single lift of each inverse integer generator acts by the literal tuples on both full tensors.
- `evaluate_injective`, `grid_invariant`: evaluation separates the full tensors, and both grid images are invariant under the respective actions of the common integer pullback.
- `rectangular_first_tests`, `rectangular_second_tests`, `rectangular_sign_actions`, `common_rectangular_comparison`: both rectangular realizations satisfy the cylinder tests, with one common central sign and both `IntertwinesGenerators` instances at the same scalar.
- No new print. No remaining finite rectangular hypothesis.
- Base objects: restored from the independent build at the exact base.
- Serial Lake dependency build: `ZInQKernel.Contrib.OneProof.RC.Metaplectic2.CommonRectangular`, pass.
- Host load and available memory gates passed; serial Lean invocations.

| Module | lake env lean | Axiom audits |
| --- | --- | ---: |
| SignArithmetic | pass | 27 |
| SignedRelations | pass | 8 |
| CommonLocal | pass | 13 |
| CommonSections | pass | 10 |
| FiniteAssembly | pass | 3 |
| FiniteSign | pass | 10 |
| CentralTensor | pass | 6 |
| IntegerLifts | pass | 13 |
| TensorFaithful | pass | 8 |
| RectangularRestriction | pass | 8 |
| CommonRectangular | pass | 6 |
| **Total** | **11 pass** | **112** |
