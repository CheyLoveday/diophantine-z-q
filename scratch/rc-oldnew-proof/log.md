# Old/new proof sizing

The exact leaf is
`∀ (N : ℕ) [NeZero N], LinearIndependent ℂ (fun x : CuspDilation N => x.form)`.
The index consists of a normalized weight-two newform with its source level
and a dilation degree whose product with that level divides `N`.

The vendored `EigenformAwayFromLevel.heckeTCuspNat_levelRaise_eq_eigenvalue_smul`
already gives the good prime Hecke eigenvalue on every such dilation.
The library also gives the inflated diamond character via
`CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd`.
The vendored across-level theorem
`Newform.level_eq_and_coe_eq_of_comp_unitsMap_eq` identifies the source at
equal inflated character and equal good eigenvalues. Its same-character
premise is essential to the API, so the separating operators include diamonds.
`OldAtPrime` and `PrimeDecomposition` support the across-level theorem.
The old/new spanning theorem alone does not give linear independence.

Use simultaneous eigenspaces for source separation and read the coefficient
at the least degree in a nonzero relation within that source. `coeff_form`,
`Odd.divCoeff` and `Newform.isNorm` give the required triangular coefficients.
The proof needs only the two short linkages (eigenspace separation and the
triangular argument) beyond the vendored modular-form results. These linkages
are on-the-spot (provenance (c)). Injectivity will follow from independence.

The worktree was already on the requested branch at the exact base SHA.
The requested fetch failed with HTTP 403 and the exact base is available locally.

The previous inventory report records the missing base factor in the
simplified expansion at tex 8162–8167, repaired by the exact expression at
8168–8182. It also records that Li's theorem cited for old/new independence
is a strong multiplicity-one theorem. No locators were independently checked.

The main-branch cache lacked the inventory dependency graph. Seeded the
ignored cache with source-matched artifacts from an existing build, then
used Lake for dependency validation and builds at the requested base.
The across-level strong multiplicity-one module built successfully.

The two initial imports built successfully. `lake env lean` accepts
`OldNewProof.lean`, including the exact old/new proposition, the
injectivity consequence, and independence of the Fourier columns.
