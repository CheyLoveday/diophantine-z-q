# Results

- Base: `9fd35f7b649d41784462a9448edf8918e16ff78f`.
- Tex 2837–2838 and 2915–2919 (provenance (c)): `eventually_hasSum_laurent_mul` and `eventually_hasSum_laurent_inv` prove the Cauchy product and inversion on a smaller punctured disk, given convergence at a nonzero point for each input. Inversion strips the leading monomial and matches the Taylor coefficients of the analytic unit inverse to the formal inverse by the power series product and uniqueness.
- Tex 2915–2919 (provenance (c)): `lattice_eq_of_weierstrass_invariants` proves equality of period lattices from equality of their Weierstrass invariants. Equality of the punctured germs at zero follows from the differential equation, and meromorphic continuation identifies the pole sets.
- `LaurentConvergence.lean` and `LatticeRigidity.lean`: serial `lake env lean -j1 -DautoImplicit=false` passed, 12 and 4 axiom checks respectively, with dependencies in `{propext, Classical.choice, Quot.sound}`.
