# Results log

- Base: `c2e8ccd0803190c13f4a1077a4ba87ec0c8b10f4`.
- Mathlib: finite adele units, finite support of their valuations, local uniformizers, factorization and counts for fractional ideals, and the fractional ideal definition of `ClassGroup` are available. No finite idele to ideal map found.
- `IdeleClass.lean`: proved valuation exponents, onto map to nonzero fractional ideals, principal diagonal, kernel equal to integral units, quotient by diagonal and integral units. Compiled with `lake env lean --threads=1`; committed as `05039931d`.
- `Grouped.lean`, `AdelicFactor.lean`, `RationalCentralizer.lean`, `OrbitQuotient.lean`: compiled. Regroup at the primes over each rational prime, glue local intertwiners within a finite exceptional set, identify rational units with the embedded quadratic field, compare the abstract torus orbit quotient. Committed as `5eb224217`.
- `LocalConjugacy.lean`: compiled. Full odd filter includes explicit splitting at every prime dividing `2N`. Equality of actual orientations is equivalent to conjugacy at every completed order and to an adelic centralizer factorization after rational reframing.
- `Representatives.lean`: compiled. Finite patch using the affine generator, rational frame selection, exact rational-centralizer/right-unit equality criterion, surjectivity onto the actual support orbits, and equivalence of orientation equality with adelic factorization.
- `BasedFiber.lean`: compiled. Left centralizer multiplication preserves admissibility; for a fixed tuple basepoint the corresponding double classes and the actual orientation fiber are equivalent. This supplies `PicardFibers` conditional on centralizer comparison and tuple representatives.
- `TorusComparison.lean`: compiled. `LocalTorusChart` is the placewise comparison (diagonal and integral tests); its charts imply the global centralizer equivalence and both subgroup identifications.
- `Realization.lean`: compiled. The labeled placewise witnesses preserve the level and division bits after a rational frame change and patch to an actual representative. Commit `8a92fa20d`.
- `Assembly.lean`: compiled. The reference generator has trace zero and the actual norm. `picardFibers_of_local` and `orbitFibers_of_local` use the existing actual orientation and constructor.
- Verification note: compilation jobs were run serially with the devserver load and memory gate. One brief `lean --print-prefix` toolchain query to locate source bypassed that gate while the serial verification batch was active.
- Final builds: all 11 modules compiled. The final `Representatives.lean` was recompiled after the linter cleanup.
- `Axioms.lean`: passed. Audited 292 theorems (69 written and 223 generated) and 59 definitions, including private declarations. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The raw `#print axioms` output for every written theorem is in `scratch/rc-picard-fibers/axioms.txt`.
