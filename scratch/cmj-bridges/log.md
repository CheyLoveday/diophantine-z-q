# Results

- VERIFIED (repository): the clean base is `b64a5639575bdb655ba5e2f8e1779ef84a4a1f35`.
  `cmjDegree` is GLUE in both columns; the H part has 29 rows (4 LEAF / 25 GLUE).
- VERIFIED (manuscript): L584–587 use a CM elliptic curve over the bounded-degree field,
  the discriminant of its full geometric endomorphism order, and the degree of its j-invariant.
  STANDARD (published, exact locator): the supplied human reading of Fowler §2·1, p. 613
  (fork issue #14, comment 6973419601) gives the equality over ℚ; p. 612 gives its
  primitive-equation discriminant. No independent PDF reading was performed.
- VERIFIED (Lean): `CMjBridgesPrint.lean` compiled with `lake env lean`. The printed
  `CMjDegreePrint` uses the lattice j-value, the actual primitive equation of a
  quadratic upper half-plane period, and Fowler's proper ideal class number.
  `modularJ_eq` validates the classical normalization.
