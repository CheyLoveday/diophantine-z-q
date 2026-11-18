# Results

- VERIFIED: the frozen base tests biadditivity on all schemes and fibre principality against a scheme kernel. Normalization along the two zero sections rules out a base twist; geometric detection over a nilpotent base still requires a rigidity argument.
- VERIFIED: the manuscript fixes the lattice type at L410–421 and uses polarizability and preservation at L467 and L474–475. Its auxiliary-level citation was not re-read. The ambiguity in the indices at L421–422 is recorded in the report.
- VERIFIED: the native theorem of the square is for abelian varieties over characteristic-zero fields; its unrestricted parameters are test schemes for those varieties. Its statement is not a relative square theorem for an abelian scheme over an arbitrary test base.
- VERIFIED (Lean): `Y3RelLemmaP.lean` compiles. Its 14 public theorems and five private helper theorems report only `propext`, `Classical.choice` and `Quot.sound`. The marking at zero suffices to pull back both axis identities; the comparison uses this fact without assuming transport of multiplication. `CanonicalPolarizationPullback` is equivalent to `CanonicalPolarizationFibreComparison` given `NormalizedPairFibreRigidity`.
