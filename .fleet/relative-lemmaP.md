# Relative Lemma P for full level three

**Scoped stop.** The frozen statement passes the base-twist check: Lean
proves that biadditivity excludes a twist by a line bundle from the base.
The value of the marking at zero ensures that both zero axes are preserved
by the cartesian identification. Lean also proves global detection of
normalized classes from geometric restrictions over fields, and local
detection over the second projection for reduced locally noetherian bases.

**Remaining geometry.** The weakest two interfaces used for the pullback
half are `CanonicalPolarizationFibreComparison` (equality on the geometric
fibres) and `NormalizedPairFibreRigidity` (a zero detection statement for
actual normalized Picard classes). The latter still needs reduced relative
gluing and rigidity over nilpotent bases. The original
`CanonicalPolarizationExists` still needs an actual relative construction,
including in positive characteristic. With these three inputs Lean gives
the frozen representability equivalence. The row stays ELLIOT and ON THE SPOT.

**Source issue.** L467 and L474–475 use the polarization and its preservation;
the lattice datum at L410–421 does not supply either in families. The
polarization content of Buzzard's auxiliary-level citation is unverified.
At L421–422 the indices 4, 6 and 2 are normalizer orbifold orders; they would
be incorrect for the coarse level-one quotient.

**Verified.** Both new modules and the independent import audit compile.
All 24 new theorem checks report only `propext`, `Classical.choice` and
`Quot.sound`. No existing module or row was changed, and no leaf was added.
Full report: `docs/research/relative-lemmaP.md`.
