# Results log

- Baseline: the prime trace comparison accepts a Galois family of embeddings with simultaneous local coordinate matching. The family is not present at the baseline.
- Build configuration: `-j 1` was rejected by Lake. A subsequent prerequisite build with `-Kjobs=1` started concurrent Lean subprocesses, breaching the single-process rule. The build was interrupted. Subsequent Lake jobs use a compiler wrapper with an exclusive lock and the host load and memory checks.
- Splitting approach: nonzero torsion sections in each prime direction come from changing basis for the holomorphic Weber mark at level `p`. A monic polynomial remainder transfers pointwise root exhaustion to the germ field without assuming simple roots.
- `BShFamily.dvd_prod_pow_of_exhaustion`: a split polynomial with all roots in a finite list divides a power of its linear-factor product; compiled.
- `BShFamily.splits_of_eventually_exhaustion`: a monic polynomial with eventual pointwise root exhaustion over an algebraically closed field splits over the field supplying its germ coefficients and those roots; compiled.
- `lake build +ZInQKernel.Contrib.OneProof.BShFamilySplittingCriterion`: passed; both axiom scans contain only `propext`, `Classical.choice`, and `Quot.sound`.
