# Laurent expansions and normalized branches of X₀(N)

Scoped stop: `X0Model2.modelOne : PreparedParam.X0Model 1` is constructed.
For every nonzero level, the entire `sectionExpansion` field is proved.
The Cauchy product and reciprocal use convergent power series after the
leading Laurent power is removed; the coefficients of the reciprocal are
those of the formal inverse.

The finite first projection of the normalized chart is analytic j.
Equality of analytic j is exactly full modular-group equivalence.
The normalized chart respects Γ₀(N)-orbits and the right action of the
center stabilizer on the labels Γ₀(N)γ. A match of punctured sheet germs
gives the corresponding orbit, and proper discontinuity and the identity
principle give that match from recurrent local overlap, including at i and ρ.

One implication remains at general level (tex 2915–2919): if two sheets over
the same j-value specialize to the same normalized point, their punctured
second-coordinate germs agree after a reparametrization by the stabilizer
of the center. The missing link is from the valuative lifts to local
overlap on the smooth complex curve. Coincident plane values at the center
do not give this link. The exact proposition and the existing complex chart
infrastructure are recorded in `docs/research/rc-x0-model-2.md`.

Citation check: the manuscript's Shimura citation at 770–771 and
11053–11057 is to the 1973 paper for a different step. The possible typo
reported in the base report is unused and unverified. This lane adds no
print; all proofs here have provenance (c).

All nine modules in `ZInQKernel/Contrib/OneProof/RC/X0Model2/` compile
serially. All 84 axiom checks use only `propext`, `Classical.choice`,
and `Quot.sound`. Results: `scratch/rc-x0-model-2/log.md`.

Final implementation and report SHA: `b6161a317c4b7435394edf479cb2b9b2fc649828`.
The SHA of the final handoff commit is returned by
`git log -1 --format=%H -- .fleet/rc-x0-model-2.md`; a commit cannot
contain its own SHA.
