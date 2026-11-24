# Shimura's positive-index ring and quotient split

`printRing` now uses only the positive Hecke indices. Lean checks that
changing `ξ 0` does not change this ring, and that the old all-index
closure agrees with it when `ξ 0 = 0`, as in the existing Hecke bridge.
The [error verdict](shimura-ring0-verdict.md) records the inherited
counterexample and precedes the repair.

`ShimuraThm1Printed` retains the printed clauses (i)–(iii), coefficient
field finiteness, and uniqueness up to isomorphism over ℚ.
`ShimuraQuotientByC` names the p. 526 quotient construction separately
as GLUE, provenance (c). The focused check confirms that these are the
only assumptions of `shimuraThm1Af_of_split_closed`, which proves the
unchanged `R16Thm1b.ShimuraThm1Af` row. The construction still needs the
geometry of quotients by abelian subvarieties and the dimension
calculation for Shimura's `C`. No fold or count change was made.

The serial offline Lake build passed for `ShimuraRing0`,
`ShimuraSteps`, `ShimuraHeckeJ`, `ShimuraPointDict`, `SameDimFinite`,
`ShimuraOrbits`, `ShimuraHeckeClosed`, and `BShFamily`. The
[axiom scan](../scratch/shimura-ring0/Axioms-output.txt) shows only
`propext`, `Classical.choice`, and `Quot.sound`. See the
[report](../docs/research/shimura-ring0.md) and
[focused discharge](../scratch/shimura-ring0/Discharges-output.txt).

Verified code and outputs: `d5e8d4414c9bfbd768187be302d4d070e42ff7eb`.
Final SHA (the commit adding this note):
`git log -1 --diff-filter=A --format=%H -- .fleet/shimura-ring0.md`.
