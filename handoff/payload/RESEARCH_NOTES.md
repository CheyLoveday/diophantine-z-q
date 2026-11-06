# Reading the Version 4 research handoff

Start with `current/quartic_4973.pdf` or its TeX source. The main file contains
the original huge polynomial and the selected quartic. Earlier polynomials in
separate historical packages are not additional current constructions.

The selected quartic is formed from the sum of squares of 4,552 quadratic
integer residuals. A complete replay checks its 551 transformations and every
coefficient in its expansion. This finite verification is separate from the
arithmetic proof that the source projection is the integers.

The arithmetic path uses 37 contacts, divided into 13 full, eight beta-only
and 16 Lucas-only comparisons. General roots use integer doubled indices.
The common denominator comparison has order 12 in beta-only mode and order
40 otherwise. The source also uses the reviewed linear ordinary pole,
normalized Lucas equations, direct tangents, shared field squares and
first-norm denominator change. The scalar pole is retained. H19, precisions
40 and 12, anchor exponent 25 and scalar order 32 remain unchanged.

Read the final inventory before treating an older proof note as applicable.
It pins the selected statements, source files and independent review records,
and retains the five inherited source-version qualifications. Hash agreement
establishes artifact identity, not the truth of a mathematical premise.

For computation, use the package's self-contained Linux reproduction runner.
It requires at least 8 GiB available memory, stops below 4 GiB, caps each child
at 2 GiB and does heavy work remotely in this campaign. Mandatory reproduction
rebuilds the source and replays the fixed certificate. Optional heuristic
rediscovery can choose a different search path and is reported separately.

Version 5 requires at most 2,486 total variables, including input zero. That
number is a future search target, not an established construction.

## November 6 revision 2

Read `current/research/2026-11-06-collaborator-notes/README.md` for the new collaborator collection and `height-replacement.md` for the exact substitution removing the von Känel–Kret input. Exponent 24 and five contacts are retained. The supplied originals, comparison, existing H5 proof extract, source hashes and small-check script are included. This does not change the selected polynomial or resolve the collaborator's remaining parity assertion.

The same collection includes the reported Fable repository audit, with its exact stated exclusions, and explains the frozen source label and the original-only Lean target.
