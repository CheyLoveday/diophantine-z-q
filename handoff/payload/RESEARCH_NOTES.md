# Research state at the Version 2 handoff

The current result is the exact quartic in
`current/quartics/quartic-12504/`. It has 12,504 total variables, including
input 0, and 12,503 rational witnesses. Its 11,939 quadratic residuals have
weight one. The expanded polynomial has 135,721 nonzero monomials, degree
four, and maximum absolute coefficient 685783949153203534233601, below 2^80.
The coefficient-table digest is
`7f5aa3117af82a0b323f0a4e74a18599204f5540408106d3ce99612b5ed830ca`.

The named source is
`reciprocal64-beta16-compressed-s1-b5e836d77643`. Its reciprocal logarithms
use precision 64 except for the designated beta tests, which use 16.
It retains 24 anchor squarings, scalar orders 1, 1, 1, 1, 48, 48, and 41
root comparison calls. Compressed primary charts are part of the audited
source. These parameters distinguish it from the unadopted experiments
preserved below.

The final certificate records 205 norm-inverse replacements, 41 redundant
inverse removals, six chart replacements, two ordinate removals, 42 parity
replacements, one batch-absorption operation, 366 linear operations, 800
eliminations, and four shears. The independent checker verifies every
operation against the current equations and variable occurrences and then
expands the full sum of squares. It preserves the rational input projection
in both directions. The source audit and arithmetic proof reviews address
different parts of the result and retain their own scopes.

The current snapshot includes the fresh full-reproduction receipt referenced
by `CURRENT_STATE.json`. Reproduction reruns the original finite arithmetic
checks, reciprocal checks, complete source audit, 38 malformed-source tests,
five resource-error regressions, and 30 malformed-certificate tests. It
regenerates the source and final quartic, with independent replay after each
reduction stage. Read the actual receipt for the environment and timing.

## Earlier work

The nested public November 4 revision-2 archive preserves the original large
construction, earlier manuscripts, reviews, and incomplete formalization.
Its `current/` tree is historical. The separately selected
`history/earlier-quartic/ALGEBRA.md` describes the later conversion from the
old 15,671-witness source and the original sparsity search. Its source hash,
targets, test suite and resource policy belong to that older work. It does
not describe the current source or replace the current checks.

The selected reciprocal, chart, parity and batch notes explain intermediate
ideas used by Version 2. They are preserved unchanged. Statements that an
audit or run was pending describe the date of that note. Current receipts
and source identities settle the present computational status. No older
review is silently extended to a different source hash.

## Unadopted circuit experiments

`history/unadopted-lowprecision/` preserves exact finite circuits for
precisions 12, 40, 44 and 48, their independent polynomial checker and review,
and the recorded 44-profile check summary. These circuits are not used by
Version 2. Their isolated target counts and coefficient bounds are not a
measurement of a new full quartic and do not justify changing its arithmetic
parameters.

To repeat that isolated experiment, use the original builder already
preserved in the current package:

```sh
python -E -B history/unadopted-lowprecision/probe_lowprecision.py \
  --builder current/quartics/quartic-12504/source/compiler/archive_build.py \
  --out NEW_PROBE_DIRECTORY
python -E -B history/unadopted-lowprecision/check_lowprecision.py NEW_PROBE_DIRECTORY
```

Run substantive computations under an external time and memory budget.
Proposals involving height exponent 19, scalar order 32, 37 root comparisons,
or different anchor and logarithm parameters remain outside the released
source. Their appearance in research discussions is not acceptance of a
different integer-defining system. This handoff does not contain a verified
quartic below 12,504 variables.

The main Lean theorem remains unproved. The current accepted helper snapshot
and the historical formalization record are useful inputs to further work;
neither is a complete formal proof of the manuscript.
