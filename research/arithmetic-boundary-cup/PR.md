# Proposed contribution structure

No upstream PR is created by this work. The authorized delivery is a commit
and push to `CheyLoveday/diophantine-z-q`, branch
`codex/derivative-switch-boundary-v13`.

Review this new delta against `e653d6ff295ae4e0535710a7d64aa255d294d211`.
That base is the frozen cloud handoff; a comparison against `main` includes
the preceding 13-commit research history, with 245 added files. It would not
be a small arithmetic-bridge PR.

For eventual upstream submission, use two logical contributions:

1. The foundational common-strict algebra and its verification package,
   against upstream `main` (observed `9c0b3aba60d90fdcac82115f0582a6f52f1054f7`).
   Consolidate the review surface around the latest algebra while preserving
   historical receipts. Do not submit separate overlapping six/21/39 claims.
2. This dependent arithmetic normalization bridge, based on that foundational
   contribution: one addendum, one explicit source application, one Lean
   module and its focused evidence.

## Suggested title

Derive derivative-switch unit normalization from the retained duality interface

## Suggested description

The scalar-ratio theorem previously required normalized boundary–cup identities
as inputs. This change derives them from the raw mixed cup, the specified
orthogonal partner, shared conjugate transport and same-row/class realizations.
The tame sign gives opposite normalizers and an explicit integral-unit witness;
the existing unit theorem then compares the actual matrix coordinates.

A source-pinned LaTeX addendum supplies the ordinary arithmetic argument and
the separate-triangle determinant-tensor comparison. Its generated insertion
patch is checked against V13 but is not applied to the frozen manuscript.
The Lean result remains conditional on the explicitly recorded retained-duality
and common-strict realization inputs; it does not formalize the entire
arithmetic Selmer construction or determinant functors.

Validation: native Lean 4.35 compilation, elaborated statement inspection and
transitive axiom audit for nine declarations; exact finite sign controls;
three focused read-only reviews; frozen-input preservation and byte-identical
39-project generation. The existing Open Math paranoid run is unchanged and
does not cover these new declarations.

## Evidence to keep prominent

- `APPLICATION.md`, `FORMAL_SPEC.md` and the authoritative insertion source.
- New `ArithmeticBridge.lean` and `evidence/native/RESULT.json` with full
  commands, statements and axiom outputs.
- The three focused reviews and `evidence/preservation.json`.
- The generated insertion patch and its [generation/check receipt](evidence/insertion-check.json).

Historical archives, component investigations and earlier proof receipts remain
available by link. They are not independent votes for the new theorem, and
failed local compiler iterations are not part of the delivery package.
