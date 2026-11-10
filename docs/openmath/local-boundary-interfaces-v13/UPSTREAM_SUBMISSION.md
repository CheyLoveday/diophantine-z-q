# Local conjugation and boundary interfaces: upstream submission

Prepared locally on 10 November 2026 against upstream commit
`009b47f84ffe484a1cdbe187a75fe2c21b3df1f8` (Version 14). This is the current
reader entry for the combined contribution and its completed checking evidence.

## What this contributes

Four Lean modules prove three compatibility steps used in the construction of
derivative-switch functionals:

1. Derive the shared conjugation unit from the twisted representation and
   descend local evaluation and pullback to Mathlib's actual first group
   cohomology, retaining the distinct conjugate coefficient system.
2. Derive the cup coboundary correcting a local-condition representative to
   global localization, and remove that correction under a supplied chain trace.
3. Prove the degreewise cone comparison and show that a supplied right homotopy
   inverse preserves the common global projection and its localizations on
   homology.

The [specification](../../../research/local-boundary-interfaces/README.md),
[41-root inventory](../../../research/local-boundary-interfaces/TARGETS.json),
and [premise-to-theorem-to-consumer application map](../../../research/local-boundary-interfaces/APPLICATION.md)
state the exact hypotheses and remaining arithmetic inputs. Those are the
agreed conditional local interfaces; this submission does not assert the full
arithmetic determinant comparison or the main Diophantine theorem.

## Contribution and evidence are one submission

[Fork PR #2](https://github.com/CheyLoveday/diophantine-z-q/pull/2) supplied the
four modules and their original support, at reviewed head
`3e01aa877cd7434fdc759fe7b6a9271de6deff2e`. It is merged in the fork.
[Fork PR #3](https://github.com/CheyLoveday/diophantine-z-q/pull/3) supplied the
later evidence only, at `cdb1a92c41832b1631baf9391fd5f6b9c0c57157`.
The local upstream candidate includes both selections. Preparing it does not
merge PR #3 or publish an upstream PR.

The completed evidence covers all four modules, all 41 selected roots and all
16 printed definitions. The fresh Lean 4.35.0 build, transitive axiom audit,
source-bound export and all six checkers passed. The permitted axioms were
`propext`, `Quot.sound` and `Classical.choice`.

- [Latest evidence guide](openmath-os-evidence/PR_GUIDE.md)
- [Statement and application review](openmath-os-evidence/INDEPENDENT_STATEMENT_REVIEW.md)
- [Validation receipt](openmath-os-evidence/EVIDENCE_VALIDATION.json)
- [Complete six-checker output](openmath-os-evidence/paranoid.stdout.txt)
- [Retained export ZIP and payload identities](openmath-os-evidence/PACKET_ZIP.json)

The export contains 88,408,652 bytes and has SHA-256
`4dca1de2e2450011f8ec32eb8cd9c17b531c7fbedd813ce75b0221dfe30e42aa`.
Its selected roots and larger transitive dependency closure are distinguished
in the evidence guide. Checking took place in the documented Linux VM with
sandboxing; it is not an Open Math cloud run, protected comparator challenge,
hermetic dependency rebuild or external human specialist acceptance.

Earlier preparation documents and raw timeout/checkout logs retain their dated
status. Their then-pending checker statements are superseded by the completed
evidence linked above. No further run is waiting on those historical failures.

## Current base and retained source bindings

The four mathematical files and all 159 files selected from the combined fork
package are byte-identical to their source at `cdb1a92`. This entry is the sole
additional presentation file. Source and evidence manifests, earlier review
bindings and receipts are preserved unchanged.

The application map remains explicitly anchored to Version 13 at
`9c0b3aba60d90fdcac82115f0582a6f52f1054f7`. Its manuscript file and the Lean
toolchain, dependency lock and Lake configuration have unchanged bytes at the
new upstream base. This packaging step does not rebind the V13 application
review to the expanded Version 14 manuscript or claim review of that manuscript.

This is an additive, non-release helper contribution. The current manuscript,
PDFs, construction artifacts, accepted Lean library, release records and prior
acceptances are not edited. No broader research packet is imported. These
preserved interfaces do not require completion of the remaining arithmetic
instance before being proposed as conditional helpers.

## Reproduction and remaining review

The original [native verification instructions](../../../research/local-boundary-interfaces/VERIFICATION.md)
and [Open Math handover](HANDOVER.md) remain available. Prepare a source-bound
project into a new directory with:

```sh
python3 -B scripts/prepare_local_boundary_openmath.py --output /tmp/local-boundary-verification-NEW
```

This command prepares inputs only. It does not build Lean or dispatch jobs;
its own `NOT_RUN` output describes that preparation invocation, not the status
of the completed checker evidence.

Current upstream review is governed by
[Protocol_D](../../research-review/PROTOCOL.md) and the
[Astra acceptance policy](../../research-review/ASTRA-REVIEW-POLICY.md).
The retained model reviews are supporting evidence, not an assertion of eligible
controller acceptance for a new upstream revision. Exact-revision hosted checks,
eligible protocol review and maintainer consideration remain submission-stage
work. No such acceptance is manufactured by this local preparation.
