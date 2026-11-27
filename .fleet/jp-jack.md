# Javanpeykar bound over the field of definition

**VERIFIED (Lean):** `JavanpeykarThm111JacK` restricts the old row to a curve
over a number field and its tensor-compatible Pic⁰ representative over
that field. The old row implies it without extra hypotheses. The height
reader applies it directly and no longer uses a geometric Jacobian with
a separately chosen number-field model.

Propose `javanpeykarThm111JacKEx`, consequence, GLUE/GLUE, pending review.
The existential reader, witness existence and uniqueness, and invariance
across Pic⁰ representatives compile. The uniqueness proof uses the
comparison already reconstructed by the Faltings fold. The bypass dry
run checks the two top theorems and their closures: the old row is present
under the old top and absent under `frozenTarget_jp`, which uses the
existential row. All added theorems report only the three standard axioms.

The count stays at 29 H hypotheses (5 LEAF / 24 GLUE in both ratings)
plus four others. No production fold was made. The lead's ruling on the
Section 2.3 composite and review of the dictionary against the print
remain. See [the report](../docs/research/jp-jack.md) and
[replay instructions](../scratch/jp-jack/REPLAY.md).

The superseded cache rebuild overlapped with early checks, violating the
one-process limit. It was terminated; the remaining Lean checks were
serialized under a process lock.
