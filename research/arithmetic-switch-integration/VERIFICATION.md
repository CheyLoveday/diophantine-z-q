# Verification of the new interface helpers

Date: 2026-11-09. Scope: new research sources on base
`fb29fe2bc6968e178a6458357c437574221b5338`.
**Development profile: MET for the 14 selected formal helper roots.**
This decision does not certify the full arithmetic application. The ordinary
source-relative proofs have separate-agent internal reviews, with their
retained-construction assumptions visible.

## Observed evidence

The [native receipt](evidence/native/RESULT.json) records fresh compilation of
`ActualBoundaryCup` and `OrthogonalComparison`, all 14 elaborated statements,
transitive axioms, the exact source/specification hashes before and after,
commands, artifacts and all nine dependency revisions. Lean is 4.35.0,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, on arm64 macOS. No compiler
warning or stderr diagnostic was emitted. All proof roots use a subset of
`propext`, `Quot.sound`, `Classical.choice`; none uses `sorryAx`, a custom
arithmetic axiom or a native-evaluation assertion. `debug.skipKernelTC=false`
is explicit. Pinned Mathlib import caches are trusted dependencies; a complete
dependency source rebuild was not performed.

After the native run, six display-math delimiter pairs in the combined
DERIVATION.md were changed for GitHub compatibility. The original exact bytes
are retained in [DERIVATION.native-input.txt](evidence/DERIVATION.native-input.txt).
The [editorial binding](evidence/EDITORIAL_BINDING.json) verifies that this is
the only changed native input; all Lean sources, the specification, verifier
and pins are identical. The nonauthor integration reviewer acknowledged the
mathematical identity and bound the final document. No additional proof run
is attributed to this editorial check.

The [exact-check receipt](evidence/exact-checks/RESULT.json) captures all four
scripts, full JSON outputs, empty stderr, exit codes and unchanged script
hashes during execution. These scripts test different layers:

| Layer | Observed result | Limits |
| --- | --- | --- |
| Cochain cup/trace | 256 trials with nonzero corrections on a simplicial torus; bad correction sign, non-chain trace and nonclosed direction detected. | No Galois or compact-support arithmetic construction. |
| Cone comparison | 6,400 degreewise cases over dyadic finite rings, 4,680 homotopy congruence cases, 2,043 wrong-sign examples. | Random degreewise data are not asserted to form complete complexes; the Lean homotopy statements use genuine complexes. |
| Strict determinant | 180 models, 2,160 full cofactor identities, changes of complements/bases, common nonunit disks, and five adverse controls. | Generic K-matrices are distinguished from the explicit integral disk example. |
| Combined interfaces | 1,836 exact rational models, 32 opposite-boundary equations per model, cofactor identities and shared strict/unit-basis factors. | Actual global classes, trace and retained arithmetic models are not computed. |

The same run verified every old tracked file against the base Git tree:
3,083 unchanged files, including all 216 frozen packet/source files. This is
byte preservation; it does not repeat or enlarge the historical cloud claim.
The repository audit-history self-test also passed its structural and adverse
controls with the canonical manuscript and acceptance register unchanged.

## Gate record

| Gate | Status | Evidence / scope |
| --- | --- | --- |
| A01 — exact snapshot | PASS | Native input hashes, base identity, dependency pins; exact-check preservation record. New dirty sources are retained in this packet. |
| A02 — fixed specification | PASS | SPEC.md, hashed in native receipt and independently reviewed in the integration review. |
| A03 — statement fidelity | PASS | Printed explicit statements/definitions in native audit; root inspection and nonauthor reviews of each helper's premises and source application. |
| A04 — reviewable proof | PASS | New Lean sources mapped by the individual DERIVATION notes; root combined argument. |
| A05 — scoped build/checks | PASS | Two new modules compiled, no warnings; audit-history self-test passed. No frozen module or project-wide target was rebuilt as a substitute. |
| A06 — transitive axioms | PASS | All 14 roots audited against the predeclared three-axiom baseline. |
| A07 — boundary analysis | PASS | Exact finite checks and explicit failures for weakened interfaces; zero-trace rank and dyadic/descent scope guards retained. |
| A13 — evidence/claims | PASS | This record, exact receipts and source-bound review limitations. |
| A08–A11 — replay, protected comparison, external checking, clean reproduction | NOT_RUN | Outside this development run; no release-profile or six-checker claim for the new helpers. |
| A12 — independent mathematical review | PASS for bounded internal model review | Three separately authored reviews; not external human or whole-paper acceptance. |

## Independent reviews and unresolved arithmetic work

- Orthogonal agent reviewed the boundary proof against the published cone
  product and shared-trace square, and reran its cochain checks:
  [BOUNDARY_REVIEW.md](../orthogonal-comparison/BOUNDARY_REVIEW.md).
- Determinant agent independently rederived the orthogonal homotopy argument
  and strict-H² dictionary, and reran the finite-ring checks:
  [REVIEW.md](../orthogonal-comparison/REVIEW.md).
- Boundary agent independently checked the determinant and root integration
  arguments, and reran the determinant and combined checks:
  [DETERMINANT_INTEGRATION_REVIEW.md](../actual-boundary-cup/DETERMINANT_INTEGRATION_REVIEW.md).

The independent reviews bind the mathematical source bytes. A declaration
locator and a provenance wording error were corrected by the respective authors
and rereviewed. Earlier receipts remain historical; no old verdict was rewritten.

The new proof steps remove a representative mismatch and an unexplained
localization-compatibility premise, and explicitly retain the common strict
determinant scale. Complete formal arithmetic closure remains **OPEN**: actual
global Galois cups/trace, coherent retention of the full diagram through the
inner limit, all permitted localized inverses, actual trace nonvanishing where
rank is inferred, and universal integral group-ring descent need their own
realization or independent validation. No confidence claim about the main
Diophantine theorem follows from the check counts.
