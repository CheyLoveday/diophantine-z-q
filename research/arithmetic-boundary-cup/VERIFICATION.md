# Conditional arithmetic bridge: local verification

Profile: **development — MET**. Final semantic review is recorded in the focused
core review. No release/critical, protected-comparison, export-replay,
external-kernel or paranoid result is claimed for this new module.

Lean: 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`,
native Apple Silicon build. Mathlib: pinned
`56a005855ea17e0b0958f73ec801ae140b0a1679`; all nine locked dependencies
were checked against their actual clean source revisions. Previously
provisioned pinned Mathlib import closures are trusted dependencies.

The new module and its four unchanged common-strict dependencies were freshly
compiled with `-Ddebug.skipKernelTC=false`. The new module emitted no
diagnostics. The unchanged `Coordinate.lean` emitted its three historical
unused-section-variable linter warnings; it was not edited during the freeze.

The nine audited declarations comprise the cocycle conjugation and shared-unit
lemmas, two area helpers, coefficient-form symmetry, pure-boundary cone
evaluation, actual-partner localization, normalized boundary identities and
the final integral-unit comparison. All transitive axioms are among
`propext`, `Quot.sound`, `Classical.choice`. No `sorryAx`, custom arithmetic
axiom, native-evaluation bypass or kernel-check bypass is present.

| Gate | Evidence/status |
| --- | --- |
| A01 snapshot | PASS: `evidence/native/RESULT.json` input hashes, source base and dependency identities |
| A02 specification | PASS: `FORMAL_SPEC.md` and exact application crosswalk |
| A03 semantics | PASS: `focused-reviews/core.md`; elaborated definitions and statements in `evidence/native/axioms-and-statements.txt` |
| A04 proof mapping | PASS: `APPLICATION.md` maps every interface and substantive inference to sources and targets |
| A05 build/lint | PASS: five freshly compiled modules; new target clean, inherited warnings described above |
| A06 axioms | PASS: all nine declarations audited transitively against the stated allowlist |
| A07 boundaries | PASS: zero/common nonunit factors, explicit integral units, typed cone degrees and same-class/row identities inspected; 675 finite sign controls retained as supplementary evidence |
| A08 replay | NOT_RUN: source compilation is not export-kernel replay |
| A09 protected comparison | NOT_RUN: no new protected challenge/comparator packet |
| A10 external checkers | NOT_RUN |
| A11 clean environment reproduction | NOT_RUN: fresh local output directory with trusted dependency cache |
| A12 non-author mathematics | PASS within the declared conditional scope: `focused-reviews/core.md`, with internal-model independence limits |
| A13 claim discipline | PASS: explicit retained-source/realization assumptions and the ordinary/formal split are recorded throughout |

The final development-profile decision is recorded with the focused reviews.
A successful cloud check of the old 39 declarations supplies no additional
verification of this new module.

The authoritative native record is `evidence/native/RESULT.json`, with
`commands.json`, complete text logs and generated `Audit.lean`. Binary build
products are recoverable from the pinned sources and are identified by hashes;
they are not committed. `verify_native.py` is a narrow local driver, not a
fourth cloud/comparator project.

The source addendum is ordinary mathematics under the retained arithmetic
inputs. Its actual Galois, localized orthogonal-duality, common-strict model
and limit realizations are not constructed in Lean. The direct
determinant-functor argument is not claimed as a formal theorem.
