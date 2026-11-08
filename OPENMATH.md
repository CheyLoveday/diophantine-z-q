# Open Math: boundary-scalar repository handoff

Open Math pulls this repository and performs the Lean 4.35 paranoid run in its
cloud environment. All preparation inputs are committed here; no local ZIP,
Mac build directory or attachment is needed.

| Item | Value |
| --- | --- |
| Repository | `https://github.com/CheyLoveday/diophantine-z-q.git` |
| Branch to pull | `codex/derivative-switch-boundary-v13` |
| Reviewed boundary-scalar snapshot | `7ca086adf4298e2b611b9fa0b954eab838873bf3` |
| Selected declarations | 21: original six, thirteen principal matrix results, two typed adapter results |
| Local preparation | [prepare_derivative_switch_openmath.py](scripts/prepare_derivative_switch_openmath.py) |
| Proof scope and local results | [Boundary-scalar verification](research/boundary-scalar/VERIFICATION.md) |
| Original freeze | [Preserved six-lemma packet](research/determinant-switch/FREEZE.md) |

Pull the research branch, which contains these instructions and the reviewed
snapshot. `main` is the unchanged Version 13 baseline and does not contain the
research packet. Record the actual checkout commit; the preparation receipt
records it too. Use the research branch explicitly when configuring Open Math's
repository checkout.

The existing fork above is the active Open Math pull destination. A private
working copy also exists at `CheyLoveday/diophantine-z-q-private`; it retains
the same reviewed source and can be used if private access is preferred later.

## Prepare directly from the checkout

From the repository root, with Git and Python 3.9 or newer:

```sh
python3 -B scripts/prepare_derivative_switch_openmath.py --packet boundary-scalar
```

This offline command verifies both frozen manifests: the original 63 entries
and the new 65 entries. It uses the reviewed generator to create
`lean/.checks/openmath-boundary-scalar`. It checks the 17-file generated project
against its frozen manifest digest and records the checkout in
`OPENMATH_PREPARATION.json`.
It requires no Lean installation, dependency cache or untracked local input.
For another attempt use `--output lean/.checks/openmath-boundary-scalar-2`;
existing output directories are never overwritten.

The [matrix proof](lean/Research/BoundaryScalar.lean),
[typed adapter](lean/Research/BoundaryCupAdapter.lean),
[original module](lean/Research/DerivativeSwitchBoundary.lean),
[separate specifications](research/boundary-scalar/verification/Challenge.lean),
[21-name configuration](research/boundary-scalar/verification/comparator.json),
dependency lock and toolchain are copied from this checkout. The inherited
default `ZInQ` target excludes the research lemmas, so use the generated project.
Its default is the solution library; its challenge is separate.

The default is the current combined project. Use `--packet six-lemma` to
reproduce the original target and its original output directory explicitly.
The three specification modules preserve the exact import context of each
paired solution module, including its elaborated coercion instances.

## Open Math's cloud execution

Open Math supplies Linux, pinned Lean 4.35.0, Git, Python, and a working
`bubblewrap` sandbox. Keep the reviewed challenge/configuration protected by
the pinned manifest. The cloud setup resolves the nine locked dependency
revisions and uses the official Mathlib cache for the required imports:

```sh
set -eu
cd lean/.checks/openmath-boundary-scalar
sha256sum -c MANIFEST.sha256
lean --version
lake --version
MATHLIB_CACHE_DIR="$PWD/.lake/mathlib-cache" lake exe cache get \
  Mathlib.Algebra.Module.Equiv.Basic Mathlib.Tactic.Ring \
  Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.Tactic.FieldSimp \
  Mathlib.LinearAlgebra.BilinearForm.Properties
sha256sum -c MANIFEST.sha256
lake comparator --config comparator.json --paranoid
sha256sum -c MANIFEST.sha256
```

Run each command only if the preceding command succeeded. The cloud runner must
capture the comparator's own exit status and complete stdout/stderr, in addition
to the final manifest check. Preserve the preparation receipt and actual
dependency/checker revisions or hashes with that result. Use the locked
dependencies; do not update them or disable sandboxing to obtain a pass.

Success requires the 21 specified declarations, the unchanged concrete
definitions, the allowed axiom policy, and acceptance by `Lean default`,
`Lean paranoid`, `lean4lean`, `nanoda`, `con-leche`, and `con-ron`.
The 21 challenge `sorry` warnings are specification placeholders; `sorryAx`
is forbidden in solution proofs. Full interpretation and evidence requirements
are in the [reviewed verification instructions](research/boundary-scalar/verification/README.md).

The mathematical review, native macOS compilation/axiom audit, exact models,
and local statement/definition comparison are already complete. The cloud run
is the next execution step. Actual arithmetic tensor compatibility remains
open. The common-strict-to-normal-form construction and determinant-line/DVR
interpretations are ordinary algebra in the [derivation](research/boundary-scalar/DERIVATION.md),
not additional Lean constructions. The typed adapter assumes the actual two
boundary--cup identities; it does not establish them for the arithmetic data.

Command semantics were checked on 8 November 2026 against the installed Lean
4.35.0 sources (`Lake/Load/Resolve.lean`, `Lake/CLI/Check.lean`), the
[4.35 release documentation](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/),
and the [pinned Mathlib cache documentation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/README.md).
Local preparation checks establish checkout completeness; they do not claim
execution of Open Math's Linux environment or paranoid kernels.
