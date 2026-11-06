# Building and checking the research package

Run these commands from the repository root. Python scripts use the standard library. The current quartic and the original large construction have separate checks.

## Current quartic

To replay the frozen certificate and reproduce the complete 12,504-variable construction:

```sh
python3 -E -B quartics/quartic-12504/reproducibility/run.py --output build/quartic-reproduction --stage-seconds 180
```

Use a fresh output directory outside the package. The runner reads the package without changing it and writes generated files, logs and reports to that directory. Exact-byte reproduction uses Linux with CPython 3.12.14. The runner checks the gzip/zlib output before proceeding and rejects incompatible serialization. See the [reproduction instructions](../quartics/quartic-12504/reproducibility/README.md) for its stages and failure conditions.

For the frozen artifact's algebraic replay alone, copy `quartics/quartic-12504/` to a writable directory and run:

```sh
python /path/to/writable-copy/verify_certificate.py /path/to/writable-copy
```

This checker writes `verification.json` in the supplied directory. Use the copy to preserve the released receipt. It verifies exact projection-preserving equivalence to the pinned source and the complete integer expansion, including the variable count, degree and coefficient bound. These checks do not prove the source system's arithmetic characterization of the integers. The [Version 2 evidence](quartic-12504/README.md) records that separate argument and its review scope.

## Version 2 manuscript

```sh
python scripts/build_paper.py
```

The script downloads a SHA-256-verified Tectonic 0.17.0 binary for the host platform, then builds a copy of [quartic_12504.tex](../quartic_12504.tex) in an isolated temporary directory. It uses the fixed `tlextras-2022.0r0` bundle URL and checks the selected bundle's fingerprint. Tectonic fetches the required support files. The first run requires network access; later runs reuse the local resource cache.

If Tectonic 0.17.0 is already installed:

```sh
python scripts/build_paper.py --tectonic /path/to/tectonic
```

Results are written to `build/paper/`, including `quartic_12504.pdf`, `quartic_12504.log`, `compiler.log`, and `build-report.json`. The script fails on a compilation error, unresolved references or citations, or an unexpected bundle fingerprint. Typesetting warnings remain in the log.

The build does not replace the checked-in PDF. Fixed engine, bundle and timestamp inputs improve reproducibility, but PDF byte identity across operating systems is not claimed. The old receipts under `docs/theorem-application-audit/` describe their frozen historical manuscript, not the Version 2 build.

## Manuscript inventories

```sh
python docs/theorem-application-audit/validate.py
python docs/quartic-12504/validate.py
```

The first command validates the [historical theorem-application inventory](theorem-application-audit/README.md) against its archived baseline. The second checks the [Version 2 inventory and manuscript bindings](quartic-12504/README.md). Read those instructions for the exact scopes. These structural checks do not prove mathematical statements. Primary-source verification for the historical inventory additionally requires its separately restored research workspace.

## Original large construction

This check uses Python 3.11 or later and Node.js 22 or later. CI pins Python 3.12.14 and Node.js 24.22.1.

```sh
python scripts/check_construction.py --report build/construction-checks.json
```

It regenerates the original rational expression from its pinned natural-polynomial input, checks hashes and wiring, recalculates syntactic bounds, and runs the supplied finite arithmetic checks. See the [original construction README](../construction/README.md) for each check's scope. This is separate from the quartic reproduction above.

## Lean helpers

Install [elan](https://github.com/leanprover/elan), then run:

```sh
cd lean
lake exe cache get
cd ..
python scripts/check_lean.py --build --output build/lean-local
```

The output directory must not already exist. The checked-in toolchain and Lake manifest pin Lean and Mathlib. The checker validates source hashes and dependency revisions, compiles the 48 accepted helper modules and their root into fresh project artifacts, and runs the axiom audit. Dependency binaries come from the pinned Mathlib cache and are not rebuilt by this command.

For the quick source and quarantine checks without compiling:

```sh
python scripts/check_lean.py
```

Read the [Lean README](../lean/README.md) for the trust boundary and allowed axioms. The main theorem remains unproved; its frozen `sorry` is excluded from the default imports and accepted-helper audit.

## Continuous integration

The [Version 2 workflow](../.github/workflows/manuscript-integration.yml) reproduces the quartic, validates the historical and current manuscript inventories, and compiles the current manuscript. It runs on relevant pushes and manual dispatch. The [research workflow](../.github/workflows/research-checks.yml) checks the original construction, the historical inventory, manuscript compilation and the accepted Lean helpers.

GitHub Actions dependencies are pinned to commit hashes; the elan installer and Tectonic archives are pinned by SHA-256. Workflows upload their reports and logs. A green run means the named checks passed on that commit. It does not certify the global arithmetic inputs or complete the main Lean proof.
