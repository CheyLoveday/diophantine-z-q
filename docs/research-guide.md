# Research guide

This guide describes the [November 4, 2026 research handoff](https://github.com/elliotglazer/diophantine-z-q/releases/tag/research-handoff-2026-11-04). It is a map of the saved evidence, not a replacement for the paper's proofs.

## Suggested reading order

1. Read **The main theorem and proof structure** in the paper for the statement and the roles of the component arguments.
2. Read **A finite specification of the polynomial**, **A variable-shift relation for ordinary values**, and **The cutoff and polynomial size** to see what is constructed and how it defines ordinary integer values.
3. Follow the technical argument through the elliptic model, height estimate, pole predicate, multiplication, and restricted converse. The arithmetic and limit sections and source-application appendices supply the dependencies.
4. Read **Consequences of the integer definition** for the three corollaries and their scope.
5. Use the archive to inspect literal specifications, calculations, source checks, historical alternatives, or formalization work.

The TeX source has stable descriptive labels such as `thm:target`, `sec:syntax`, `sec:height`, `sec:rc`, `sec:limits`, `sec:compiler`, `sec:bridge`, and `sec:size`. Refer to those labels when page numbers differ between builds.

## Map of the argument

The paths below are **original project-relative paths recorded in the archive manifest**. Search for them in `INDEX.html`, or restore them with `restore_history.py`. They are not paths in this small Git checkout. Some files predate the final manuscript; compare their scope with the current paper and later audits.

| Topic | Paper section | Archive starting points |
| --- | --- | --- |
| Literal polynomial specification | A finite specification of the polynomial; Literal finite-constructor specification | `outputs/ordinary-integer-definition.json`; `outputs/ordinary-integer-polynomial.js` |
| Elliptic model and generator | The elliptic model of integer indices | `outputs/elliptic-generator-proof.txt`; `outputs/z-in-q-generator-audit.txt`; `outputs/verify-z-in-q-generator.py` |
| Height estimates | The six-contact height estimate | `outputs/six-contact-height-proof.txt`; `outputs/explicit-noncm-height-bound.txt`; `outputs/effective-cm-height-bound.txt` |
| Pole completeness and restricted converse | The pole predicate and its converse input; The restricted converse and its dependency order | `outputs/restricted-converse-and-pole-completeness-proof.txt`; `outputs/z-in-q-restricted-converse-assembly.txt` |
| Arithmetic dependencies and limits | Actual classes, local conditions and central comparison; The two limits and determinant transfer | `outputs/z-in-q-global-selmer-assembly-audit.txt`; `outputs/z-in-q-common-packet-audit.txt`; `work/sol-rc-arithmetic-graph-review-001/` |
| Computation and compilation | Exact precision computation and polynomial compilation | `outputs/integer-halting-correctness-proof.txt`; `outputs/integer-diophantine-compiler.js`; `outputs/hierarchical-integer-compiler.js` |
| Ordinary rational values | A variable-shift relation for ordinary values | `outputs/ordinary-input-bridge.txt`; `outputs/z-in-q-exact-value-bridge-audit.txt`; `outputs/z-in-q-ordinary-integer-assembly-proof.txt` |
| Variable, degree, and coefficient bounds | The cutoff and polynomial size | `outputs/ordinary-integer-polynomial-size-bounds.json`; `outputs/z-in-q-polynomial-size-bound-proof.txt` |
| Universal and ZFC-related constructions | Consequences of the integer definition | `outputs/universal-rational-equation.json`; `outputs/zfc-inconsistency-polynomial.json`; `outputs/zfc-inconsistency-polynomial-proof.txt`; `work/k215-pa/` |
| Sources and dependency graphs | Bibliography and source-application appendices | `formalization/z-in-q/ProofSources/`; `work/main-proof-graph/` |
| Earlier versions and discarded routes | Historical record | `drafts/z-in-q-candidate-preprint/`; `outputs/z-in-q-research-status.json`; archive-root `DISCARDED_APPROACHES.md` |

The archive's K215 and ZFC-related files record additional research. The current paper describes the general specialization argument; it does not specify an additional explicit ZFC polynomial there. Check each historical construction's dependencies before treating it as a consequence of the final manuscript.

## Verify and restore the archive

Download the handoff zip from the release. Its SHA-256 is:

```text
522c61d723841a41bd3d920d1b3160f8ffbeb5fe5bb68f0dbb0c48432f88d665
```

On Windows PowerShell:

```powershell
Get-FileHash -Algorithm SHA256 .\z-in-q-research-handoff-2026-11-04.zip
```

On Linux:

```sh
sha256sum z-in-q-research-handoff-2026-11-04.zip
```

On macOS:

```sh
shasum -a 256 z-in-q-research-handoff-2026-11-04.zip
```

The repository's [SHA256SUMS](../SHA256SUMS) also records the TeX and PDF hashes. Matching a hash establishes file identity, not mathematical correctness.

Extract the zip, then open `START_HERE.md`, `CURRENT_STATE.json`, and `INDEX.html`. The HTML index works locally without a server. Original file paths map to their stored copies through `MANIFEST.json` and `FILE_INDEX.csv`.

From the extracted archive directory, use Python 3.9 or later to restore a selected subtree:

```sh
python restore_history.py restored-outputs --prefix outputs/
python restore_history.py restored-lean --prefix formalization/
```

Or restore all indexed files:

```sh
python restore_history.py restored-project
```

Each destination must be new. The utility checks file hashes before writing and does not execute research code. A full restoration occupies about 2.4 GB before filesystem overhead; use a short destination path on Windows. Historical scripts may contain paths from the original Windows workspace that need adapting.

All archive entries were checked for CRC and SHA-256 integrity during packaging. The 48 production-module source hashes were checked against integration 31, and a 54-file subset restoration was tested. No clean rebuild of the full research project was performed as part of packaging.

## Lean formalization

The saved project uses `leanprover/lean4:v4.35.0` and Mathlib `v4.35.0`; its `lake-manifest.json` records the dependency revisions. Restored sources are under `formalization/z-in-q/`. The archive also provides a readable copy under `current/lean-project/`.

Start with these records:

- `outputs/z-in-q-integration-31.json`: the last accepted production integration and its source hashes.
- `outputs/z-in-q-progress-122.json`: later accepted helper work and the state at handoff.
- `work/astra-formal-critical-path-001/REPORT.md`: the main groups of remaining obligations. This report audits integration 29, so read it alongside the later records.
- `work/sol-post32-accepted-inventory-004/HANDOFF.json`: an inventory of further accepted components. Its directory name is not evidence that integration 32 was accepted.
- `formalization/z-in-q/Frozen/BoundedIntegerPolynomial.lean`: the exact main declaration, still unproved.

The complete elliptic model, height, restricted-converse, pole-completeness, multiplication, computation, and construction/bounds groups, and their ordinary-value composition, remain open as complete formalized interfaces. Proven helper results do not by themselves close those interfaces. Integration 32's observation was interrupted and was not accepted.

The archive omits dependency caches and compiled Lean binaries. Reproducing a build requires restoring the sources and installing the pinned dependencies. There is not yet a verified clean-checkout build procedure in this repository. The saved compiler receipts describe their particular checked inputs, not every file in the historical archive.

## Preparing the public research package

The next useful additions are:

- A small, browsable source tree containing the current polynomial specification, its exact dependencies, and the checks needed to reproduce it. Keep the larger historical archive as a separate snapshot.
- A clean-checkout build procedure for the paper and accepted Lean modules, with automated checks for those specific targets.
- Citation metadata with confirmed authorship and, if obtained, an archival DOI.
- Licenses for the original manuscript and code, with separate attribution and licensing information for third-party material in the archive.
- A versioned record of substantive external review findings and how each was resolved.

Until these are added, use the release tag and file hashes to identify the exact materials under discussion.
