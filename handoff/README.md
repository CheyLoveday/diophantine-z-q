# Version 2 research handoffs

The [Version 2 release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-12504-version-2)
has two handoff formats:

| Asset | Contents |
| --- | --- |
| [Full handoff](https://github.com/elliotglazer/diophantine-z-q/releases/download/quartic-12504-version-2/z-in-q-version2-full-handoff.zip) | Exact current public snapshot, selected mathematical notes, and the unchanged public November 4 revision-2 baseline ZIP |
| [Current-only handoff](https://github.com/elliotglazer/diophantine-z-q/releases/download/quartic-12504-version-2/z-in-q-version2-current-handoff.zip) | The same current snapshot and selected notes, with a URL and checksum for the baseline instead of embedding it |

Use the full ZIP for a handoff self-contained for these included collections.
It is not a copy of every private research file or every historical primary
source. The current-only ZIP is useful when the historical baseline is
already available separately.

Before opening or running archive contents, compare the ZIP's SHA-256 with
the release's [SHA256SUMS](https://github.com/elliotglazer/diophantine-z-q/releases/download/quartic-12504-version-2/SHA256SUMS).
The [build receipt](https://github.com/elliotglazer/diophantine-z-q/releases/download/quartic-12504-version-2/BUILD_RECEIPT.json)
records the snapshot commit, archive identities and frozen-plan digest.
An embedded manifest alone does not authenticate its own claimed source.

After extraction, start with `START_HERE.md` and `CURRENT_STATE.json`.
The layout is:

- `current/`: every regular tracked file of the exact public snapshot commit,
  including the Version 2 manuscript, exact quartic, source, checks, evidence,
  dependency inventories and accepted Lean helpers.
- `history/`: 18 selected mathematical proof, review and circuit records.
  The low-precision experiments are explicitly marked unadopted.
- `baseline/`: the unchanged historical ZIP, present only in the full handoff.
- `RESEARCH_NOTES.md` and `COVERAGE.md`: current status and the precise limits
  of the selection.
- `PLAN.json`, `MANIFEST.json` and `verify_handoff.py`: exact identities and
  an integrity checker with optional safe extraction.

To verify an archive using this checkout's verifier:

```sh
python -E -B handoff/verify_handoff.py PATH_TO_HANDOFF.zip
```

Add `--expected-plan-sha256 DIGEST` using the digest obtained from the release
receipt. Add `--extract NEW_DIRECTORY` to verify and extract into a new
directory. The verifier rejects unsafe paths, duplicate or case-colliding
members, symlinks, modified entries and missing current proof-package files.
It also checks every entry's CRC and SHA-256.

Run the manuscript and quartic build commands from the extracted `current/`
directory. The exact quartic reproduction instructions are in
`current/quartics/quartic-12504/reproducibility/README.md`. Archive integrity
checks and mathematical proof reviews have distinct scopes.

The historical baseline has 339,860,770 bytes and SHA-256
`827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b`.
Its own `current/` directory means current at that archive's date. Extract
the nested ZIP separately and use its own index and restoration tool for
older research paths. Its recorded filtering and third-party notices remain
in force; it is not a new copy of Version 2.

A later commit may add the ZIP's receipt or checksum to the repository.
The archive names the earlier exact snapshot it actually contains. See
[BUILDING.md](BUILDING.md) for the remote build sequence and
[SCOPE.md](SCOPE.md) for selection rationale.
