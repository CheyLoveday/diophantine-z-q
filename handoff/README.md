# Version 3 research handoffs

Date: November 6, 2026.

The Version 3 handoffs contain the 9,625-variable quartic and selected project research. The release target is [quartic-9625-version-3](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-9625-version-3). The build produces two assets:

| Asset | Contents |
| --- | --- |
| `z-in-q-version3-full-handoff.zip` | Exact public snapshot, selected proof and review notes, and the unchanged public November 4 revision-2 baseline ZIP |
| `z-in-q-version3-current-handoff.zip` | The same current snapshot and notes, with the baseline's URL and checksum instead of the nested ZIP |

The full ZIP is self-contained for these included collections. It does not contain every private research record. The [Version 2 handoffs](releases/version2/README.md) remain historical and unchanged.

Before opening or running archive contents, compare the ZIP's SHA-256 with the release's `SHA256SUMS`. `BUILD_RECEIPT.json` records the exact snapshot, archive identities and frozen-plan digest. The [completed Version 3 release record](releases/version3/README.md) supplies the download links, sizes, hashes and build evidence.

After extraction, read `START_HERE.md`, `CURRENT_STATE.json` and `COVERAGE.md`. `current/` contains every regular tracked file from the recorded public commit. `history/version3/` contains selected evidence for this release. `history/not-in-version3/` contains separate three-mode, Jacobi and other research; those notes do not define the released source or its count. The earlier selected Version 2 records preserve their original status wording.

Verify or safely extract with:

```sh
python -E -B handoff/verify_handoff.py PATH_TO_HANDOFF.zip --expected-plan-sha256 DIGEST
python -E -B handoff/verify_handoff.py PATH_TO_HANDOFF.zip --expected-plan-sha256 DIGEST --extract NEW_DIRECTORY
```

Obtain `DIGEST` from the independently downloaded release receipt. The verifier checks every member's CRC and SHA-256, current proof-package closure, release counts and reproduction receipt. It rejects unsafe names, duplicates, case collisions and symlinks. It also rejects entries absent from the plan and binds generated guides and helpers to that plan.

The old Version 2 format remains supported by the preserved legacy integrity checker. For those archives, first check the independently published whole-ZIP SHA-256, then run this tool without `--expected-plan-sha256`. Plan-only authentication is rejected for the historical format; its integrity check does not provide the new Version 3 exact-plan guarantees.

Run the mathematical checks from the extracted `current/` directory using [the current package instructions](../quartics/quartic-9625/reproducibility/README.md). Archive integrity, exact algebraic replay and the arithmetic proof have distinct scopes.

The historical baseline is 339,860,770 bytes with SHA-256 `827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b`. Its own `current/` directory means current at its historical date. Extract it separately and retain its notices and filtering policy.

See [BUILDING.md](BUILDING.md) for the remote build sequence and [SCOPE.md](SCOPE.md) for the selection rules. A later repository commit may record completed archive checksums; the archive continues to identify the earlier snapshot it actually contains.
