# Version 4 research handoffs

Date: November 6, 2026.

The [Version 4 release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-4973-version-4) contains two archives:

| Asset | Contents |
| --- | --- |
| `z-in-q-version4-full-handoff.zip` | Exact public snapshot, selected mathematical research and reviews, and the unchanged November 4 revision-2 baseline ZIP |
| `z-in-q-version4-current-handoff.zip` | The same current snapshot and selected notes, with the baseline URL and checksum instead of the nested ZIP |

The current manuscript is `quartic_4973.tex/pdf`, Version 4. Its selected quartic has 4,973 total variables, 72,925 monomials and degree four. Source arithmetic reviews, finite certificate replay and fresh reproduction have separate roles in the included evidence.

Compare each archive's SHA-256 with the release's `SHA256SUMS`. `BUILD_RECEIPT.json` gives the exact snapshot and frozen-plan digest. An internal manifest does not authenticate its own origin.

After extraction read `START_HERE.md`, `CURRENT_STATE.json`, `COVERAGE.md` and `RESEARCH_NOTES.md`. `current/` is every regular tracked file at the recorded public commit. `history/version4/` contains selected proof and review provenance; its dated pending statuses are historical. Optional scalar/J0 fusion is excluded from the selected source. Earlier version directories retain their original meaning and claims.

```
python -E -B handoff/verify_handoff.py PATH_TO_HANDOFF.zip --expected-plan-sha256 DIGEST
python -E -B handoff/verify_handoff.py PATH_TO_HANDOFF.zip --expected-plan-sha256 DIGEST --extract NEW_DIRECTORY
```

Use the plan digest from the independently obtained release receipt. The verifier checks every member, exact planned file coverage, source-package closure and the selected reproduction receipt. It rejects unsafe names, duplicate paths, case collisions and symlinks. The archived Version 3 verifier and matching helpers remain under `history/version3/tooling/` for Version 3 archives. Version 2 uses the preserved legacy verifier with its independently published whole-archive checksum.

Run the actual mathematical computations from `current/` using the [reproduction instructions](../quartics/quartic-4973/reproducibility/README.md). Archive integrity does not establish the arithmetic theorem. The finite checks do not upgrade the inherited theorem qualifications or complete the Lean formalization.

The unchanged historical baseline is 339,860,770 bytes, SHA-256 `827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b`. Its own `current/` directory means current at its historical date. The full archive is self-contained for the included collections, not a claim to contain every private research record. Conversational transcripts and credentials are excluded.

See [BUILDING.md](BUILDING.md) and [SCOPE.md](SCOPE.md). A later commit may record the finished archive checksums; the archive continues to identify the earlier snapshot it actually contains.
