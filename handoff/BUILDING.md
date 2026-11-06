# Building the Version 3 handoffs

Date: November 6, 2026.

Commit the complete public Version 3 snapshot first, including `quartic_9625.tex`, `quartic_9625.pdf`, `quartics/quartic-9625/`, the current dependency inventory and successful fresh reproduction receipt. Also include the actual regenerated certificate at `docs/quartic-9625/verification/regenerated-certificate.jsonl.gz`. `handoff/release.json` binds the exact 9,625-variable source, certificate, verifier and polynomial. The preparer checks that this descriptor is itself in the recorded commit.

Run on the bounded remote worker:

```sh
python -E -B handoff/test_handoff.py
python -E -B handoff/prepare_handoff.py \
  --repo . --commit SNAPSHOT_SHA --release handoff/release.json \
  --verification-receipt docs/quartic-9625/verification/REPRODUCTION.json \
  --output /tmp/version3-handoff-plan.json
python -E -B handoff/build_handoff.py \
  --repo . --plan /tmp/version3-handoff-plan.json \
  --baseline /tmp/baseline-r2.zip --output /tmp/version3-handoff
```

The baseline is the unchanged [November 4 revision-2 archive](https://github.com/elliotglazer/diophantine-z-q/releases/download/research-handoff-2026-11-04-r2/z-in-q-research-handoff-2026-11-04-r2.zip). Its required size is 339,860,770 bytes and SHA-256 is `827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b`. The builder streams it unchanged using ZIP_STORED. It does not download or publish anything itself.

Plan preparation checks all current commit files and selected notes for forbidden paths and credential or conversation markers. It validates the exact artifact pins, current source closure, reproduction package manifest, and the completed reproduction receipt. Counts and source identity must agree across `release.json`, `evidence/stages/coordinates.json`, the reproduction manifest and the fresh receipt. The builder independently matches the complete Git tree before writing either ZIP.

The frozen certificate retains its exact released SHA-256. The regenerated certificate must match its own SHA-256 in the fresh receipt. Their decoded JSONL records must then agree after removing only `final.report.seconds`. No other field, operation or coefficient is ignored. Duplicate JSON keys, nonfinite numbers and numeric-type changes are rejected.

The output contains both Version 3 ZIPs, `SHA256SUMS` and `BUILD_RECEIPT.json`. Both archives are verified before a successful receipt is written. Preserve the frozen plan too. Build sizes and hashes are reported only after this run. The large ZIPs belong in release assets, not Git.

The proposed workflow creates a draft at the exact snapshot commit and refuses to overwrite an existing tag. Dispatch, final inspection and publication remain separate actions. Later receipt/checksum commits do not change the snapshot already recorded inside the archives.
