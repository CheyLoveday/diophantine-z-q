# Building the handoffs

Run the build on a remote worker with sufficient disk space and an external
time and memory limit. The scripts use Python's standard library and Git.
They do not download the baseline or publish releases.

First commit the complete public snapshot, including `quartic_12504.tex`,
`quartic_12504.pdf`, the exact quartic package, the evidence inventory, and
the successful full-reproduction `SUMMARY.json`. Record that immutable
commit ID and the receipt's repository-relative path. Then run:

```sh
python -E -B handoff/test_handoff.py
python -E -B handoff/prepare_handoff.py \
  --repo . --commit SNAPSHOT_SHA \
  --verification-receipt REPO_RELATIVE_REPRODUCTION_SUMMARY.json \
  --output /tmp/handoff-plan.json
python -E -B handoff/build_handoff.py \
  --repo . --plan /tmp/handoff-plan.json \
  --baseline /tmp/baseline-r2.zip --output /tmp/version2-handoff
```

The baseline input is the public
[November 4 revision-2 archive](https://github.com/elliotglazer/diophantine-z-q/releases/download/research-handoff-2026-11-04-r2/z-in-q-research-handoff-2026-11-04-r2.zip).
Its required SHA-256 is
`827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b`,
and its size is 339,860,770 bytes. The builder verifies these before packaging
and stores the ZIP unchanged, without recompressing it.

Plan preparation reads the exact Git tree, checks all new payload files for
credential or conversation markers, verifies the current quartic package
manifest, and requires a successful fresh reproduction receipt. Nothing is
silently omitted from the current commit. The builder independently compares
the plan with the complete commit tree before writing either archive.

The output directory contains both ZIPs, `SHA256SUMS`, and
`BUILD_RECEIPT.json`. Both ZIPs are checked entry by entry before a successful
receipt is written. Preserve `/tmp/handoff-plan.json` as well. The large full
ZIP is intended as a release asset, not a Git-tracked file. Determine the
current-only ZIP's suitability for any other transport from its measured
size after the build.

The release target is the same snapshot commit used by the builder. A
manually dispatched workflow can upload these outputs to a draft release
for review. Keep publication separate from construction and integrity
verification. If later repository metadata records the completed archive's
checksum, retain the earlier snapshot ID in the archive and receipt.
