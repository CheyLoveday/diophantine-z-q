# Handoff selection rationale

The private-v5 inventory was inspected as a historical index, not selected
as a publication source wholesale. Its receipt identifies a 503,417,868-byte
private archive with 537 snapshot files and 3,641 later historical paths.
Those numbers and its private release identity do not describe this handoff.
Its own documentation says that it contains unpublished inputs and grants no
public redistribution rights.

The new handoff preserves the already-public revision-2 baseline unchanged.
The public `SHA256SUMS` and archive-reference inventory identify SHA-256
827765f17087e1794c15770221a3a2d0fefed25839566a4a9bfb3b5aaa1ed42b.
The old `research-handoff-20261104/VALIDATION_RECEIPT.json` belongs to revision
1 and is not used as evidence for revision 2. The new remote build verifies
the entire revision-2 ZIP digest without claiming a new content audit.

Only `work/quartic-search-20261105/ALGEBRA.md` is selected from the older
private-v5 history list. Its exact hash is
5ed46349c6fc96e3a1f5183b666ab8afee9c01837f7b340a60577a31541be029.
It is a standalone account of the old conversion algebra, independently read
for this handoff and explicitly marked historical. The old completion report
is omitted because it combines stale endpoints with conversational progress
narration. Access files, job payloads and unpublished comparison collections
are omitted.

The remaining 17 historical files are newly selected mathematical proof,
review, circuit and finite-check records from the work leading to Version 2.
The six-file low-precision subset is explicitly unadopted. The exact list,
original paths, byte counts, content hashes and reasons are in
`selection.json`. Two new orientation documents summarize status without
rewriting the preserved research records.

The current collection is every regular tracked file of a single reviewed
public commit. Plan preparation fails on forbidden path types, credential or
conversation markers, missing current manuscript/evidence files, an invalid
quartic package manifest, or a missing successful full-reproduction receipt.
No file is silently dropped from that current snapshot. The builder compares
the plan's full path/blob list against the actual Git tree again.

Archive verification checks all entry hashes and CRCs, validates the exact
current proof-package closure, and checks the unchanged baseline identity.
It rejects unsafe, case-colliding, nonregular and nonportable extraction
paths. Snapshot authenticity still requires the independently published
whole-ZIP checksum or frozen-plan checksum. The archive never authenticates
its own claimed origin merely by containing a manifest.
