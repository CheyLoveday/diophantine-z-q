# Handoff coverage

| Collection | Included material | Status |
| --- | --- | --- |
| `current/` | Every tracked regular file of the exact public commit in `CURRENT_STATE.json`, including Version 2 TeX/PDF, quartic, source, checks, evidence, inventories, public research guide and accepted Lean helpers | Current snapshot |
| `baseline/` in the full ZIP | Complete public November 4 revision-2 ZIP, 339,860,770 bytes, unchanged | Historical; original filtering and scope retained |
| `history/earlier-quartic/` | One standalone algebra note selected from the private-v5 inventory | Historical old-source conversion, not the current source |
| `history/reciprocal/` | Reciprocal-log proof, beta16 review, identity/nonvanishing review and compiler review | Intermediate proof and review records used by Version 2 |
| `history/source-audit/` | Explanation and independent review of the source auditor | Source construction and flattening scope |
| `history/charts/`, `history/parity/`, `history/batching/` | Exact solution-map proofs and available independent reviews | Intermediate algebraic reductions |
| `history/unadopted-lowprecision/` | Five circuit/probe/checker/proof/review files and the recorded 44-profile summary | Unadopted finite experiments, not a new source or quartic |

The current-only ZIP contains the same current snapshot and selected notes,
but omits the large nested baseline. Its `START_HERE.md` provides the public
baseline URL and exact checksum. The full ZIP is self-contained for these
included collections.

This is not a dump of the private-v5 archive or the working directory. The
private-v5 inventory listed 537 current files and 3,641 later history paths;
those counts describe that private artifact, not this public handoff.
Unpublished third-party comparison archives, private source collections,
operational access records, API payloads, model conversations, raw event
streams, credentials, build caches and unrelated experiments are omitted.
No private-v5 validation receipt is presented as validation of this archive.

New payload files are explicitly selected or drawn from the complete public
commit. They are checked for credential and conversation markers. The large
baseline is checked by its already-public whole-file SHA-256; its contents
are not newly republished under a different license or represented as a
freshly reviewed current source. Read the baseline's own notices and the
current repository's `THIRD_PARTY_NOTICES.md`.

The final manifest gives exact paths, sizes and SHA-256 hashes. Match the ZIP
against the published checksum before trusting its embedded manifest or
running its code. `verify_handoff.py --expected-plan-sha256 DIGEST` can also
bind the archive to an independently obtained frozen-plan digest. A final
Git commit that adds the ZIP receipt is later metadata; the archive records
the earlier exact snapshot commit it actually contains.
