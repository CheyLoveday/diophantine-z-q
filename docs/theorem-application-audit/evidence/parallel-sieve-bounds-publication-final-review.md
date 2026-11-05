# Final publication review

I inspected the integrated local repository after the final manuscript and public-documentation edits. This is a publication consistency review, not another proof audit. No shared files or release assets were changed.

The reviewed manuscript is SHA256 `f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3`. The PDF is SHA256 `571f3b0cf5861e788c098f7d55f4d75536eb857fe46b4ac55bd8335ab6d5f39a`, 892654 bytes and148 pages. I independently hashed both files and counted the PDF pages. These match SHA256SUMS, MANUSCRIPT_BUILD.json and the public README/building claims.

## Required corrections or pending finalization

1. **Contradictory AFP source status.** In sources.json, source `afp`, version_notes still says the original revision identity “still requires authentication,” immediately followed by the authenticated development-mirror revision and date. The obsolete sentence also appears in SOURCES.md L16 and the generated SOURCE_RESTORATION.json. Replace it with a historical qualification or remove it. Suggested complete opening: “The three original Isabelle source files are exact-byte pins matching AFP development mirror b4f3b892d0ae25cea27412ba4007cdb63e44b0eb dated 2026-05-10T07:38:12Z.” Preserve the separate statement that no Isabelle build or stable release is inferred. Update the authoring source of this note, regenerate the source register, then regenerate the restoration manifest since its source-register hash will change.
2. **Pending validation receipt.** Audit README L42 calls VALIDATION.json the final workspace check, but at review time that file still records106 citations and66 source files. The current check passes with147 citations and97 source-file entries. Replace the receipt with the actual final run, as root already plans.
3. **Pending restoration receipt/link.** Audit README L44 links RESTORATION_CHECK.json and says a fresh-directory verification was performed. That file is the sole missing local file among71 Markdown link targets checked across the main public documents. Produce the promised fresh-directory check and receipt before publishing that sentence. Do not replace it with an unexecuted plan. Root already identified this as next work.
4. **Visibility wording at public release.** docs/archiving.md L9 still says “The repository remains private while the research package is being completed.” I did not inspect remote visibility. If this is a public release, remove that now-stale operational statement or state the actual visibility; the neutral replacement “The release tag, commit hash, source manifests, and SHA-256 checksums identify the materials” preserves the point without asserting private status. This is conditional on the actual publication action, not a request for another approval flow.

No other required defect was found in the inspected final status/hash/page/source-coverage claims.

## Checks that pass

Both repository-only and workspace inventory validation pass against the integrated manuscript. The workspace run checks97 declared source-file entries. The public figures agree with generated data:82 families,147 citations with134 application/10 summary/1 provenance/2 source-scope occurrences,163 citation keys referring to62 works,443 contexts,228 internal references,72 source records with71 byte-pinned, and zero open items within the recorded scopes. All82 entries have the explicit scoped-check status. The edit ledger contains53 edits as stated. The authoring README describes the new frozen inputs and distinguishes preserved historical Python specifications from the inputs actually executed.

The source restoration manifest already present during review has the current manuscript hash and correct source-register hash, with92 distinct restoration paths. That does not contradict97 source-file entries: some paths are used by multiple records. The manifest's scope correctly says it covers declared primary files, not the entire generator workspace. The authoring README separately requires original evidence paths to be restored. Do not describe a successful primary-source restoration as a full generator-workspace reconstruction.

The CI workflow contains the new inventory validator step. Root README and docs/building.md describe that check and retain the distinction between structural consistency and mathematical verification. The current build link now targets the matching MANUSCRIPT_BUILD.json; the obsolete AI-attribution receipt is no longer presented as current.

The root README, audit README and dependency discussion distinguish scoped acceptance from proof of internal premises and the main theorem. They retain the incomplete Lean status and deny semantic exhaustiveness. The source register retains author-version and published-version distinctions, including the newly pinned Pazuki publication and GTZ v5 plus its separate erratum. The inspected Cornut–Jetchev and Dokchitser notes explicitly disclaim unverified publisher equivalence rather than claiming it.

Root README clearly states that the November4 handoff is historical and does not contain the November5 audit. The existing340MB/57450-location claims therefore still describe that unchanged historical asset. CITATION.bib identifies the November5 paper repairs while retaining the dated handoff citation. Updating the sole existing release's paper assets while leaving that dated archive unchanged is consistent with this wording. Verify the downloaded paper assets after upload against the final hashes; no second release or rebuilt historical archive is necessary for that publication plan.

The exact local checks and missing-link list are in PUBLICATION-FINAL-CHECKS.json. External URLs, GitHub fragment rendering, the actual release upload and remote CI status were not checked in this pass. These are not inferred from local validation.

## Optional improvements

Link the source-restoration manifest directly from the root README's existing source-restoration phrase. The audit README already supplies that link, so it is not broken navigation. A separate downloadable audit supplement or a full regenerated handoff is optional; neither is required while the public text clearly identifies the repository as the location of the new audit. Avoid changing the historical archive merely to make its date match the paper.
