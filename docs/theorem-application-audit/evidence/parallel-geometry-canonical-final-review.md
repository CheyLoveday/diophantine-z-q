# Canonical final spot review

Read-only review of the integrated repository, 2026-11-05. The manuscript still has SHA256 `f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3`. No generator, rebuild or shared-file edit was run.

## Structural result

I independently parsed every explicit citation before the bibliography and compared its position, keys and locator with `citations.json`: all 147 match. I compared all frozen citation memberships and role fields with the final citations: all match. The role counts are 134 application citations, 10 summaries, one provenance citation and two source-scope declarations. All 443 manuscript excerpt hashes were recomputed from the current TeX and match.

The generator reads `FROZEN_APPLICATIONS.json` and `CITATION_ROLES.json` directly. It does not import or execute the superseded application specifications or closure scripts. It checks the final TeX hash, exact coverage of citation roles, and application membership before generating anchors. For the eight requested application records, every frozen field agrees with the generated record; the expected generated anchors and final manuscript hash are added. Thus the accepted scopes are reproducibly represented rather than depending on an unrecorded patch to output JSON.

## Requested source roles

- A001: the Lin–Yang equation (3)/Lemma 3 locator is retained, together with Baba–Granath's branch description and Buzzard's polarization scope. C003/C004 are the current applications. Full-level degree/descent calculations are not attributed to a single-component source statement.
- A002: C005 invokes the corrected Buzzard model in its initial V1(5) role; the extra marking and free quotient remain separate arguments. Stacks 07S7 is pinned as the finite-quotient bridge.
- A028: all current Cornut–Jetchev sites and the Voight prerequisite are attached. `upstream_dependencies` includes A052. The sign fiber, arbitrary prime-power level, unaveraged sum and single factor 1/2 are preserved. Historical citation IDs occur inside explicitly named baseline proposals, not in current citation membership.
- A052: `voight-quaternion` is the actual canonical source key. Both new classification/embedding citations are attached, with the corrected-edition locator and rational-versus-optimal-embedding distinction retained. The Jetchev–Kane geometric interpretation is not promoted to a weighted theta or later orbit-count theorem.
- A054: the corrected title and translation now state automorphy and holomorphy in M_(3/2); the unused all-cusp vanishing assertion is removed from the operative fields. The old proposal's explanation survives only as historical review content.
- A077: the exact AFP revision and definition/lemma names are retained, and C080 identifies the inserted source paragraph. No Isabelle build, stable release or Lean proof completion is asserted. Two stale sentences still need the metadata cleanup below.
- A078: the three checked Stacks source IDs and the local normalization/smoothness argument are retained. It correctly has context anchors rather than inventing an explicit TeX citation. Its concluding operative sentence still has stale obligation wording, noted below.
- A079: C006 is the current analytic-to-algebraic application. The locator distinguishes Milne I.2.8–2.9 from I.12.1(a), which serves another consumer. It retains the rational centralizer and the split/non-CM alternatives.

The README's distinction between 82 scoped acceptance decisions, 60 separately named fresh-check fields and incomplete Lean work is accurate. Its role counts and anchor count agree with the independent check. It does not claim that empty open items prove all internal premises or that every cited version is published.

## Stale prose to clean before final publication

These are metadata/documentation findings, not new mathematical gaps. Correct the frozen inputs or generator strings and regenerate the affected output, rather than editing only `applications.json` or `INVENTORY.md`.

1. **AFP source version note contradicts its appended authentication.** The final `sources.json` entry starts: “Original AFP revision/release identity still requires authentication,” then correctly states the byte match to revision b4f3b892d0ae25cea27412ba4007cdb63e44b0eb. Replace the old version note, rather than appending to it. Suggested full note:

   “The three original Isabelle files match the AFP development mirror revision b4f3b892d0ae25cea27412ba4007cdb63e44b0eb dated 2026-05-10T07:38:12Z byte for byte. The additional modulo definition is pinned at the same revision. No Isabelle build or stable release identity is inferred.”

2. **A077 still describes completed correspondence as missing.** Its `translation_justification` ends “Need exact definition/theorem correspondence to claim certified reuse.” Suggested replacement:

   “The checked definition/lemma correspondence is recorded in the linked A077 report. The manuscript supplies the specialized algebraic translation; the AFP pin authenticates source reuse, not a new Isabelle build or certification of the surrounding compiler.”

3. **A078 still asks for source identifiers now present.** Its `translation_justification` ends “Exact normality/smoothness/descent theorems behind global cover and abelian scheme need source identifiers.” Suggested replacement:

   “The linked geometry report supplies the local invariant-parameter and normalized-pullback argument, with Stacks 0E97, 07S7 and 0EYG providing the stated stable-model, quotient and tame local bridges. The argument retains the good-model and distinct-branch premises.”

4. **The generated inventory introduction is still written as a pre-review worklist.** The generator string says the hypotheses and translations “need verification” and that prior evidence is historical rather than fresh approval. Some prior evidence now consists of the current bounded independent reviews. Suggested replacement:

   “This document records the checked source applications, their exact consumers, and the hypotheses, translations and dependencies retained by each decision. Linked evidence includes historical reports and current bounded reviews; their own stated scope and source version govern. An accepted application is not a certificate of every internal premise or the main theorem.”

5. **Three operative field descriptions still contain unlabeled original-baseline line numbers.** A001 says “397–424,” A002 “426–465,” and A077 “5587–5702.” The inventory introduction says line numbers refer only to the final frozen source, making these ambiguous or wrong. Prefer removing those prose line numbers and referring to the current registered anchors. Preserve original line numbers inside the explicitly named historical/baseline review objects. The current generated anchor ranges are correct.

6. **Cosmetic duplication:** `milne-av.version_notes` repeats the entire version/date paragraph twice. Keep one copy. This does not affect the two intentionally retained file entries or the source-role distinction.

## Disposition

The final source roles, acceptance scopes and mechanically generated anchors pass this spot review. Clean the six stale prose items above. No manuscript mathematical change or additional source audit is requested. Recheck generated counts and hashes after that metadata-only regeneration; no PDF rebuild is needed because the TeX remains unchanged.
