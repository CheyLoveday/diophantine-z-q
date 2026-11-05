# Final staging merge review

Reviewer: `/root/astra_audit_galois_height_009`. Date: 2026-11-05.

Result: pass for the merge and integration obligations examined. No omitted application field, source identity, or retained upstream dependency remains in the inspected outputs. This is an integration review of the already bounded acceptance decisions, not a new proof of the manuscript.

Exact reviewed outputs:

- `staging/rebind-final.json`: SHA256 `41a3daa1f5a41f3d8d9f557dd381377b601404d268e9f1a7ac8a27d06980e97b`.
- `staging/sources-final-additions.json`: SHA256 `defa3daadf0e0b9589d382312098a6f16db9e109e1cda185477623e39897eff1`.
- `staging/diophantine_zq.tex`: SHA256 `f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3`.

`FINAL-MERGE-REVIEW.json` records the remaining input hashes and verification counts. `final_merge_review.py` reproduces the checks without editing shared files.

## Required corrections

A018 now gives the actual `10000*2^24*X` bound and its metric conversion. It no longer uses 700X as its asserted bound. The published Pazuki file is present with SHA256 `9f957d234f98aee294676cc97e103a61559722ba1749c58d523bb1ca398c5206`; the prior author file remains separately pinned. The replacement version notes identify the 24-page February 4, 2012 author version and the 33-page published file. They claim agreement of the applied constants, metrics and coordinates, not whole-document identity.

A052 uses `voight-quaternion`, matching the actual bibliography key. The corrected online v1.0.7u pin and the distinct printed/PDF page convention are retained. Its object, hypothesis and translation fields include both quaternion existence and rational quadratic-field embedding. They do not claim an optimal embedding into an arbitrarily fixed order. A028 explicitly retains A052 as its upstream rational-embedding premise. The exact prepared Voight citation replacements occur in revised TeX.

The first read found both A052 subobligations still marked `checked_pending_citation_integration`. I reported that stale status to root. The inspected final hash above includes the correction; no pending subobligation status remains. This was a registry consistency issue, not a mathematical defect.

A054 now has the title "Global theta modularity and holomorphy at cusps". Its hypothesis and translation fields require positive definiteness, finite lattice-coset support after cusp transforms, normal convergence and holomorphy. They explicitly state the consumer's M_(3/2) scope and exclude an imported all-cusp vanishing assertion. The old stronger cusp-vanishing obligation is no longer the accepted top-level description.

All eight added context points are present and correctly mapped:

| Application | Baseline lines | Revised lines |
|---|---|---|
| A057 | 1836, 1837 | 1984, 1985 |
| A057 | 2494, 2496 | 2643, 2645 |
| A065 | 572, 573 | 596, 597 |
| A065 | 1622, 1628 | 1761, 1767 |

Each mapping preserves the exact line text and belongs to the corresponding application's revised `additional_lines` list. The historical baseline ranges in the verbatim reviewer payloads remain historical and are not mistaken for revised line numbers.

The exact A080 local-resolution, restriction/corestriction and homotopy replacement text occurs in revised TeX. Thus the patch dependencies retained for A038, A041, A043 and A044 have concrete integrated text. This check does not replace their mathematical acceptance reports or remove the distinct A075 finite-model premises.

## Preservation and source identities

All 82 application records remain present with the expected accepted-with-dependencies status and no open item. All 43 newly appended acceptance payloads are byte-for-data equivalent to the isolated merge input. Their complete scopes and named dependencies survive, including dependency arrays that are not duplicated into top-level convenience fields. All inherited evidence and source lists remain included. Forty-six final proposed registry field values match their intended values; source-list comparisons allow the deliberate additional entries.

The source additions preserve Pan's exact arXiv v2 identity and expressly decline publisher-equivalence claims. Serre's entry is the inspected *Local class field theory* chapter extract, not the uninspected 1979 *Local Fields* book; its replacement flags prevent the old identity and files from being silently retained. Li's four original page scans, printed-page locators and arbitrary-nebentypus Fricke role remain pinned. Conrad and Shimura retain their exact downloaded files and source URLs. Voight and Pazuki retain the version distinctions described above.

I recomputed all 38 file hashes in `sources-final-additions.json` and all 27 hashes in `evidence-final-additions.json`. The revised TeX hash agrees with the rebind result, which has no errors or unclassified new citation. No further repair is requested by this review.
