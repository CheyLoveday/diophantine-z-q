# Integration data review

Reviewed 2026-11-05 without editing shared files. This is a data and statement-fidelity review of collect_reviewed_updates.py, staging/applications-baseline-reviewed.json, prepare_rebind_review.py, staging/REVIEWED_REBIND.json and staging/rebind-reviewed-result.json. It is not a new proof of all 82 applications.

## Result

The 39 closed records in the inspected staging snapshot have identified evidence and resolvable source IDs. The explicit citation replacements and deletions are substantively justified, subject to the application-link and source-metadata corrections below. The rebind is bound to baseline a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e and staged manuscript f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3. Its reported 150 citation mappings and 286 context mappings have no unresolved automatic mapping failures. That mechanical result does not catch missing application-to-source edges.

The separate eight-record acceptance batch in forward-modularity/ACCEPTANCE-UPDATES.json was not yet imported into this inspected 39-closure snapshot. Thus A023-A027 and A049-A051 remaining pending in that snapshot are an expected unfinished integration step, not an unsupported rejection or a new mathematical gap.

## Required data corrections

1. New C021 is a Silverman IV.6.4 citation classified to both A012 and A071. A012.sources currently contains only serrelocal. Add silverman to A012.sources. This records the actual formal-logarithm input used for the dyadic beta bound, independently checked in A012-SECOND-REVIEW.md.

2. A082's rebound citations are C029, BCDT, and C031, Kato. They omit C030, the Kolyvagin Theorem 1 citation that proves the rank-zero part of the reusable forward lemma and is expressly credited in A082.source_locator. Add the shared C030 application edge to A082. Since C030 is already mapped from old C021, this is not an unclassified new citation and cannot be added through the current new_citations-only mechanism without another explicit application-edge update.

3. A082's two inherited context anchors, old 7303 and 7403 mapped to 7613 and 7713, were already not the precise forward-rank-zero uses. Preserve or replace them with actual calls to the forward-rank result, including old 7318 and 7472 and the genus-partner use near old 7959, after locating the exact staged lines. The newly added Kato citation alone does not document all those applications. This issue was identified in the initial forward-modularity report and should not be lost in rebind integration.

4. A009 retains old C106 as new C147, citing Faltings Chapter III Theorem 4.1, but A009.sources excludes faltings1988. The text explicitly explains that Hodge-Tate comparison alone does not prove de Rhamness. Prefer classifying this citation as a source-scope declaration or contextual remark; if it remains an application edge, add faltings1988 with that narrow role. Do not label it as the de Rham comparison input. A complete mechanical comparison found no other citation keys absent from their application source lists besides this case and item 1.

5. The canonical Kolyvagin source record still calls the pinned MPI/90-69 text Euler systems in the Grothendieck Festschrift. collect_reviewed_updates.py does not currently emit a Kolyvagin source correction. The final source record must use On the Mordell-Weil group and the Shafarevich-Tate group of modular elliptic curves, MPI/90-69 (1990), with the inspected hash already present. Merely fixing the manuscript bibliography while leaving contradictory source version notes would be incomplete.

6. The serrelocal source addition correctly pins Serre's Local class field theory chapter in Cassels-Frohlich (1967). It must replace the stale canonical Local Fields (1979) identity and source_pin_missing status. Do not merge these as two purported versions of one inspected book. Root acknowledged that source additions will replace version notes authoritatively and the final bibliography/source identity will be corrected.

## Closure scope and evidence checks

The updater loads the baseline application specifications and earlier fresh/closure checks, then supplies the new reports through explicit per-application calls. It does not close every pending row by default. Its status text explicitly retains listed dependencies and denies whole-manuscript acceptance. The source additions validate file existence and hashes; the evidence additions bind report paths and hashes. I independently checked all 18 added evidence records and all 31 added source-file pins in this snapshot. No stale hash or missing file was found. All source IDs used by closed records resolve against canonical sources plus additions. All prior_evidence IDs resolve against canonical evidence plus additions.

The newly closed geometry records A001,A002,A078,A079 have the corresponding geometry report and exact source additions. A011,A012,A061,A064 use the Galois-height report; the Fricke and conductor second reviews are attached to the appropriate records. A017,A032,A069 use the local source report, with independent A032 review. A071 and A072 use the second local report. A021,A046 preserve their source corrections and coverage review. A020,A066,A070,A080,A082 cite the appropriate forward-modularity and local second reviews. A077 binds the authenticated AFP revision rather than claiming an Isabelle build. A056 attaches the division-polynomial second review and the existing closure-batch computation. Earlier already-closed rows retain their named closure batches instead of being misrepresented as freshly proved by the new reports.

The source/application summaries match the reports' scope. In particular, A080 does not claim that its local repair proves global bounded models or exact-annihilator assertions. A032's local scalar check does not itself construct integral projectors. A056 does not claim a new proof of the entire published lecture theorem. A066 does not claim publisher-byte equality for the BCDT author manuscript or equality of integral Tate lattices. These limitations must remain in the final records.

## Citation replacement and deletion checks

Old C013 -> new C019 is the genuine Serre source substitution, not a cosmetic locator change. Old C018 -> new C025 retains Lin-Yang; new C026 separately records the Lauter-Naehrig-Yang part. Old C021 -> new C030 retains Kolyvagin in the expanded forward lemma, with new C029 for modularity and C031 for the independent Kato rank-zero consequence. The A082 shared edge still needs item 2 above.

Old C022 -> new C036 retains the Green-Tao application. Newly classified C035 and C037-C041 record the added Mertens, Moebius, GTZ and finite-complexity inputs. They are separate source applications rather than aliases for the original combined citation.

Deleting old C031 is justified. The short local-normalization summary remains at rebound context 2569 and explicitly points to the detailed normalized-induction/Whittaker calculation. A032 retains detailed Carayol C137 and adds Casselman C138,C139. Deleting old C098 is justified for the same reason: its geometric/arithmetic-Frobenius convention is now part of that detailed calculation, not an omitted hypothesis. The old detailed Carayol C097 -> new C137 replacement retains the correct source and precise pages.

Deleting old C041 is justified. The application is still visible at rebound A020 context 4017, with the text at 4020 onward invoking Lemma forward-rank at known simple zeros to obtain rank one and finite Sha. The source citation now occurs once in the reusable lemma. Thus deleting the duplicate does not discard this application site. The subsequent isogeny-ratio argument still explicitly assumes the finite-Sha consequence.

The explicit context replacements mostly retain the repaired paragraph rather than trying to map a deleted sentence mechanically. Automatic unchanged-context matching is restricted to exact text unique in both versions; ambiguous cases require hash-bound review entries. No source identity or closure claim should be inferred merely from these textual matches.

## Finalization checks

After applying items 1-6 and importing the remaining acceptance batches, rerun citation-key versus application-source membership, evidence/source hash checks and the rebind. Record the final staged manuscript hash and regenerate application-site hashes. A subsequent text edit changes the reviewed target and requires rebind against that new exact target. Do not claim final integrated acceptance from this intermediate report while its listed data corrections remain outstanding.
