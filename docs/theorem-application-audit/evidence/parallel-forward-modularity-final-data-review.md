# Final staging data review

Reviewed 2026-11-05. Accepted for the bounded data/statement-fidelity scope below. The target is staging/rebind-final.json produced by finalize_staging_data.py, not the superseded rebind-reviewed-result.json. No shared file was changed.

The final rebind names baseline SHA256 a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e and staged manuscript SHA256 f880d559e9a76281573e4d5110852f347bc422af3f2daf0b483fbb7f01c62fb3. I recomputed the staged manuscript hash and it matches. Rebind reports ok=true with no errors. All 82 records have status direct_source_application_check_complete_with_listed_dependencies and empty open_items. This status is limited to the source applications and their recorded translations; it does not certify all internal premises or the main theorem.

## Six integration findings resolved

1. A012.sources contains both serrelocal and silverman. Its final citations C019 and C021 have matching source edges. The formal logarithm input to the dyadic conductor calculation is no longer omitted.

2. A082 has final citations C029, C030 and C031. C030's role record explicitly names both A020 and A082, preserving the shared Kolyvagin theorem application. The modularity and independent Kato rank-zero inputs also remain.

3. A082 has the nine actual use contexts. Baseline lines 2239,2467,3802,4998,7318,7472,7959,9762,9901 map to final lines 2387,2616,4052,5266,7626,7780,8267,10140,10279. These include the companion, mixed isogeny/Sha, even scalar and genus-partner uses. The two changed forward-lemma references use the explicit reviewed mappings. The obsolete context pair is no longer the sole application evidence.

4. Final C147, baseline C106, has role source-scope declaration and no application IDs. A009 excludes it from its theorem-application citations, but retains context line 11003 for the explanatory warning. Its actual Scholze, erratum and de Rham comparison citations remain. The earlier reference in my first integration note to baseline C100 was corrected; C100 is Scholze and was not removed.

5. Kolyvagin's source addition has explicit replacement version notes identifying the inspected MPI/90-69 text, On the Mordell-Weil group and the Shafarevich-Tate group of modular elliptic curves. It expressly disclaims the former Festschrift title. The replacement file pin is the inspected bacdf23d... file. The staged manuscript bibliography at lines 11163-11167 has the corrected title and source URL.

6. Serre's source addition has explicit replacement version notes identifying Local class field theory, Chapter VI of Cassels-Frohlich (1967), with the actual pp.155-159 interfaces and inspected e0367b25... extract. It expressly disclaims Local Fields (1979). The staged bibliography at lines 11081-11083 agrees. The source entries set replace_version_notes and replace_files, preventing accumulation of contradictory current identities.

The last two are fully represented across the final source-addition data and staged bibliography. finalize_staging_data.py does not itself place bibliography or source_status fields in these two source additions. Consequently the canonical-generation step must derive bibliography from the corrected staged TeX and recompute pin status from the replacement files. It must not carry the old canonical Serre source_pin_missing value or old Kolyvagin bibliography forward. This is a final-generation invariant, not an outstanding source/application finding in the reviewed staging data.

## Evidence and edge checks

I independently checked all final citation roles against all application records in both directions. Every citation assigned to an application occurs in that application's citation list; every application citation has the corresponding role edge. Every citation key belongs to that application's source list. There are no mismatches.

All source IDs in the 82 application records resolve against canonical source records plus final source additions. All prior_evidence IDs resolve against canonical evidence plus final additions. Every application has evidence. The 43 new independent-acceptance payloads remain in the final records, together with their verbatim proposals and attached report IDs. The earlier 39 decisions retain their prior closure reports and independent reviews; they are not mislabeled as having been re-proved by the 43 later reviews.

I recomputed all 27 final added evidence hashes and all 38 final added source-file hashes. Every file exists and every hash matches. I also checked the 29 inherited canonical evidence files actually referenced by the final applications; all their hashes match.

The eight forward-modularity acceptance proposals retain their explicit downstream_assumptions inside independent_acceptance_reviews.verbatim_application_proposal. These are not copied into the optional top-level retained_internal_premises field because that import recognizes other proposal key names. The assumptions are nevertheless retained verbatim and in ACCEPTANCE-REPORT.md; no evidence is lost. If a downstream renderer displays only top-level premises, it should include that key as well rather than hide the conditions.

The revised source/application summaries preserve the scope restrictions identified in the earlier review. In particular, the A080 local comparison construction does not prove the separate global bounded-model or exact-annihilator claims; the division-polynomial review does not claim a fresh proof of the whole published theorem; BCDT remains an inspected author-manuscript application; the forward analytic theorem uses both ranks and finite Sha with the correct source identity.

## Disposition

The six requested fixes are present, and no new source-edge, evidence-loss, citation-role or unsupported data-closure defect was found in this final staging snapshot. Preserve its exact hash binding and the source-field replacement semantics during canonical generation. The prior duplicate-citation deletions remain accepted for the reasons in INTEGRATION-REVIEW.md: their actual consumer contexts and replacement source applications are retained.
