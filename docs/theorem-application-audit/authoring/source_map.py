BASE = 'work/astra-final-height-producers-001/primary/'
SOURCE_PATHS = {
 'babagranath':[BASE+'baba-granath-2005.pdf'], 'buzzard':[BASE+'buzzard-1996.pdf'],
 'linyang':[BASE+'lin-yang.pdf'], 'lny':[BASE+'lny-2015.pdf'], 'pazuki':[BASE+'pazuki-2012.pdf'],
 'gr2014':['work/gaudron-remond-polarisations.pdf'],
 'greentao':[BASE+'green-tao-linear.pdf'], 'moebius':[BASE+'green-tao-mobius.pdf'],
 'gtz':[BASE+'gtz-inverse-v5.pdf',BASE+'gtz-erratum.pdf'],
 'silverbergzarhin':['work/independent-height-review-20261104/conductor/primary/silverberg-zarhin.pdf'],
 'serrelocal':[],
 'poonenstoll':['work/astra-final-pole-completeness-review-001/poonen-stoll.pdf'],
 'bmor':['work/astra-final-ordinary-definition-001/primary/bmor-2018-v3.pdf'],
 'milne':['work/astra-arithmetic-final-composition-001/milne-ADT-2006.pdf'],
 'nekovar':['work/nekovar-selmer-complexes-2006.pdf'],
 'afp':['work/Alpha_Sequence.thy','work/Exponential_Relation.thy','work/Exponentiation.thy'],
 'silverman':['work/astra-final-size-independent-review-001/silverman-2009.pdf'],
 'dd':['work/astra-weighted-theta-audit-001/primary/dokchitser-parity-2009.pdf'],
 'gz':['work/gross-zagier-1986.pdf'],
 'kolyvagin':['work/astra-weighted-theta-audit-001/primary/kolyvagin-1990.pdf'],
 'kato':['work/kato-2004.pdf'], 'bfh':['work/bfh-1990.pdf'], 'hl':['work/hoffstein-luo-1997.pdf'],
 'desjardins':['work/astra-weighted-theta-audit-001/primary/desjardins-2020.pdf'],
 'cst':['work/cai-shu-tian-2014.pdf'],
 'ccl':['work/astra-final-finite-arithmetic-audit-001/primary/cai-chen-liu-2018.pdf'],
 'jetchevkane':['work/jetchev-kane-2009.pdf'],
 'cornutjetchev':['work/cornut-jetchev-2010.pdf','work/astra-final-external-applicability-001/cornut-jetchev-author-current.pdf'],
 'waldspurger':['work/waldspurger-1981.pdf'], 'ramsey':['work/ramsey-2006.pdf'],
 'carayol':['work/astra-t3-opus-reconciliation-001/primary/carayol-1986.pdf'],
 'waldspurgerICM':['work/waldspurger-1983.pdf'],
 'weil':['work/astra-weighted-theta-audit-001/primary/weil-1964.pdf'],
 'serre':['work/serre-1972-open-image.pdf'],
 'mazur1995':['work/astra-mazur-corollary-001/primary/mazur-1995.pdf'],
 'matiyasevich1971':['work/astra-mazur-corollary-001/primary/matiyasevich-1971.pdf'],
 'openaihtp':[],
 'howard2012':['work/astra-final-finite-arithmetic-audit-001/primary/howard-2012v1.pdf'],
 'lang1956':['work/astra-final-finite-arithmetic-audit-001/primary/lang-1956.pdf'],
 'milne-cft':['work/astra-final-moving-character-audit-001/primary/milne-cft.pdf'],
 'casselman':['work/astra-t3-opus-reconciliation-001/primary/casselman-1973.pdf'],
 'edixhoven':['work/fable-review-packet-20261104/primary/edixhoven-1992.pdf'],
 'bcdt':['work/astra-final-pole-completeness-review-001/bcdt-2001.pdf'],
 'kato1999':['work/astra-kato-primary-001/kato-1999.pdf'],
}
NOTES = {
 'serrelocal':'The cited 1979 book has not been byte-pinned. The cached serre-local-cft file must not be silently substituted for Local Fields.',
 'openaihtp':'Provenance citation. No theorem from this preprint is granted as an external assumption by the present manuscript; reconstructed arguments need their own audit.',
 'afp':'Three local Isabelle source files are exact-byte pins. Original AFP revision/release identity still requires authentication; a current browse URL is insufficient.',
 'berger2002':'The author article has Theorem 0.7/Corollary 5.22; arXiv v3 has Theorems 0.6/5.19. Both files are separately pinned. Do not transfer numbering.',
 'pan2022':'Consulted arXiv:1901.07166v2. Bibliography names JAMS 2022. Publisher/preprint statement equivalence is not established by this inventory.',
 'fowler':'Publisher PDF retrieved 2026-11-05. Proposition 2.7; source PDF pagination may differ from final volume pagination.',
 'faltings1983':'Inventiones 73 (1983), pp.349–366. Read together with the separately pinned 1984 erratum: Satz 2 has eventual stationarity, not equality of all tower heights. The erratum states this suffices for subsequent results.',
 'faltings1984':'Inventiones 75 (1984), p.381. Publisher one-page erratum, visually read on 2026-11-05. Corrects Satz 2 of the 1983 article.',
 'faltings1988':'Journal of the American Mathematical Society 1 (1988), pp.255–299; cached PDF has 46 scanned pages including cover. III Theorem 4.1, printed p.298, is Hodge–Tate comparison. It does not supply the de Rham conclusion attributed to it at manuscript lines 711–714.',
 'poonenstoll':'Author version dated November 6, 1998 with minor correction August 23, 2014; states publication in Annals of Mathematics 150 (1999), pp.1109–1149. Locator page numbers in this audit refer to the corrected author version, not journal pagination.',
 'bcdt':'Author manuscript of On the modularity of elliptic curves over Q: wild 3-adic exercises. Its date line contains placeholders (? 2000; ? January 2001). Exact bytes are pinned, but equivalence to the final 2001 JAMS article has not been independently checked.',
 'scholze2013':'Author PDF of p-adic Hodge theory for rigid-analytic varieties; Forum of Mathematics Pi 1 (2013), e1. Proposed replacement input, not yet a manuscript bibliography entry. Read Corollary 1.8 with the separately pinned corrigendum.',
 'scholze-erratum':'Author erratum to p-adic Hodge theory for rigid-analytic varieties, 3 pages. Corrects the pro-étale covers and period-sheaf details; states the main results remain intact with those changes. Required companion to scholze2013.',
 'brinon-conrad':'CMI Summer School Notes on p-adic Hodge Theory, preliminary version dated June 24, 2009. Supplementary exposition, not a published research article; do not classify all sources in this audit as published literature.',
 'milne-av':'Abelian Varieties v2.00. Title page says March 16, 2008; version history says March 17, 2008. Exact bytes disambiguate the file. Proposition numbers include the part/chapter.',
 'milne-ant':'Algebraic Number Theory v3.08, July 19, 2020, author course notes. Supplementary source, not a manuscript bibliography entry.',
 'cornutjetchev':'Two author versions are pinned. Prior comparison found the used statements equivalent; publisher PDF equivalence remains unverified. Bibliography explicitly cites 2010 preprint.',
 'dd':'Consulted arXiv:0906.1815v1; bibliography also names 2011 journal. Exact publisher equivalence is unverified. Use Theorem 1.8, not the finite-Sha statement 1.2.',
 'gtz':'The actual input is corrected arXiv:1009.3998v5 (23 April 2026), together with the separate author erratum. Do not describe the input as only the 2012 printed article.',
 'hl':'The cached PDF contains the main article pp.435–442. It does not contain Rohrlich’s separate appendix pp.443–444; no application here is assigned to that appendix.',
 'howard2012':'arXiv:1202.6340v1 is a 2012 posting of a paper published in 2004. Only Section 1.7 formula (13) is a comparison; the broader-conductor argument is local to the manuscript.',
 'cst':'Prior audit records cached PDF equality with publisher PDF, SHA256 3eef3f34a03d21575bdb352acfaa0bef2fbe3701068a65798cb89a6ae84333e7.',
 'milne-cft':'Class Field Theory v4.03, August 6, 2020, author course notes. Supplementary source not separately in the manuscript bibliography. Theorem locators specify the chapter as numbering repeats.',
}
EVIDENCE = {
 'height':'work/independent-height-review-20261104/height/AUDIT.md',
 'descent':'work/independent-height-review-20261104/descent/AUDIT.md',
 'descent-addendum':'work/independent-height-review-20261104/descent/ADDENDUM.md',
 'conductor':'work/independent-height-review-20261104/conductor/AUDIT.md',
 'height-whole':'work/independent-height-review-20261104/whole/REPORT.md',
 'height-whole-addendum':'work/independent-height-review-20261104/whole/ADDENDUM.md',
 'applications':'work/astra-final-external-applicability-001/APPLICABILITY.md',
 'applications-correction':'work/astra-final-external-applicability-001/RC_REPORT_CORRECTION_001.md',
 'kato-carayol':'work/astra-kato-primary-closure-002/REPORT.md',
 'cj':'work/astra-bfh-cst-cj-closure-002/REPORT.txt',
 'finite':'work/astra-final-finite-class-production-independent-001/REPORT.md',
 'finite-crosscheck':'work/astra-finite-production-crosscheck-001/REPORT.md',
 'local-control':'work/astra-local-control-independent-003/REPORT.md',
 'kummer':'work/astra-kummer-reconciliation-001/REPORT.md',
 'arithmetic':'work/astra-arithmetic-final-composition-001/REPORT.txt',
 'theta':'work/astra-weighted-theta-audit-001/REPORT.md',
 'theta-upstream':'work/astra-weighted-theta-audit-001/UPSTREAM_CLOSURE.md',
 'carayol-operators':'work/astra-t3-opus-reconciliation-001/REPORT.md',
 'geometry':'work/astra-t2-opus-reconciliation-001/REPORT.md',
 'pole':'work/astra-final-pole-completeness-independent-review-001/REPORT.md',
 'primary-review':'work/root-primary-applications-final-review-001/REVIEW.txt',
}

# Closure batch source records, 2026-11-05.
SOURCE_PATHS['scholze2013'] = ['work/theorem-application-audit-20261105/closure/primary/scholze-published.pdf']
SOURCE_PATHS['scholze-erratum'] = ['work/theorem-application-audit-20261105/closure/primary/scholze-erratum-published.pdf']
NOTES['scholze2013'] = 'Published Forum of Mathematics Pi 1 (2013), e1, 77 pages. Corollary 1.8 is on pp.5-6; Theorems 9.1 and 9.3 are on pp.74-75. The author version is also retained separately. The applied repair uses the published article with its published corrigendum.'
NOTES['scholze-erratum'] = 'Published Forum of Mathematics Pi 4 (2016), e6, four pages, DOI 10.1017/fmp.2016.4. Read with the 2013 article; the author version is retained separately.'
NOTES['faltings1988'] += ' The working manuscript now identifies this limitation and uses a separate de Rham comparison/descent lemma.'
NOTES['silverman'] = 'Second edition (2009), exact PDF pinned. Direct inspection found the omega sign typo on p.105 and a^2-b instead of a^2-4b in X Proposition 4.9, p.337. The division-polynomial correction is visible in the official indexed errata but full errata retrieval remains open. The isogeny kernel calculation is derived independently in closure-batch-002.'
EVIDENCE['closure-batch-001'] = 'work/theorem-application-audit-20261105/closure/BATCH-001.md'
EVIDENCE['closure-batch-002'] = 'work/theorem-application-audit-20261105/closure/BATCH-002.md'
EVIDENCE['closure-batch-003'] = 'work/theorem-application-audit-20261105/closure/BATCH-003.md'
EVIDENCE['closure-batch-004'] = 'work/theorem-application-audit-20261105/closure/BATCH-004.md'
EVIDENCE['closure-batch-005'] = 'work/theorem-application-audit-20261105/closure/BATCH-005.md'
EVIDENCE['closure-batch-006'] = 'work/theorem-application-audit-20261105/closure/BATCH-006.md'
EVIDENCE['closure-batch-007'] = 'work/theorem-application-audit-20261105/closure/BATCH-007.md'
EVIDENCE['closure-batch-008'] = 'work/theorem-application-audit-20261105/closure/BATCH-008.md'
SOURCE_PATHS['crainic2004'] = ['work/theorem-application-audit-20261105/closure/primary/crainic-perturbation-v1.pdf']
SOURCE_PATHS['stacks-derived'] = ['work/theorem-application-audit-20261105/closure/primary/stacks-03T3.html']
SOURCE_PATHS['stacks-finite-limits'] = ['work/theorem-application-audit-20261105/closure/primary/stacks-086J.html', 'work/theorem-application-audit-20261105/closure/primary/stacks-08ZY.html']
NOTES['crainic2004'] = 'arXiv:math/0403266v1, 16 March 2004. Supplementary comparison for the standard perturbation formulas; not asserted to be a published research article. The specialized nilpotent algebra is checked directly in closure-batch-006, including reversal of the source homotopy sign. No general quasi-isomorphism argument from this preprint is imported without that calculation.'
NOTES['stacks-derived'] = 'Exact HTML snapshot of Tag 03T3 retrieved 2026-11-05. Lemma 64.6.3(2) concerns bounded-above projective complexes. The audit also supplies the bounded finite free splitting argument; a live tag URL is not treated as an immutable edition.'
NOTES['stacks-finite-limits'] = 'Exact HTML snapshots of Tags 086J and 08ZY retrieved 2026-11-05. These concern finite inverse limits and profinite topology, not existence of the arithmetic stages. The ultrafilter-extension proof is supplied directly in closure-batch-006.'

EVIDENCE['closure-batch-009'] = 'work/theorem-application-audit-20261105/closure/BATCH-009.md'
EVIDENCE['parallel-a009-independent'] = 'work/theorem-application-audit-20261105/closure/A009-INDEPENDENT.md'
EVIDENCE['parallel-a068-independent'] = 'work/theorem-application-audit-20261105/parallel-009/sieve-bounds/A068-SECOND-REVIEW.md'
