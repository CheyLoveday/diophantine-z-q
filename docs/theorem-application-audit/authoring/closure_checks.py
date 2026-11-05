"""Bounded closure reviews; no whole-proof acceptance is asserted."""

UPDATES = {
    'A009': dict(sources=['scholze2013','scholze-erratum','brinon-conrad','milne-av'],
        citations=['C010',*[f'C{i:03}' for i in range(100,107)]],
        source_locator='Scholze published 2013, Corollary 1.8 pp.5-6, Theorems 9.1 p.74 and 9.3 p.75, with published 2016 corrigendum; Brinon-Conrad 2009 Theorem 5.2.1 and Propositions 6.3.3,6.3.8; Milne AV v2.00, I Theorem 12.1(a)',
        result='Independent review accepts inserted Lemma H.1: algebraic/rigid comparison, the covariant Tate dual without extra twist, coefficient extension, identical Morita summands, coefficientwise Hodge weights and finite filtered descent. The preceding construction of r_l and its actual restriction decomposition remain inputs.',
        reviewer='Astra galois-height agent, independently checked by root against the stated review scope',
        evidence='parallel-a009-independent'),
    'A068': dict(sources=['milne-cft'],
        source_locator='Milne CFT v4.03, V Theorem 1.7 pp.150-151, V.1.9-1.10 pp.152-153, Proposition 3.3 p.157, Theorems 3.5-3.6 and Remark 3.8 p.158, Proposition 5.2 p.178, Theorems 5.3 and 5.5 pp.178-179; closure-batch-009 and independent second review',
        objects_and_maps='Ring-class quotient by K^* and completed order units; arithmetic local/global Artin maps; residue-ratio inclusion delta at a split moving prime; norm pullback of quadratic characters; derivative-prime relative kernels and conjugation action.',
        hypotheses_and_discharge='Use invertible order ideals, K imaginary with units +/-1, conductors outside 2ND_K and containing the actual finite-character supports. Derivative primes are new and inert; moving primes split. Exact finite Galois realization remains the A067 input. Opposite orientations use conjugate Frobenius lifts; other lifts give the same corrected element.',
        conventions='Arithmetic Frobenius x -> x^N(p), positive prime ideal classes. The local-idelic delta is the negative of the ray principal-residue map, yielding the negative weighted Kummer prescription. Coefficient rings are fixed under Galois pullback.',
        translation_justification='Batch 9 explicitly derives the ring/ray quotient, all relative local groups, principal-relation sign, norm identities, finite character descent and Frobenius-lift independence. Independent review checks each map. CM point norm/congruence formulas, Tate images, pairings and determinant identities remain distinct dependencies.',
        result='Checked the actual ring-class maps and reciprocity conventions, including the moving-prime sign, inert-prime splitting, full product relative kernel, finite coefficient descent, genus-character norm, and orientation independence. Independent second review agrees with conductor-support and conjugate-lift qualifications retained.',
        reviewer='Root assistant with separate Astra sieve-bounds review',
        evidence='closure-batch-009'),
    'A067': dict(sources=['milne-cft'],
        source_locator='Milne CFT v4.03, VIII Theorem 7.4 p.259; V.1 and V.1.9 pp.152-153; finite-field application register and compatibility checks in closure-batch-008',
        objects_and_maps='Finite normal closures of: the Hilbert class field; the moving-character radical/cyclotomic/Tate compositum; the fixed witness division torsor; finite quotients for the original basis cochains; and joint finite reductions of weight-two constituent representations. Each prescribed element is the restriction of an actual Galois element, and each non-class-function use selects a place realizing that representative.',
        hypotheses_and_discharge='The moving radical multipliers respect every Kummer relation; Tate adjustment lies in the actual radical-fixing kernel. The witness detector uses one h*tau before precision varies. Finite cochains factor through finite quotients, made normal over Q before applying density. Joint representation reductions and actual elements make trace prescriptions compatible. Each extension is finite Galois and the conjugacy class nonempty; exclusions are finite.',
        conventions='Arithmetic Frobenius x -> x^N(p). A rational prime supplies a conjugacy class; the chosen place fixes its representative and transported coordinates. Cochain equality is established at increasing finite precision before multiplying by localized minimal-model inclusions. No infinite-level density assertion or independent constituent prescriptions.',
        translation_justification='The explicit composita, maps and nonempty classes for every registered use are given in batch 8. Existing Hilbert-class, open-image, Kummer, kernel-detection and coefficient/local-representation inputs are retained as dependencies. In particular this does not close A032, A064, A068, A070 or A080.',
        result='Checked all registered finite Chebotarev uses: Hilbert-class split ideals, compatible moving radical and trace conditions, fixed-witness detector, finite cochain realizations, opposite-sign localization, and simultaneous trace/determinant approximation. The relevant auxiliary fields and Galois elements are specified before density; choice-of-place and precision conventions are explicit.',
        evidence='closure-batch-008'),
    'A076': dict(sources=['stacks-finite-limits','milne-cft'],
        source_locator='Stacks Tags 086J and 08ZY, exact HTML snapshots of 2026-11-05; Milne CFT v4.03, V Theorem 2.2 p.155, VIII Corollary 7.3 p.258; direct common-alphabet and finite-stage arguments in closure-batch-006 and closure-batch-007',
        objects_and_maps='At each odd stage F=K F_o F_e F_s; common labels are the image of Gal(F/K) in retained quadratic coordinates. Projection to the K-split even alphabet is onto by definition; projection to the full odd alphabet is onto by K intersection F_o=Q. One ultrafilter retains these diagrams and finite coefficient tables.',
        hypotheses_and_discharge='Consume the actual quadratic coefficient factorization, fresh ramification of K, fixed nonempty seeds and detector stages with ell_0=-1 mod 2^M. Fresh ramification proves disjointness; the determinant congruence makes finite prime exclusions cofinite. Actual labels give nonempty unit residue classes; CRT adds finite independent incidence conditions before Dirichlet. The final intersection uses finitely many sets in one ultrafilter.',
        conventions='K-splitting is an individual prime condition; coefficient filters and stationary zero tests are total-label conditions. Each projection is separately onto; product surjectivity is not used. Choose b and its finite budget, then an actual stage, then prime representatives. Existing nonabelian detector and trace realizations remain A067.',
        result='Checked the common field and actual image maps, preservation of the odd alphabet by fresh ramification, the restricted even alphabet, bounded projection diagrams, cofinite moving-prime exclusions, reduced CRT classes, zero-total packets and the final finite-intersection order. Together with batch 6 this closes the bounded A076 deductions; coefficient, seed, detector and address theorems remain listed inputs.',
        evidence='closure-batch-007'),
    'A075': dict(sources=['nekovar','milne','crainic2004','stacks-derived'],
        source_locator='Nekovar 2006, 5.1 pp.113-114, 5.2.4, 5.4.3, 6.2.5-6.2.8 and 6.3.4 p.143; Milne ADT I.4.10(c), I.4.15-I.4.16; Crainic arXiv:math/0403266v1, 2.1-2.4 and 3.2; Stacks Tag 03T3, Lemma 64.6.3(2); closure-batch-006',
        result='Checked nilpotent contraction signs, composition and tensor homotopy corrections, minimal-model lifting, the compatible positive tower, and evaluation on the product group. Detecting lists are explicitly chosen before the inner limit, with retained cone contractions for nonflat changes. The integral Kummer budget uses the listed arithmetic duality and corank inputs. A076/A067 still track arithmetic realization premises.',
        evidence='closure-batch-006'),
    'A042': dict(sources=['milne'],
        source_locator='Milne ADT second edition, I Theorem 4.10(c) p.57, Corollaries 4.15-4.16 p.62, Theorem 5.1 and footnote 13 p.67; closure-batch-005',
        result='Checked finite support including all dyadic and archimedean places, finite cohomology, the absence of real places, ordinary H0 in the archimedean numerator and the squared complex absolute value. This gives Euler characteristic -2, h2=h1-4 and exactly the stated two global dimension bounds.',
        evidence='closure-batch-005'),
    'A073': dict(sources=['milne-cft','milne-ant'],
        source_locator='Milne CFT v4.03, II Proposition 1.22 and Corollary 1.23 p.67, VII Appendix A.1-A.5 pp.226-227; Milne ANT v3.08, Theorems 4.3-4.4 p.70 and 5.11 p.90; closure-batch-005',
        result='Constructed every map in the S-unit Kummer exact sequence and checked its kernels and surjectivity. Verified the explicit Hilbert90 orientation, nonempty ramified-prime relation including at 2, and the quotient 2-rank inequality via A/2A. These give h1(W)<=4s.',
        evidence='closure-batch-005'),
    'A074': dict(sources=['milne-cft'],
        source_locator='Milne CFT v4.03, VII Appendix A.1-A.5 pp.226-227 for squareclasses; explicit pro-2 generation and index-two word-rewriting proof in closure-batch-005',
        result='Proved the exact 2d-1 generator bound directly, including the pro-2 basis-lifting argument and the quotient map from the quadratic-field extension. With d=s+1 and A042, this gives the optional global dimension bound 8s+2. No freeness or H2 generator bound is assumed.',
        evidence='closure-batch-005'),
    'A081': dict(sources=['nekovar','kato','milne','silverman'],
        source_locator='Nekovar 2006, Proposition 8.4.8.1(ii), Corollary 8.4.8.2, Proposition 8.4.8.3, pp.214-216, and Lemma 8.11.3 p.256; Kato 2004 (12.2.3) p.220; Milne ADT I Corollary 2.3 p.28; Silverman IV Theorem 6.4(b), Remark 6.5 p.132; closure-batch-004',
        result='Checked the actual derived augmentation map, top-degree vanishing, dyadic finite-sign components after inverting 2, local Tate self-duality, finite local torsion, and Nakayama at (t). These prove nonzero central value for the fixed product of local clearing factors without relying on generic nonvanishing alone.',
        evidence='closure-batch-004'),
    'A006': dict(
        source_locator='Faltings 1983, metric on p.351 and Lemma 5 on p.358, visually checked; 1984 erratum; closure-batch-003',
        hypotheses_and_discharge='Use stable heights and genuine isogenies in the displayed directions. Only h_F(target)<=h_F(source)+(1/2)log deg(phi) is consumed. Product additivity follows from the determinant lattice and original integral metric.',
        conventions='Original stable metric. The target/source direction is retained; an unused two-sided inequality is not part of this closure.',
        result='Visually checked the conormal-term sign and original metric. Derived the one-sided inequality actually used, product additivity, and both applications. The previous inventory unnecessarily asked for a two-sided bound.',
        evidence='closure-batch-003'),
    'A007': dict(
        source_locator='Milne CFT v4.03, III Theorem 3.4 and VIII Theorem 4.2; closure-batch-002 gives the local character and cochain calculations',
        result='Checked the constant-module boundary, the local square-root obstruction at odd primes and at 2, the real-place Brauer compatibility, conjugacy invariance, and ramification cleaning. The earlier construction of the field and sign cocycle remains an input.',
        evidence='closure-batch-002'),
    'A048': dict(
        source_locator='Matiyasevich 1971 English translation, pp.2-3, definition of an enumerable predicate, Basic Theorem and positive-to-integer conversion',
        result='Constructed the single enumerable predicate H(e+1,n+1), preserved ordinary integer parameters, and checked the private witness blocks and both computable reductions. This consumes, rather than proves, the main integer-defining polynomial theorem.',
        evidence='closure-batch-001'),
    'A019': dict(sources=['poonenstoll','silverman'],
        source_locator='Poonen-Stoll corrected author version, Corollaries 4 and 7, Theorem 8(3), p.11; Silverman 2009, X Theorem 4.2(a), p.333 and VIII Theorem 6.7; closure-batch-003',
        result='Checked the finite Kummer sequence and its direct-limit maps. In the actual case Sha[2] has dimension at most one, its 2-primary group is finite cyclic or quasicyclic; alternation excludes the finite nonzero case. This gives Selmer corank one without finite Sha.',
        evidence='closure-batch-003'),
    'A055': dict(sources=['matiyasevich1971'],
        source_locator='Matiyasevich 1971 English translation, p.2, explicit statement and use of Lagrange four squares; closure-batch-001 checks rational and typed-index translations',
        result='Checked positivity and absolute-value encodings over Q, including zero, and checked that the natural-number encoding consumes integer typing before using four squares.',
        evidence='closure-batch-001'),
    'A058': dict(
        source_locator='Milne ANT v3.08, Theorems 4.3 and 5.1; Silverman 2009, X Example 4.8, pp.336-337; corrected coordinate and kernel derivations in closure-batch-002',
        result='Checked the class/unit computations, explicit isogenies, both squareclass kernels, all valuation cases and both image orders. The printed a^2-b in X.4.9 is a typo; the correct a^2-4b is derived directly. Rank one uses finite generation and the already displayed full rational 2-torsion, not the separate computation of the entire torsion group.',
        evidence='closure-batch-002'),
    'A059': dict(
        source_locator='Silverman 2009, VIII Theorem 6.7, p.239; VII Proposition 3.1, p.192; closure-batch-001 and exact generator-arithmetic receipt',
        result='Checked finite generation, good reduction, independent point counts 20 and 24, and the separate 17- and 23-primary torsion cases. Together with A058 this gives rank one.',
        evidence='closure-batch-001'),
    'A060': dict(
        source_locator='Silverman 2009, VIII Theorem 9.1, following definition, Remark 9.2 and Theorem 9.3, pp.247-249; closure-batch-001 and exact generator-arithmetic receipt',
        result='Checked the factor-two canonical-height convention, duplication bounds at every place, coefficient/discriminant box, the exact integer comparison, and all seven surviving abscissas. This consumes A058/A059.',
        evidence='closure-batch-001'),
}


def apply_closures(apps):
    for app in apps:
        update = UPDATES.get(app['id'])
        if update:
            update = dict(update)
            result = update.pop('result')
            evidence = update.pop('evidence')
            reviewer = update.pop('reviewer', 'root assistant; not an independent referee')
            app.update(update)
            app['prior_evidence'] = [*app['prior_evidence'], evidence]
            app['status'] = 'direct_source_application_check_complete_with_listed_dependencies'
            app['open_items'] = ''
            app['fresh_source_check'] = dict(
                date='2026-11-05', reviewer=reviewer,
                scope='Bounded application and listed translations only. Referenced internal premises are not certified by this closure.',
                result=result)
        if app['id'] == 'A009' and not update:
            app.update(
                sources=['faltings1988','scholze2013','scholze-erratum','brinon-conrad','milne-av'],
                citations=['C010',*[f'C{i:03}' for i in range(100,107)]],
                source_locator='Scholze published 2013, Corollary 1.8 pp.5-6, Theorems 9.1 p.74 and 9.3 p.75, with published 2016 corrigendum; Brinon-Conrad 2009 Theorem 5.2.1 and Propositions 6.3.3,6.3.8; Milne AV v2.00, I Theorem 12.1(a)',
                status='citation_repair_applied_separate_acceptance_pending',
                open_items='Separately review the inserted de Rham lemma, including algebraic/rigid comparison, coefficient embeddings, duality and finite filtered descent. The repair has been applied and the manuscript builds.',
            )
            app['fresh_source_check']['result'] = 'Replaced the insufficient Hodge-Tate citation with an explicit de Rham comparison/descent lemma. The published Scholze article and corrigendum are pinned, including algebraic/rigid comparison maps; no independent acceptance is claimed.'
        if app['id'] == 'A045':
            app['source_locator'] = 'Nekovar 2006, 5.1.1-5.1.6 pp.113-114 and 6.3.4 p.143 for imaginary K; 5.7.1.4-5.7.1.7 pp.130-132 for the separate real-field application; closure-batch-006'
            app['prior_evidence'] = [*app['prior_evidence'], 'closure-batch-006']
        if app['id'] == 'A076':
            app['prior_evidence'] = [*app['prior_evidence'], 'closure-batch-006']
            app['additional_lines'] = sorted(set(app['additional_lines']) | {
                1867,1902,2003,2446,2456,2479,9418,9881,10210,10414,10437})
        if app['id'] == 'A067':
            app['additional_lines'] = sorted(set(app['additional_lines']) | {
                3297,3303,3376,3414,3422,4541,4550,7999,8024,8053,9541})
        if app['id'] == 'A068':
            app['prior_evidence'] = [*app['prior_evidence'], 'parallel-a068-independent']
        if app['id'] == 'A056':
            app['prior_evidence'] = [*app['prior_evidence'], 'closure-batch-002']
            app['source_locator'] = 'Silverman 2009, III Exercise 3.7 pp.105-106, with the author correction to the omega sign; see closure-batch-002'
            app['status'] = 'recurrences_checked_erratum_byte_pin_pending'
            app['open_items'] = 'Pin the full official Silverman errata and finish the corrected-source acceptance record. The official indexed correction, parity recurrences and 44 valid / 74 invalid scalar cases have been checked.'
