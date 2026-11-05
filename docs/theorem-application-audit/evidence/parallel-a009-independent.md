<!-- Frozen excerpt of Astra galois-height report, 2026-11-05. -->
# Independent review of the Galois and height interfaces

Review date: 2026-11-05. Manuscript SHA256: a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e. Scope: A009, A011, A012, A061, A064. This report does not certify the rest of the height argument.

## A009: accept the inserted Lemma H.1

Consumer: lines 711-714; lemma and proof at 10560-10622. The lemma supplies de Rhamness and weights for r_l over Q_l, after restriction to F=L'_v identifies its double with V_l(A) tensor E. Berger and Pan consume these conclusions separately.

I independently read the pinned published Scholze article, Corollary 1.8 on pp.5-6 and Theorems 9.1 and 9.3 on pp.74-75, together with the published 2016 corrigendum. Corollary 1.8 explicitly asserts de Rhamness and identifies the associated filtered vector space with de Rham cohomology. It is stronger than its preceding Hodge-Tate assertion. The corrigendum p.2 says the results remain intact after the change to the definition of pro-etale covers; its period-sheaf corrections must also be retained. No withdrawn comparison theorem is used.

The abelian surface is smooth and proper over the finite extension F/Q_l, so its rigid analytification satisfies this corollary. Theorem 9.1 compares coherent cohomology under a proper morphism and applies to the differential sheaves. The comparison is natural for the de Rham differential, and therefore for its finite stupid-filtered complex and its hypercohomology, not merely for the separate cohomology groups. Theorem 9.3 applies to the locally constant finite sheaves Z/l^n because l^n is invertible in the characteristic-zero field F. Taking the inverse system and tensoring Q_l compares the algebraic and analytic etale representations. Naturality supplies the G_F action. The finite groups satisfy Mittag-Leffler, so no inverse-limit obstruction appears in degree one.

Milne AV v2.00, Part I Theorem 12.1(a), printed p.55, gives the canonical H^1_et = Hom(T_l A,Z_l) identification. Rationalizing and dualizing gives the covariant Tate module, without a Tate twist. Brinon-Conrad, June 24 2009, Theorem 5.2.1, pp.68-69, and Proposition 6.3.3, pp.76-77, give closure under duals and subquotients and the strict filtered duality. Thus cohomological weights 0,1 become Tate weights 0,-1 in the manuscript's stated convention. Coefficient extension with trivial Galois action is a finite direct sum on underlying Q_l-representations and preserves de Rhamness. The displayed double-copy decomposition makes the underlying Q_l-representation of r|G_F a direct summand.

For finite descent, choose finite Galois F'/K containing F. Each Fil^i D_dR,F'(W) is a finite-dimensional F'-space stable under the semilinear Gal(F'/K) action, with invariant space Fil^i D_dR,K(W). Vector-space Galois descent applied separately to each step gives F' tensor_K Fil^i D_K = Fil^i D_F'. The dimension equality proves admissibility over K. This is precisely the finite-extension proof of Brinon-Conrad Proposition 6.3.8, pp.80-81. It does not descend semistability, which would be false in general.

For the coefficientwise claim, enlarge the local field once more so that it contains the normal closure of E=C_l. Split F' tensor_Q_l E into factors indexed by embeddings of E. The geometric H^1 has graded dimensions 2,2 in each such factor. Its dual has degrees 0,-1. The two copies of r in the hypothesis are E-linearly isomorphic, hence their filtered de Rham realizations and all the embedding factors are isomorphic. Each factor therefore has graded dimensions 1,1, with no other degrees. Filtered finite descent preserves these dimensions. This is a multiplicity argument, not a claim that dimension two alone forces the weights. There is no additional quaternionic hypothesis hidden in the lemma: the required Morita conclusion is explicitly its double-copy hypothesis. In the consumer it follows from matrix units commuting with Galois and the stipulated actual Tate action over L'.

Recommendation: close A009 for the repaired statement, conditional only on the separately audited construction of r_l and its displayed restriction isomorphism. No manuscript repair is required for H.1. This acceptance does not close A008, A010, A011, or the geometric construction.

## Source pins read for A009

All paths below are relative to the workspace. These were existing files, not new downloads.

- work/theorem-application-audit-20261105/closure/primary/scholze-published.pdf, SHA256 f47a05bbcdd1ac69deb87ce4b6af5bbbc245cbbf0e99df74e8bf73b6d89227d7. Forum of Mathematics Pi 1 (2013), e1, pp.1-77. DOI https://doi.org/10.1017/fmp.2013.1.
- work/theorem-application-audit-20261105/closure/primary/scholze-erratum-published.pdf, SHA256 3caea8d89df1e7d047d4edc89a679cd1deb2a19ec350effb450305a9c8eef3d1. Forum of Mathematics Pi 4 (2016), e6. DOI https://doi.org/10.1017/fmp.2016.4.
- work/theorem-application-audit-20261105/primary/brinon-conrad.pdf, SHA256 f27d508bc64b3c9e2e9de5041429b2cb6a909b2cd72ff8096c20493f27b5a187. Preliminary notes dated June 24 2009, https://math.stanford.edu/~conrad/papers/notes.pdf.
- work/theorem-application-audit-20261105/primary/milne-av.pdf, SHA256 f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef. Version 2.00, title page March 16 2008, https://www.jmilne.org/math/CourseNotes/AV.pdf.

