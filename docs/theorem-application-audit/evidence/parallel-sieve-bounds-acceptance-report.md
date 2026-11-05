# Acceptance review of seven recorded applications

Reviewed by `/root/astra_audit_sieve_bounds_009` on 2026-11-05, within the user-requested independent parallel review. The baseline manuscript SHA256 is `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. I compared the recorded applications with the actual manuscript and exact primary files. Earlier height reports were read as supporting history, not substituted for these comparisons.

A003, A004, A005, A018, A047, A057 and A065 pass within the stated application scopes and retained dependencies below. No mathematical repair is required. A018 needs a source-register correction: the previously pinned Pazuki file is a 24-page author version dated February 4, 2012, not the cited published PDF. The newly retrieved 33-page published file supports the same applied statements. Register it and preserve the older file's true identity. Add the repeated uses at L1836–1837 to A057 and L1622–1628 to A065. Empty `open_items` was not treated as evidence of acceptance.

`ACCEPTANCE-UPDATES.json` supplies source paths, hashes, locators, per-application decisions and dependencies. `acceptance_exact.py` and its receipt check the finite arithmetic appearing below. The primary PDF extractions in this directory were generated from the pinned files; damaged extracted formulas were checked against page images where necessary. No shared file was edited.

## A003 and A065: full CM order and classical elliptic j

At L557–569, the established input is an abelian surface A/L with End_L^0(A)=End_Qbar^0(A)=M_2(k), where k is imaginary quadratic, and d=[L:Q]<=D. The D at L377 is a positive integer. Clear denominators of e_11 and take its image E over L. The complementary idempotent gives the other factor. Both have dimension one: they are nonzero, complementary up to isogeny, and their dimensions sum to two. The off-diagonal matrix units identify them up to L-isogeny. Thus E^2 is L-isogenous to A, and End_Qbar^0(E)=e_11 M_2(k)e_11=k. This justifies the actual elliptic factor used in the CM inputs. No bound on the degree of this preliminary isogeny is needed.

Fowler's publisher PDF, *Math. Proc. Cambridge Philos. Soc.* 180 (2026), 607–641, states at section 2.1, printed pp612–613, that singular moduli of an imaginary quadratic order have a monic integral irreducible class polynomial, with degree the order class number. It explicitly distinguishes the order discriminant Delta from the field discriminant. Hence j(E) is an algebraic integer and [Q(j(E)):Q]=h(Delta), including nonmaximal orders. Because j(E) belongs to L, h(Delta)<=d<=D. The quaternionic moduli coordinate also called j elsewhere in the manuscript is not used in this deduction.

Proposition 2.7, printed pp615–616, applies to negative discriminants Delta congruent to 0 or 1 modulo 4 and positive integers k with h(Delta)<=k. It gives sqrt(|Delta|)<=2k^2 exp(21000k^2). Substitute k=D. The proof explicitly handles field discriminants -3 and -4 separately; there is no exceptional-field exclusion. Proposition 2.5, which does have such an exclusion, is not the invoked statement. This accepts A003, conditional only on the prior geometric/endomorphism-field construction already identified as its input.

For the other A065 use, L958–960 and the repeated argument L1622–1628 concern E_ell:y^2=x(x-ell)(x+3ell). Expanding gives a2=2ell, a4=-3ell^2, a6=0. Therefore b2=8ell, b4=-6ell^2, b6=0, b8=-9ell^4, c4=208ell^2 and Delta=2304ell^6. For nonzero ell this is nonsingular and j=c4^3/Delta=35152/9. The exact calculation appears in the receipt; 9 does not divide 35152. A rational algebraic integer is an integer, so this nonintegral rational j excludes geometric CM. All quadratic twists have the same geometric j, so the same test applies to them. The repeated L1622–1628 anchor should be added to A065. The use of integral j at L572–573 should also be explicitly linked to A065.

## A004: metric, potential good reduction and the CM bound

The actual published Barquero-Sanchez et al. file is *Research in Number Theory* 3 (2017), article 13. Page1 defines the original Faltings normalization using (i/2) integral omega wedge conjugate omega. Page2 defines stable height and invariance after a semistable extension. Page15, proof of Theorem1.3, explicitly uses integral CM j to obtain potential good reduction and then a finite extension with everywhere good reduction. Combining the finitely many local extensions at bad primes is legitimate; good reduction is preserved under further extension.

Equation6.2 on p14 is the general elliptic discriminant formula, with analytic discriminant (2pi)^12 eta(tau)^24 and a finite minimal-discriminant contribution. The hypothesis about a model with coefficients in Q(j(E)) belongs to the subsequent regrouping by class group in Proposition6.1; it is not required for Equation6.2 or the baseline's direct average over complex embeddings. The proof starts the formula before invoking that coefficient hypothesis. We do not apply the stronger regrouped formula to the original E/L.

After good reduction the finite term is zero. Write eta(tau)=exp(pi i tau/12) product(1-exp(2pi i n tau)). Substituting into -log(y^6 |Delta(tau)|)/12 gives exactly

    -log(2pi) + pi*y/6 - (1/2)log y - 2 sum_n log|1-exp(2pi i n tau)|.

Every conjugate has the same order discriminant. Fowler section2.1, p612, gives tau=(-b+i sqrt(|Delta|))/(2a) in the reduced domain, with integer a>=1. Thus sqrt(3)/2<=y<=sqrt(|Delta|)/2. For rho=exp(-2pi y), the elementary inequality -log(1-t)<=t/(1-t) yields the tail upper bound 2rho/(1-rho)^2. We have rho<1/100: pi>3 and sqrt(3)>5/3 give pi sqrt(3)>5, while the rational degree-six partial sum for exp(5) is 16289/144>100. Also -(1/2)log y<1/10 because it is at most (1/4)log(4/3)<1/12. The two positive errors sum to less than1, checked rationally.

Discarding the negative -log(2pi), averaging, and applying A003 gives h_F(E)<=pi sqrt(|Delta|)/12+1<=D^2 3^(21000D^2)+1. The last inequality uses pi/6<1 and e<3. This verifies L571–588 and the exact B_cm normalization. It retains A065's integral-j conclusion and A003's discriminant bound as inputs.

## A005: isogeny over the original field

Gaudron–Remond's pinned file is the published Duke163 (2014) article, pp2057–2108. Printed p2058 defines kappa(A) using stable height in the original Faltings normalization. Printed p2059 defines their paired-isogeny notation, with degree the maximum of the two directions. Theorem1.4 on p2060 states the degree bound for K-isogenies between abelian varieties defined over k that are K-isogenous. It has no principal-polarization or maximal-endomorphism-order hypothesis.

Take source A_source=E^2, target A_target=the manuscript's A, base k=L, extension K=L, and g=2. The preceding matrix-unit argument supplies L-isogeny. Their exponent 2^10 g^3 is 8192 and 64g^2 is256, giving exactly L594. Taking just the direction E^2 to A is allowed. The good-reduction extension used to evaluate stable height is not the base field in this theorem.

Stable height additivity gives h_F(E^2)=2h_F(E)<=2B_cm. Also log d<=D<=2B_cm and 1<=2B_cm. Applying the separately reviewed A006 height-change inequality with coefficient1/2 yields the factor4096 at L600. Finally log28<4, logd<=D and

    log(2B_cm)<=log4+2logD+21000D^2 log3
               <=2+2D+42000D^2

give 1028+5D+84000D^2 inside the parenthesis. The finite coefficient checks are in the receipt. This accepts the A005 application, retaining A006's additivity/height variation and the earlier geometric field construction. It does not promote other applications of GR elsewhere in the paper through this decision.

## A018: theta coordinates, published version and normalization

The original registered file begins with a February4,2012 author-version title page and has24 pages. I independently fetched the actual [published article](https://www.numdam.org/item/10.24033/bsmf.2623.pdf), *Bull. Soc. Math. France* 140 (2012),19–49, with33 PDF pages. Corollary1.3(2), pp21–22, the Deligne metric on p26, and the coordinate constructions pp27–31 agree in the applied content. The source register should include both identities rather than silently relabel the author file.

The source requires a principal polarization represented by a symmetric ample line bundle and an even r>=2. Here g=2,r=2; the earlier geometric construction supplies the principal polarization. The required finite extension to define the line bundle, rigidification and fourth-torsion data is permitted and does not alter absolute heights. The source's pp28–29 show that the allowed choices permute coordinates and multiply them by roots of unity. Pages30–31 identify the coordinates with the half-characteristic theta nulls for r=2. The six odd values vanish, and at least one theta coordinate is nonzero. Thus the baseline's sixteen-coordinate projective point has the same height as its ten even coordinates, in the same theta convention retained as A017's input.

The metric on p26 divides the squared differential norm by pi^g relative to the original metric. The norm itself is multiplied by pi^(-g/2), so the degree-normalized height increases by (g/2)logpi. With g=2 this is +logpi, exactly as at L886. The source uses Euclidean norms at infinity, which dominate the manuscript's supremum norm; finite-place norms agree. No reverse comparison or hidden additive log16 is needed for this direction.

Corollary1.3(2) is for the truncated heights max(1,h_theta) and max(1,h_F^D), and the logarithm contains their minimum plus2. Replacing that minimum by X_D gives an upper bound, while the untruncated h_theta is no larger than its truncation. Its constant at g=r=2 is 1000*16*(log16)^5. With log16<4 this is less than1000*2^24. Since X_D<=3X and log(X_D+2)<=2X_D for X_D>=1, the claimed 10000*2^24 X bound follows. The final coefficient 40*10000*2^24+96 is 6710886400096<10^13, checked exactly.

The application is accepted with its existing principal-polarization and A017 theta-coordinate identification inputs. The inventory's translation text mentioning “700X” is stale: the baseline uses 10000*2^24 X. Replace that summary with the actual bound. This is a registry repair, not a mathematical manuscript repair.

## A047: precise conjecture and conditional consequence

Mazur's pinned Numdam file is the published *Asterisque*228 (1995),165–181. Printed p165, PDF p2, defines a variety as a reduced finite-type scheme and states Conjecture3 for the closure of its rational points in its real locus. There is no irreducibility, smoothness or properness condition on Conjecture3. Those restrictions must not be imported from Conjecture1.

At L6179–6192, V is the reduced zero scheme of one polynomial in finitely many variables, so it meets that definition. Reduction does not change its rational or real point sets. Conditional on the exact projection equality from the main theorem, every rational point projects to Z and every integer has a rational witness. The inverse image of the closed set Z under the continuous projection is closed, so it also contains C, the closure of V(Q). Thus pi(C)=Z. Each connected component projects to a connected subset of Z and hence to one point. Representatives over distinct integers cannot lie in the same component. This establishes infinitely many components without needing projection to commute with closure or be a closed map.

Accept this as a correct conditional consequence. The required main theorem is a retained dependency, not proved or independently certified by A047. The nearby universal-polynomial context at L6200–6204 is not another Mazur application.

## A057: each prime-choice use

Milne, *Class Field Theory* v4.03, August6,2020, V Theorem2.2, printed p155, PDF p164, gives positive Dirichlet density1/phi(m) for primes in every residue class coprime to fixed m. Thus it gives infinitely many positive primes; finite avoidance and successive distinct choices are valid. It supplies no uniform quantitative bound or general nonabelian Frobenius prescription.

I checked every recorded prime-choice context, and the extra repeated source use at L1836–1837:

- L224–226 defines the first22 primes above324 in each unit class modulo W. W=4 product_{p<=324}p has 2-adic valuation3, so this is modulus8 at two, not modulus4. Infinitude proves termination. L1212–1224 only requests ratios of nonzero units modulo8 and each odd prime<=324. CRT gives a unit class modulo exactly W. At most22 demands per class can be met from its22 stored primes.
- L979–1002 requests auxiliary types (s,lambda)=(0,0) or(1,1). They are realized by residues1 or7 modulo12, respectively. Each extra forward Legendre symbol at an odd old prime is a choice of a nonzero square/nonsquare residue; different old primes are coprime to12. Reverse symbols are fixed by quadratic reciprocity, as in the preceding matrix prescription. Choose primes successively and omit the finite previous set. The matrix argument selecting the bits is retained as the input to this prime-realization step.
- L1836–1837 and L9635–9639 choose a signed prime in a nonempty signed unit-squareclass filter. Fix its real sign sigma. At every odd support prime select a unit representative of the desired squareclass after multiplication by sigma; at two select the required odd residue modulo8. CRT gives a unit class for its positive absolute value. Dirichlet supplies infinitely many primes outside S union B. Neither step asserts that the resulting signed prime is a fundamental discriminant.
- L2003–2025 uses the actual individually realizable type group defined at L1867–1917. Its relations are retained; it is not an arbitrary list of character values. Fix a representing unit residue modulo the fixed label modulus, including8. At old vertex primes outside that support, each desired forward bit has a nonzero representative. Combine by CRT and choose a new prime outside the finite exclusion set. Reciprocity supplies the reverse bit. Repeating yields the finite graph. Products are replaced only when their resulting type is permitted. There is no assumption of surjectivity onto a product of two label groups.
- L2507–2523 and L10437–10450 use that finite realization after the combinatorial bits and finite stage have been selected. The budget is finite at each invocation. No one modulus or bound must work for all binary dimensions. The combinatorial and stage-selection assertions remain separate dependencies.
- L9577–9591 uses finite realization for the bridge copy. For disjoint originals, a bridge vertex can impose nonzero residue classes at all distinct original primes. The corresponding copies carry the same type and graph bits, so the incidences requested when switching one vertex at a time agree with the required forward/reverse relation. A vertex's own copy is never compared to it in an evaluated graph; that unused incidence is free. Overlapping originals are first replaced by a fresh disjoint copy, as expressly stated. No inconsistent two prescriptions at one modulus are forced.
- L10104–10110 requests p=1 mod4, (ell/p)=-1 and(k/p)=1. The selected K=Q(sqrt(k)) has a prime ramified outside the old support by L2446–2465; this includes the ramification of Q(i,sqrt(ell)). Therefore K is not a quadratic subfield of that biquadratic field, and the three quadratic characters are independent. Equivalently, at a fresh odd ramified prime of k the unit residue can change the k-character without affecting the other two. Choose p=1 mod8, prescribe the ell-character on its odd support, then adjust at that fresh prime and use CRT. This gives an actual nonempty unit residue class, to which Dirichlet applies. The analogous abbreviated choice at L2494–2496 should be cross-linked to this same justification.

These checks accept the Dirichlet application in each stated context. Retain the existence of the actual types, the finite compatible graph prescriptions, and the fresh-ramification construction as internal inputs. The theorem does not itself prove those inputs or any nonvanishing result used after the selected prime. Add L1836–1837 and the L2494–2496 cross-reference to the anchor record; the former explicit invocation was absent.

## Disposition and reproducibility

The seven accepted entries should be marked as checked with stated dependencies, supported by this report, the source-file records and the arithmetic receipt. For A018 the source register and stale “700X” text must be corrected; no assertion that the old file was the published article should survive. The manuscript citation already names the correct published article, so its substantive text requires no repair.

This review establishes the correctness of these source applications given their identified internal inputs. It does not re-prove the published theorems, certify the full geometric construction, or establish the main theorem through its corollary. The old no-open-item status played no role in the decisions.
