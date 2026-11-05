# Theta and local-convention audit

Reviewed 2026-11-05 against diophantine_zq.tex SHA256 a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e. Only A017, A032, A069 are covered. No manuscript, canonical audit, or git state was changed. The report uses primary source text and page images, not earlier acceptance labels. No AGENTS.md was found in the workspace or repository locations checked. The unslop skill was read and applied.

## Decisions and scope

- A017 can close as a normalization application, with the explanatory replacement supplied below. Its dependency on the identification of the actual principal polarization and the map to the discriminant-six locus remains A001/A002. This review does not close those geometry items or the Pazuki comparison A018.
- A032 can close the bounded characteristic-zero local statement after the replacement below makes the automorphic contragredient and the Fourier operator explicit. Casselman's theorem alone does not identify the Fourier operator. The supplied elementary induced-model calculation fills that gap. This does not independently certify the construction of the half-integral-weight blocks, their level bounds, or every integral trace-module argument elsewhere in the manuscript.
- A069 can close the local component calculation after adding the missing citation and specifying rational components. The sign follows by substitution into the displayed isogeny identity. This does not certify that identity's other hypotheses or the global arithmetic calibration.

## A017: theta coordinate

Consumers: lines 872–878, with normalization supplied at lines 398–406 and the finite nonzero condition at line 524. The height is used again at lines 895–907.

Primary sources: Lin–Yang, arXiv:1807.00466v1, printed p.3 equation (2), and printed p.17 equation (14); Lauter–Naehrig–Yang, publisher proof dated 22 April 2015, printed p.4 §2.2, the unnumbered definitions of psi_4 and chi_10. LNY p.3 §2.1 defines its characteristics and theta nulls. These are the pinned local PDFs. Their exact relevant equations were read. Lin–Yang p.3 assigns j=0,infinity,-16/27 to CM discriminants -4,-3,-24, matching the manuscript, rather than one of the alternative scalings of the quaternionic Hauptmodul.

Equation-by-equation check, in one weighted-projective representative:

J2=12(j+1), J4=6(j^2+j+1), J10=j^3.

psi4=J2^2-24J4=144j, and chi10=-J10/4=-j^3/4.

Thus j=16*144^5*chi10^2/psi4^5. Weighted rescaling cancels because both numerator and denominator have weight 20. LNY uses precisely psi4=(1/4) sum_even theta_m^8 and chi10=-(1/2^14) product_even theta_m^2. Consequently chi10^2/psi4^5=2^-18 (product theta_m)^4/(sum theta_m^8)^5. The coefficient is 2^6*3^10=3779136. The sign in chi10 disappears only because chi10 is squared. No absolute Igusa invariant j1,j2,j3 from LNY is being substituted for this Hauptmodul.

There are ten even coordinates, not all sixteen in the product or sum. The odd theta constants vanish. A symplectic basis and compatible theta structure are used for the same polarized surface on both sides. The identity is one of modular functions and extends to special points where defined. The manuscript's finite nonzero j condition implies psi4 is nonzero in this representative, so the displayed quotient is defined. The CM case does not change the coefficient, and this calculation does not require absolute simplicity. It does require the correct polarized locus, as expressly separated above.

The homogeneous polynomials have degree 40. Their coefficient l1 norms are 3779136 and 10^5 respectively. At finite places their integral coefficients give no positive local constant. At infinite places the common constant is at most log(max(3779136,10^5))<16<22. Therefore h(j)<=40 h([theta_m])+22 is valid, even with room to spare. Appending the six zero coordinates preserves the supremum projective height.

## A032: Carayol, Casselman and U_p

Consumers: summary lines 2421–2433; detailed proof lines 9460–9535, especially the displayed O.12. Hypotheses taken from the consumer: odd p, coefficient characteristic 2, a cuspidal weight-two constituent or an explicitly separate Eisenstein constituent, level exponent at most one, and determinant with ramified quadratic restriction to inertia.

Primary source locators checked in the actual page images:

- Carayol, Ann. Sci. ENS 19 (1986), pp.409–411, §§0.3–0.7 and Theorem A. Section 0.4 sends geometric Frobenius to a uniformizer. Section 0.5, printed p.410, gives for normalized induction Ind(xi1,xi2) the parameter xi1^-1 omega^-1/2 direct sum xi2^-1 omega^-1/2, with omega=|.|. The half power and contragredient are both part of the statement. Theorem A covers every finite p away from the coefficient characteristic. Odd [Q:Q]=1 removes the extra discrete-series-place assumption.
- Casselman, Math. Ann. 201 (1973), Theorem 1 p.302, proof pp.304–306, Corollary to the proof p.306, Theorem 4 p.313. His K0 character is epsilon(a), not epsilon(d). The level-p Atkin–Lehner matrix h_p=[[0,1],[-p,0]] normalizes K0(p) and interchanges the diagonal entries under conjugation, carrying epsilon(a) to epsilon(d). The ordinary Weyl matrix alone does not normalize K0(p). His normalized induction is explicitly defined on p.304. Principal-series conductor is the product of character conductor ideals, p.306. Special conductor is p if the twisting character is unramified, and the square of its conductor otherwise. The oldspace dimension at conductor times p^r is r+1.

The sentence 'dualizing the geometric-Frobenius convention' does not specify the automorphic representation. To avoid ambiguity, let Pi_f denote the unitary automorphic normalization whose unramified Satake roots alpha,beta satisfy a_q=sqrt(q)(alpha+beta), chi(q)=alpha beta. Apply Carayol to Pi_f^vee, and put rho_f=sigma(Pi_f^vee)^vee. At a principal-series p, write Pi_f,p=Ind(mu1,mu2). Carayol's geometric parameter is mu1 omega^-1/2 plus mu2 omega^-1/2, so its eigenvalues at geometric Frobenius are sqrt(p) mu_i(p). Dualizing and evaluating at arithmetic Frobenius gives the same eigenvalues. This yields the good polynomial stated by the manuscript and fixes the bad-place normalization without suppressing the half Tate twist. All square roots here are only a way to express the complex unitary normalization; the resulting rho and a_p have the algebraic coefficient field used in the manuscript.

Conductor one and ramified determinant exclude an unramified special representation and every ramified special twist, and exclude supercuspidals. Alternatively on the Weil side, conductor one forces one-dimensional inertia invariants; the ramified determinant excludes unipotent-only inertia and forces a semisimple ramified line. A principal series must therefore have one unramified mu1 and one conductor-one mu2. It has no local old multiplicity at p. The inertia action of its ramified line is the prescribed quadratic character.

Here is the missing Fourier-operator bridge, as a direct calculation rather than an attribution to Casselman. In the normalized induced model with right K0(p) character mu2(d), let v(1)=1 on the new line. The vector exists with support B K0(p); unramified mu1 makes its definition consistent. Set H=sum_{b mod p} Pi([[p,b],[0,1]]). This operator preserves that line and

(Hv)(1)=sum_b mu1(p)|p|^(1/2)=sqrt(p) mu1(p).

For a normalized weight-two Whittaker expansion, W(diag(n,1))=a_n/n at positive integers n prime to all other local supports. Locally, a(n)[[p,b],[0,1]]=n(nb)a(np). The additive character is trivial on nb in Z_p, so the translated Whittaker value is p W(a(np)). The weight-two coefficient normalization therefore makes the resulting classical Fourier coefficient a_{pn}. Hence H is precisely the Fourier U_p, not p U_p or a unitary-normalized U_p. Its eigenvalue is sqrt(p)mu1(p), equal to rho_f(Frob_arith) on the unramified line. This calculation uses additive character conductor Z_p and normalized induction |a/d|^(1/2); changing those conventions without changing the bridge would be erroneous.

For Eisenstein series, one can avoid Carayol entirely. Its Fourier coefficients at p powers are powers of the unique unramified character value, with the weight-one power of p included in the second character. Thus the same U_p statement follows from the divisor-sum coefficients. No cuspidal theorem is being applied to Eisenstein constituents.

Old multiplicities away from p carry the same scalar U_p. For blocks already defined at level prime to p, inertia is trivial and both differences in O.12 vanish regardless of nonsemisimplicity of U_p on the p-old space. This is exactly the distinction needed, rather than pretending U_p is scalar on every oldspace.

Finally, in characteristic zero rho(tau)=diag(1,-1), rho(phi)=diag(lambda,mu), U_p=lambda. For rho(g) with lower-right entry e, the differences are -2e and -2e mu; multiplying the latter by lambda gives determinant(phi) times the former. This proves O.12 without dividing by 2. It descends to any preserved integral lattice as an equality; it does not construct integral projectors. Preservation/closedness of the particular integral trace module remains an explicit external dependency of this bounded review.

## A069: component numbers of a tame quadratic twist

Consumers: lines 3751–3756, 3784–3794, 3864–3872. Set E0=E^(h), F=Q_p, L=K tensor Q_p at p|k. The assumptions make p odd, L/F ramified quadratic, and E0/F good. The relevant component number means #Phi(F_p), not the order of Phi over the algebraic closure.

Primary source: Edixhoven, Compositio Math. 81 (1992), Theorem 5.3 p.299 and Remark 5.4.1 p.300, read from the actual page images. The hypotheses require a totally ramified tame cyclic extension and the roots of unity mu_n in the base DVR. For n=2 at odd p, -1 is already in the base and all hypotheses hold. The theorem identifies Gr^0 of the Neron special fiber with the fixed subgroup of the good special fiber and gives connected vector-group higher pieces. In particular F^1 is connected. For the quadratic twist, descent acts on the good special fiber as [-1]. Its fixed subgroup is E0_tilde[2], finite etale since p is odd. Hence Phi(E0^(k))=E0_tilde[2] as a finite etale F_p-group scheme, not merely as a geometric abstract group. The construction is residue-field equivariant, so the Frobenius action is retained.

Thus c_p(E0^(k))=#E0_tilde[2](F_p), and t_p=v2 c_p=dim_F2 E[2]^Frob_p is in {0,1,2}. Twisting E by h has no effect on its 2-torsion Galois module, since [-1] acts trivially there. In the manuscript all E[2] is rational, so t_p=2. Arithmetic versus geometric Frobenius is immaterial for fixed points, since these automorphisms are inverses.

For the Weil restriction of the good E0/L, its Neron model is the Weil restriction of the good model: the universal property verifies this, and smoothness is Edixhoven Lemma 2.2 p.292. On the special fiber, reduction from the dual-number thickening O_L/p to F_p has connected vector-group kernel and quotient E0_tilde. Thus its special fiber is connected. This gives c_p(A)=1, while c_p(B)=c_p(E0)c_p(E0^(k))=#E[2]^Frob_p. The local ratio is exactly 2^t_p.

At split primes the local varieties and component factors agree. At nonsplit unramified primes away from old support and hk all varieties have good reduction. Old bad primes are split because k is locally square at 2N; the active h primes are stipulated split. Thus the companion primes are precisely the remaining component contributions, subject to those stated support hypotheses. Substituting +v2(C_B/C_A) into the displayed formula for s_A-s_B and then into the coordinate containing -s_A gives the negative sum in (4.6). This sign calculation does not use BSD leading terms.

The earlier sentence saying the twist has component factor four is correct only in the present rational-two-torsion setting. The general t_p sentence should use #E[2]^Frob_p. The replacement below makes the distinction explicit and adds the absent primary citation.

## Sources and errata limitation

No new PDF was downloaded. SOURCE_MANIFEST.json records the existing primary bytes used, URLs and page locators. Search of author/publication pages found no correction to these particular displayed statements; that is not a proof that no errata exist. Casselman's author page warns about errors in his separate IAS notes, not this 1973 article. Lin–Yang is explicitly the pinned v1; no claim of publisher-version equivalence is made. The normalization check depends only on its displayed (2),(14), verified algebraically against LNY. Relevant web records: https://arxiv.org/abs/1807.00466 ; https://personal.math.ubc.ca/~cass/research/publications.html ; https://www.numdam.org/item/CM_1992__81_3_291_0/ .
