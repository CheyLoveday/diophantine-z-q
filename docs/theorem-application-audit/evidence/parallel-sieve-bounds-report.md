# A021 and A046 audit

Audited 2026-11-05 against `work/github-research-upload-20261104/repository/diophantine_zq.tex`, SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. Scope is A021, the finite-complexity prime asymptotic and tail removal, and A046, the progression estimate through the catalogue bound. This is not an audit of the later formal-group calculation or the entire manuscript.

Both applications pass this review. No mathematical repair is proposed. The remaining citation precision can be supplied by `replacement-text.tex`. In particular the prime-pattern argument does not require an error term uniform in a growing CRT modulus. The progression estimate includes exceptional zeros. Exact arithmetic verifies its threshold and counting substitutions.

I read the registered applications, inventory, open items, sources and findings, then checked the primary statements and the manuscript independently. No applicable AGENTS.md was found in the workspace ancestry or the searched work tree. I applied the unslop skill to this report. All output is confined to this directory.

## Sources and versions

`sources-manifest.json` records URLs, hashes, byte counts, and provenance. The files named `*-selected.txt` are fresh extractions from the PDFs, with one-based PDF page markers. PDF pagination differs from printed pagination in the Green–Tao article because its PDF has two front pages.

| Input | Exact locator | Version check |
| --- | --- | --- |
| Green–Tao, *Linear equations in primes* | Definition 1.5, printed pp.1759–1760; Lemma 1.6, p.1761; unnumbered Main Theorem, p.1763; Conjecture 1.2 and equation (1.7), p.1757 | Pinned Annals 171 (2010) article. The main finite-complexity theorem is unnumbered; calling it Theorem 1.2 would be wrong. |
| Green–Tao, *The Möbius function is strongly orthogonal to nilsequences* | Theorem 1.1, printed pp.542–543; immediately following remarks on p.543 | Pinned Annals 175 (2012) article, 26 PDF pages. The remarks explicitly discharge MN(s). |
| Green–Tao–Ziegler, *An inverse theorem for the Gowers U^{s+1}[N]-norm* | Conjecture 1.2, p.3; Theorem 1.3, p.4 | Fresh [arXiv:1009.3998v5](https://arxiv.org/abs/1009.3998v5), 23 April 2026, 116 pages, agrees byte-for-byte with the registered file. |
| GTZ separate erratum | Sections 2–4, pp.2–6; Proposition 3.1, p.3 and ensuing deduction of original Proposition 7.3, pp.3–5 | Fresh [author PDF](https://people.maths.ox.ac.uk/greenbj/papers/GI(s)-erratum.pdf), six pages, agrees byte-for-byte with registered file. |
| Bennett–Martin–O'Bryant–Rechnitzer | Theorem 1.2, p.5; equations (1.10)–(1.11), p.4; Corollary 6.17, pp.78–79 | Fresh [arXiv:1802.00085v3](https://arxiv.org/abs/1802.00085v3), 27 November 2018, 103 pages, agrees byte-for-byte with registered file. |
| BMOR published comparison | Theorem 1.2, printed p.431; equations (1.10)–(1.11), p.430; Corollary 6.17, pp.507–508 | Fresh [author-hosted published article](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf), Illinois J. Math. 62 (2018), 427–532, 106 pages. These statements and constants agree with v3. This is an explicit local comparison, not a claim that all text of the versions is identical. |

The GTZ v5 abstract page identifies its new repair as a wrong filtration in Lemma 13.2 and two typographical errors on p.28. The corrected filtration is visible on pp.72–73, including footnote 7. The separate erratum is still necessary: v5 retains the original Proposition 8.3 wording. The erratum says that proposition is false as stated, adds the top-group conditions for filtrations in Section 2, and supplies Proposition 3.1 plus the modified proof of the actual downstream Proposition 7.3. Section 4 corrects the quotient-group argument and smaller errors. Consequently the accepted input is Theorem 1.3 read with both corrections, exactly as the manuscript's bibliography specifies. It is not the uncorrected 2012 printed proof, nor a claim that v5 alone incorporates the 2024 erratum.

## A021: hypotheses and main term

Consumer lines 1182–1329 construct the system and lower count. Write the sieve cutoff as L and reserve a different symbol for the coefficient-size bound in Green–Tao. Fix A first. The 22 original forms have coefficient vectors `(0,0,1)`, `(1,0,-b)`, `(0,1,-b)` and `(-1,-1,A-b)`, for the seven distinct b in `{0,-15,-20,-24,-30,-60,1}`. Their nonzero two-by-two minors are either units or nonzero contact differences of absolute value at most 61. Thus every pair of linear parts is independent over Q, and remains independent modulo every prime greater than 324. Three-form independence is not needed.

The initial construction uses only A and the fixed catalogue. A primitive form has exactly q^10 zeros modulo q^5 among q^15 triples, so the union bound is 22/q^5<1, even at q=2. Lifting to q^8 fixes its valuation e<=4 and its divided unit modulo q, or modulo 8 at 2. Distinct chosen catalogue primes exceed 324. On the selected plane modulo h, excluding 42 lines removes at most 42h<h^2 points. A coefficient ±1 makes the lift modulo h^2 surjective on the divided unit. The residues 0 and -1 can therefore be avoided. These checks justify integral affine forms and nonzero constants at all primes dividing W0.

Choose the bounded rectangular box with closure in a chamber, then signs. The signed forms divided by k_nu satisfy alpha_A X <= Psi_nu <= beta_A X on X Omega. This gives positivity and a uniform logarithmic weight bound. For fixed L and r, use the affine forms

`psi_nu(n) = epsilon_nu F_nu(r+W_L n)/k_nu`

on `K_X = (X closure(Omega)-r)/W_L`. Their coefficients are integral because k_nu divides W0, and their linear parts remain pairwise independent. Singleton classes in Definition 1.5 give complexity <=20. Alternatively rank three and Lemma 1.6 give <=19. It suffices to use s=20. GTZ Theorem 1.3 supplies GI(20). Möbius Theorem 1.1 and its p.543 specialization supply MN(20); its ineffective constant causes no problem for an existence threshold.

K_X is convex and lies in [-N,N]^3 with N=ceil(C_A,L X), for a fixed positive C_A,L. The coefficient-size parameter is bounded independently of X once A,L,r are fixed. The Green–Tao Main Theorem therefore proves equation (1.7) with error o_A,L,r(X^3). Its archimedean term is `vol(Omega) X^3/W_L^3`. Replacing the closed box by the open box changes at most O_A,L(X^2) lattice points and O_A,L(X^2(log X)^22) weight, which is negligible. No boundary regularity assumption is missing.

At q|W_L all affine variable coefficients vanish modulo q, and the constants are units. Thus beta_q=(1-1/q)^(-22)>=1. If q does not divide W_L, q>324 and the CRT affine change and the factors k_nu are invertible. The original homogeneous planes apply. Each plane has q^2 points and each intersection of two has q points. The two Bonferroni inequalities give precisely

`1-22/q <= P(no zero) <= 1-22/q+231/q^2`.

This yields beta_q=1+O(q^-2). More explicitly, expansion of the logarithms gives

`log beta_q >= -sum_{j>=2}(22^j-22)/(j q^j) >= -242/[q^2(1-22/q)] >= -484/q^2`

for q>=331. The last inequality is also checked by rational arithmetic. The resulting product is bounded below by exp(-484 sum_{n>=331}n^-2)>0 independently of L,r. No assertion of uniform Green–Tao errors follows from, or is needed for, this uniform local lower bound.

For primes newly included in W_L, excluding at most 44 planes gives density at least 1-44/q. All such q exceed 324. Summing `log(1-44/q)=-44/q+O(q^-2)` and using the classical prime harmonic asymptotic gives a positive lower constant independent of L. The modulus W0 remains fixed. There are finitely many r for fixed L, so one maximum of their individual asymptotic thresholds suffices. The lower weight is at least c_A X^3/(log L)^44. Proper powers have O_A(sqrt(X)log X) possible values for any one form. Each value fixes a plane with O_A(X^2) integer points, and every weight is O_A((log X)^22). Their total weight is negligible for fixed L. Dividing by the weight bound establishes line 1327 with a_A independent of L and threshold X0(A,L).

## A021: upper sieve and tail quantifiers

Consumer lines 1331–1426 prove the needed elementary upper sieve, not an invocation of the prime asymptotic. For squarefree d, CRT gives rho(d) residue classes in two dimensions and error O(rho(d)(N/d+1)). Since rho(d)<=d^2 this is O(Nd+d^2), uniformly in square location. The displayed Selberg weights have lambda_1=1. The diagonalization using `1/g(m)=sum_{r|m}1/h(r)` gives the quadratic form 1/G(Z). The bound |lambda_d|<=d and [e,f]<=Z^2 give error O(NZ^6+Z^8). These steps do not depend on the varying fibre prime or L.

The truncated denominator argument is valid. In the auxiliary Euler product supported on primes <=z=Z^(1/100), the random squarefree divisor has E(log d)<=0.42 log Z for sufficiently large Z. Markov leaves at least 0.58 of the mass at d<=Z, hence G(Z)>=H(z)/2. The first sieve has g(q)=2/q-1/q^2 on q=1 mod 4, omitting at most one prime. The fixed-progression Mertens estimate gives H(z) comparable to log z, and the omission reduces it by at most a factor two. The second sieve has 21/q-210/q^2<=g(q)<=21/q, giving H(z) comparable to (log z)^21. All excluded primes are <=the fixed Q*. Constants remain independent of L.

Lines 1462–1507 count bad prime values. For L<ell<=X^(1/8), N is comparable to sqrt(X)/ell and at least a constant times X^(3/8). With Z=X^(1/100), the error/main ratios contain powers X^(0.06-3/8) and X^(0.08-3/4), which vanish even after multiplying by log X. The at most two roots of -1 modulo ell and omission of ell from the sieve do not alter the constant. Summing ell^-2 is O(1/L). For ell>X^(1/8), the fact a!=0 removes an additive constant from the count of multiples a; also ell<=|a|. The direct sum is O_A(X^(7/8)+sqrt(X)log X). These prove the stated bad-value estimate uniformly in L. In the final use X can and does exceed a threshold depending on the already fixed L.

Lines 1509–1541 count each fibre. Solving a coefficient ±1 parametrizes its integer lattice by two original coordinates. For q>Q* and q<=Z, q cannot divide k_nu or p, so c=epsilon_nu k_nu p is nonzero modulo q. A remaining form is nonconstant on the fibre by pairwise independence. Coincident zero lines would imply `F_j-lambda F_k=mu(F_nu-c)`; comparison of constants gives mu=0, contradicting independence. Hence there are 21 distinct lines, and the stated bounds on g(q) apply. The resulting bound O_A(X^2/(log X)^21) is uniform in p and L. In particular q=p is outside the sieve range, so no unbounded exceptional factor is hidden.

Lines 1543–1565 multiply the two bounds and sum over 22 forms. The leading removed count is b_A X^3/[L(log X)^22]; the errors divided by the lower main term, with L fixed, are bounded by constants times X^(-1/8)log X and X^(-1/2)(log X)^2. First select L>max(Q*,B0,3) with b_A/L<a_A/[2(log L)^44]. This is possible because (log L)^44/L tends to zero. Next fix all residues and take X above their finite maximum threshold and the error-absorption thresholds. The strict half bounds leave a positive number of patterns. This proves the needed order of quantifiers. It does not prove, or claim, simultaneous validity at L=L(X).

This review uses the manuscript's already established reduction-order implication that a bad prime gives ell|a and b^2=-1 mod ell, with a!=0. The CM and reduction-order source audit itself belongs to A072, outside this assignment.

## A046: exact progression substitution

Consumer lines 6015–6028 take W=4 product_{p<=324}p and X=2^(W^3). The actual value has 435 bits, so 10^5<W<2^512. Also 324! has 2241 bits, so 2^2000<324!<2^2250. `check.py` computes these integers by trial division and multiplication, using no floating point arithmetic.

In BMOR v3, Theorem 1.2 assumes q>=3 and gcd(a,q)=1. It bounds the theta error by c_theta(q)x/log x with c_theta<=c0 and threshold x_theta<=x0. At q>10^5, equations (1.10)–(1.11) give c0=1/160 and x0=exp(0.03 sqrt(q)(log q)^3). Corollary 6.17 gives the non-strict version for q>=10^5 and real parameter 1<=A<=8; specialize its parameter to 1. This A is not the manuscript's prime-pattern integer A. There is no assumption excluding an exceptional zero. The text after the corollary treats the absence of an exceptional zero as allowing a better threshold, confirming it is not needed here. The published statements on pp.430–431 and 507–508 agree.

The following elementary bounds rigorously verify the substitution without approximating a huge exponential. Since 1/2<log 2<1, log W<512 and sqrt W<=W,

`0.03 sqrt(W)(log W)^3 < (3/100) W 512^3 < W^3/2 < (log 2)W^3 = log X`.

The middle inequality is the exact check `6*512^3 < 100*W^2`. Thus X exceeds the source threshold. Further,

`X/(160 log X) < X/(80 W^3) < X/(2W)`.

Since phi(W)<=W, theta(X;W,a)>X/(2W). Every summand is at most log X, so

`pi(X;W,a) >= theta/log X > X/[2(log 2)W^4] > X/(2W^4)`.

Finally 44W^4<2^2054<2^(W^3)=X, so this count exceeds 22. Every prime <=324 divides W and cannot lie in a unit class. The endpoint X is composite, so all the catalogue primes are strictly below X. There are 22phi(W)<=22W catalogue entries. Thus H_max<X and H_cat<=X^(22W), and

`log_2 N_s < 512+22 W^4 < 512+22*2^2048 < 2^2054`.

All integer comparisons are asserted in the script and pass. This closes A046's progression and numerical-threshold obligation. It does not assert that exact-arithmetic checks replace the source theorem's hypotheses; those have been checked separately above.

## Deliverables and disposition

`check.py` regenerates the extractions, manifest, and `exact-receipt.json`. The receipt gives the literal W and integer bit lengths. The fresh GTZ and BMOR downloads were compared with the existing pinned files, while the two Green–Tao journal PDFs were read from their pinned local copies. The newly downloaded BMOR published PDF has SHA256 `958b0390475236b68afdec28ce006b1a1d6ac59484eea9443e0b287e9f61a541`.

`replacement-text.tex` supplies optional citation and calculation detail. It repairs the documentation gaps in A021 and A046, not a false mathematical assertion. No shared manuscript, PDF, audit register or git state was modified. No further failure remains within the assigned A021/A046 scope on this review.
