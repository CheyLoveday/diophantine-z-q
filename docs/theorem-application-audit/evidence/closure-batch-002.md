# Second closure pass: the sign cocycle and two-isogeny maps

Review date: 2026-11-05. Reviewer: root assistant. This is a direct check, not an independent second review. It consumes the premises identified below and does not certify the main theorem.

## A007: local obstruction and global sign splitting

Disposition: closed for this source/application interface. Sources are the pinned Milne, Class Field Theory, v4.03, III Theorem 3.4 and VIII Theorem 4.2. The former identifies finite abelian local Galois characters with continuous finite-order characters of the multiplicative local field. The latter gives injectivity of the global Brauer group into the local groups, with the sum-of-invariants relation. The additional group calculations required by the application follow here.

Every occurrence of mu_infinity in this argument has trivial Galois action. Its subgroup mu_2 also has trivial action, which agrees with the usual roots-of-unity action on mu_2 over Q. Consequently the boundary from the constant-module square map lands in the usual H^2(Q,mu_2)=Br(Q)[2]. Replacing all roots of unity by the cyclotomic Galois module would be a different argument and is not done here.

For an odd prime p, decompose Q_p^* as p^Z times mu_(p-1) times (1+p Z_p). On Z a finite character has a finite character square root by choosing a square root of its generator's value. On the pro-p factor squaring is invertible on every finite character group. On the cyclic factor of even order p-1, a character with exponent a has a character square root if and only if a is even, equivalently if its value at -1 is 1. At p=2 the decomposition is 2^Z times {1,-1} times (1+4 Z_2). The last factor is Z_2; a finite character of order 2^k has a continuous square root factoring through Z/2^(k+1). The middle factor again gives the sole obstruction, the value at -1.

Local reciprocity therefore gives delta(chi)=0 exactly when chi(-1)=1. Since Br(Q_p)[2] has precisely two elements, this characterizes the local boundary completely. Arithmetic versus geometric reciprocity replaces chi by its inverse and does not change its value on -1 or this obstruction.

The manuscript's sign cocycle is inflated from Gal(L/Q), a premise proved in its preceding construction. At a finite prime outside T, L/Q is unramified. Thus its local class is inflated from the unramified quotient, of cohomological dimension one for the finite module mu_2, and vanishes. For each odd prime where its invariant is 1/2, choose a character modulo p with odd exponent relative to a generator of the character group. It has value -1 at -1. At 2 use the nontrivial character modulo 4. The product character is unramified outside T, and its local obstruction agrees with the sign cocycle at every finite place. Other factors are unramified at p and hence trivial on the unit -1. The Brauer sum relation gives equality at the real place, and global injectivity gives equality of the global H^2 classes.

Choose a square root beta_0 of each value of chi. Since chi is finite and continuous, this is a continuous finite-valued cochain in mu_(2m). Equality of the H^2 classes supplies a continuous sign cochain a with delta(a)=delta(beta_0)/epsilon. Then beta=beta_0/a has beta^2=chi and delta(beta)=epsilon. Thus no global character square root is falsely asserted.

For h in G_L, the inflated normalized cocycle satisfies epsilon(g,h)=epsilon(h,g)=1. The cochain identity then shows both that beta restricted to G_L is a character and that it is invariant under conjugation by G_Q. This proves normality of its kernel field and the extension bound [L':L]<=2m. The order of chi is at most twice the product of p-1 over the relevant odd primes, giving the manuscript's larger bound.

The ramification-cleaning step also works with this cochain. At a prime outside T, inertia lies in G_L and chi is trivial on inertia, so beta on inertia is quadratic. Only finitely many such inertia restrictions are nontrivial because the kernel field of beta restricted to G_L is finite. At an odd prime there is only one nontrivial quadratic character of inertia: the wild inertia is pro-p and the tame inertia has a unique quotient of order two. The global character of Q(sqrt(D)), where D is the squarefree product of those odd primes, has exactly those restrictions. Multiplying beta by it kills the unwanted inertia, changes neither beta^2 nor delta(beta), and adds ramification only possibly at 2. The construction explicitly has 2 in T. Thus the cleaning does not enlarge the allowed support.

This closes the cohomological interface. It consumes the earlier construction of L, its ramification support, and the normalized sign cocycle. It is not a review of the quaternionic geometry producing those objects.

## A058: quadratic-field arithmetic and two-isogeny descent

Disposition: closed for this application. Sources are Milne, Algebraic Number Theory, v3.08, Theorems 4.3 and 5.1, and Silverman 2009, X Example 4.8 and the surrounding descent construction. The elementary coordinate and kernel checks below remove dependence on a misprinted equation in X Proposition 4.9.

The integral basis of Q(sqrt(2)) is 1,s, its discriminant is 8, and Minkowski's bound is sqrt(2)<2. Every ideal class therefore has an integral representative of norm 1. The ring is a PID. Its unit rank is one and its roots of unity are {1,-1}, so its unit squareclass group has order four. The signs of -1 and 1+s are independent under the two real embeddings. Thus the sign map on unit squareclasses is an isomorphism; every totally positive unit is a square.

Here are explicit maps with no coordinate convention suppressed. Put E_b: y^2=x^3+b x, b nonzero, and E': Y^2=X^3-4b X. Choose

    phi(x,y) = (x+b/x, y(1-b/x^2)),
    hat_phi(X,Y) = ((X-4b/X)/4, Y(1+4b/X^2)/8).

Substitution in the equations verifies both maps on their affine domains. Their poles extend to the identity, and their kernels are the identity and (0,0). Their composition is [2]: its x-coordinate is (x^2-b)^2/(4x(x^2+b)), and substitution gives the ordinary tangent-law y-coordinate as well. Equivalently, both compositions have that x-coordinate and their invariant-differential pullback is multiplication by 2, fixing the sign. Silverman's Example 4.8 takes the negative of our phi. This does not change either image or the kernel calculation. Its y denominator x^2 is correct.

Define alpha_b(O)=1, alpha_b((0,0))=b, and alpha_b((x,y))=x in K^*/K^{*2}. The chord-and-tangent law makes this a homomorphism. For a line y=mx+c, the product of its three nonzero intersection abscissas is c^2. The exceptional line through (0,0) gives x(P+(0,0))=b/x(P), exactly the special value specified above. The tangent case is the same identity with a repeated root; vertical lines use alpha(P)=alpha(-P). These cover the exceptional cases.

One can check the kernel directly. The x-coordinate of hat_phi(Q) is (Y/(2X))^2 when X is nonzero, so its image is in ker(alpha_b), with the exceptional points checked by the displayed values. Conversely let x=u^2 be nonzero and put v=y/u. Then v^2=x^2+b, and

    X=2(x+v),    Y=2uX

defines a point of E' mapping to (x,y). Here X is nonzero since b is nonzero. If P=(0,0) and b is a square, use Q=(2 sqrt(b),0). The identity lifts to the identity. Thus ker(alpha_b)=hat_phi(E'(K)). Applying this same argument to E' and identifying E_(16b) with E_b by (x,y)->(4x,8y) gives ker(alpha_(-4b))=phi(E_b(K)). This supplies exactly the two quotients needed by the manuscript.

In the pinned 2009 PDF, X Proposition 4.9 on printed p.337 has a^2-b instead of a^2-4b in E'. Example 4.8 on p.336, the Kummer value on p.337, and direct substitution give a^2-4b. This is a genuine printed inconsistency, not an alternative convention. The application uses the correct E': Y^2=X^3+4d^2X. The preceding explicit proof is valid independently of that typo.

Now take b=-d^2. The norm of d=75-53s is 7, and (1+s)^4 d=3-s. Away from the prime (d), an odd valuation of a nonzero x makes the minimum of 3v(x) and v(x) odd and unique; a square y^2 cannot have that valuation. The squareclass of x is therefore represented by a unit times 1 or d. The first image has at most eight classes generated by -1,1+s,d. The two-torsion supplies 1,-1,d,-d. On the isomorphic curve with delta=3-s, the point R=(1+s,2s) supplies the class 1+s; scaling x by (1+s)^4 does not change a squareclass. Homomorphy gives all eight.

On E', every nonzero abscissa is positive under each real embedding. At a prime away from (s),(d), the same minimum-valuation argument forces even valuation. At (s) the valuations are 3m and m+4, so they are distinct and odd for odd m. At (d) they are 3m and m+2. The only odd equality case is m=1, where cancellation would require u^2=-4 in F_7. The squares in F_7 are 0,1,2,4, so this is impossible. Thus every valuation is even. The PID property and positivity show that x is a square. The special value alpha_E'((0,0))=4d^2 is also a square. The second image is trivial.

Consequently E'(K)=phi(E(K)), and hat_phi(E'(K))=[2]E(K). The first kernel calculation gives |E(K)/2E(K)|=8. Finite generation and the displayed full rational 2-torsion give rank one, since |E(K)/2E(K)|=2^rank |E(K)[2]| and |E(K)[2]|=4. Correction on 2026-11-05: the separate two-prime computation A059 is needed to determine the entire torsion subgroup, not to deduce this rank. The earlier assertion that the rank must consume that computation was too strong.

## A056: general scalar identity, with source retrieval still open

The parity-normalized recurrences in construction/elliptic-division-polynomials.js agree with Silverman III Exercise 3.7 after setting a1=a2=a3=a6=0 and a4=A. In the odd recurrence the even-indexed factor contributes (2y)^4=16(x^3+Ax)^2 on exactly the branch selected in the code. In the even recurrence the factors of 2y cancel on either parity of the half-index.

The book's printed plus sign in the omega formula is wrong. The author's 2011, 2013 and 2014 errata, as exposed by the primary-site search index, give the corrected formula

    2(2y+a1 x+a3) omega_n
        = psi_(n-1)^2 psi_(n+2) - psi_(n-2) psi_(n+1)^2.

On the short model, comparison with the even-index recurrence yields psi_(2n)=2 psi_n omega_n for n>=3. The n=1,2 cases follow from the initial values. Combined with the multiplication ordinate omega_n/psi_n^3, this is the repository's psi_(2n)=2 y([n]P) psi_n^4. The identity branch and n=0 are treated separately; negative n uses group negation. A nonzero division polynomial on a nonzero torsion-free point supplies the inverse-norm guard. The general-Weierstrass ordinate convention is not imported into the short model.

The existing exact regression check passed 44 valid scalar cases, rejected 44 modified abscissas, and rejected 30 wrong ordinate signs. It supplements the general identity and is not its proof.

Open documentation obligation: attempts to retrieve the full official errata PDF timed out. The correction above is visible in the official search result, but the full errata bytes have not been pinned. A056 is therefore not marked fully closed by this pass. Primary URLs: https://www.math.brown.edu/johsilve/AEC/AECErrata2014.pdf and https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf. The X.4.9 coefficient discrepancy was verified in the pinned book itself; no claim that the author lists that discrepancy in the errata is made.
