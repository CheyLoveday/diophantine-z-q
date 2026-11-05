# Second review: A071 and A072

Reviewed against the same a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e manuscript. No shared file was edited. Recommend bounded closure of A071 and A072 after adding the precise citations and clarifications in SECOND-REPLACEMENTS.md. The pole valuation argument, generator/rank certificate, prime-sieve construction, global height estimate and encoding are dependencies, not certified by these two source checks.

## Primary source

Silverman, The arithmetic of elliptic curves, second edition, 2009, pinned PDF work/astra-final-size-independent-review-001/silverman-2009.pdf, SHA256 72ee67bfa1e3fdf582ac7e4b032d7ca0b35a168ed6443ac39c121fbb788cab25. The complete extracted text was checked and the critical formula pages were also rendered and read, saved here as silverman-pdf-117.png, -150.png, -159.png and -207.png. These are PDF page numbers, corresponding to printed pp.99,132,142,191.

Exact locators:

- IV.1, pp.115–119, particularly Proposition 1.1 and the Laurent expansions on p.118: integral formal coordinates, x=z^-2 times a unit, y=-z^-3 times a unit. Source w=-1/y is not the manuscript's w=1/x.
- IV Proposition 2.3(a), p.122: [n](T)=nT+higher terms. This supplies the real and nonarchimedean derivative used here.
- IV Proposition 3.2, p.124: formal filtration and prime-to-residue-characteristic multiplication; IV Proposition 5.2, p.128: logarithm homomorphism; IV Proposition 5.5, p.129: logarithm coefficients a_r/r with a_r integral.
- IV Lemmas 6.2–6.3, p.131, and Theorem 6.4, p.132: logarithm converges on v(z)>0; logarithm and exponential are inverse isometries on v(z)>e/(p-1), e=v(p). The inequality is strict. Convergence alone does not imply injectivity on a shallower subgroup.
- VII Proposition 2.1, p.188, and Proposition 2.2, p.191: exact reduction sequence and formal identification for a minimal equation. VII Proposition 3.1, p.192: prime-to-p torsion reduction injectivity. VII Corollary 6.2 and Proposition 6.3, pp.199–200: finite index of sufficiently deep local formal subgroups.
- III Theorem 7.4, pp.89–91: injectivity of Hom tensor Z_l into Hom of Tate modules; III Proposition 8.6, p.99: determinant equals degree and trace equals 1+deg(phi)-deg(1-phi). V Theorem 1.1, p.138: Hasse bound; V Theorem 2.3.1, p.142: integral Frobenius polynomial.

No new download was necessary. This review does not assert that the whole book is free of errata. In particular the known division-polynomial sign issue is unrelated to these statements. The formal-group argument below uses the displayed theorem and its coefficient estimates, not the informal example following IV.6.1.

## A071: source-to-consumer map

### General local estimate

For any integral one-dimensional formal group over a characteristic-zero complete DVR, write log(z)=z+sum_{r>=2}(a_r/r)z^r with a_r integral. For z of valuation s>0, terms tend to zero because rs-e log_p(r) tends to infinity. If s>e/(p-1), then

v((a_r/r)z^(r-1)) >= (r-1)s-e v_p(r)>0.

The last strict inequality follows from v_p(r)<= (r-1)/(p-1). Hence log(z)=z(1+epsilon), v(epsilon)>=1 for normalized integral valuation. The same estimate for exp proves the inverse statement, so v(log z)=v(z). On that subgroup, v(z([n]Q))=v(z(Q))+v(n) for every nonzero integer n, as long as Q is nonzero. At the identity use z=log=0.

The integral formal law exists at the identity of the given integral Weierstrass equation even without global minimality. VII.2.2 identifies it with the full E1 of the minimal equation when the equation is minimal. At two this review uses only the formal neighborhood of the displayed equation, and makes no unproved minimality claim.

### Lines 1054–1097: multiplication tests and degree-25 logarithm

The equation is y^2=x^3-d^2 x, z=-x/y. With w=1/x, direct substitution gives w=z^2(1-d^2 w^2), hence w=z^2 times an integral unit. Therefore v(w)=2v(z) in the formal neighborhood. This is the manuscript's reciprocal abscissa, not Silverman's w=-1/y.

Solving for x gives x=(1+sqrt(1+4d^2 z^4))/(2z^2). Differentiation gives the invariant differential

omega=dx/(2y)=dz/sqrt(1+4d^2 z^4).

Thus log(z)=sum_{j>=0}(-1)^j binom(2j,j)d^(2j) z^(4j+1)/(4j+1). For j=0,...,6, multiplication by 16575 gives exactly [16575,-6630,11050,-25500,68250,-198900,612612], the displayed L. This is an algebraic coefficient calculation, not a numerical fit.

Every contact prime is outside S_mul, hence p>324, unramified in Q(sqrt(2)), good for E, and p does not divide c*. The first eight tests force v(z)>=1. Each omitted degree r>=29 term, after division by z, has valuation at least r-1-v_p(r)>=28. For 29<=r<p this is immediate; for r>=p>324, the inequality is stronger. Therefore L(z)/16575=log(z)(1+epsilon_z), v(epsilon_z)>=28. The normalizing 16575 is a p-unit, though it cancels in the ratios regardless.

One of h,h-c* is a p-unit. The full-log ratio for that denominator is an integral ratio of ordinary integer indices. The multiplicative error transfers its integrality to the truncated ratio. The difference test transfers it to the other truncated ratio, and the unit error transfers it to the other full-log ratio. Only then may the multiplicative errors be read as absolute congruences modulo p^28. If A_i denotes the unprimed truncated ratio and B_i the primed one, A_i-B_i=0 modulo p^25. Consequently

z_i-h A_i=0 mod p^25,
z_i-c*n_i-(h-c*)A_i=0 mod p^25.

Subtracting gives c*(n_i-A_i)=0 modulo p^25. Since c* is a unit at this prime, n_i=A_i modulo p^25. The product test yields the required p^25 divisibility. No division by h or h-c* modulo p is being silently made.

### Lines 5842–5852: real approximation

[n]'(0)=n on both real embeddings, and the rational parameter ratios used there have this limiting value as the nonzero formal parameter tends to zero. Compactness of the closure of the cyclic subgroup supplies positive multiples tending simultaneously to the identity; infinite order rules out a bounded sequence of positive differences. This uses no p-adic convergence assertion.

### Lines 5898–5921: the six local tests

Here again p>324, e=1, and first four tests put the relevant points in the formal neighborhoods. The displayed estimate (r-1)v(z)-v_p(r)>=1 for r>=2 is correct. It implies the log ratio differs by a unit congruent to one modulo p. Because D5 makes z(U)/z(H) congruent to integral t, it is integral. The log ratio is therefore integral and congruent to t. The relation [s0]H=[h]U gives log(U)/log(H)=s0/h; h is nonzero because H is nonidentity and P0 has infinite order. The conjugate pair gives the second ratio. Multiplication by the integer denominators is legitimate even if either is divisible by p. Subtracting gives kappa(n-t)=0 modulo p. Zero numerators U or V1 cause no problem. Nonzero denominators are precisely the guards and the log isometry, not a generic assertion that every convergent formal log is nonzero.

### Lines 5929–5940 and 1585–1590: sufficiently small neighborhoods

VII.6.3 gives finite index, and [n]'(0)=n gives arbitrarily accurate ratio approximation for a fixed integer n. A finite intersection over the specified places still has finite index. A multiple of its quotient order therefore places kappa P0 there. This justifies the existence argument for the six tests.

For the fixed old-prime clearing in the multiplication construction, M0's defining condition gives 1/x(M0P0) in N_s^4 Z[s] localized away from N_s. At odd places this gives v(z)>=2v_p(N_s)>=2, hence the log-isometry range; at two it gives v_s(z)>=4v_2(N_s)>=4>e=2. All multiples H of M0P0 and V0=(h-c*)P0 remain within these subgroups. For a true triple U_i=[n_i]H and V_i=[n_i]V0. The ratios of logs are integral integers. At these depths the truncated-log/log ratio is a unit also at the small primes: for omitted r>=29, (r-1)s-e v_p(r)>0. Thus the inverse-abscissa and ratio tests are integral, as used in the old-prime clearing. A factor 16575 in L cancels between numerator and denominator; it is not necessary that it be a unit at old primes.

### Lines 6030–6047: actual reduction orders and the dyadic search

Odd bad reduction can occur only over 7. At s=3 mod 7, d=0 and P0=(2,6); the reduced curve is y^2=x^3, and partial derivative 2y is 5 mod 7, so the point is nonsingular. Its smooth group has order 7. At the other place s=4 mod 7, d=3 and the curve is good; P0=(4,0). Thus taking its actual order in the smooth reduction group is legitimate at every odd place in the product.

For good residue field F_{p^f}, f<=2, the group cardinality is at most (p^(f/2)+1)^2< p^3 for odd p; for f=2 the smallest case p=3 gives 16<27. The bad smooth group at 7 has order 7. Hence the product m0 of actual point orders is <=N_s^6. The group cardinality is only an upper bound for each order; m0 uses actual orders, as required.

At two use v_s(s)=1, v_s(2)=2. The displayed coordinates give v_s(x)=-6, v_s(y)=-9 and v_s(z)=3, while d is a unit. This is already strictly deeper than e/(p-1)=2, so v_s(z([2]Q))=v_s(z(Q))+2, an equality stronger than the claimed inequality. The initial point and every positive multiple stay in this formal subgroup. A nonidentity point has negative x valuation and therefore x!=0; if an identity occurs, the search expressly uses reciprocal abscissa zero. No infinite-order assumption is needed merely for the search to be defined.

After multiplication by m0 all odd places have v(z)>=1. Multiplication by N_s^4 adds 4v_p(N_s) at each odd place by the log isometry, so v(1/x)>=2+8v_p(N_s). At two it gives v_s(z)>=3+8v_2(N_s), so v_s(1/x)>=6+16v_2(N_s). These inequalities are stronger than membership in N_s^4 Z[s] localized away from N_s. For an explicit coefficient check at two, if w=a+bs then a=(w+sigma(w))/2 and b=(w-sigma(w))/(2s), losing at most 2 and 3 units of v_s. Both rational coefficients still have v_2 at least 4v_2(N_s). Hence the successful index <=N_s^4 m0<=N_s^10 is justified.

### Other local formal uses checked

Lines 794–795, multiplicative formal group: log gives U_F^(e+1) isomorphic to m_F^(e+1), since e+1>e. Multiplication by 4 takes this ideal exactly to m_F^(3e+1), so (U_F^(e+1))^4=U_F^(3e+1). This is the multiplicative formal law, not an elliptic-curve log.

Lines 2890–2898: successive formal quotients are m^r/m^(r+1), additive residue modules. Unramifiedness gives a Galois-fixed uniformizer; the residue normal-basis argument then applies to each quotient. No logarithm on a shallow subgroup or division by the unramified degree is needed. This reviews the formal-group step only, not the Lang-theorem or component-group steps.

Lines 3020–3022: multiplication by 2^a is an automorphism of the entire formal group over a residue-characteristic-ell local field with ell odd. Its linear coefficient is a unit, so the integral formal inverse exists. This argument is valid even though the extension is ramified and the full formal group may lie outside the logarithm-isometry radius.

## A072: conjugate reduction orders

Consumers are lines 1425–1460, followed by CRT use at lines 1569–1577. Here d1,d2 are the cardinalities of the two reduced groups. They are valid annihilating multiples of the orders of reduced P0, but need not equal those point orders. The replacement names them group orders to avoid the ambiguous phrase 'reduction orders.'

p=1 mod 8 gives splitting in Q(sqrt(2)) and i in F_p; p=3 mod 7 together with p=1 mod 4 gives (7/p)=(p/7)=-1. The conjugate d values have product 7, so they are units of opposite squareclass. Their curves y^2=x^3-d_i^2 x are opposite quadratic twists. For a twist isomorphism over F_{p^2}, arithmetic Frobenius acts through the extra sign -1, so the Tate traces are opposite. This can also be seen directly by changing variables in the quadratic-character point-count sum. No quartic-twist identification is substituted here.

On either reduction, i acts by (x,y)->(-x,iy), is defined over F_p, and satisfies i^2=[-1]. It commutes with arithmetic p-power Frobenius because both coordinate expressions do, using i^p=i. III.7.4 for l=3, permissible since p>324, embeds the rational endomorphism algebra tensor Q_3 into M_2(Q_3). The polynomial T^2+1 is irreducible over Q_3, so the matrix centralizer of i is the two-dimensional field Q_3(i). The rational centralizer is at most two-dimensional and contains Q(i), hence equals Q(i).

Frobenius lies in this centralizer and is integral over Z by V.2.3.1(b). The integers of Q(i) are Z[i], so write it a+bi with a,b integers. On the two-dimensional Tate space, trace(i)=0, determinant(i)=1; therefore trace(a+bi)=2a and determinant(a+bi)=a^2+b^2. III.8.6 gives determinant(Frob)=p and trace(Frob)=p+1-#E(F_p). Thus the two group cardinalities are p+1-2a and p+1+2a. This uses arithmetic Frobenius on the Tate module, matching the source's p-power endomorphism. a!=0 since a=0 would make prime p a square b^2.

All 2-torsion points (0,0),(d,0),(-d,0) are distinct rational points, so both group orders are divisible by 4. Their sum is 2(p+1) of valuation exactly 2 since p=1 mod8. Thus min(v2(d1),v2(d2))=2. This proves the exact 2-part of the gcd, not just divisibility by 4. Hasse gives 0<d_i<=p+1+2sqrt(p)<2p for p>324. Since 4 divides d_i and p is odd, d_i!=p; therefore p divides neither group order.

If odd ell divides both, it divides 4a and 2(p+1), hence ell|a and ell|(p+1); reducing a^2+b^2=p gives b^2=-1 mod ell. These are precisely the algebraic inputs used in the sieve. The sieve exclusions themselves are outside this review.

Additional consistency checks: the two reductions used for torsion at manuscript line 291 have group cardinalities 20 at (17,s-6), and 24 at (23,s-5), by a complete finite-field enumeration. Their discriminants are units. VII.3.1 applies prime by prime: 17-primary torsion is excluded using p=23, 23-primary using p=17, and all other primary parts inject at both. Thus the total rational torsion order divides gcd(20,24)=4. This is consistent with the displayed full rational 2-torsion. It does not prove the rest of the generator certificate.
