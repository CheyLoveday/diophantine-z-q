# T2 upstream closure: the fixed BFH witness and compatible Kummer primes

This additive report preserves the sealed weighted-theta report. It closes that report's fixed-witness and Kummer-existence input for the actual non-CM pole family E_l:y^2=x(x-l)(x+3l), with l positive squarefree and l=11 modulo 12. It does not assert the complete restricted converse, the odd lower-index estimate, or the integer-definition theorem.

Result: the required witness and the actual arbitrarily advanced detecting stages follow from the primary statements and deductions below. No new unproved hypothesis is needed for this T2 input. Published modularity, nonvanishing, Gross–Zagier, Mordell–Weil and open-image theorems remain external foundations; their particular applications are stated explicitly.

## 1. The actual filter and the BFH clauses

Write w(A) for the root number of a modular elliptic curve A/Q. Bump–Friedberg–Hoffstein, Inventiones 102 (1990), printed pages 543–544, state their theorem for a cuspidal newform of even weight and trivial character, with any finite set S containing the level primes. If epsilon is its functional-equation sign, their clause (i) gives a fundamental discriminant d with epsilon*d<0, splitting at every prime of S, and a simple central zero. Clause (ii) gives epsilon*d>0, the same splitting conditions, and a nonzero central value. These are existence statements, not prime-count estimates.

The actual pole curve is modular and has a weight-two normalized newform with trivial character. In the final RC application its 2-primary Selmer corank is one. The rational point (0,0) has order two, so quotienting by its rational subgroup gives a rational 2-isogeny. Dokchitser–Dokchitser, arXiv:0906.1815v1, Theorem 1.8 on printed page 4, gives (-1)^(Selmer corank)=w(E) for a rational isogeny of degree 2 or 3. Its corank is explicitly the Z_2-corank of the discrete 2-infinity Selmer group; no finiteness of Sha is assumed. Hence the root number needed here is -1. Its positive odd coefficient filter contains 1. Thus every original local squareclass condition is the square unit condition. Include 2,3, every conductor prime, all original coefficient/class-group support primes and every fixed forbidden prime in S_0.

Apply BFH(ii) to E with S_0. Since epsilon=-1, its discriminant h_* is negative. Splitting at 2 makes h_* odd and h_*=1 modulo 8; splitting at the other S_0 primes makes it a local square there and coprime to the full support. The two exceptional imaginary quadratic fields are excluded already by splitting at 2, so |h_*|>4. Its central value is nonzero. This h_* is fixed once.

Adjoin every prime dividing h_* to S_0 and fix the required square unit tests there. Apply BFH(i) to the original E with this enlarged splitting set. It gives one positive fundamental discriminant D_w, a local square at the entire enlarged support, with

    ord_(s=1) L(E^(D_w),s) = 1.

The word "quadratic field" in the BFH statement excludes d=1, although no argument would require a numerical bound on this witness. Its support is disjoint from h_* and the conductor, D_w=1 modulo 8, and D_w remains on the prepared T2 Schwartz filter. Choose D_w once, before theta precision, odd normalization, graph size or determinant precision.

This application does not ask BFH to prescribe unrelated actions in nonabelian extensions. All of its local prescriptions here are splitting at a finite set of rational primes. The more general signed-unit reduction, when needed outside this exact filter of 1, is as follows. For a nonempty filter with a fixed real sign and local unit squareclasses at S containing 2,3 and the bad primes, choose one signed prime q0 in those classes by CRT and Dirichlet, outside all fixed exclusions. Apply BFH to the actual modular curve A^(q0), now also requiring its discriminant d to split at q0, all conductor primes and all exclusions. Then d is positive in the needed clause when w(A^(q0)) has the designated odd or even sign, and q0*d retains the original sign and local classes.

The root number is constant on that signed unit filter. At S this follows from local isomorphism of twists. At every new good odd prime p>=5 the ramified quadratic twist has factor (-1/p), and at the remaining good primes the unit twist has factor 1. These are the good-reduction cases of Desjardins, Proposition 3.3, printed page 84; its restriction p!=2,3 is respected because both primes are in S. Their product is determined by the real sign and the fixed 2-adic squareclass. Thus the signed-prime preparation is legitimate even for odd parameters 3 or 7 modulo 8. Such parameters may have field discriminant 4t; they are not silently called odd fundamental discriminants. T2 itself uses the fundamental-discriminant square filter just treated directly. No at-most-five-primes conclusion is drawn from BFH; that separate even-branch conclusion uses Hoffstein–Luo.

## 2. The primary height formula applies to the actual unaveraged point

Put K=Q(sqrt(D_w h_*)). Since D_w and h_* are coprime odd fundamental discriminants, D_w h_* is the fundamental discriminant of K. Every prime dividing 2N splits in K. The genus character chi on Pic(O_K) attached to the biquadratic extension Q(sqrt(D_w),sqrt(h_*))/K is unramified and equals chi_h*(Norm a) on ideals prime to the discriminant.

Use Cai–Shu–Tian, "Explicit Gross–Zagier and Waldspurger formulae", Theorem 1.1, printed pages 2524–2525. Its normalized weight-two form is the original form of E; the conductor of its ring-class character is c=1. Its condition (1) holds because all N-primes split. Condition (2) concerns primes dividing both N and the quadratic discriminant, of which there are none. The units factor is u=1 because K has only units +/-1. The parametrization is the fixed phi with phi(infinity)=0. These are exactly the source hypotheses, including the non-squarefree levels permitted by the condition on p^2|N.

The elliptic-curve clause of that theorem uses

    P'_chi(phi) = sum_[a in Pic(O_K)] phi(P_a) chi([a]),

without division by the class number. This is exactly the P_(D_w) of the T2 source, for its chosen cyclic level orientation. Its formula is

    L'(1,E,chi)
      = [8 pi^2 (f,f) / sqrt(|D_w h_*|)]
        * hhat_K(P_(D_w)) / deg(phi).

Here the possible 2^(-mu) and u^(-2) factors are 1 under the checked coprimality and unit hypotheses. In particular every displayed scalar is nonzero.

Induction of the genus character gives chi_Dw plus chi_h*. Consequently the full Rankin L-function, including the finite Euler factors, is

    L(s,E,chi) = L(E^(D_w),s) L(E^(h_*),s).

Its derivative at 1 is the product of the nonzero simple derivative and the nonzero central value fixed in section 1. The height formula therefore makes the actual P_(D_w) nontorsion. It is not being inferred merely from the dimension of a Selmer group or from the existence of some rational point. We use Theorem 1.1, not the BSD formula labeled "Conjecture" immediately after it in the primary paper.

The point lies in E(F), where F=Q(sqrt(D_w),sqrt(h_*)). The Galois action on the unaveraged class sum is the genus character. Thus its rational representation components over this biquadratic field are the D_w and h_* twist components. Kolyvagin's Theorem 1 in MPI/90-69, printed page 4, gives rank zero for E^(h_*) because its analytic rank is zero. Its modularity hypothesis is satisfied. That theorem is about the whole Mordell–Weil group and finite Sha; it carries no restriction to odd primary torsion. Only its rank-zero conclusion is needed here.

Choose the same uniform integer L which kills the relevant torsion and clears the biquadratic projections. Its choice depends only on the fixed curve, parametrization and fixed setup, not on D_w; it can be made before the witness is selected. The uniform degree-at-most-four torsion bound and the fixed cuspidal factors were proved in the sealed T2 report, section 2. The h_* component of L P_(D_w) is then zero, and L P_(D_w) is an exact D_w-eigenpoint. Under the fixed quadratic twist isomorphism it is one nontorsion point

    Q in A(Q),    A=E^(D_w).

All these objects, including L, are fixed before any detecting prime or precision. There is no new conductor-|h| ring-class point in this argument.

## 3. Non-CM open image gives the required integral Kummer translations

For the actual pole curve the invariant is j=35152/9. It is not an integer, whereas a rational CM j-invariant is an algebraic integer. Thus E and its quadratic twist A are non-CM. Serre, "Proprietes galoisiennes des points d'ordre fini des courbes elliptiques", printed pages 259–260, states that for a non-CM elliptic curve over a number field the adelic image is open; in particular each ell-adic image is open. This explicitly includes the 2-adic component. It does not require E[2] to be irreducible or the mod-2 image to be all of GL_2(F_2).

Set T=T_2A, V=T tensor Q_2, and J=rho_A(G_Q). Openness gives an integer n for which 1+2^n M_2(Z_2) is contained in J. Hence V is irreducible and J contains a central scalar z=1+2^n distinct from 1.

Choose a compatible system of 2-power division points of Q and let c_Q:G_Q->T be its continuous Kummer cocycle. On H=ker(rho_A), it is a homomorphism. Its image is a closed Z_2-submodule of T, since H is compact. The conjugation formula makes its rational span J-stable.

Suppose that span were zero. Then c_Q is zero on H, so it descends continuously to J. For every g in J, equality of the two cocycle evaluations at zg=gz yields

    (z-1)c_Q(g) = (g-1)c_Q(z).

Since z-1 is invertible over Q_2, the descended rational cocycle is a coboundary. This contradicts Kummer injectivity for a nontorsion point of the finitely generated group A(Q). Explicitly, a rational coboundary has a bounded denominator; after multiplying by one power of 2 it would make the integral Kummer class zero, so a nonzero multiple of Q would be divisible by every 2^m in A(Q). Mordell–Weil excludes that for a nontorsion point.

Irreducibility therefore makes the span all of V. The closed image contains 2^a T for some finite a. If H is intersected with the kernel of any FIXED finite Galois data, its image still contains a full lattice: take a finite-index normal subgroup H_0 and an exponent e of H/H_0; then e*c_Q(H) is contained in c_Q(H_0). This argument is integral and uses no index bound uniform over all possible new finite extensions.

## 4. One actual lift supplies all advanced stages

Fix an actual complex conjugation tau. Because D_w is positive, the twist identification makes rho_A(tau)=rho_E(tau)=C. The two eigenspaces over Q_2 have signs + and -. Choose one nonzero integral covector b with bC=b. It need not be a unit vector or come from an integral eigenspace splitting.

Let F_0/Q be any fixed finite Galois extension whose required additional actions agree with tau. Include Q(sqrt(D_w)) and Q(sqrt(h_*)) in F_0. Take H_0=ker(rho_A) intersect G_(F_0), and choose h in H_0 with v=c_Q(h) such that b(v) is nonzero. This is possible by the full-lattice result. Put sigma=h*tau. Then

    rho_A(sigma)=C,
    sigma|F_0=tau|F_0,
    c_Q(sigma^2)=(1+C)v,
    b(c_Q(sigma^2))=2 b(v) != 0.                            (U1)

The cocycle of tau itself cancels because tau^2=1. Define c_w=v2(2b(v)). It is one finite constant, fixed with Q,b,F_0 and h before varying M. Since sigma fixes sqrt(D_w), its action on T_2E is also C. It negates sqrt(h_*).

For every M>c_w, form the finite Galois quotient cut out by rho_A modulo 2^M, the division cocycle c_Q modulo 2^M, and F_0. The semidirect-product representation of the actual division points gives this quotient; it is not an abstract proposed Frobenius table. The image of sigma is one element of it. Chebotarev supplies infinitely many rational primes in its conjugacy class. A compatible prime above each rational prime represents that exact element. Avoid all bad primes, 2, the fixed support, D_w, h_*, and any further finite set of forbidden rational primes.

It follows that at each such prime ell,

    rho_E(Fr_ell)=C mod 2^M,
    (D_w/ell)=1,   (h_*/ell)=-1,
    b c_Q(Fr_ell^2)=2b(v) mod 2^M.                          (U2)

The determinant gives ell=-1 modulo 2^M. Good reduction identifies the prime-to-ell torsion and the division-point Frobenius with their specializations. The same chosen place must be used for these identifications, for reduction of the genus point and for the covector b; conjugating only one of these would be an invalid comparison.

For this fixed M, finite-field Kummer theory gives

    E(F_(ell^2))/2^M E(F_(ell^2))
       ~= T_2E / (2^M T_2E + (Fr_ell^2-1)T_2E)
       =  T_2E/2^M T_2E.

One can see the required H^1(F_(ell^2),E)=0 directly from surjectivity of the nonzero isogeny Fr_ell^2-1 on E over the algebraic closure. The integral row b therefore defines the actual map lambda_M used in T2. It has Frobenius sign +1 because b rho_E(Fr_ell)=b modulo 2^M. Equation (U2) and specialization of the division points give

    v2(lambda_M(red_ell(L P_(D_w)))) = c_w,

where exact valuation means that of a nonzero residue modulo 2^M, with c_w<M.

This proves more than the needed unbounded subsequence: for every sufficiently large M there are infinitely many suitable primes. One may choose a sequence with both M and ell increasing. Excluding a later fixed finite set of rational primes does not alter c_w, because it only discards Chebotarev primes. In particular, the later requirement that the theta prime avoid the chosen companion's ramified primes causes no new Kummer denominator.

There is no claim that c_w is uniform when F_0 itself is replaced by an arbitrary growing extension, or that arbitrary unrelated Frobenius actions can be imposed. If extra nontrivial actions are requested, a common lift compatible with C and the fixed quadratic actions must be supplied. The actual construction needs only the already fixed conjugation-compatible data and subsequent finite prime exclusions. Its graph primes being split in a companion field is a separate condition on separate primes; no unsupported splitting requirement on the theta prime is inserted.

## 5. The same coefficients detect the native point index

This paragraph supplies the all-D interface used before the odd minimum. It does not assume a uniform lower bound for that index.

For a simple-zero admissible D, put A_D=E^(D) and K_D=Q(sqrt(Dh_*)). The genus-character transformation of P_D identifies it with a point P_D^nat in A_D(K_D). The rational rank of A_D is one by the forward rank theorem, and its quadratic companion over K_D is E^(h_*), of rank zero. Thus A_D(K_D) modulo torsion is a rank-one free group. If G_D is a generator, write

    P_D^nat = m_D G_D + T_D,     j_nat(D)=v2(m_D).

Under the twist isomorphism all these torsion points lie on the fixed E over a field of degree at most four. The same fixed L from T2 kills T_D for every D. Consequently L P_D^nat=m_D(LG_D) is an exact equality of points, without a torsion error.

At a stage where D is admissible, (D/ell)=1 and (h_*/ell)=-1. Therefore K_D is inert at ell and the whole biquadratic field has residue degree two. The twist isomorphism and reduction carry LG_D into E(F_(ell^2)). Both reduction and lambda_M are integral homomorphisms. Hence

    v2(lambda_M(red_ell(LP_D))) >= min(M,j_nat(D)).

The nonzero c0*2^omega(N) factor in (T2.2) only improves divisibility, and its root-of-unity factor is a unit. We obtain

    v2(a_M(D)) >= min(M,j_nat(D)).                            (U3)

This uses the actual native point and the same L, not a point selected from a rank-one vector space after specialization.

To compare index conventions, conjugation acts trivially on the native free group, since the other rational twist component has rank zero. The norm of a native point is rational and is twice its class modulo torsion. Thus the image of A_D(Q)/tors in A_D(K_D)/tors has index dividing 2. Passing between these lattices and a fixed scalar normalization of the point changes the index valuation by a fixed bounded amount. Let C_det cover exactly those retained conventions. Then (U3) implies the source's form

    v2(a_M(D)) >= min(M,j_gen(D)-C_det),
    v2(a_M(D))<M  =>  j_gen(D)<=v2(a_M(D))+C_det.              (U4)

The second inequality is the contrapositive content of the first once the valuation is below M; it asserts no upper bound on arbitrary Kummer images.

For every admissible D on the odd-sign filter, the same primary height formula gives that P_D is torsion if the product derivative vanishes. Since the fixed partner has nonzero central value, and the root number of E^(D) is -1, a nonsimple odd D has zero product derivative. The uniform L then kills P_D, and (T2.2) gives a_M(D)=0 modulo 2^M. Conversely a visible coefficient is incompatible with torsion, so that height formula forces a nonzero derivative of E^(D), hence a simple zero.

Thus (U4), visibility implies simple zero, and the fixed-witness upper bound are all supplied by the same actual forms. The separate R/even-coefficient estimate gives a lower bound for j_gen(D) afterward; it is not an assumption in (U3) or (U4).

## 6. Passing this input into the sealed T2 construction

The choices are now in the required order:

    E, phi, original filter and fixed support;
    h_*, the enlarged support and the uniform L;
    D_w, the rational twist point Q and b;
    fixed compatible finite data, h, sigma and c_w;
    arbitrary advanced M and actual Chebotarev primes ell;
    the actual weighted-theta form at that stage.

The sealed T2 identity gives

    a_M(D_w)
      = c0 2^omega(N) zeta_M(D_w)
        lambda_M(red_ell(LP_(D_w))) mod 2^M O_coef.

All its constants and its coefficient field have already been fixed. Once M>c_w+v2(c0)+omega(N), this coefficient is nonzero with exactly that valuation. Thus the same fixed witness remains visible throughout the retained advanced stages. The denominator bound does not depend on D_w's later reuse, M, ell, a graph size, or determinant precision.

This proves nonemptiness and a fixed upper bound for the visible odd coefficients. The numerical lower-index estimate in terms of omega(D) and Sha is a different input, obtained from the R/even-coefficient argument before taking the odd minimum. It is not proved by BFH or by this one witness, and it has not been smuggled into the present closure.

## 7. Primary checks and preserved scope

Fresh checks made for this addendum:

* Dokchitser–Dokchitser Theorem 1.8 and the definition of its Selmer rank were read in the primary paper. The actual rational 2-torsion point discharges its isogeny hypothesis.
* Desjardins Proposition 3.3 was read in the primary text for the optional signed-unit reduction. At 2 and 3 the proof uses local isomorphism, not that proposition.
* The original BFH pages 543–544 were rendered and inspected. Both clauses, the trivial-character/even-weight condition and the arbitrary finite splitting set were read directly.
* The original Serre pages 259–260 were rendered and inspected. The non-CM assumption and the all-primes open-image statement were read directly.
* Cai–Shu–Tian Theorem 1.1 and all its preceding Heegner hypotheses were read in the primary PDF. The actual unaveraged elliptic-curve point and degree of the fixed parametrization match the consumer.
* Kolyvagin MPI/90-69, Theorem 1 on printed page 4, was read in the primary paper. Its modularity and analytic-rank-at-most-one hypotheses apply to the fixed rank-zero partner. The stronger conclusions on Sha are not needed here.
* The fixed-witness and finite-stage formulas were compared with CO140–252 and with the sealed T2 report. The old Point2 report is navigation and an earlier argument, not a substitute for these primary checks.

The remaining external foundations used literally are modularity of elliptic curves over Q, Mordell–Weil, the integrality of CM j-invariants, CRT/Dirichlet for the optional general unit filter, and Chebotarev for the actual finite Galois quotients. No reverse Gross–Zagier implication, Selmer converse, BSD leading-term equality, residual irreducibility, or uniform conductor-independent index of all Kummer images is assumed.

Within this actual non-CM T2 family, the upstream witness/Kummer input is supplied. This does not extend the raw source's optional general CM formulation. All sealed reports and delivered drafts remain unchanged.
