# Fifth closure pass: global cohomology and the two generator bounds

Review date: 2026-11-05. Reviewer: root assistant. This checks A042, A073 and A074 at the fixed working manuscript SHA256 `fa03c67c7944054314b941f6c4e99d0116d08e0f438d6da331c3a7e120e4755a`. It is a direct review of these applications, not an independent second review or acceptance of the restricted converse. No manuscript formula needs correction for these three applications.

## A042: the global Euler characteristic

Source: Milne, *Arithmetic Duality Theorems*, second edition, 2006, I Theorem 4.10(c), printed p.57; Corollaries 4.15 and 4.16, printed p.62; Theorem 5.1 and footnote 13, printed p.67. The PDF is the exact file in the source register. The theorem on p.57 and the formula and footnote on p.67 were checked visually. The support hypotheses preceding Theorem 5.1 require a finite nonempty set containing the archimedean places and a finite module whose order is invertible in the ring of S-integers.

The manuscript's S_0 specifies finite places. For this application use S=S_0 union the archimedean places of K. Adding the complex place does not change its Galois group. Every place above 2 belongs to S_0. Thus W=E[2], of order 4, has order invertible in O_{K,S}. Full rational 2-torsion identifies W with the direct sum of two trivial F_2 modules; this is an identification of Galois modules, not just vector spaces. The field K is imaginary quadratic, so it has one complex place and no real places.

Corollary 4.15 gives finiteness in all degrees. The map in Theorem 4.10(c) is the restriction map to the product over real places. For degrees at least 3 its target is zero here, so the global groups vanish. This application only needs vanishing for W; it does not infer cohomological dimension from a generator count.

There are two conventions that change the numerical answer if misread. In Theorem 5.1 the archimedean numerator is ordinary H^0, not Tate-modified H^0. At a complex place the normalized absolute value is the square of the usual absolute value. Milne's footnote 13 explicitly warns about both. Consequently the one archimedean factor for W is

    #H^0(C,W) / |#W|_C = 4 / 4^2 = 1/4.

Taking base-two logarithms gives h^0-h^1+h^2=-2. Since h^0=2, this yields h^2=h^1-4 and total cohomology dimension 2h^1-2. Thus the primary bound h^1<=4s gives at most 8s-2; the alternative bound h^1<=4s+2 gives at most 8s+2. Both numbers in the manuscript have the correct signs and factors of two.

This result supplies only the global contribution to the finite-model size estimate. It does not by itself check the local cone ranks, their comparison maps, or the later limit construction.

## A073: S-units, Kummer theory and the genus estimate

Sources: Milne, *Class Field Theory*, v4.03, 2020, II Proposition 1.22 and Corollary 1.23, printed p.67; VII Appendix A, Propositions A.1-A.2 and Theorem A.3, printed p.226, and Proposition A.5, printed p.227. For units and finiteness use Milne, *Algebraic Number Theory*, v3.08, 2020, Theorems 4.3-4.4, printed p.70, Theorem 5.1, and Theorem 5.11 with the preceding description of torsion, printed p.90. Both notes are byte-pinned in the source register. The pages for Kummer theory, class-group finiteness and S-units were checked visually. These are author course notes, not research articles; their publication status is not upgraded by this review.

The following verifies the exact sequence and its maps rather than citing Kummer theory without specifying the S-condition. Let S_T be the finite primes of K over T, with all dyadic primes included. A squareclass a in K^*/K^{*2} defines the character

    sigma |-> sigma(sqrt(a))/sqrt(a) in mu_2 = F_2.

At an odd prime outside S_T it is unramified exactly when v(a) is even. Necessity follows because an odd valuation of a would force a half-integral valuation of sqrt(a) in an unramified extension. For sufficiency remove an even power of a local uniformizer; the remaining unit has a square root in an unramified extension by the separable residue polynomial and Hensel lifting. There is no condition to impose at dyadic primes, since they are in S_T. Thus H^1(G_{K,S_T},F_2) is precisely the group of these even-outside-S_T squareclasses.

Work with fractional ideals of the Dedekind ring R=O_{K,S_T}. For an allowed class a, define I(a) by the valuations v(I(a))=v(a)/2 at primes outside S_T. Then I(a)^2=aR, and a maps to [I(a)] in Cl(R)[2]. Replacing a by ab^2 replaces I(a) by bI(a), so the map is well-defined. If I(a)=bR, then a/b^2 is an R-unit. Conversely units have trivial image. An R-unit that is a square in K is a square in R^*, because all its valuations outside S_T vanish. Finally, if [I] has order dividing two, I^2=aR for some a and that a maps back to [I]. This proves the exact sequence, including injectivity and surjectivity,

    0 -> R^*/R^{*2} -> H^1(G_{K,S_T},F_2) -> Cl(R)[2] -> 0.

For imaginary quadratic K, the S-unit rank is |S_T|. The torsion is the finite cyclic group of roots of unity and has even order. Its quotient by squares has dimension one, including the possible extra roots of unity in Q(i) and Q(sqrt(-3)). Therefore the unit contribution is 1+|S_T|.

Here is a check of the genus argument used in the manuscript. Conjugation acts by inversion on the ordinary ideal class group: a times bar(a) is rational principal. If [a] has order dividing two, choose alpha with bar(a)=(alpha)a. Conjugating once more shows that the rational number alpha bar(alpha) generates the unit ideal. It is positive because K is imaginary, so it is 1, not -1. With beta=1+alpha when alpha!=-1, or beta=sqrt(d) when alpha=-1, one has alpha=beta/bar(beta). Thus the ideal beta a is fixed by conjugation. This is the explicit quadratic instance of the cited Hilbert 90 result; the orientation of beta/bar(beta) is verified directly.

A conjugation-invariant fractional ideal is, modulo rational principal ideals, a product of ramified prime ideals. At a split prime the two exponents agree and their product is rational principal; an inert prime ideal is already rational principal; and at a ramified prime the square of the prime ideal is rational principal. If r denotes the number of ramified rational primes, Cl(K)[2] is therefore generated by at most r classes. The ideal of sqrt(d), with d the squarefree radicand, gives a nonzero relation among them whenever d!=-1: each prime dividing d has exponent one in this relation. When d is odd, an additional ramified prime at 2 may have exponent zero in that particular relation, which is harmless. The relation remains nonzero because d has an odd prime divisor. When d is even, the dyadic exponent is one. For d=-1 the class group is trivial by the Minkowski bound. Hence dim Cl(K)[2]<=r-1 in all cases at issue.

The S-class group is a quotient of the finite ordinary class group, but its 2-torsion need not be a quotient of the ordinary 2-torsion. The valid argument uses A/2A: for a finite abelian group, dim A[2]=dim A/2A, and A -> B surjective implies A/2A -> B/2B surjective. Thus dim Cl(R)[2]<=dim Cl(K)[2]. This is the rank inequality actually needed.

Since T includes every ramified rational prime, |S_T|<=2s-r. The exact sequence now gives

    dim H^1(G_{K,S_T},F_2) <= 1+(2s-r)+(r-1) = 2s.

Allowing ramification at S_T instead of S_0 gives a surjection of Galois groups G_{K,S_T} -> G_{K,S_0}. Pullback of characters is injective. Doubling for W=F_2^2 gives h^1(G_{K,S_0},W)<=4s, as used in A042. The only dependence on the ramified-prime count cancels before the later bound is formed.

## A074: a direct proof of the optional generator bound

The Kummer identification above and the explicit rational squareclasses in Milne CFT VII Example A.4(b), printed p.227, supply the arithmetic input. The needed group-theoretic assertion is proved here in its exact index-two form. No claim of freeness of a Galois group is used, and no unattached reference to a general Schreier theorem is needed for this calculation.

Let G be a pro-2 group with finite d=dim Hom_cont(G,F_2). Put Phi equal to the closed subgroup generated by commutators and squares. Continuous characters separate points in the elementary abelian profinite quotient G/Phi; hence that quotient is the finite group F_2^d. Choose lifts x_1,...,x_d of a basis. They topologically generate G. Indeed, if their closed generated subgroup were proper, some finite 2-group quotient would have a proper image of that subgroup. A maximal subgroup containing that image has index two. Its quotient character would be nonzero and vanish on all the x_i, contradicting the basis property. The finite-group assertion follows, for example, by induction using a central subgroup of order two: a maximal subgroup either omits that subgroup and has index two, or reduces to a maximal subgroup of the quotient. This also shows that such a maximal subgroup is normal.

Let H be an open subgroup of index two in G. After rearranging the generators, take x=x_1 outside H. Replace every other outside generator x_i by x_i x^{-1}; all remaining generators y_2,...,y_d now lie in H, and x,y_2,...,y_d still topologically generate G. The subgroup H is topologically generated by

    x^2, y_2,...,y_d, x y_2 x^{-1},...,x y_d x^{-1}.

To check this without assuming that G is free, take a word in x and the y_i whose total x-exponent is even. Move the x-letters to the right. The result is a product of conjugates x^k y_i^{+/-1} x^{-k}, followed by an even power of x. Even k uses powers of x^2 to conjugate y_i; odd k uses powers of x^2 to conjugate x y_i x^{-1}. Thus every such word lies in the subgroup generated by the displayed 2d-1 elements. Words in the topological generators are dense in G, and H is open; words of the required parity are therefore dense in H. Taking closure proves the bound d(H)<=2d-1.

Now let L/Q be the maximal pro-2 extension unramified outside T and infinity. The quadratic characters are exactly the independent squareclasses -1 and p for p in T. All dyadic ramification is permitted because 2 belongs to T. Consequently G=Gal(L/Q) has d=s+1. Since T contains the ramified primes of K/Q, the quadratic field K lies in L. Its subgroup H=Gal(L/K) has index two and d(H)<=2s+1.

The maximal pro-2 extension of K unramified outside S_0 lies in L. For a finite Galois 2-extension M/K in it, compose M with its conjugate under K/Q. That compositum is Galois over Q and is a 2-extension: its Galois group over K embeds in the product of the two 2-groups, and the quotient over Q has order two. It is unramified outside T and infinity, since S_0 lies over T and K/Q is unramified outside T. Passing to the union proves the containment. Thus the relevant pro-2 group over K is a quotient of H. Characters with values F_2 factor through that pro-2 quotient, so

    h^1(G_{K,S_0},W) <= 2(2s+1) = 4s+2.

Combined with A042, this gives the manuscript's alternative total dimension bound 8s+2. It is a bound on generators, not a presentation or a bound on H^2 without the Euler-characteristic theorem.

## Consequence for the finite-model audit

These checks provide finite bounded residual global cohomology over K, which is a hypothesis of the finite-model construction, not its conclusion. Over Q or the totally real cyclotomic layers, ordinary global 2-cohomology need not be bounded. For the positive complex one must instead use the fiber of restriction to ordinary real cochains. Theorem 4.10(c) cancels the high-degree groups, and Corollary 4.16 makes degree-two restriction onto the real terms surjective because a finite dyadic prime remains available. These source facts support that separate audit. They do not close A075 or A076, which also concern comparison maps, local conditions, contractions and simultaneous limits.

Disposition: A042, A073 and A074 are closed for these specific applications and direct translations. A075 and A076 remain open. No whole-proof acceptance or publication is claimed.
