# Independent whole-chain height review

Reviewed source: `outputs/diophantine-zq-fable-followup-2026-11-04.tex`.

SHA256: `3f0b79f3d4a074a47ca8165f1d6075f167e51f0d764b774a294cdb8c04e56aa8`.

The hash was checked twice during this review. Line references below refer to that exact file. The scope is the six-contact theorem, lines 363–875, including its geometric premises and the interface to the unchanged cutoff. I did not assume the author's checks or another reviewer's acceptance. No manuscript was edited.

## Verdict

No material mathematical defect found in this whole-chain review. The replacement establishes the stated H6 bound using the cited published results and standard Galois-cohomological, reduction, and comparison theorems. In particular, I found no first unsupported inference that would require changing the theorem or its constants. This is an independent informal review, not a formal verification or a review of the remaining main theorem.

Two compressed transitions would benefit from explicit explanations: potential semistability in the application of Pan, and the Herbrand conversion in the dyadic conductor estimate. Both have repairs within the existing argument and constants; details appear below. They are not counterexamples to the proof.

## Geometric input and field of moduli

Lines 397–461 use the specified maximal order and principal polarization. Buzzard's theorem is invoked first at the permitted auxiliary level five, not incorrectly at the discriminant prime three. Adding full markings is finite étale over Z[1/30]. The three-marking eliminates stabilizers because a finite-order automorphism congruent to one modulo three is trivial. Thus quotienting by changes of five-marking descends the universal family and does not multiply the degree of the final three-level cover. Buzzard, Theorem 2.1 and Corollary 2.3, provide the proper smooth representable starting model. [Primary source](https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf).

Lines 463–513 give a workable tame extension argument. The component genus is at least two, so uniqueness of the stable model extends automorphisms. For residue characteristic greater than 324, the acting group order is invertible. Cyclic stabilizers and their faithful tangent characters prevent collisions or new branch sections. The normalized pullback retains degree at most 324, and its only residual ramification has index two over the six contacts. Properness of the original moduli model is enough to extend a K-valued point and obtain good reduction of A over K outside S, even when K itself ramifies at a contact prime.

I independently checked the polynomial identity G^6−97200F^2=H^2. The discriminants of F, G, H and their pairwise resultants have no prime factors outside {2,3,5}. Leading coefficients add only 7,11,13. This verifies the claimed exclusion of primes greater than 324. Exact results are in `arithmetic.json`.

Lines 515–525 genuinely establish geometric isomorphism of the conjugates, not merely isogeny. Baba–Granath §2.1, Theorem 1, identifies V_Z with V/W; §3.2 supplies the displayed Igusa invariants. Their definition of the equivalence relation is polarized isomorphism after forgetting the O-label. Since J(u) is finite, nonzero and rational, the displayed weighted moduli point is rational. Consequently every Galois conjugate of A is geometrically isomorphic to A. This does not claim a Q-model of A and does not suppress a field-of-moduli obstruction. [Primary source](https://webdoc.sub.gwdg.de/ebook/serien/e/mpi_mathematik/2005/18.pdf).

Lines 527–545 correctly use Res(K/Q)A to put the Hom groups into a single genuine integral Galois module. Its rank bound is 16[K:Q]^2. The finite action injects modulo three; adjoining its kernel field to K gives degree at most D. At primes outside T, unramifiedness of K and good reduction of its conjugate factors make inertia trivial on this module. The resulting L defines the actual conjugacy Hom groups needed next.

## Scalar descent and modularity

Lines 547–553 split the geometric endomorphism algebra into the two required cases. The centralizer of the complex structure in the right quaternion factor is Q or an imaginary quadratic field. In the second case that field splits B, giving M2(k).

In the non-CM case, lines 608–635 legitimately apply Skolem–Noether to correct each geometric isomorphism to a B-linear quasi-isogeny and then clear denominators over L. The discrepancy is in the center of End^0(A)=B, hence Q*. Normalizing by the positive fourth root of degree changes it into a sign. Algebraic coefficients here are constant coefficient scalars, not scalars acted on cyclotomically. This convention is also explicit in the later cohomology sequence.

Lines 637–680 give an actual finite-image cochain splitting with controlled ramification. For Q_p*, a finite character admits a finite-character square root exactly when it is trivial on the element of order two, −1. The free valuation factor and Z_p factors pose no obstruction. The chosen odd local Dirichlet factors therefore prescribe precisely the nonzero finite Brauer invariants. Global Brauer reciprocity determines the real invariant and injectivity determines the class. The resulting beta has values in mu_(2m); its restriction to G_L is a conjugacy-invariant character because epsilon is inflated from Gal(L/Q). Quadratic twisting removes the finitely many unwanted odd inertia characters without changing delta(beta) or beta^2. These are standard consequences of local reciprocity and the global Brauer exact sequence. [Milne, Arithmetic duality theorems, Chapter I](https://www.jmilne.org/math/Books/ADTnot.pdf).

Thus lines 682–688 bound the splitting field L' by 2md ≤ QM. No degree of the coefficient field or size of the chosen quasi-isogenies is inserted into this bound.

Lines 690–728 obtain a two-dimensional representation after splitting B. The restricted commutant is scalar and the representation is semisimple, so it is absolutely irreducible. The Hodge summands each carry the simple two-dimensional B_C-module. Complex conjugation followed by the holomorphic quasi-isogeny exchanges them, so it acts nonscalarly on the multiplicity space. As its square is one, the multiplicity eigenvalues are 1 and −1. This proves oddness independently of residual image assumptions.

Pan's Theorem 1.0.4 imposes its additional residual restriction only at p=3, so coefficient prime five is permitted. Its cited Conjecture 1.0.1 formulates the geometric hypothesis as potential semistability. The manuscript says de Rham. For complete citation hygiene, add either the p-adic monodromy theorem (de Rham implies potentially semistable), or directly invoke semistable reduction and the semistable comparison theorem after extending L'. This is available for the actual Tate module over L', and potential semistability is unchanged by finite extension. The representation's weights then give weight two, with finite twist absorbed into the eigenform. [Pan, Theorem 1.0.4 and Conjecture 1.0.1](https://arxiv.org/pdf/1901.07166v2).

Lines 730–739 compare the same endomorphism of the reduction, namely a conjugacy isogeny composed with relative Frobenius. Its trace is independent of the Tate prime. The fixed algebraic factors a_sigma and beta give a common algebraic trace system. Semisimplicity and Chebotarev then justify using the three-adic member at residue prime five.

## Conductor interface

Lines 741–784 have sufficient room for their asserted local bounds. To make the dyadic step at lines 769–771 explicit, put F=L_v. Its largest positive absolute upper break is at most 4D^2 by the preceding normal-closure estimate. Above this break, the absolute upper group lies in G_F. The subgroup formula sends upper index u to psi_(F/Q_2)(u), and psi(u) ≥ u for u ≥ 0. The character beta restricted to G_F is trivial above relative index 3e. Therefore it is trivial for absolute u greater than max(4D^2,3e), which is at most U0. No extra factor D or new exponent of M is needed. For the Tate module, the same argument applies after adjoining torsion and passing to the normal closure; semistability kills wild inertia. The degree bound DG0 therefore gives U0=4(DG0)^2 as written.

At primes p>R, good reduction and the tame degree bound for L_v/Q_p kill wild inertia outright. The two-dimensional conductor exponent is consequently at most two. Combining this with the small-prime exponent E0 gives exactly N≤QM^2. I found no hidden dependence on [L':Q] multiplying the conductor exponent.

## Transfer to a modular Jacobian and heights

Lines 787–794 do not require A to descend to Q or have GL2-type over Q. Over L', its Tate module and that of J1(N) share a constituent. Invariants in a finite-dimensional Hom space commute with extension of coefficient fields: this follows by expressing invariants as the kernel of finitely many linear constraints. Thus a nonzero intertwiner exists over Q_l. Faltings' Hom theorem gives a nonzero L'-homomorphism A→J. Absolute simplicity makes its kernel finite, and Poincaré reducibility supplies the complementary factor Z over L'. An isogeny A×Z→J is precisely the input needed by Gaudron–Rémond.

Javanpeykar's Theorem 1.1.1 gives 13·10^6 g deg_B(X)^5; g,deg_B(X)≤N^2 yields 13·10^6 N^12. Section 2.3 identifies this with the stable height of the Jacobian, and §2.1 uses the original Faltings metric i/2 on differentials. The normalization at lines 799–803 is therefore correct. [Primary source](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf).

Gaudron–Rémond define their bound using original stable Faltings height, exponent 1024g^3, and factor (14g)^(64g^2). Theorem 1.4 gives both isogeny directions, so the application with source J at lines 805–811 is permitted. Their §9 also records the lower bound h_F(Z)≥−3 dim(Z)/2. Consequently the complement cannot conceal an unbounded negative height. [Primary source](https://lmbp.uca.fr/~gaudron/art13.pdf).

The arithmetic in lines 813–831 checks independently. The logarithmic bounds 5QM^4, 2QM^4, 19QM^4 lead to 1024(320+40)Q^16 M^24=368640Q^16 M^24. For Q≥10^12 this is ≤Q^17M^24. Finally Q^13+(1/2)Q^17+2Q^3≤Q^17. The CM side uses source E^2 over the original L, so the auxiliary field for good reduction does not enlarge the isogeny bound. Its stated constants fit the same maximum.

Lines 843–856 use Pazuki's r=2 coordinates correctly: §2.3 has all sixteen half-characteristic theta values, and the six odd values vanish. His metric differs by the factor pi^(−g) in the squared norm, so for g=2 his height is h_F+log(pi), as used here. Corollary 1.3(2) then gives the stated loose linear bound. [Primary source](https://www.numdam.org/item/10.24033/bsmf.2623.pdf).

## Exact H6 and downstream numerical interface

The rational-root argument at lines 858–863 controls both numerator and denominator after deleting an initial zero power. I checked the coefficient norm bound independently. The final theta constant is exactly 6,710,886,400,096, less than 10^13. Hence lines 869–871 prove H6/2 and therefore the advertised H6 without spending its remaining factor two.

Lines 877–880 preserve the distinction between S_ht and S_mul. Lines 5961–5963 use exactly the same H6 formula with a common permitted R. With R=D and Q_D^17 dominating C_cm, the cutoff exponent is 13·17·10=2210, yielding the exact displayed identity at line 5971. The replacement introduces no new parameter into that cutoff. This checks the interface and arithmetic; it is not an independent audit of the separate prime-catalogue or formal-group construction used to show R=D.

No correction to H6, its exponent 24, or the literal cutoff is required by this review.
