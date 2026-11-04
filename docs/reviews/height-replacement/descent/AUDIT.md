Independent review of the non-CM descent and modularity argument

Reviewed on 2026-11-04. The frozen source is `outputs/diophantine-zq-fable-followup-2026-11-04.tex`, SHA256 `3f0b79f3d4a074a47ca8165f1d6075f167e51f0d764b774a294cdb8c04e56aa8`. Line numbers below refer to that file. I read the surrounding geometric construction, lines 397–553, and the current argument, lines 608–800. The earlier author report was used to identify claims, not as evidence that they hold. No manuscript edits were made.

My verdict is that I found no substantive mathematical obstruction in the assigned descent, oddness, modularity, compatible-representation, and Jacobian-transfer steps, conditional on the geometric premises listed below. There is an omitted published-theorem bridge between de Rhamness and Pan's potentially semistable hypothesis, and several passages would benefit from explicit conventions and short proofs. The proposed additions below are NOT present in the frozen source and are not counted as if they were. This review does not certify the geometric construction, the numerical conductor bound, the CM argument, or the final height inequality.

The premises used here are that A/L is an abelian surface; L/Q is finite Galois of degree at most D and unramified outside T; A has good reduction outside S; every geometric endomorphism and conjugacy Hom is defined over L; all conjugates are geometrically isomorphic; and the non-CM case has End^0(A_Qbar)=B, the quaternion division algebra of discriminant six. These are claimed at lines 507–553. The assumption 2 in T, needed for the quadratic ramification cleanup, follows from lines 369–370. Their mathematical validity belongs to the separate geometric review. An isogeny to every conjugate would in fact suffice in place of isomorphism for the descent below.

1. B-linear conjugacy isogenies and the sign cocycle, lines 608–635: valid given those premises.

   Conjugation by an initial isomorphism identifies the two copies of the full endomorphism algebra and gives a Q-algebra automorphism of B. Skolem–Noether makes it inner. Correcting by the inverse inner element and multiplying by a nonzero integer produces the stated B-linear isogeny. Its discrepancy lies in End^0(A), and centralizing B inside B forces it into Q*. This is not a claim about centralizing B inside all Q-linear endomorphisms of homology, where the commutant would be larger.

   The degree calculation is exact for quasi-isogenies: if c is that rational scalar, then

   `deg(mu_sigma) deg(mu_tau) / deg(mu_sigma_tau) = c^4`.

   Consequently the normalized discrepancy is c/|c|. Associativity gives the cocycle identity. Galois acts on morphisms and trivially on the added coefficient scalars; with that convention the a_sigma terms form an ordinary coboundary. The source already calls the modules in lines 654–656 constant, but should state the same convention at lines 624–630 and 691–696. Treating the a_sigma as numbers on which G_Q acts naturally would give a different, incorrect computation.

   Independent context: Ribet's original Q-curve construction uses a scalar cocycle and coefficient-field extension in section 6, especially Theorem 6.3. The current controlled sign construction does more than merely invoke that existence theorem. [Ribet, Abelian varieties over Q and modular forms](https://math.berkeley.edu/~ribet/Articles/korea.pdf).

2. Controlled splitting of the sign class, lines 637–680: valid.

   At p outside T, inertia has trivial image in Gal(L/Q). The restricted class therefore inflates from the procyclic unramified quotient, whose second cohomology with these finite torsion coefficients vanishes. The passage to Br(Q)[2] is legitimate because the constant module {+1,-1} is also the usual Galois module mu_2; this does not assert that constant mu_infinity is the usual roots-of-unity module.

   I checked the local square-root assertion directly. For odd p, Q_p* is p^Z times mu_(p-1) times Z_p; for p=2 it is 2^Z times {+1,-1} times Z_2. A finite character has a finite character square root on the valuation and procyclic factors. On the even finite cyclic torsion factor, its exponent must be even, exactly the condition that its value at -1 is 1. Thus the local boundary is nonzero precisely at the chosen primes T_-. Other Dirichlet factors are unramified there and do not change this value on the local unit -1.

   The finite local invariants determine the real invariant by their sum, and the global Brauer map is injective. These are the local/global class-field-theoretic inputs to the equality of classes, consistent with the cited Chapter I. [Milne, Arithmetic duality theorems, Chapter I](https://math.stanford.edu/~conrad/BSDseminar/refs/MilneADT.pdf). The elementary calculations in this paragraph and the preceding paragraph are my checks of their application, not a claim that Milne states this exact construction.

   If b is a pointwise root of chi, its values lie in mu_(2m). Equality of the two H^2 classes supplies a continuous sign cochain t with delta(t)=epsilon/delta(b). Then beta=bt has both required identities. This does not require the cocycle to split on Gal(L/Q).

   For n in G_L, normalized inflation gives epsilon(g,n)=epsilon(n,g)=1. Hence beta(gn)=beta(g)beta(n), and comparing gn with (gng^-1)g proves conjugacy invariance of beta restricted to G_L. Outside T, inertia lies in G_L and beta is quadratic there. A continuous finite-valued cochain factors through a finite quotient, so only finitely many inertia restrictions are nontrivial. At odd primes the nontrivial quadratic inertia character is unique. The quadratic character of the product of those primes therefore cancels every unwanted restriction and creates no new odd ramification. Possible new ramification at 2 is allowed. Multiplication by a quadratic character preserves beta^2 and delta(beta).

3. The field L' and its degree, lines 682–688: valid.

   The kernel of beta restricted to G_L is open and normal in G_Q by the conjugacy invariance just checked. Its index in G_L is at most 2m. Thus L'/Q is Galois and [L':Q] at most 2m[L:Q]. No degree of a coefficient field enters this index. The order bound m at most 2 times the product of (p-1), and then at most 2 R^R M, is deliberately loose but valid: each prime of S is at most R; primes of T outside S divide the squarefree M. I have not separately audited the subsequent comparison with Q_R.

4. Two-dimensional representation, irreducibility, and Hodge–Tate weights, lines 690–708: valid with an omitted theorem bridge before Pan.

   With constant coefficients, multiplying beta^-1 by the normalized projective action cancels epsilon exactly. The result commutes with B. Over a splitting coefficient field, Morita decomposition gives V_l(A)=S tensor r_l, where S is the two-dimensional simple B-module with trivial Galois action. This is the meaning of the two identical summands in the source. On G_L', both scalar correction and conjugacy isogeny are 1.

   Faltings proves semisimplicity in Satz 3, the endomorphism comparison in Satz 4, and the Hom comparison in Corollary 1, printed pp. 360–361. These are the precise original statements needed here and in item 8. [Faltings 1983](https://pazuki.perso.math.cnrs.fr/index_fichiers/Faltings83.pdf).

   Applying these statements to A over L' gives End_G(V_l(A))=B tensor Q_l. After splitting, End_G(r_l) is the coefficient field. Semisimplicity and scalar extension imply absolute irreducibility. The full Tate module has two copies of each elliptic Tate-module Hodge–Tate weight, so each identical r_l summand has one of each. De Rhamness descends through a finite extension and passes to summands.

   However, Pan's quoted hypothesis is potentially semistable, not merely de Rham. The frozen passage does not state the implication it needs. Insert Berger's p-adic monodromy theorem, which supplies exactly this implication without changing any field or numerical bound. The author's linked article has Theorem 0.7 and Corollary 5.22. [Berger, Representations p-adiques et equations differentielles](https://perso.ens-lyon.fr/laurent.berger/articles/article02.pdf). Publication metadata is Invent. Math. 148 (2002), no. 2, 219–284, confirmed on [the author's article page](https://perso.ens-lyon.fr/laurent.berger/articles.php). The [arXiv version 3](https://arxiv.org/pdf/math/0102179v3) instead numbers this result Theorem 0.6 and Theorem 5.19; the versions must not be confused. This is an omitted standard theorem/citation, not an unresolved mathematical lemma or a counterexample.

5. Oddness, lines 709–716: valid; a linearity convention should be explicit.

   Use the Q-linear map on singular homology induced by the antiholomorphic conjugation map A(C) to its conjugate, followed by the holomorphic mu_c. Extend that map C-linearly. It exchanges H^(-1,0) and H^(0,-1). These are nonzero two-dimensional simple B_C-modules. In V_C=S tensor W, they are S tensor two distinct lines of W. The normalized action exchanges the lines; it cannot be scalar. Its square is 1 because it is the value of the already constructed representation at c. Its eigenvalues on W are therefore 1 and -1. Scalar beta(c)^-1 a_c does not change the fact that it exchanges the lines. This argument does not assume L' is real, does not appeal to residual oddness, and is unchanged by any finite character twist.

6. Pan and weight two, lines 720–728: applicable after the bridge in item 4; the finite-twist reduction should be expanded.

   I read Theorem 1.0.4 together with Conjecture 1.0.1 in the primary source. It requires continuity, irreducibility, finite ramification, oddness, potential semistability at p, and distinct Hodge–Tate weights. Its additional residual condition applies only at p=3. Thus there is no missing residual-image or residual-irreducibility hypothesis at p=5. [Pan, The Fontaine–Mazur conjecture in the residually reducible case, pp. 2 and 5, Theorem 1.0.4](https://arxiv.org/pdf/1901.07166v2).

   Here is my check of the remaining twist inference. A character eta twisting a modular representation to the constructed one is a one-dimensional subrepresentation of their Hom representation. Since both representations are de Rham, eta is de Rham. It is unramified outside finitely many primes. Global class field theory over Q then writes eta as a finite-order character times an integral power of the cyclotomic character. One can see this directly by removing its integral local Hodge–Tate weight at 5: the remaining character is finite on inertia at 5, finite on inertia at every other prime, and hence factors through a finite ray-class quotient. In the Tate convention HT(cyclotomic)=-1, the modular weight-k pair is {0,1-k}. Comparing after the cyclotomic twist with {0,-1} forces k=2 and twist exponent zero. The residual finite Dirichlet twist is again a weight-two cuspidal eigenform; take its primitive newform. This gives the claimed constituent of a modular abelian variety.

   The source's dual/cohomology formulation can express the same argument, provided the cohomological modular representation has pair {0,k-1} and is the dual of the Tate constituent. It must not mix that convention with the arithmetic-Frobenius Deligne/Tate pair {0,1-k}.

7. Compatibility at 3 and 5, lines 730–739: valid, with a short construction suppressed.

   Choose one number field C containing all a_sigma and beta values, a splitting field for B, and, once f is chosen, its coefficients. Choose embeddings C into Q_lbar consistently with the already fixed embedding at 5. At a prime p outside T and the coefficient primes, choose a place v of L and an arithmetic Frobenius sigma. Since L_v/Q_p is unramified and A has good reduction, specialization identifies the action on prime-to-p torsion with relative p-Frobenius

   `F_p: Abar_v -> (Abar_v)^(p) = ({}^sigma A)bar_v`.

   Composing with the reduction of mu_sigma is an actual endomorphism of Abar_v. Its characteristic polynomial on rational Tate modules is independent of l, by the characteristic-polynomial theorem for endomorphisms of abelian varieties. Thus the trace in the source is an integer independent of l, and its half multiplied by beta(sigma)^-1 a_sigma is one element of C. This handles nonsplit p as well as primes splitting in L; merely comparing powers of Frobenius would not suffice. It is the composite endomorphism, not a trace assigned to a semilinear map alone, that is used.

   Equality at 5 identifies these algebraic traces with those of the chosen modular Tate constituent. Transporting through the other embedding gives equality at 3 outside a finite set. Chebotarev plus semisimplicity gives the desired isomorphism. Semisimplicity here follows already from absolute irreducibility on G_L'. Using the compatible modular representation at 3 to compute the conductor at 5 is therefore justified. The exact numerical local conductor estimates at lines 741–784 are outside this assigned review.

8. Transfer to J_1(N), lines 787–794: valid; no coefficient-field degree estimate is missing.

   The modular weight-two constituent occurs in the Tate module of A_f, with A_f a quotient, hence an isogeny factor, of J_1(N). The construction and compatible-system conventions are recorded in Ribet's section 3, printed p. 4, with the original Shimura references. [Ribet](https://math.berkeley.edu/~ribet/Articles/korea.pdf).

   Over L', the common constituent yields a nonzero equivariant Hom after a finite coefficient extension. Invariants commute with that extension: in a finite-dimensional Hom space, the simultaneous linear equations defining invariance are equivalent to finitely many linear equations. Faithful scalar extension therefore leaves a nonzero invariant space over Q_5. The Faltings Hom comparison cited in item 4 produces a nonzero L'-homomorphism A to J. Absolute simplicity makes its connected kernel zero. Its image is isogenous to A, and Poincare reducibility gives the stated A times Z isogeny to J over L'.

Concrete insertions for a referee, without changing statements or constants

The following are proposed text, not a transcription of the reviewed manuscript. The first can follow line 625 and be recalled at line 691.

```tex
All coefficient extensions below have trivial Galois action: Galois
acts on the varieties and morphisms, and each resulting map on
homology is extended linearly over the coefficient field. In particular,
the scalars $a_\sigma$ are not acted on when multiplying the projective
operators. Choose a number field $C$ containing these scalars, the
values of $\beta$, and a splitting field of $B$, and use its completions
for all coefficient primes.
```

After line 708:

```tex
Berger's $p$-adic monodromy theorem implies that this de Rham
representation is potentially semistable, as required in Pan's theorem.
```

At lines 710–712:

```tex
On rational Betti homology take the map induced by the antiholomorphic
conjugation map, followed by $\mu_c$, and extend it linearly over $\mathbb C$.
```

A replacement expansion for lines 720–728, using one convention throughout:

```tex
Use the Tate convention in which the cyclotomic character has
Hodge--Tate weight $-1$. Pan's Theorem 1.0.4 applies at five and gives
a cuspidal eigenform up to character twist. The twisting character is
a de Rham subrepresentation of the Hom representation, and is
unramified outside finitely many primes. By class field theory over
$\mathbb Q$, it is a finite character times an integral power of the
cyclotomic character. Comparing $\{0,-1\}$ with the modular weights
$\{0,1-k\}$ after that power forces $k=2$ and power zero.
Absorb the finite Dirichlet character into the eigenform and take the
associated primitive newform $f$. Thus $r_5$ is a constituent of
the Tate module of $A_f$, or equivalently $r_5^\vee$ is its
cohomological constituent. This duality preserves the conductor.
```

An expansion for lines 730–738:

```tex
Enlarge $C$ to contain the coefficients of $f$, retaining the chosen
embedding at five. For $p\notin T\cup\{3,5\}$, choose a place $v$ of
$L$ and arithmetic Frobenius $\sigma$ at $v$. Relative $p$-Frobenius
maps $\overline A_v$ to $({}^\sigma A)_v$; composing with
$\overline\mu_\sigma$ gives an endomorphism of $\overline A_v$.
Its Tate-module characteristic polynomial, hence trace, is independent
of the coefficient prime. Multiplication of half this trace by
$\beta(\sigma)^{-1}a_\sigma$ therefore gives one element of $C$
whose images are the traces of every $r_\ell$.
The equality with the modular trace at five is an equality of
algebraic numbers. Transport it through an embedding at three and
apply Chebotarev and semisimplicity.
```

This last insertion uses the usual extension of homomorphisms of good-reduction abelian varieties and the characteristic-polynomial theorem for abelian-variety endomorphisms. The latter is explicitly proved in [Milne, Abelian varieties, Proposition 10.20, printed p. 50](https://www.jmilne.org/math/CourseNotes/AV.pdf); its Frobenius/specialization interpretation is also stated at printed p. 142. A precise reference for extension of homomorphisms would further improve the bibliography; the existing sentence is mathematically correct but names neither theorem. Excluding the additional finite set of primes dividing the primitive level during the trace comparison is harmless and should be understood if the modular unramified traces have only been defined there.

No actual counterexample was found within this scope. The first strictly missing named hypothesis bridge is the application of Pan at line 720 after proving only de Rhamness at lines 705–708. Berger repairs it unconditionally. The other suggestions make already valid calculations checkable; they require no new assumptions, no enlargement of L', and no alteration of the claimed height bound.
