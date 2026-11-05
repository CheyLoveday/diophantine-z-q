# Forward rank and modular parametrization audit

Reviewed 2026-11-05. Scope: A020, A082, A066, A070. Baseline `diophantine_zq.tex` SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e` was checked directly. No shared manuscript, canonical audit file, PDF, or git state was changed. `PATCH.diff` is an unapplied proposal against that baseline. The unslop skill was read and applied. No applicable AGENTS.md was found in the ancestor paths or repository tree searched.

## Results

| Application | Recommendation | Remaining limitation |
|---|---|---|
| A020 | Close the forward theorem applicability obligation after the bibliography correction and explicit lemma in the patch. | This does not prove the earlier RC premise or the manuscript's height/determinant formulas. |
| A082 | Close the forward rank-zero/finiteness source obligation using Kato Corollary 14.3 or the correctly identified Kolyvagin Theorem 1. | The integral length/calibration argument remains a separate application. |
| A066 | The rational elliptic curve modularity and actual-target parametrization are supported by the sources and maps below. Accept the explicitly identified author version if closing. | No inspected BCDT file is the publisher's final typeset article. Publisher/preprint identity cannot be marked verified. The arbitrary-coefficient A_f occurrence is shared with A011 and is separately recorded below. |
| A070 | Close after specifying the global cuspidal annihilator and the degree-zero quotient map as in the patch. | This closes cusp corrections and quotient equivariance, not the CM norm formula or the numerical theta normalization. |

## A020: the cited Kolyvagin document is misidentified

The local PDF `work/astra-weighted-theta-audit-001/primary/kolyvagin-1990.pdf`, SHA256 `bacdf23d05d5120defe923c8dcccd7c5bc525fe7b32239552b04fd6567726f2f`, is **On the Mordell-Weil group and the Shafarevich-Tate group of modular elliptic curves**, MPIM preprint MPI/90-69, 1990. It is not a PDF of **Euler systems** in the Grothendieck Festschrift. The title page and the MPIM catalog https://archive.mpim-bonn.mpg.de/id/eprint/325/ agree. The manuscript currently combines the title of one work with the URL and theorem numbering of another. This is a real bibliographic defect; the mathematical forward statement is present in the pinned PDF.

The source assumes E/Q modular on printed p.3, PDF p.5, meaning a weak Weil parametrization X_0(N) -> E, with N its conductor. Theorem 1, printed p.4, PDF p.6, states rank(E)=analytic-rank(E) and finite full Sha(E) whenever analytic-rank(E)<=1. I rendered and inspected the inequality and the full Sha statement; they are not inferred from OCR. The source is valid for both CM and non-CM modular elliptic curves. No good-ordinary, residual irreducibility, or prime-two exception occurs in this theorem.

Its explicit proof chain is on printed pp.4–5, PDF pp.6–7:

1. Choose a negative fundamental discriminant D, D square modulo 4N, D not -3 or -4, and (D,2N)=1. These conditions give the split Heegner hypothesis at every prime dividing N and avoid extra units. K=Q(sqrt(D)).
2. Theorem 4 supplies infinitely many such D for which analytic-rank(E/K)=1 when analytic-rank(E/Q)<=1. The source attributes the rank-one-base case to Waldspurger and the rank-zero-base case independently to Bump–Friedberg–Hoffstein and Murty–Murty. This is a precise packaged theorem in the inspected Kolyvagin source; this audit does not claim to have re-proved those analytic nonvanishing theorems.
3. The factorization is L(E/K,s)=L(E,s)L(E^(D),s). For an analytic-rank-one base the auxiliary twist has nonzero central value. For an analytic-rank-zero base the auxiliary twist has a simple zero. Thus the two cases use different auxiliary twists, not a rank-one theorem applied directly to a rank-zero base.
4. Theorem 3, attributed there to Gross–Zagier, says that under (D,2N)=1 this simple zero over K is equivalent to the Heegner point P_D being nontorsion.
5. Theorem 5 gives rank(E(K))=1 and finite full Sha(E/K) from this nontorsion point. Theorem 2, and then Theorem 1, descend to Q.

For completeness the actual descent is visible in the source. If epsilon is the root number and e kills E(Q)_tors, its equation (3) is sigma(eP_D)=-epsilon(eP_D), where sigma is the nontrivial automorphism of K/Q. The free rank-one line is invariant for an analytic-rank-one base and anti-invariant for an analytic-rank-zero base. Restriction on Sha lands in Sha(E/K), since locally trivial torsors remain locally trivial after extension. Its kernel lies in H^1(Gal(K/Q),E(K)), hence is killed by 2, and therefore lies in the finite group Sha(E/Q)[2]. Finite target and finite kernel imply finite full Sha(E/Q). This proof includes its two-primary subgroup; no claim about primes being odd is needed.

Actual manuscript maps: apply this theorem to E_n and E_(n theta) only after RC supplies analytic rank one, and to E^(h) at the known simple-zero calibration. These are elliptic curves over Q with nonzero discriminant. Full rational two-torsion contributes dimension 2 to E(Q)/2E(Q); rank one contributes another 1. The already computed dim Sel_2=3 therefore gives Sha[2]=0 by the finite Kummer sequence. Finite Sha alone would not give Sha[2]=0. The patch retains the rank and finite-Selmer-dimension premises.

## A082: a direct rank-zero source including p=2

The inspected published Kato PDF is `work/kato-2004.pdf`, SHA256 `3c6e14b11fa60262db8aff782ce3cf4d83e9100c0be83621a7e4ce502cec605d`, Asterisque 295 (2004), pp.117–290. The exact source is Corollary 14.3, printed p.235, PDF p.120, and the preceding definition in 14.1 on pp.234–235. I rendered and inspected p.235. It asserts finite full Selmer and finite rational points in the chosen character part for an abelian variety A/Q admitting a surjective homomorphism J_1(N)->A, a finite abelian extension K/Q, and L(A,chi,1) nonzero.

Use A=the actual twist E^(h), K=Q, chi=1. The extension and character hypotheses are then automatic. BCDT supplies a nonconstant Q-morphism X_1(N_h)->E^(h), where N_h is the twist's conductor. Translate its rational cusp image to zero. The Jacobian universal property gives a nonzero homomorphism J_1(N_h)->E^(h), which is surjective because the target is an elliptic curve. Thus Kato applies to the actual curve, not just an isogenous optimal quotient. The nonzero central L-value is a premise established earlier in each relevant use.

Theorem 14.2(2) immediately above explicitly allows every finite coefficient place and every stable lattice. Section 14.1 says the ordinary abelian-variety Selmer group is the direct sum of its Sel(K,T_p(A)) groups over all primes p. Consequently Corollary 14.3 includes p=2. The p!=2, potential-good-reduction, and image condition (12.5.1) in Theorem 14.5(3) concern a different integral bound, not Corollary 14.3. They must not be imported into this rank-zero finiteness result. Conversely, this audit does not justify using the stronger 14.5(3) at two.

The exact ordinary Kummer sequence is

`0 -> E^(h)(Q) tensor Q_2/Z_2 -> Sel_{2^infinity}(E^(h)/Q) -> Sha(E^(h)/Q)[2^infinity] -> 0`.

Finite full Selmer implies rank zero and finite Sha[2^infinity]. Equivalently the corrected Kolyvagin Theorem 1 gives rank zero and finite full Sha, with the same consequence. It is false that finite Sha by itself forces Selmer corank zero; the rank-zero conclusion is essential. For general E, corank Sel_{2^infinity}=rank E(Q)+corank Sha[2^infinity]. No finiteness theorem is applied here at the unknown corank-one base.

The recorded A082 anchors 7303 and 7403 are not the actual forward-theorem sentences. On the baseline the relevant calibration sentences are at 7318 and 7472–7473. Other forward rank-zero uses include 2238–2239, 4998, 7959, 9762, and 9901. The proposed reusable lemma covers these uses without adding new analytic premises. Source closure does not validate the subsequent determinant length identities.

## A066: versions and the actual curve

The original pinned BCDT file has hash `cbbdc24c26cdfcbd77f0e084194643e8804a724f004eb02e431ead9d932c498d`. Theorem A is on PDF p.1; the equivalences defining modularity occupy pp.2–3. In particular conditions (1)–(2) give the elliptic L-series and a weight-two form at the conductor, and (6) gives a Q-morphism X_1(N(E))->E. These conditions explicitly concern E itself. Theorem A is unconditional for every elliptic curve over Q; the residual conditions in intermediate lifting results are not extra conditions on this final theorem.

Two new author-hosted versions were checked. Conrad's `tswfinal.pdf`, hash `13043cf6e9043a69dc7988882658cd92595efc88dfd4fd2f326ac3ef3cae8e06`, still prints Volume 00, Number 0, Pages 000–000 and placeholder received dates. Harvard DASH, hash `26a45279c0f03bb28b3a0ed54eb0a47b622dd40e19fc25f971c47b2fadb84c5c`, has a repository cover linking the published DOI but the enclosed article also has placeholder journal metadata. Theorem A and the six modularity equivalences agree in these files and the baseline file at the inspected locations. This is a local statement comparison, not certification of complete article equivalence. The AMS publisher download returned HTTP 403. The filename `bcdt-published.pdf` was an initial download name; it has been renamed `bcdt-author-typeset.pdf` to avoid a false publication label.

The proposed bibliography explicitly cites the inspected author manuscript, while separately giving the historical journal citation. This resolves which theorem version is being used without asserting that the file is the publisher PDF. If the project insists on final-publisher byte equivalence, retain that as an open documentation obligation.

For E_ell, the displayed discriminant 2304 ell^6 is nonzero for the positive ell in the manuscript. Its coefficients lie in Q, so Theorem A applies. Each nonzero rational quadratic twist is again an elliptic curve over Q and has its own conductor. The condition ell=11 modulo 12 is not required for modularity. Neither full rational two-torsion nor non-CM is a modularity obstruction.

To make X_0(N) and the isogeny explicit, use the rational coefficient newform f attached to E, its elliptic quotient q_f:J_0(N)->A_f, and a Q-isogeny alpha:A_f->E. Define phi=alpha q_f and pi(x)=phi([x]-[infinity]). This is a nonconstant morphism to the actual E, normalized at infinity. Faltings's isogeny comparison transports the same L-series realization to E; no isomorphism between E and the optimal curve is assumed. Milne's *Modular Functions and Modular Forms* v1.31, Remark 11.18 and Theorem 11.19 with its proof, printed p.117, describes the Jacobian map, the quotient E', and the isogeny E'->E at the conductor. The pinned notes are exposition, not a new primary modularity proof. Do not use the imprecise 'one-to-one' wording of Proposition 11.21 to claim a unique curve in the isogeny class.

The quotient is chosen for the f-eigensystem, so phi T_q=[a_q(f)]phi for q not dividing N. Composition with alpha preserves this identity because alpha commutes with multiplication by integers. An equivalent verification is to pull back a nonzero invariant differential: the difference homomorphism has zero differential and is therefore zero in characteristic zero. None of this identifies the integral Tate lattices. Alpha identifies rational Tate modules; the actual T_2(E) and an image lattice can differ by a fixed finite index. The map is chosen before conductors vary, so its denominator is fixed.

The different occurrence at line 744 has arbitrary coefficient field and possible nebentypus. It must not be justified by the rational-coefficient elliptic quotient alone. Ribet, *Abelian varieties over Q and modular forms*, author manuscript for the 1992 KAIST lectures, Section 3, PDF p.4, states the construction of A_f/Q for a normalized weight-two eigenform on Gamma_1(N), dim A_f=[Q(a_n):Q], as a quotient of J_1(N), citing Shimura Theorem 7.14. The same page decomposes the covariant rational Tate module into two-dimensional coefficient-place constituents. Its later compatibility statements use those covariant Tate modules. The file is pinned here for the A011 reviewer. Shimura's original book bytes were not newly inspected in this audit. The A011 reviewer independently handles the precise r_5 constituent and its duality, rather than granting this broader use from the elliptic-curve theorem.

## A070: normalized good Hecke action and nonzero Atkin–Lehner constants

Elkik, *Le theoreme de Manin-Drinfeld*, Asterisque 183 (1990), pp.59–67, theorem on printed p.59, PDF p.2, states that every degree-zero divisor supported at cusps of a congruence modular curve has torsion class in Pic^0. The downloaded file is the published Numdam scan, hash `7618e61b8ec287b9fcce61fb4ac7d89ea98d58ca9274fa899ed52cda670b19b5`. This is a published proof of the theorem, not a citation to a review label.

Let C_N be generated by [c]-[infinity] over all cusps of X_0(N). There are finitely many cusps; finitely many torsion generators give a finite subgroup of J_0(N)(Qbar). Its image under phi is finite. Choose C_pi to annihilate that image once. No rationality of every cusp is needed. The whole set of cusps is Galois-stable and the homomorphism is defined over Q. The bound depends only on the fixed N and phi, never on a ring-class conductor, a companion discriminant, or a binary precision.

For q not dividing N, the standard q+1 upper-half-plane representatives send infinity to infinity, hence T_q[infinity]=(q+1)[infinity]. Therefore

`phi(T_q([x]-[infinity])) = [a_q]pi(x)`

says exactly that the sum of the q+1 pi-images of the Hecke neighbors equals [a_q]pi(x). There is no correction in the displayed good-prime norm relations of (4.1), and no C_pi is needed for those normalized relations alone. The degree-zero homomorphism is phi, not literally the point map pi; the patch makes the notation precise.

However a nontrivial correction is used elsewhere. Baseline line 9026 says the actual parametrization transforms by the Atkin–Lehner eigenvalue after L kills the cuspidal translation. If W is the relevant Atkin–Lehner involution and f|W=w f, then

`pi(Wx) = [w]pi(x) + pi(W infinity)`.

Indeed subtract [W infinity] before applying phi W=[w]phi on the quotient. The correction is the image of [W infinity]-[infinity] and lies in phi(C_N). Normalization pi(infinity)=0 does not imply pi(W infinity)=0. The local operators here are the Atkin–Lehner operators at exact prime powers p^e||N on a trivial-nebentypus newform; the eigenvalues w are the signs already used by the manuscript. The patch defines B_cusp=C_pi at the fixed multiplier construction, so the later L kills every such constant. It does not assert that any particular constant is nonzero; it identifies the potentially nonzero term actually required by the proof.

## Artifacts and validation

- `PATCH.diff` contains the exact proposed TeX changes: correct Kolyvagin identity, add a common forward lemma, specify the actual parametrization map, define the finite cuspidal annihilator, and attach the rank-zero references.
- `primary/downloads.json` records retrieval URLs, byte counts and SHA256 hashes for new source files, plus the failed publisher retrieval.
- Extracted text and rendered source pages in `primary/` permit independent checking. The Kolyvagin printed pp.4–5 and Kato p.235 were visually inspected, as were the textual publication headers and exact source statements described above.
- All patch replacement anchors were asserted to occur in the baseline. No TeX build is claimed, since the shared manuscript was not edited. The root integrator must rebuild after combining patches.
- No assertion here establishes the restricted converse, the central saturation formula, the arithmetic length comparisons, or the full manuscript theorem.
