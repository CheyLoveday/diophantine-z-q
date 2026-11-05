# Acceptance review: ten external application families

Consumer: canonical `diophantine_zq.tex`, SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. All line numbers below refer to that baseline. This review checked the actual consumers against the pinned primary statements, using earlier bounded reports as navigation. It does not promote a record merely because its `open_items` field is empty.

I recommend accepting all ten families within the scopes below. A052 requires the already prepared Voight source additions and coverage record; A054 requires a correction to the inventory's description of the conclusion actually consumed. No new manuscript mathematical repair was found. Acceptance of these external applications is not certification of the whole proof or of unrelated internal constructions.

## Evidence and version scope

`acceptance-primary/pins.json` records the ten original source files whose hashes were freshly checked against `sources.json`. Fresh full text extractions are alongside it. I also checked the Voight file hash against `sieve-bounds/COVERAGE-SOURCES.json`, and read its two relevant pages. The baseline hash was checked again during this pass.

New page-image inspection in this pass includes Waldspurger 1981 pp.377,467,483–484; Waldspurger's ICM contribution pp.527,529; Serre's opening statement p.259; Cai–Chen–Liu p.3730; and Howard v1 p.19. These images are in `acceptance-primary/`. The other cited portions were checked in the freshly extracted primary text, with the earlier source inspections retained as bounded supporting evidence. The Serre scan has a cover sheet: its PDF page 2 is printed p.259. The source text layer is empty there, so the image rather than an empty extraction supplies that check.

Cornut–Jetchev is the explicitly cited arXiv:1012.0725v1 and the separately pinned author-hosted text. The matching theorem formulations in these files do not assert identity with an inaccessible publisher PDF. Jetchev–Kane is explicitly arXiv:0908.3905v1. Howard is arXiv:1202.6340v1; its date must not be confused with the original publication date. The accepted scope is those exact statements, not a claim that every filename authenticates a journal version or an erratum search.

## A028 — oriented supersingular reduction

Consumers: L2374–2388 and L8882–9052, including all eight recorded citation sites. Primary locators: Cornut–Jetchev H.1–H.3 and sections 3.1–3.3, pp.4–6; Lemma 2.1, p.4; Theorem 3.1 and Corollary 3.2, p.9; section 3.6 and Lemma 3.4, pp.9–10; sections 4.9–4.10, pp.15–16. The newly recorded global embedding prerequisite belongs to A052 below.

The substitution is base field Q, imaginary quadratic field F=Q(sqrt(Dh_*)), source algebra M2(Q), and changed set {ell_0}. The set avoids finite source ramification, its parity is 1+0+1=2, and its single place is inert since the support imposes (D/ell_0)=1 and (h_*/ell_0)=−1. It avoids N and the quadratic discriminant. Both fine conductors are one: intersecting with either containing maximal order cannot enlarge the maximal quadratic order. The local distance at ell_0 is zero, so Lemma 2.1(ii) gives N_ell(0,0,0)=1, and the relative class-field factor is one. Thus the source's kappa is exactly one.

The source target is the specified sign fiber, not both residue orientations. At the old split prime powers Lemma 2.1(iv) gives two choices even when the prime is 2; in the division algebra the norm valuation modulo two gives the separate two residue orientations. The target count is therefore 2^(omega(N)+1). The manuscript retains these orientations. Its embedding stabilizer is O_F^times={±1}, so the factor from counting actual vectors and dividing by the automorphism group is 1/2. Combining these gives exactly 2^omega(N), with no further quotient by conjugate pairs. Section 4 identifies the equivariant adelic map with reduction of the same enhanced elliptic curve. Consequently the genus-weighted unaveraged sum is the same P_D, not an averaged or different-conductor point. Inverting Artin symbols reindexes the sum harmlessly because its character is quadratic.

I checked the consumer's two orientation flips: at p^e||N the root sign and norm-weighted Atkin–Lehner sign agree; at ell_0 the residue sign is −1 and the norm-character sign is −1, while the chosen functional has Frobenius sign +1. The arithmetic/geometric Frobenius ambiguity disappears on the indicated F_(ell_0^2) points. Outside the inert support the consumer asserts zero, not the reduction formula. These checks discharge the source-to-consumer count and normalization.

## A029 — full-space Fourier proportionality

Consumers: L2405–2419 and L7633–7731. Primary locators: Waldspurger 1981 section I.2, Proposition 2, p.377; Corollary 2 and its proof, pp.483–484. The source defines the full almost-all-Hecke space and states its coefficient identity for every member. Its proof explicitly extends the linear identity by linearity before squaring.

Use k=3, chi=psi, chi_0=psi chi_(−1), phi_0=f_E tensor eta, eta=psi chi_(−sigma), n1=D0 and n2=D. Then phi_0 tensor chi_0^−1=f_E tensor chi_sigma. Nonzero existence has already been supplied by A030, so Proposition 2 supplies H1 rather than the manuscript assuming H1 for an arbitrary packet. The ratio D/D0 is a square at every prime in the actual level support S0, including 2. The final paragraph of p.484 explicitly removes H2 in this same-dyadic-squareclass comparison.

The printed character is chi(n2/n1), hence psi(D/D0). The printed exponent is k/2−1=1/2, giving the displayed square-root normalization. The corollary concerns literal squares, not absolute-value squares. A nonzero reference coefficient and central value permit the stated division. Polarization over characteristic zero gives one proportionality scalar for the entire space; zero analytic value gives the zero functional. Old multiplicities are retained. The later common-level comparison has only S0 prime support; the extra coprimality sieve is applied afterwards. No dimension-one assumption or missing good-prime factor is used.

## A030 — nonzero packet and reference coefficient

Consumers: L7513–7632. Primary locators: Waldspurger ICM, Proposition 1 p.527 and Theorem 1 p.529; 1981 Proposition 18 proof pp.466–467 and section I.3 pp.377–378.

The ICM theorem gives nonzero lift from the nonzero central value; Proposition 1 places a nonzero lift in the indicated irreducible cuspidal space. The 1981 proof connects this nonzero value with the nonzero specified Fourier functional. The packet is chosen by this lift and frequency, not chosen arbitrarily first. Positive real frequency selects the holomorphic weight-3/2 constituent. The elementary unary constituents are outside this cuspidal packet scope.

I checked the consumer's additional local selection argument rather than attributing it to the theorem. Its additive average preserves ell_D0. The unit action yields support u²=1 modulo p^R; smoothness reduces the surviving neighborhoods to those of ±1, with the two dyadic neighborhoods correctly encompassing four residue classes. Choosing alpha(−1) to equal the central scalar makes both contributions agree. Their sum is 2 vol(K_R) ell_D0(v), nonzero in characteristic zero. The unit-squareclass projector preserves D0 and commutes with units; smoothness provides deep lower-unipotent invariance. This changes depths only at S0. At unramified primes, including primes dividing D0, the source's c_p^0 is one at squarefree valuations zero and one. Thus retaining the spherical vectors does not introduce D0-primes into the level or kill the coefficient. These are precisely the admissibility and level-support interfaces needed by A029.

## A031 — algebraic section model and descent

Consumers: L7733–7810. Primary locators: Ramsey Definition 3.1, printed p.606/PDF p.9; Theorem 4.2, p.609/PDF p.12; Remark 4.4, p.610/PDF p.13.

Definition 3.1 applies to k=3 and any positive auxiliary N over a ring in which 4N is invertible. The consumer works over characteristic-zero fields and includes character values and cusp roots of unity in one number field. Theorem 4.2 is a q-expansion descent statement in its stated module convention, not a general cohomology-vanishing theorem. The consumer's finite-affine-cover kernel argument proves the only base change used: flat extension between fields. Finite dimensionality reduces its algebraic linear constraints to finitely many equations. Nonzero reference evaluation therefore descends to an algebraic vector and can be normalized to one. Remark 4.4's warning about weights 1/2 and 3/2 is respected.

The Galois comparison is a separate manuscript argument: coefficient conjugation transports psi to psi^e, while twisting by nu=eta^((e−1)/2) supplies the same character and good eigenvalues. Both operations remain at S0-supported level; D0 is prime to it. A029 then compares their normalized coefficient functionals. Nothing in Ramsey alone is represented as proving rational coefficient ratios or preserving an unchanged character under Galois action.

## A033 — non-CM open image

Consumers: L2733–2763, L3349–3385 and L8010–8032. Primary locator: Serre 1972 opening theorem and reformulation, pp.259–260. The actual j=35152/9 is a nonintegral rational number, so this elliptic curve and its quadratic twists are non-CM. Serre's theorem applies over Q and includes the 2-adic component. It requires neither rational 2-torsion to be absent nor residual surjectivity.

Openness supplies 1+2^n M2(Z2) and a nontrivial central scalar. The first consumer then constructs g² tau g² tau^−1, using generalized-dihedral ring-class action to fix each field; its image is u^4 I and v2(u^4−1)=n+2. Squaring the displayed matrix preimages places them in any quadratic kernel, and their Z2-span contains 2^(n+1)M2(Z2). The second consumer restricts to determinant one, intersects an index-at-most-two subgroup, and uses explicit unipotent/commutator products to obtain its congruence subgroup inside the actual radical-fixing kernel. It does not invoke linear disjointness. The third uses irreducibility and the central scalar to prove the Kummer image spans the rational Tate module; compactness and finite index then give the integral lattices stated there. These are manuscript deductions from openness, not stronger assertions attributed to Serre. No parameter-uniform theorem about all auxiliary Kummer extensions is silently imported.

## A034 — Heegner norm relations

Consumer: L2765–2789. Primary locator: Cai–Chen–Liu, Theorem 2.15, printed p.3730/PDF p.10, with condition (*) on p.3722.

Take source base conductor c=d and old multiplier m=1 for each currently used d. All N-primes split, so N1=1, X_K(N)=X0(N), and (*) reduces to (d,N)=1. The new prime avoids 6dND_K. This application does not require d itself to be an inert squarefree product. The source's u1 is [O_K^times:Z^times]=1; the field exclusions ensure exactly this. Its inert trace is T_ell and its split trace is T_q minus the two Frobenius actions. The product of the latter Artin symbols is the principal ideal (q), so they are inverses. Passing to the fixed elliptic quotient gives the displayed eigenvalues. The cusp at infinity removes the degree correction; any previously chosen cusp translation is killed by the fixed C_pi. The source sum is unaveraged. No class-number or conductor-dependent multiplier is introduced.

## A035 — Frobenius congruence, restricted source role

Consumer: L2791–2810. Primary locator: Howard arXiv:1202.6340v1, section 1.7, formula (13), printed/PDF p.19.

Howard's formula has the displayed arithmetic Frobenius at a compatible place and his restricted n-family. The manuscript accurately labels it as a record of that special case, not a theorem for arbitrary d. Its broader assertion is proved locally: d prime to ell makes the CM order maximal unramified quadratic at ell; inert reduction is supersingular; the raising isogenies specialize to the unique subgroup scheme of order ell, the relative Frobenius kernel. The prime-to-ell cyclic N-structure follows the same map. Good integral models extend the fixed quotient. Transporting the place with the old class action gives the equivariance needed. No odd coefficient-prime or residual-surjectivity hypothesis from Howard's unrelated Kolyvagin theorem is imported. Accept as a corroborating source with the supplied broader local argument, not as a direct arbitrary-conductor application of (13).

## A052 — quaternionic geometry, including new coverage obligations

Consumers: L8153–8180 and L8839–8843. Primary locators: Jetchev–Kane v1 sections 1.1–1.2, pp.1–2, and 2.5, p.6; Voight corrected online v1.0.7u (August 5, 2026), Main Theorem 14.6.1 p.223/PDF p.243 and Proposition 14.6.7 p.224/PDF p.244. Voight SHA256 is `a9316b834dbd500c52cd3a981c3205c9f4145b217042b213d23f696aee84b0f0`.

Jetchev–Kane takes general N>1 with ell prime to N, not squarefree N. Its enhanced supersingular curves have Eichler endomorphism orders of full level N, automorphisms R_z^times, and the stated adelic double-coset description. Its field-of-definition statement and the scalar-Frobenius explanation in the consumer handle prime-power cyclic subgroups. We do not use its later orbit-count corollary or identify its unweighted ternary lattice with the present weighted Schwartz construction. That distinction leaves the weighted modularity in A053/A054 and exact orientation count in A028.

Voight's classification applies over Q to the two noncomplex places {ell_0,infinity}. His embedding proposition applies to the separable quadratic extension Q(sqrt(Dh_*)): the real completion is C, and the ell_0 completion is a field by inertness. These are all the ramified places. Thus a rational embedding exists. This is not an optimal embedding into an arbitrarily fixed global order. The following choice of z0 is adelically variable and uses the preceding local constructions; no selectivity assertion is being assumed.

Accept after including these two Voight subobligations, source pin and already prepared citation additions from `sieve-bounds/COVERAGE-REPLACEMENTS.json`. Cross-reference the rational embedding prerequisite in A028. The exact source hash and corrected-edition page convention must be retained.

## A053 — local Weil operators

Consumers: L8312–8563. Primary locators: Weil 1964 I.13–I.14/Theorem 2, pp.160–162; II.25, p.173; II.28/Proposition 4, pp.175–177.

The local field is Q_p (including 2) or R, the nondegenerate form has rank three, the additive character is fixed globally, and the self-dual measure is |det(2A)|_v^(1/2) times coordinate measure. The Fourier pairing is B_Q=2x^tAy. These yield Fourier-square reflection and the stated completed-square integral. Compact translation invariance of the actual locally constant weights supplies dual-lattice support and lower-unipotent invariance. No self-duality of Z2^3 is incorrectly assumed: its reference dual is (1/2)Z2^3 with measure 2^(−3/2).

The index identity follows from the quaternion norm form <1,−u,−a,ua>, multiplicativity and the split/division values +1/−1. The determinant quotient relative to Q0 is therefore (u,det Q), including at 2. The manuscript uses the same Fourier convention and lifts for both rank-three representations. Changing both conventions inverses the indices without changing this quadratic quotient. Its explicit common-cover relations retain the order-four lift of −I at 2. For Q_B the determinant is square; for Q_B/m its squareclass is m. Thus there is no missing dyadic squareclass 2 or uncontrolled eighth-root factor. This checks the convention-sensitive external interface; the finite local weight recipes are internal constructions, not an extra conclusion of Weil's theorem.

## A054 — global theta modularity and cusp holomorphy

Consumers: L8627–8725. Primary locators: Weil II.27, pp.174–175; II.30/Proposition 5, p.179; III.41/Theorem 6, p.193.

Outside the prescribed finite support, the characteristic function is that of an integral self-dual lattice at an odd split place, so the local index and spherical action are trivial. At the remaining places A053 supplies the required congruence invariance. The finite tensor times the real Gaussian is a Schwartz–Bruhat function. Proposition 5 gives the product of local indices equal to one; the product formula also cancels the determinant measure factors. Theorem 6 therefore gives rational invariance of its theta sum. The archimedean Gaussian has weight 3/2. At an arbitrary rational cusp the finite transform still has bounded-denominator lattice-coset support; positive definiteness gives nonnegative exponents and normal convergence. This supplies holomorphy, a conclusion the source's invariance theorem alone does not state.

The adelic identity in the consumer uses gamma_f^−1, so the relative character is evaluated at its upper-left entry d. Extraction replaces Q_B by Q_B/m with the same weights; coefficients are exactly H_M(mn), with no Haar-measure multiplier in this discrete sum. Its determinant quotient produces (m/d), and division by the stated genus character gives chi_(−1). All level primes remain in the original support.

**Inventory correction required:** the existing A054 record claims an odd-factor proof of zero constant terms at every cusp. The actual baseline consumer here asserts M_(3/2), not cuspidality, and supplies only the holomorphy argument just checked. Remove the unused stronger cusp-vanishing obligation and narrow the translation to automorphy plus holomorphy at every cusp. Do not falsely record that a cusp-vanishing proof appears at these anchors. This is a record-scope correction, not a manuscript defect. The separate even-source cuspidality belongs to A030.

## Integration disposition

`ACCEPTANCE-UPDATES.json` supplies the ten recommendations, exact scopes and the two conditional record/citation updates. A052/A028 should link the new Voight coverage; A054 should be narrowed as above. Existing staged mathematical patches do not alter the formulas used in these ten applications. Rebind all anchors to the eventual final manuscript and verify the final source-role map before publishing. No shared file was edited.
