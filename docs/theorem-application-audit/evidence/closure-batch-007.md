# Seventh closure pass: common alphabets and actual finite stages

Review date: 2026-11-05. Reviewer: root assistant. This completes the bounded A076 review begun in batch 6. It does not independently accept the coefficient rules, the existence of the companion or the detector construction. Their exact roles are listed below. No manuscript change is needed for this closure.

The consumer is the working `diophantine_zq.tex`, SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. Relevant passages are lines 1867-1917, 2003-2025, 2446-2465, 2479-2504, 9418-9437, 9881-9908, 10130-10174, 10210-10245 and 10414-10481. The detector's determinant congruence is at line 8065.

## Exact external inputs

The finite-limit and ultrafilter arguments in batch 6 are retained. Its source pins for Stacks Tags 086J and 08ZY remain the source versions for those topological statements.

For prime realization use Milne, *Class Field Theory*, v4.03, August 6, 2020, V Theorem 2.2, printed p.155. It gives density `1/phi(m)` for positive primes in a residue class prime to `m`. In particular there are infinitely many such primes. VIII Corollary 7.3, printed p.258, gives the equivalent abelian Frobenius realization statement. VIII Theorem 7.4, printed p.259, is the finite nonabelian Chebotarev theorem retained separately in A067. The existing exact PDF pin is used; no inference about publication status is made from these course notes.

The application below only uses a nonempty reduced residue class. It does not deduce the compatibility of field restrictions from their individual realizability. It establishes compatibility first.

## 1. The common type group and its two maps

Fix an actual odd stage with moving prime `ell_0`. Let `F_o` be the finite elementary quadratic field cut out by the intrinsic odd label characters, and let `L_o = Gal(F_o/Q)`, with its actual coordinate relations. Let `F_e` cut out the fixed even label characters for `E^k`, and let `F_s` cut out all additional stationary quadratic tests. Put

    F = K F_o F_e F_s,       H = Gal(F/K).

All these fields are finite and Galois over Q. View H as the subgroup of `Gal(F/Q)` with trivial restriction to K. The actual common alphabet is the image of H in the retained odd, even and stationary coordinate groups. If the coordinates omit a redundant character, take this image rather than asserting that H itself embeds. This definition retains all relations among the coordinates.

The even alphabet used in this construction is

    L_e = image(H -> Gal(F_e/Q)).

Equivalently it is the image of `G_K` in the fixed even label group. Enlarging the finite field F by `F_o` or `F_s` does not shrink this image: every automorphism of `K F_e` fixing K extends to the finite normal extension F. Thus the common-to-even projection is surjective by construction. This is the alphabet of individually K-split primes, not a claim that every unrestricted even label is K-split.

This restriction is legitimate for the actual consumer. The even seed in lines 2479-2504 and 9881-9889 is specifically proved to consist of K-split primes. Restriction preserves the coefficient rules: the permitted types form a subgroup, contraction adds two types in that subgroup, and primary type zero belongs to it. The coefficient filter imposes total-label conditions rather than requiring every individual prime to satisfy the filter. In particular line 9975 explicitly does not impose the individual filter on the prime used in the nonempty-seed argument.

For the odd projection, let p be the fresh rational prime ramified in K but outside the old odd support. At stages with `ell_0 != p`, the coefficient factorization states that `F_o/Q` is unramified at p. If `K` were contained in `F_o`, its ramification index at p would divide that of `F_o`, which is one. This contradicts the choice of p. Since `[K:Q]=2`, it follows that

    K intersection F_o = Q.

Consequently `Gal(K F_o/K) -> Gal(F_o/Q)` is an isomorphism. Extension from `K F_o` to F proves that `H -> L_o` is surjective. The map is ordinary restriction of automorphisms. No isomorphism from the common alphabet to `L_o x L_e` is asserted or needed.

The input that `F_o` is elementary quadratic and unramified outside the old support and `ell_0` is exactly the coefficient factorization at lines 9418-9437. This closure consumes that input; it does not replace the Carayol and trace-operator checks that establish it.

Stationary tests at primes dividing k impose coordinate relations within the common alphabet. They do not prescribe extra individual coordinate values beyond K-splitting. The eventual total label zero is imposed by packets below. This distinction is necessary: arbitrarily prescribing all those individual values could destroy the odd projection's surjectivity.

## 2. Why the existing ultrafilter survives fixing k

The detector stages have `M_theta -> infinity`. Their determinant congruence is

    ell_0 = -1 mod 2^M_theta.

For any fixed positive prime p, equality `ell_0 = p` therefore implies `2^M_theta <= p+1`. It occurs at only finitely many stages of an index sequence whose precisions tend to infinity. Every fixed finite avoidance set is thus avoided on a cofinite set of stage indices. A nonprincipal ultrafilter contains that set. This supplies a specific reason that fixing k after the intrinsic odd minimum does not require replacing the ultrafilter or choosing a new minimum.

The fixed old support contributes a fixed number of quadratic generators, and the single moving prime contributes at most one additional generator to the rational elementary quadratic extension. Indeed squareclasses unramified outside that support are generated by `-1`, `2` and its odd primes. Repeated characters and higher exponents do not increase this dimension. After k is fixed, the even and stationary fields contribute only a further fixed number of coordinates. Thus the common alphabets have uniformly bounded cardinality.

Choose presentations with the coordinate maps retained, not just abstract group orders. There are finitely many subgroup and projection diagrams inside these fixed finite coordinate spaces. One such diagram occurs on a set in the same ultrafilter. Its two projections remain surjective because they are surjective at each stage in that set. This selection refines the earlier large sets; it does not substitute another odd symbol or another witness.

The fixed even source and its graph function do not depend on the moving stage. The intrinsic odd tables and all their restrictions were selected using the same ultrafilter in batch 6. Refining by the common projection diagram therefore retains them. A least nonempty odd seed uses finitely many labels and bits, so it too is retained at every sufficiently large selected cutoff.

## 3. Realizing all finite type and incidence prescriptions

At a fixed stage let m be a modulus supported on `S_lab`, divisible by eight and by the conductors of every retained quadratic character, including `chi_K`. A common type is an image of an actual Galois element with `chi_K=1`. For rational quadratic fields, quadratic reciprocity expresses each character as a character of `(Z/mZ)^*`. Thus its inverse image in `(Z/mZ)^*` is nonempty. Choose a representative a in that inverse image. It is a unit modulo m by definition.

For each already chosen vertex r outside `S_lab`, either value of the Legendre symbol `(q/r)` is represented by a nonzero residue modulo r. If the specified direction is `(r/q)`, first convert it by the reciprocity sign, using the q-mod-four coordinate already fixed by a. These constraints have moduli r coprime to m and to each other. CRT supplies a residue class modulo `m product(r)` that is nonzero at every prime divisor. Milne V.2.2 applies to this reduced class. Infinitely many positive primes remain after removing the finite avoidance set and all earlier vertices.

Choose the new vertices successively. At each step only incidences with already chosen vertices are imposed; later ones will be imposed at their own steps. This proves simultaneous realization of the finite graph. It also covers a contraction: the new type is the sum of types in the actual subgroup and is therefore realizable, while every required external bit is assigned in the same CRT construction. No old prime lies in `S_lab`, and a fresh representative is chosen outside the original graph, so no self-Legendre condition is used.

The output primes split in K because that coordinate was fixed to zero before applying Dirichlet. The arithmetic/geometric Frobenius distinction is immaterial for these exponent-two characters, whose values equal their inverses. This observation is not used for the nonabelian detector or trace representations in A067.

## 4. Total labels and nonzero terminal polynomials

Separate surjectivity does not imply that a prescribed odd seed and a prescribed even seed lift simultaneously, or that a lifted seed has common total zero. The packet construction at lines 10210-10245 does not make either assertion.

Choose an even number of copies of each common label, with enough copies for the anchors of either seed. Their common total is zero. For one projection at a time, retain anchors for the first `r-1` labels of its r-vertex seed. Contract the nonempty remainder to the last anchor. The projected total of the seed is zero because both final filters contain 1. Hence the sum of the remaining projected labels is exactly the last seed label. If `r=1`, the whole packet contracts to the one zero-label anchor; it remains nonempty throughout.

Choose the requisite free incidence bits in this contraction test. The coefficient contraction rule makes the resulting iterated difference equal to the seed value one. Therefore each projected terminal function is a nonzero polynomial. These are two separate certificates of nonzeroness, which are the input to the simultaneous-address argument. They are not a proof that one common assignment already realizes both seeds. The latter conclusion requires the separate simultaneous-address theorem.

Give one such packet to each nonzero activation. Every nonzero address activates `2^(b-1)` packets. Thus its configuration is nonempty and its common total is zero. Added primary vertices have common label zero, so the stationary totals remain zero. The packet construction is finite for fixed b and fixed seeds.

## 5. Selecting an actual stage in the required order

After k and the common projection diagram are fixed, choose b and run the finite abstract address construction. Let `W_b` bound its graphs, contractions, auxiliary tests and operator sets. The statement requires no bound uniform in b. Intersect the following finitely many sets of stage indices:

- the chosen common-diagram set;
- the selected truth-table sets for the finitely many cutoffs used by this construction;
- the valid-stage set for the full operator budget, including the additional division allowance `R=2` and its threshold T;
- the cofinite sets imposing the required precision and finite prime exclusions.

Each set belongs to the same ultrafilter. Their intersection belongs to that proper filter and is nonempty. Choose a stage there, and only then perform the finite CRT prime realization of section 3. The coefficient readings at that actual stage agree with the selected graph tables. No prime chosen for a different moving theta prime is retained without checking its new type. No infinite intersection over b, all cutoffs or all Galois elements is taken.

The scalar constants in the final valuation inequalities were fixed before b. Only `W_b`, its threshold, and the actual stage depend on b. This verifies the quantifier order asserted at manuscript lines 2554-2558 and 10437-10481.

## Disposition and remaining dependencies

A076 is closed for the finite-limit, common-alphabet and stage-selection deductions above and in batch 6. The manuscript already contains the needed restrictions, so this is an expanded audit justification rather than a change to a claimed theorem.

This review consumes the actual coefficient factorization and contraction/isolation identities, the fresh-ramified negative even unit k, the nonempty K-split even seed, the odd fixed-witness detector and its precision congruence, and the simultaneous-address theorem. It does not certify those statements merely because it uses them. In particular A032 still contains the local-representation normalization check, A017 the theta-formula normalization check, A067 the finite nonabelian detector and trace composita, and A082 the forward rank-zero input. Their open obligations remain open. The A067 graph-label slice uses only the explicit abelian construction above; it does not close A067's other applications.
