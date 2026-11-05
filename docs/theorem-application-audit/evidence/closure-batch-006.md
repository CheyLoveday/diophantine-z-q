# Sixth closure pass: finite models, evaluation maps and limit conventions

Review date: 2026-11-05. Reviewer: root assistant. This is a bounded direct review of A075. A076 remains open for the arithmetic realization of the common alphabets and valid stages. The finite-model construction is separated below from its arithmetic inputs and from those outstanding realization questions. This is not an independent second review or acceptance of the restricted converse.

The working manuscript now specifies that the finite detecting lists are chosen at the finite stages before taking their common limit. It also corrects the imaginary-quadratic duality citation at line 5008 from Nekovar 5.7.1.6-5.7.1.7 to 5.1.1-5.1.6. Neither change alters a formula or line numbering. The precise final manuscript hash and changed lines are recorded in ANCHOR_REBIND.json.

## Source versions and limits of this closure

- Nekovar, *Selmer complexes*, Asterisque 310, 2006: 5.1, pp.113-114, for the no-real-place case; 5.2.4 and 5.4.3 for the actual local/global duality maps; 6.2.5-6.2.8 and Theorem 6.3.4, p.143, for the orthogonality criterion and Selmer duality. Section 5.7, pp.130-132, handles the different case p=2 with real places. It remains the correct reference for the manuscript's later calculation over Q. The finite-field calculation over imaginary K instead satisfies condition (P) of 5.1. The page containing 5.1.4-5.1.6 was checked visually.
- Milne, *Arithmetic Duality Theorems*, second edition, I.4.10(c), I.4.15-I.4.16 and I.5.1. BATCH-005 checks the field, support and degree conventions. These supply finite bounded residual global cohomology over K. Over a real field one uses the positive fiber described below, not boundedness of ordinary cochains.
- Crainic, *On the perturbation lemma, and deformations*, arXiv:math/0403266v1, 16 March 2004: 2.1-2.4, pp.1-3, and 3.2, p.4. This exact preprint is a supplementary formula comparison for the standard perturbation calculation, not a new arithmetic assumption or a claim of journal publication. The formulas and sign convention on pp.1-2 were checked visually. The specialized algebraic verification is given below. In particular no unexamined appeal to the general quasi-isomorphism argument on p.4 is needed; our normalized contraction has pi=1 directly.
- Stacks Project, Tag 03T3, Lemma 64.6.3(2), downloaded 2026-11-05 with exact HTML bytes pinned. It identifies derived maps from bounded-above projective complexes with maps up to chain homotopy. The bounded finite free instances used here satisfy its hypotheses. The elementary splitting and minimal-model arguments below give the additional facts actually needed. Current chapter numbers are not substituted for the pinned tag and bytes.

The arithmetic local-condition, pairing and support-change inputs remain A037-A039 and A045. The existence of the finite characters and compatible prime realizations remains A067-A068. The forward corank-zero input in the integral Kummer budget remains A082. This review verifies the derived-algebra deductions from those inputs; it does not re-prove them or grant an unresolved input as a theorem.

## 1. Finite models over the actual Artin rings

The rings are A_i=(Z/2^i)[t]/t^i and, for one fixed finite elementary abelian 2-group G, A_i[G]. Their maximal ideals are nilpotent. The coefficient modules are finite free over the indicated rings. Each module of continuous cochains is the filtered colimit of modules of functions on finite clopen partitions, hence is flat. The tensor comparison with any finite coefficient quotient is valid on these function modules and therefore on the colimit. The cone constructions preserve termwise flatness.

For completeness, a flat module M over an Artin local ring A is free even in infinite rank. Lift a basis of M/mM to a map F -> M from a free module. Its cokernel satisfies Q=mQ and is zero by nilpotence. If K is the kernel, flatness of M makes K/mK inject into F/mF. That latter map to M/mM is an isomorphism, so K/mK=0 and K=0. This argument does not apply finite-generation Nakayama to an infinite module.

Split the residual complex into its finite-dimensional cohomology and disks, and lift graded bases. The lifted disk differential d0 has a normalized contraction i0,p0,h0 with p0i0=1, h0^2=h0i0=p0h0=0, and 1-i0p0=d0h0+h0d0. Write the actual differential d=d0+epsilon, whose error has coefficients in m. Nilpotence makes the following finite sums meaningful even in the infinite-rank original cochain modules:

    B = (1+epsilon h0)^(-1) epsilon = epsilon (1+h0 epsilon)^(-1),
    dC = p0 B i0,
    i = i0-h0 B i0,   p = p0-p0 B h0,   h = h0-h0 B h0.

These equal the displayed manuscript formulas. To compare signs with Crainic, his h is -h0, his delta is epsilon, his large-complex b is d0 and his small-complex b is zero. His convention is ip=1+bh+hb. Replacing h by -h0 is essential.

Here is the algebraic check. The inverse identities give epsilon h0 B=B h0 epsilon=epsilon-B. Expanding d^2=0 and using 1-i0p0=d0h0+h0d0 gives B i0p0 B+B d0+d0 B=0. Multiplying this identity by p0 and i0 gives dC^2=0; multiplying the same identities with the formulas for i and p gives di=idC and pd=dC p. Expanding dh+hd gives 1-ip. Finally pi=1 follows immediately from the three normalization identities for h0. Thus these are actual chain maps and a contraction, not an inference from equal cohomology ranks. The finite cohomology summand supplies a bounded finite free model. Its homotopy equivalence with the original complex also justifies the derived coefficient changes; a bounded-below complex of flat modules was not assumed automatically K-flat.

For fixed K, active support and binary group, the residual dimensions are bounded as the moving prime changes. One can use the finite-support global bounds and the local finite complexes before removing active primes; no bound uniform over all active supports is needed at this point. The sharper A042/A073 bound after t-inversion serves a different purpose in the outer limit.

## 2. Transport of maps, products and higher homotopies

For a chain map f:X->Y, its transported map is F1(f)=pY f iX. A homotopy is transported as a homogeneous map, and composition includes an extra term. With delta denoting the Hom-complex differential, put

    F2(g,f)=pZ g hY f iX.

For degree-zero chain maps f and g the contraction identity gives

    delta F2(g,f)=F1(gf)-F1(g)F1(f).

For three such maps the second correction is F3(k,g,f)=p k h g h f i, and direct use of the graded Leibniz rule gives

    delta F3(k,g,f)
      =F2(kg,f)-F1(k)F2(g,f)-F2(k,gf)+F2(k,g)F1(f).

These formulas explain how to retain the second compatibility homotopies instead of assuming that f -> pfi preserves composition strictly. Original specified homotopies are included through F1, with these correction terms inserted at compositions. For a finite diagram the required number of such insertions is finite. The same construction with the Hom differential handles nonzero-degree maps and fixes their signs.

Cup products use tensor complexes. A contraction on a tensor product has inclusion iX tensor iY, projection pX tensor pY, and homotopy hX tensor 1+(iX pX) tensor hY, with the usual graded sign in evaluating the second term. Its Hom differential is 1-(iX pX) tensor (iY pY). Thus bilinear products, pairings, local isotropy homotopies and the second localization compatibilities transport by the same procedure. The target trace complex and its grading are retained. A rational pairing or equality of Euler characteristics cannot replace these maps.

An actual quasi-isomorphism between bounded projective models has a homotopy inverse: its bounded acyclic projective cone splits, starting at its highest nonzero degree. Therefore the inverse maps and contractions that the manuscript retains may be chosen before any coefficient limit. Their chain identities survive any coefficient extension, including nonflat ones.

## 3. Minimality, lifting and the compatible positive tower

Over a local ring, a unit entry in a differential splits off a disk by invertible row and column operations. Since the complex is bounded finite free, this terminates. In a minimal complex every differential is zero modulo the maximal ideal. A homotopy equivalence between two minimal complexes therefore reduces to degreewise inverse matrices. Their determinants are units, so the original comparison is degreewise invertible. This is the exact Nakayama argument used in the marked model lift around lines 5129-5155.

For Lambda[G], the augmentation ideal lies in the Jacobson radical. Lifts of the unit pivots at augmentation remain unit pivots. After adding the explicitly specified split disks, the graded isomorphism at augmentation lifts to an invertible graded matrix; conjugating the differential realizes the required upper-triangular augmentation. No assertion about a random cohomology isomorphism lifting to a chain isomorphism is used. Added disks count toward the stated comparison model rather than being discarded from its rank budget.

The positive complex over Q is the fiber of ordinary global cochains to ordinary real cochains, with real degree zero included. Ordinary global 2-cochains are not bounded in cohomology. Instead Milne I.4.10(c) cancels the global and real groups above degree two, and I.4.16 makes degree-two restriction onto the real terms surjective because the support contains a finite dyadic place. The fiber has finite bounded residual cohomology. This is the hypothesis used for its finite free model.

Here the coefficients really do form a compatible tower. At adjacent finite quotients, both reduced minimal models are models of the same reduced cochains. Their comparison is degreewise invertible by the preceding argument. Lift these matrices and change bases so that the differentials reduce exactly. The comparison to cochains initially agrees up to homotopy. Cochain reduction is termwise surjective, and the source model is termwise free, so the homotopy lifts; subtracting its Hom boundary makes the comparisons agree strictly. The comparison cones are then acyclic with termwise-surjective transitions.

For such a countable tower K_n, the sequence of complexes

    0 -> lim K_n -> product K_n --(1-shift)--> product K_n -> 0

is exact: surjectivity is constructed recursively using the surjective transition maps. Products are exact for modules, so the two products are acyclic and the inverse-limit cone is acyclic. This proves the comparison with continuous compact-coefficient cochains. It is not an assertion of exactness for arbitrary inverse limits.

## 4. The different inner-limit construction and its evaluations

When moving primes vary, the original representations need not be a compatible tower. The manuscript does not need that assertion. Choose the entire finite diagram and its bases at each stage, and fix a rank pattern on an ultrafilter-large set. Modulo each fixed A_n there are only finitely many matrix tuples, so exactly one occurs on an ultrafilter-large set. Reducing the selected tuple modulo A_m for m<n gives the selected tuple there, since the two selection sets intersect. Thus the tuples define matrices over Lambda. Every finite polynomial identity survives, including differential, inverse and homotopy identities. This part only uses finite partition selection; A076 separately records the arithmetic stage-existence questions.

Maps into original cochains are treated by evaluation, not by pretending that all original cochain modules have become one fixed module. For each sequence of Galois elements g=(g_i), evaluate the chosen finite list of cochains at g_i. Their values at every fixed finite precision again have a unique ultrafilter limit. One fixed ultrafilter defines this for all sequences. For each particular finite collection of sequences, the finite intersection of its selection sets preserves every identity. The resulting representation and evaluations obey

    e1_g d=(rho(g)-1)e0,
    e2_(g,h) d=rho(g)e1_h-e1_(gh)+e1_g.

A cycle therefore gives an abstract crossed homomorphism on the product group. There is no continuity conclusion on a single original Galois group. There is also no need to intersect selection sets over all sequences at once.

The detecting-list argument must start at the finite stages. Over the residual field choose representatives V for H1 of the original continuous cochains and write W for the coefficient space. Evaluate (c,w) by b_c(g)-(rho(g)-1)w. An element in every kernel represents a coboundary; since V consists of representatives, its class coordinate c is zero. Its remaining coordinate lies in W^G. Repeatedly choose an evaluation that decreases the current intersection until it equals this common kernel. At most dim V+dim W choices suffice. Pad to a fixed bound and keep the chosen Galois elements as sequences. The manuscript's clarification makes this order explicit, avoiding a circular assumption of injectivity after taking the limit.

The map to [W -> W^d] is an isomorphism on residual H0 and injective on residual H1. Its bounded finite free cone has no residual cohomology in degrees <=0. Cancel unit disks to obtain a cone starting in degree one, retaining the cancellation maps. The limit cone and every coefficient extension of it still start in degree one. Its long exact sequence gives exactly the required H0 isomorphism and H1 injection. This is why arbitrary field extension and the later nonflat quotient do not create an unexplained kernel.

For primitive and derivative Selmer complexes, the map to global cochains has the same residual properties. The relevant local maps are isomorphisms on H0 and injections on H1: derived Kummer includes local torsion in degree zero, unramified conditions at good primes have those properties, full conditions are identity maps, and every derivative condition retains D0. The cone exact sequence then gives H0 isomorphism and H1 injection globally. The manuscript correctly excludes arbitrary zero local conditions, whose missing H0 can produce extra Selmer H1 classes killed by global evaluation. Transfer from an orthogonal zero/full model is used only where its actual comparison cone has a retained contraction.

After t-inversion the shorter rank bound permits a shorter detecting list over F_2((t)). Start with the already injective list, and select a sublist by the same dimension argument after passing to the minimal model. Its length is bounded by the reduced cohomology dimension plus the coefficient dimension. Choose its cone contractions over each O_j before forming the outer quotient. Their matrix ranks are bounded, and all entries are integral in O_j. The quotient by sequences with valuations tending to infinity preserves these finite identities. It need not be flat. An approximate cycle whose differential tends to zero becomes an exact cycle there by the displayed evaluation identities.

## 5. Integral Kummer budget

The derived Kummer and self-duality inputs are A037, A038 and A045. With those actual maps, finite cohomology is (2,d_K,d_K,2) in degrees 0 through 3. Over imaginary K the applicable finite duality is Nekovar 5.1.6; the former citation to the real-place subsection was misplaced. Minimal finite free rank is the sum 2d_K+4, since residual differentials are zero.

For integral coefficients H0(C_K)=0 by finite rational torsion. The exact sequence T -> V -> E[2^infinity] injects E(K)[2^infinity] into global H1, and its image is exactly the torsion there. These classes satisfy the Kummer conditions, which also make Selmer H1 inject into global H1. Hence H1(C_K)_tors=E(K)[2^infinity]. The shift-three self-duality and the fact that Z_2 has global dimension one yield H3(C_K)=Ext^1(H1(C_K),Z_2). Its length is t_K. Universal coefficients give the displayed exact sequence with middle term the full discrete Selmer group and right term H2(C_K)_tors. Full corank one consequently gives free ranks one in H1 and H2. No finiteness of the whole Sha group is inferred.

The singular disks added at the two moving-prime places have zero H1 and bounded finite H2 because their determinants have bounded finite 2-valuation. That property is detectable at fixed finite precision and survives the inner limit. The long exact sequence therefore gives the stated bounds on ranks and torsion lengths of D_c. Smith reduction over Z_2 then sums the actual nonzero disk valuations. This algebraic deduction consumes the separate Frobenius determinant bound and the known companion's corank-zero theorem; it is not a proof of either.

## A076: completed elementary checks and remaining scope

The pinned Stacks Tag 086J gives nonemptiness of a cofiltered limit of finite nonempty sets, without requiring surjectivity of all transition maps. Tag 08ZY identifies profinite spaces with compact Hausdorff totally disconnected spaces. Neither theorem establishes that a proposed arithmetic stage exists.

A nonprincipal ultrafilter on the stage indices can be obtained directly by extending the cofinite filter to a maximal proper filter using Zorn's lemma. Unions of chains of proper filters remain proper. Maximality implies that for every subset either it or its complement belongs to the filter: if adjoining a subset makes the filter improper, an existing member is disjoint from it. No finite set belongs to this extension because its cofinite complement already does. Finite partitions therefore have exactly one cell in the ultrafilter. This is the foundational choice input; it supplies no effective bound.

The valuation-ring calculation for the outer quotient is valid: a nonzero class has bounded valuations on an ultrafilter-large set and thus one fixed integer valuation there. It is a power of 2 times a unit. Every nonzero ideal has an element of least valuation and is generated by it. Fixed nonzero integers do not vanish, so the fraction field has characteristic zero. Completeness is not asserted or needed.

The compact real recurrence at lines 5842-5853 is also valid. Cover the compact closure of the cyclic subgroup in E(R)^2 by finitely many sufficiently small translates. Two among sufficiently many positive multiples have difference in any prescribed identity neighborhood. If the positive differences stayed bounded as the neighborhoods shrink, a fixed nonzero multiple would be the identity, contrary to infinite order. This provides unbounded positive return indices. The derivative/local-coordinate step remains A071.

For the odd minimum, assume the preceding coarse inequality (F.5) and fixed bounded-weight witness. Any failure of (F.6) at fixed weight W on an ultrafilter-large set selects a violating index at each such stage. Its normalized integer depth belongs to a fixed finite interval below delta_o. A value constant on an ultrafilter-large subset contradicts the definition of delta_o. Thus the finite-cutoff inequality is simultaneous over all indices at that cutoff. Precision inequalities M>N and finite exclusions then give finite intersections of cofinite or already-large sets. This deduction does not require a stage valid for every cutoff.

For a fixed finite alphabet and graph cutoff there are finitely many symbol truth tables. Ultrafilter selection makes their restrictions compatible by intersecting two large selection sets. Each finite address program consumes only finitely many tables and one finite budget; their intersection is nonempty. The remaining A076 obligation is to check that the asserted common alphabets and their separate projection maps, especially after fixing k, have the required arithmetic realizations on those large sets. A067's finite composita and conjugacy conditions are also still open. Those premises are not supplied by the elementary compactness checks here.

Disposition: A075 is closed for the derived-algebra construction and its listed arithmetic dependencies. A076 remains open with the narrowed realization obligation. The source locator and finite-stage evaluation clarifications are applied to the working TeX, with a fresh PDF and inventory to be regenerated. No new publication is authorized by this bounded closure alone.
