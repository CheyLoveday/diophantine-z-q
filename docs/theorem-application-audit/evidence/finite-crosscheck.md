# Finite arithmetic production: bounded independent cross-check

I found no new gap in the finite producer on its stated non-CM, split-Heegner domain. This is an independent challenge of work/astra-final-finite-class-production-independent-001/REPORT.md, SHA256 2f87616b5cd244392442fc3fe4f4da8873c6042d428955ca24514ee23be45058, against the original point formulas and the actual descent/localization maps. Its earlier verdict was not used as evidence.

This note supplies a bounded verification of the finite input left explicit by work/root-limits-final-review-001/RECEIPT.json. It does not re-audit the limits, moving-character theorem A4, analytic nonvanishing, or full RC. No source, manuscript, Lean file, runtime job or numerical test was changed or launched.

## 1. Exact scope and primary evidence

Fix the actual non-CM E/Q, its integral Tate module T, its normalized modular parametrization, and its permitted local quadratic types at the fixed primes of 2N. Let K be imaginary, split at 2N, and different from Q(i) and Q(sqrt(-3)). The old conductor f is prime to 2ND_K and may contain the moving prime, active primes and all already chosen derivative primes. A new derivative prime ell is inert and outside 6fND_K. The finite character factors through H_f/K. The scalar deformation is actually trivial at 2N; in the universal binary family the quadratic character is also actually trivial there.

The desired finite output uses one L=C_cusp C_bad 2^(2e), independent of K, f, the number of primes and target precision. For each requested retained level m one chooses a working level a>=m+e and the next-prime congruences at least modulo 2^(a+1). It then produces actual Selmer-cone classes with f(P_(I union ell))=0 and s(P_(I union ell))=J f(P_I), with the previously constructed scaled lower class and the old singular conditions. It is not a statement about one fixed numerical prime at all precisions.

Fresh original-page inspection in this directory consists of ten rendered pages and extracted text:

| Original primary text | Pages read | Exact use |
|---|---|---|
| Cai--Chen--Liu, Heegner points on modular curves, Trans. AMS 370 (2018), 3721-3743, DOI 10.1090/tran/7053; publisher author offprint | 3721, 3722, 3730 | Modular curve/level and conductor hypotheses; unaveraged Theorem 2.15 |
| Howard, The Heegner point Kolyvagin system, arXiv:1202.6340v1 | PDF/printed 2, 19-21 | Geometric norm and reduction (13), and the exact odd-prime descent/eigenspace steps that cannot be imported at two |
| Lang, Algebraic groups over finite fields, Amer. J. Math. 78 (1956) | 555-557 | Surjectivity of x -> x^(-1)Frob(x), hence connected finite-field H1 vanishing |

The exact original PDFs are pinned below. Lang's scanned pages have no useful extracted text; they were read visually. The current raw producer is RD182-409 in ring-determinants-frozen-4eaee875.tex. I also read the complete finite-heegner-descent-audit.txt, especially its sections 1-6 and 8. The unused-prime determinant in its section 7 is not part of this review.

## 2. Point norm and reduction before any transfer

In CCL 2.15 take c=f and m=1. Since all level primes split, N1=1 and their X_K(N) is X_0(N). The unit factor is one because the two extra-unit fields are excluded. The relative group has order ell+1, and the theorem gives

    sum_(sigma in Gal(H_(f ell)/H_f)) P_(f ell)^sigma = T_ell P_f.

There is no average. The normalized map P -> [P-infinity] -> E converts this divisor relation into Tr(y_(f ell))=a_ell y_f: both divisor sides have degree ell+1, and T_ell(infinity)=(ell+1)infinity. In this normalization C_cusp can be one. If a different fixed cusp normalization is used, only its fixed cusp differences enter C_cusp.

This geometric application does not require inventing a primitive character of conductor f. One can also check the conductor freedom directly. Since ell is inert and prime to fD_K, O_f/ell O_f is F_(ell^2). Its units act transitively on the ell+1 cyclic lines in the ell-torsion of the old CM elliptic curve; the stabilizer is F_ell^times. None of these lines is O_f-stable, so all targets have conductor f ell. Ring-class reciprocity identifies this quotient action with the entire relative ring-class group. Its orbit is exactly the Hecke divisor. This supplies the same formula for any old f satisfying the local coprimality, regardless of a character's minimal conductor.

The reduction relation is separate. At the new prime the old CM order is maximal and unramified quadratic. Potential good reduction and endomorphism specialization preclude ordinary reduction, since the ordinary rational p-divisible endomorphism algebra Q_ell x Q_ell cannot contain that quadratic field. The reduction is supersingular. Its unique subgroup scheme of order ell is the alpha_ell Frobenius kernel. Every lifted cyclic ell-subgroup has that special fiber, so each conductor-raising quotient reduces to the Frobenius quotient. A reversed characteristic-zero isogeny can be dualized first. Because ell does not divide N, the cyclic N-level subgroup passes through the same quotient. X_0(N) records the subgroup, not a generator, so no level-generator scalar is introduced. The fixed parametrization commutes with reduction and rational Frobenius. Thus

    red(y_(f ell)) = F_ell red(y_f).

Howard (13) independently displays exactly this congruence, with the place specified. Its printed conductor setup is narrower; the preceding local CM argument explains why the formula still holds at arbitrary old f. It applies to every translated pair of points. One must transport the place with the translate, or apply this geometric statement afresh to that pair at the chosen place. One must not assume an arbitrary global Galois translate commutes with a fixed local Frobenius.

These steps retain the standard CM reciprocity, potential-good-reduction, endomorphism-specialization and elliptic p-divisible-group facts as named classical inputs. The argument above checks their needed local hypotheses; it does not claim a fresh proof of those entire theories.

## 3. Uniform torsion and canonical scaled descent

Non-CM open image supplies d>=2 with 1+2^d M_2(Z_2) in rho(G_Q). Choose g with rho(g)=(1+2^d)I and fix complex conjugation tau. Put z=g^2 tau g^2 tau^(-1). The square g^2 lies in every quadratic subgroup. On every H_f/K, tau conjugates the abelian ring-class action to its inverse. Therefore z fixes every H_f, while rho(z)=(1+2^d)^4 I. With e=d+2, its scalar minus one is 2^e times a unit. Hence 2^e kills E(H_f)[2^infinity], uniformly in K and f. This permits rational two-torsion; it does not assert its absence.

For the entire finite derivative set I, the relative group is the product of the cyclic residue-unit quotients. The fixed units +/-1 have trivial image, so there is no diagonal quotient left over. For D_ell=sum_(j=1)^ell j sigma_ell^j,

    (sigma_ell-1)D_ell=(ell+1)-Norm_ell.

Together with the point norm this makes c=kum(D_I y_(fI)) invariant at E[2^a] coefficients when 2^a divides ell+1 and a_ell for every ell in I.

In inflation--restriction, both H1(Q,M^H) and H2(Q,M^H) are killed by 2^e because the coefficient module M^H itself is killed by 2^e. Thus 2^e c lifts to b. Set D(c)=2^e b. A change of b is killed by the second factor, so D(c) is canonical and restricts to 2^(2e)c. Additivity, coefficient reduction and restriction to any intermediate old field follow by applying the map to a lift and using this same independence. For an empty derivative set D(c)=2^(2e)c. This is why the lower and upper classes have identical scaling.

There is one descent from the whole conductor field, not one descent per prime. Neither a class number nor the number of cyclic factors enters e. An unmultiplied inverse to restriction, or a factor 2^(2e|I|), would be a different assertion. Howard p.20 uses absence of p-torsion to get his unmultiplied inverse; that argument fails for the actual E[2] and is not used here.

## 4. Bad places, including two

All conductor extensions in this descent are unramified at 2N. Let F'/F be such a finite local extension, allowing F itself to be an old unramified ring-class completion. For the actual allowed local twist B, the identity component B_0 satisfies H1(Gal(F'/F),B_0(F'))=0, as follows.

For the connected special fiber, a cyclic cocycle x has norm zero. Lang's theorem on the original p.557 gives y over the algebraic closure with (Frob-1)y=x. Its norm equation implies (Frob^r-1)y=0, where r=[k':k], so y is already defined over k'. This proves the finite-extension H1 assertion, including even r in residue characteristic two.

Every successive formal-group quotient is an additive k'-module with its unramified semilinear action. The normal-basis theorem identifies it as an induced module and gives H1=0. Induction gives H1=0 for each finite formal quotient. For a fixed cocycle, its solution sets modulo deeper powers lift to nonempty nested closed subsets of the compact formal group. Their intersection supplies an actual coboundary. Smooth reduction is surjective, and the exact sequence then gives H1=0 for B_0(F'). No division by [F':F] is used.

The quotient B(F')/B_0(F') embeds in the finite geometric component group. Its order therefore kills H1(Gal(F'/F),B(F')). A local class in H1(F,B[2^a]) that becomes Kummer over F' has image in H1(F,B) in the restriction kernel. Inflation--restriction and the component bound kill that image; the Kummer exact sequence then puts the multiplied class in the local Kummer image.

Unramified base change preserves the geometric component group. A product over the finitely many fixed primes and allowed local twists gives one C_bad for every such F'/F and a. Thus additive or wild reduction at two introduces no unbounded multiplier. At a good odd prime outside the conductor, restriction to the unchanged inertia group shows the descended class is unramified. Active/moving places have the prescribed full condition. These facts prove the claimed local conditions before transfer.

## 5. The two coordinates and the same Frobenius

Apply the other commuting derivatives first, obtaining lower X and upper Y. The prime (ell) of K is principal and prime to the old conductor. It splits completely in the old ring-class field, so the old residue field is F_(ell^2) and F^2 red(X)=red(X). The new relative extension is totally ramified of degree ell+1.

Choose 2^a Q=LX. Intermediate-field compatibility of D(c) identifies the old class at this split place with the actual Kummer class of LX, so

    f_old=(F^2-1)red(Q)=(a_ell F-(ell+1))red(Q).

Choose 2^a Z=L D_ell Y. Adjust the global cocycle b by a global degree-zero coboundary so that its restriction to the upper-field subgroup H is literally (h-1)Z. For the oriented inertia generator sigma,

    U=(sigma-1)Z-b(sigma)

is H-fixed: expand b(h sigma) in the two ways h sigma and sigma(sigma^(-1)h sigma). It follows that U is an upper GLOBAL field point. Also 2^a U=L((ell+1)Y-a_ell X). The explicit upper-field point

    U0=L((ell+1)/2^a)Y-L(a_ell/2^a)X

has the same multiple. Hence U-U0 is killed by the uniform 2^e. This argument would fail for two arbitrary division points over an algebraic closure.

Reducing b(sigma) gives -red(U), since inertia acts trivially on the geometric residue field. Using red(Y)=F red(X), one gets

    s_new=(a_ell-(ell+1)F)red(Q)+epsilon,  2^e epsilon=0.

The endomorphism identity

    (F-a_ell)(a_ell F-(ell+1))=a_ell-(ell+1)F

follows from F^2-a_ell F+ell=0. Thus s_new=(F-a_ell)f_old+epsilon. Projection E[2^a] -> E[2^m] multiplies points by 2^(a-m), killing epsilon when a>=m+e. The prescribed rational Frobenius congruence rho(gamma)=J modulo 2^(a+1) gives a_ell=0 and ell=-1 to that precision, and then s_new=J f_old at the retained level. No integral decomposition into the J signs is used.

The finite coordinate needs another bit, independently of the previous torsion loss:

    red(L D_ell Y)=ell(ell+1)/2 * F red(LX).

When v2(ell+1)>=a+1 this is 2^a times an F^2-fixed residue point. At the good odd prime, multiplication by two is an automorphism of the formal group. The upper local Kummer class is therefore zero on its unramified Frobenius coordinate.

This coordinate is the actual chosen gamma^2 coordinate. The image of gamma in Gal(H_(fIell)/Q) is outside its abelian K-subgroup. That group is generalized dihedral, so gamma^2 fixes the entire upper field. Thus gamma^2 belongs to its local Galois subgroup. Moreover rho(gamma)^2=1 modulo 2^a, so evaluation at gamma^2 is unchanged by the degree-zero coboundary used above. The vanishing is not obtained by silently changing the Frobenius lift. Consequently f_new=0 already at the working level.

Repeating these computations with any old derivative prime singled out preserves its singular condition. The same L is used throughout. The extra bit is paid by the prime congruence, not by multiplying L.

## 6. Transfer and finite target witnesses

After constructing at level a, reduce to the requested m, extend to the finite Artin coefficient ring, and use the actual character available at that level. No lift of an arbitrary A_m-valued character to A_a is required.

Finite-index Shapiro followed by v tensor [delta] -> theta(delta)v is equivariant for the diagonal action, because theta(g delta)=theta(g)theta(delta). It is an unaveraged finite cochain sum. For a universal family the same formula has values in A_m[G] before every sign evaluation. At old local places Kummer functoriality and the actual local character conditions preserve the Kummer lifts.

Under Mackey decomposition, each coset term uses its transported place and gamma_delta=delta^(-1)gamma delta. The identity rho(delta)rho(gamma_delta)=rho(gamma)rho(delta) brings every term back to the same J relation at the chosen target place. Scalar and group-ring weights commute with these matrices. Lower and upper weights agree because theta factors through the old field. Therefore both coordinate identities survive the finite sum with no class-number denominator or additional multiplier.

Local membership and equality of local cohomology classes supply actual local representatives and degree-zero boundaries in the target Selmer cone. The retained local H0 is essential to avoid extra classes invisible in global H1. Once those standard local complexes are used, equal global classes satisfying the same local conditions yield equal Selmer classes, and their representative difference has a target boundary witness. Retaining that witness under an actual contraction preserves the equality. This is finite existence of witnesses, not a new assertion that arbitrary cohomological equality by itself controls an inverse limit.

## 7. Disposition and remaining imports

The specified finite producer survives this cross-check. Its essential requirements are the all-split Heegner domain, a fixed non-CM scalar-image bound, the one-time canonical scaled descent, actual local triviality/allowed twists at 2N, an actual higher-precision Frobenius target, and compatible transported places. All are kept explicit; no finite-Sha or analytic-rank premise is introduced.

The standard theories named in sections 2-4 remain published classical inputs. Actual existence of the moving character and the permissible new-prime target remains in the separately reviewed A4/Chebotarev argument. This note does not re-prove those inputs. It verifies the finite point/descent/localization implications that the limits receipt leaves open and introduces no further project-specific assumption. No numerical bound on L, prime size, class number or analytic height is asserted.

No manuscript correction is required by this bounded check. The two additional explanations above, independence from a primitive old-conductor character and the actual gamma^2 coordinate, clarify existing implications rather than add hypotheses. Source pins, original-page reads and a receipt accompany this note. No full-RC or global theorem acceptance follows from it alone.
