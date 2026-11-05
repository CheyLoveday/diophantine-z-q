# Eighth closure pass: finite Chebotarev applications

Review date: 2026-11-05. Reviewer: root assistant. This is the bounded A067 application review. The manuscript is unchanged, SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. This does not certify the upstream duality, coefficient or local-representation theorems that use these realizations.

## Source statement and conventions

Use Milne, *Class Field Theory*, v4.03, August 6, 2020, VIII Theorem 7.4, printed p.259. For a finite Galois extension L/K and a conjugacy-stable subset C of its group, the unramified primes whose Frobenius belongs to C have Dirichlet density `|C|/|Gal(L/K)|`. A nonempty conjugacy class therefore supplies infinitely many primes after any finite exclusion. V.1, printed pp.152-153, defines Frobenius by the residue action `x -> x^N(p)`; V.1.9, p.153, gives the change-of-place conjugation rule. This is arithmetic Frobenius, the convention used here. The exact source bytes are those already pinned as `milne-cft`.

For an actual automorphism sigma of L/K, take its whole conjugacy class C. The rational prime determines C, not a distinguished representative. To realize sigma itself, choose a place of L above that prime: if one place has Frobenius `g sigma g^-1`, transporting it by `g^-1` gives sigma. Bases, torsion coordinates and cochain evaluations must be transported with that choice. The manuscript explicitly chooses a place at the non-class-function uses. A prime alone would not suffice there.

## Application register

| Manuscript use | Finite normal extension | Required element and compatibility |
| --- | --- | --- |
| 3282-3286, additional split ideals generating Cl(K) | Hilbert class field H_K, normal over Q | An element of `Gal(H_K/K)` representing the desired ideal class. It fixes K, so its rational prime splits in K. |
| 3297-3443, simultaneous moving character | Normal closure over Q of `K(mu_(2^B'), E[2^B'], alpha_a^(1/2^n) for all a)` | Restriction of the actual sigma constructed in `G_(K(mu_(2^infinity)))`, after multiplication in the radical-fixing kernel. |
| 2312-2349 and 7999-8067, fixed-witness detector | `F_0 E[2^M] A[2^M] ([2^M]^{-1}(Q))`, including the splitting field of the full division-point torsor | Restriction of one fixed `sigma=h tau`, with h in the Tate kernel and fixing F_0. |
| 4480-4562, kernel localization | At each finite coefficient stage, normal closure of the finite cochain quotient together with the required Tate, ring-class, quadratic and old-diagram fields | Restriction of the corresponding actual sequence component, multiplied by the specified conjugation element. |
| 4819-4844, opposite-sign localization | Same construction, with both classes and their required cochains included in a single quotient | The component of the actual kernel sequence already selected to detect both classes. |
| 9334-9355 and 9513-9524, trace and determinant limits | At each desired precision, compositum of the kernels of all finite reductions of the finitely many constituent representations and retained characters | Image of one chosen `g in G_Q`. No independent prescription of constituent values. |
| 9399-9415, finite products and coefficientwise identities | Same finite representation quotient, enlarged to the precision needed for the given finite product and Fourier coefficient | Images of the prescribed `g_1,...,g_a`; choose the realizing primes successively and distinctly. |
| 9451-9458, agreeing constituents | Same joint finite reductions for the two constituents | Class-function equality at good prime Frobenius extends to every g by simultaneous approximation and continuity. |
| 9541-9566, inertia-difference comparison | Joint quotient for both U and omitted-prime V forms, including their retained characters | Images of the four actual elements `g`, `g tau`, `g phi`, `g tau phi` in that one quotient. |

The CRT graph realizations at 2003-2025, 9580 and 10447 are abelian applications with their compatibility proved in batch 7. They are not extra uses of an infinite Chebotarev theorem.

## 1. Hilbert class generators with split rational primes

The class group is finite. For each desired generator choose the corresponding element of `Gal(H_K/K)` under the Hilbert-class Artin isomorphism. The field H_K is normal over Q because conjugation preserves the property of being an unramified abelian extension of K, hence preserves its maximal such extension. The conjugacy class over Q is contained in `Gal(H_K/K)` since this subgroup is normal. Chebotarev over Q therefore gives rational primes split in K, with a place above each one having the required Artin element. Their oriented K-primes represent the desired classes. Avoiding previous rational primes gives distinct conjugate pairs.

This uses the Hilbert class field and its Artin isomorphism, not a claim that arbitrary prescribed residue conditions are independent of it. No further local prescription is placed on these extra class generators. The active and old-support primes are included first; the extra primes can avoid them all. The allowed K in the consumer has the stated splitting at 2N, which is a separate input to its choice of oriented primes over that support.

## 2. Moving-character compatibility before density

Set `F_infinity=K(mu_(2^infinity))` and `L_infinity=F_infinity(alpha_a^(1/2^n):a)`. Although the base field is infinite over Q, `L_infinity/F_infinity` is a finite abelian Kummer extension. It is used only to construct an automorphism; density is later applied to a finite normal closure over Q.

For a relation `product(alpha_a^b_a)=y^(2^n)` in F_infinity, y belongs to a finite cyclotomic layer. At each active odd prime this layer is unramified over K. Applying its normalized valuation gives

    2^n divides sum_a b_a m_j^(a)

for each nonzero-weight index j. The prescribed multiplier exponent is the negative weighted sum of these integers, so it is zero modulo `2^n`. Weight-zero places, including the dyadic places, contribute nothing. Hence the specified multipliers respect every multiplicative relation modulo powers. The Kummer pairing supplies an actual automorphism over F_infinity, and extending it to an algebraic closure supplies sigma_0. This does not assume independence of the radicands or divide by the class number.

The subsequent Tate modification is in the actual kernel fixing L_infinity. Here are the group checks used to justify that assertion. If the fixed determinant-one Tate image contains Gamma_d, its subgroup obtained after imposing K has index at most two, so it contains the squares `U(2^(d+1)Z_2)` and `V(2^(d+1)Z_2)`. The displayed four-unipotent identity produces every diagonal unit congruent to one modulo `2^(2d+2)`. Gaussian decomposition then puts `Gamma_m`, `m=2d+2`, in this subgroup. Commuting its diagonal `diag(1+2^m,(1+2^m)^-1)` with its upper and lower unipotents yields the full unipotent groups at level `2m+1`, since `v_2((1+2^m)^2-1)=m+1`. A second Gaussian decomposition gives `Gamma_(4m+2)` in the closure of its commutator subgroup.

Commutators lift to the absolute Galois group over F_infinity, and fix L_infinity because its Galois group is abelian. The image of the compact radical-fixing group is closed, so this entire principal congruence subgroup lies in the image of that actual kernel. Thus each Tate multiplier in (4.4d) can be lifted without changing any prescribed radical action or cyclotomic action.

The trace calculation in lines 3387-3412 also holds. If a trace is too close to either 2 or -2, its distance to the other has valuation two. With even diagonal entries, the determinant-one condition makes the lower-left entry odd and multiplication by `U(2^nu)` changes trace by exact valuation nu. With odd diagonal entries, the two displayed diagonal multipliers change trace at one of the valuations at most `2nu+1`. All these changes have valuation at least three, preserving the distance two to the other forbidden value. This produces the stated sigma with both distances bounded by `c_E`.

Now choose `B' >= max(B,n)` and `B' > c_E`. The finite normal closure in the table contains every radicand root and every needed torsion and cyclotomic coordinate. Sigma is already defined on an algebraic closure, so its restrictions automatically agree on intersections. Its Frobenius class is nonempty. At the chosen place, sigma fixes K and the roots of unity, giving split r and `r=1 mod 2^B'`, while its radical action gives the required power-residue values. The trace congruence at this precision preserves both valuations. Finally

    det(1 +/- Fr_r) = 1 +/- a_r + r = 2 +/- tr(rho(sigma)) mod 2^B'

preserves their bound too. This establishes the compatibility consumed by Chebotarev. The ring-class connecting-map convention translating the radical values to xi remains in A068; it is not proved by density.

## 3. One fixed detector element

The fixed nontorsion point Q is on `A=E^(D_w)`. On the kernel H of its Tate representation, its Kummer cocycle is an additive map to T_2A with compact image. That image is a closed Z_2-submodule and its rational span is Tate-invariant. If zero, the rational cocycle would descend to the Tate image and the nonidentity central scalar would make it a coboundary. Kummer injectivity excludes that. Irreducibility therefore makes the image a full lattice.

Intersect H with `G_(F_0)` for the finite normal auxiliary field. This has finite index d, and multiplication by d on the original image lies in the new image, by `c(h^d)=d c(h)`. Thus it still contains `2^a T_2A` for a fixed a. Choose a primitive integral +1 eigen-row b for the actual conjugation matrix C. Its kernel equation gives a saturated rank-one lattice, so it can be primitive even though the integral +/- eigenspaces need not split T as a direct sum. Choose `b(t_0)=1` and h in this kernel with `c(h)=2^a t_0`.

The actual element `sigma=h tau` then satisfies

    rho_A(sigma)=C,
    c_Q(sigma^2)=(1+C)2^a t_0,
    b c_Q(sigma^2)=2^(a+1).

It acts on F_0 as tau. Since D_w is positive and h_* negative, it fixes `sqrt(D_w)` and negates `sqrt(h_*)`. No disjointness of F_0 and the Tate or division-point fields is required. Q is rational on A, so the full `2^M`-division torsor is Galois-stable and its splitting field is finite normal. Including that whole field and the two torsion fields gives the table's finite extension. The same sigma works before M varies. Its selected Frobenius representative preserves all the required conditions simultaneously, including the fixed nonzero Kummer evaluation once `M>a+1`.

This reviews the detector compatibility. Its earlier production of Q and subsequent finite-field theta interpretation remain separate inputs.

## 4. Cochains, sequence components and the exact matrix equality

A continuous function from a finite power of a profinite group to a finite set factors through a finite quotient in each argument. To see this, its fibers form a finite clopen partition of a compact domain; a finite product-open refinement exists. Intersect the finitely many relevant open subgroups and take their normal core. The resulting open normal subgroup makes the function constant on its coordinate cosets. Apply this to all the finitely many finite-coefficient basis cochains in degrees zero, one and two at the stage in question. Include the finite coefficient action as well.

These cochains are on G_K. Their open normal subgroup has finite index in G_Q, since K/Q is quadratic; taking its G_Q-normal core gives a finite normal extension over Q. Add the finitely many torsion, ring-class, quadratic and old-diagram fields required at this stage. This defines the finite compositum in the register. There is no need to include an infinite ring-class tower or the full infinite Tate field.

The exact-kernel element selected by the preceding representation argument is a sequence of actual Galois elements. Use its component at the current stage, with the specified conjugation multiplier. Its restriction to the compositum is an actual automorphism. It fixes or conjugates the required auxiliary data by construction, so the conjugacy class is compatible. The conjugation multiplier restricts nontrivially to K, hence the chosen rational prime is inert in K. Choosing its place specifies the exact representative and hence its square in G_K. All relevant cochains evaluated at that square and the finitely many other arguments agree at the retained precision.

Use retained precisions `n(i) <= i` tending to infinity. For every fixed finite coefficient quotient, the localization matrices and evaluation matrices then agree on a cofinite set of inner stages. Their limits are therefore equal in Lambda, which is the exact equality (5.4). Only afterward multiply by the O-minimal-model inclusion I_j. This justifies the equality even if I_j has denominators varying with the outer index. A long t-adic approximation was not treated as a 2-adic approximation after t becomes a unit.

The same proof handles the opposite-sign classes by including both classes' cochains in that one finite quotient. The upstream existence of an actual kernel sequence detecting both classes is part of the representation/localization argument. Chebotarev does not infer that existence merely from separate detectability. This closure uses that actual sequence, and verifies its finite realization.

## 5. Simultaneous approximation of trace and determinant operators

Fix the actual theta stage and operator set U. There are finitely many characteristic-zero constituents over a fixed finite extension of Q_2. Each continuous representation has a stable lattice: the compact orbit of an initial lattice spans a bounded, finitely generated lattice invariant under the compact image. Reducing these lattices and the retained finite characters to any chosen precision gives finite image representations. The intersection of their kernels is open normal in G_Q and defines the required finite normal extension.

For any actual g, apply Chebotarev to its image in this joint quotient. Trace and determinant are conjugacy-invariant, so their values at a realizing prime agree to that precision in every constituent. As precision grows, the corresponding scalar operators converge on the finite-dimensional characteristic-zero space. Repeated constituents and their multiplicity spaces retain identity action on the latter, as specified in the manuscript. No integral projector onto constituents is needed.

Finitely many Fourier coordinates inject that space. The module generated by the integral Hecke and diamond translates embeds in the integral coordinate lattice. It is a finite module over the complete coefficient DVR and is closed. Every approximating good Hecke or determinant operator preserves it, hence their limits preserve it. Changing from constituent coordinates to these Fourier coordinates may require a fixed extra precision to clear denominators. There is no uniform precision claim across all stages, and none is needed: the stage was fixed first.

For a finite product of a such operators, approximate each prescribed g_j to sufficient precision and choose the primes successively outside the level, the Fourier index n and the previous primes. Matrix multiplication and the coefficient functional are continuous, so one common sufficiently high precision handles this finite product. The Hecke formula then has no unwanted n/q terms because of these exclusions. This proves the coefficientwise identity; it does not choose a single prime list for every Fourier coefficient.

For coinciding constituents, good Hecke trace and determinant equality is a class-function equality. Joint approximation proves equality at every actual g, so the scalar operators agree on overlapping summands. This particular argument does not need an isomorphism of the representations. The separate semisimple-identification application is still A064.

Finally, the four inertia-difference representatives are restrictions of the actual four elements `g`, `g tau`, `g phi`, `g tau phi` in one quotient for both U and V. Their restrictions agree on all field intersections automatically. Apply the theorem separately to each class with finite exclusions. The omitted V representation is unramified at the whole prime p, so the action of tau on it is trivial. This is the local-representation input; once supplied, the finite prime realization preserves it together with every retained character. No independent specification of incompatible local actions has been made.

## Disposition

A067 is closed for the finite-compositum, conjugacy-class, choice-of-place and approximation applications registered above. This is a direct root review, not an independent referee verdict. It consumes the fixed open-image and Kummer inputs, the actual kernel-detection sequence, the coefficient/local-representation identities and the Hilbert-class Artin correspondence. In particular A032, A064, A068, A070 and A080 retain their own open source or map obligations. Closing the density applications does not close these inputs or prove the restricted converse as a whole.
