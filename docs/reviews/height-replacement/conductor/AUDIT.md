# Independent conductor review

## Scope and verdict

Final acceptance is pinned to manuscript SHA-256 `bfc4192de00ef7cfe27df586b9cdb8a9348efe3064495f566258be7152b5dec7`. See the final-version addendum below. Original-version line numbers in the body refer to the separately identified initial hash.

Reviewed manuscript `outputs/diophantine-zq-fable-followup-2026-11-04.tex`, SHA-256 `3f0b79f3d4a074a47ca8165f1d6075f167e51f0d764b774a294cdb8c04e56aa8`, especially lines 637-688 and 741-784. The surrounding definitions and geometric field construction at lines 364-382 and 506-555 were read. The author report was used only to identify claims, not to certify them.

**No mathematical blocker was found in the character, field-degree, or local conductor bounds.** The claimed bounds `[L':Q] <= Q_R M` and `N <= Q_R M^2` follow from the stated geometric and representation-theoretic inputs. No constant needs enlargement. The most compressed passage is the use of the subgroup rule in lines 759-772. `REPAIR.tex` supplies an explicit replacement, including the dyadic conductor-versus-break distinction. This is omitted explanation that can be supplied, not a counterexample or missing mathematical hypothesis.

This review does not independently certify the upstream moduli construction, Pan's applicability, or the identification of the 3-adic and 5-adic representations in lines 730-739. The conductor statement at 5 is conditional on that identification; the local argument itself does not use a 5-adic representation to compute its own residual-prime conductor.

## Primary-source checks

1. Silverberg and Zarhin, *Semistable reduction and torsion subgroups of abelian varieties*, Ann. Inst. Fourier 45 (1995), Theorem 3.5, printed page 406. The actual scan says `n >= 3`, not `n > 3`. Its assumptions permit applying the theorem over `F(A[3])` when `p != 3`, and over `F(A[5])` when `p = 3`. The web OCR dropped the equality sign. The local downloaded PDF and `primary/raynaud.png` preserve the checked page. [Publisher PDF](https://www.numdam.org/article/AIF_1995__45_2_403_0.pdf).

2. J.-P. Serre, *Local class field theory*, in Cassels and Frohlich, *Algebraic Number Theory*, sections 4.1-4.3, printed pages 155-159. The scan confirms upper numbering and quotient compatibility, reciprocity's identification of unit filtration with upper ramification filtration, the conductor/last-break shift by one, and the Artin conductor formula in terms of invariant dimensions. Checked scans are `primary/serre-14.png` through `primary/serre-16.png`. [Primary chapter scan](https://math.arizona.edu/~cais/Prelim/CFT/CaFroCFT.pdf).

The different bound and the numerical estimates below were checked directly, rather than inferred from the manuscript's general citation to Serre's *Local fields*. The subgroup rule follows from compatibility of lower numbering with subgroups and transitivity of Herbrand functions. No claim is made to have recursively reproved the published semistable reduction theorem.

## Character and extension degree

At lines 637-664, the sign class is unramified outside `T`, hence locally zero there. A normalized cocycle inflated from `Gal(L/Q)` restricts trivially as a cocycle to `G_L`. The finite-character square-root criterion used here is correct for `Q_p`: the finite cyclic torsion subgroup has exactly the obstruction detected at `-1`; the valuation factor and the procyclic principal-unit factors allow finite-order square roots. The phrase “constant discrete Galois modules” at lines 654-656 is essential; the coefficient group here has trivial action, rather than its cyclotomic action.

Odd characters modulo each odd prime exist. At 2 the character modulo 4 has the required obstruction. Other prime factors of the Dirichlet character are unramified locally and therefore trivial on local units. Thus the local obstruction is present exactly at the specified finite primes, and reciprocity gives the real invariant. The resulting global cochain beta has values in `mu_(2m)`.

For `h in G_L`, normalized inflation gives `epsilon(g,h)=epsilon(h,g)=1`. Consequently `beta(gh)=beta(g)beta(h)`, and comparison with `beta((ghg^-1)g)` proves conjugacy invariance of the character `beta|G_L`. This justifies normality at lines 682-683.

The ramification cleanup at lines 674-679 is valid. Outside `T`, inertia is contained in `G_L` and beta is a quadratic character there. Continuity into a finite group gives only finitely many unwanted ramified primes. They are odd because 2 belongs to `S`. A quadratic field defined by the product of those primes has the unique nontrivial quadratic restriction on inertia at each of them, introduces no additional odd ramification, and can change ramification only at 2. Multiplying beta by this quadratic character preserves both equations in lines 669-671 and its value group.

By lines 364-382, `M` is squarefree and supported outside `S`, while `S` consists of primes at most `R`. Therefore

`m <= 2 product_(p in T,p odd)(p-1) <= 2 R^R M`.

There are at most `R` primes at most `R`, and each contributing factor is at most `R`; primes outside `S` contribute at most their factor in `M`. Since the image of `beta|G_L` has size at most `2m`, `[L':Q] <= 2m d <= 4 D R^R M`. For `R >= D` and `R >= 10^12`, `4DR^R <= R^(R E0)` by an overwhelming margin. There is no uncounted extension needed to trivialize the character on `G_L`.

## Local bounds and small primes

Lines 754-757 use a degree bound for full torsion, not for a polarized subgroup. Direct calculation gives

`|GL_4(F_3)| = 80*78*72*54 = 24261120`

and

`|GL_4(F_5)| = 624*620*600*500 = 116064000000 = G0`.

Thus the torsion extension `E/F` has degree at most `G0`, and `[E:Q_p] <= a := DG0`. Its normal closure `H/Q_p` has degree at most `a!`. Passing to the normal closure preserves semistability. The semistable inertia action is unipotent, so wild inertia is trivial when the Tate prime differs from `p`.

For the different estimate in lines 742-752, write `e=e(H/Q_p)` and take an Eisenstein polynomial of a uniformizer over the maximal unramified subfield. The valuations of distinct nonzero derivative terms are distinct modulo `e`. They cannot cancel at the minimum. The leading derivative term has valuation `e-1+e v_p(e)`, giving `delta <= e-1+e v_p(e)`.

If `b` is the last positive upper break, the different formula gives

`delta/e = 1-1/e + integral_0^b (1 - 1/|G^u|) du >= b/2`.

Throughout the interval before the last break the nontrivial ramification group has at least two elements. It follows that `b <= 2(1+log_2(a!)) <= 4a^2`. Unramified and tame extensions have no positive break and cause no exception.

For clarity in lines 759-762, use the normal closure `H`. If `u>U0=4a^2`, quotient compatibility puts `G_Qp^u` inside `G_H`. The subgroup rule identifies it with `G_H^(psi_H/Qp(u))`; since `psi(u)>=u>0`, it is a subgroup of wild inertia of `H`. This proves triviality of the Tate action. In particular the group lies in `G_F`, so the extra isogeny factor is the identity. It is not necessary to bound the potentially huge degree of the normal closure by `a`.

For odd `p`, restriction of the locally tame character chi remains tame over `F`. On wild inertia beta therefore has square one, so beta itself is trivial on this pro-p group. This covers `p=3` and `p=5` without assuming either is tame in `F/Q_p`.

At 2, local reciprocity's norm compatibility shows that `chi|G_F` has square one on units. Odd-prime Dirichlet factors are unramified at 2; the factor at 2 is the character modulo 4 or is absent. Thus beta has fourth power one on units even after the quadratic cleanup. With `e=v_F(2)`, logarithm and exponential are inverse on `U_F^(e+1)` and the corresponding ideal. Multiplication by 4 shifts valuation by `2e`, so `(U_F^(e+1))^4=U_F^(3e+1)`. Beta is trivial there. Its conductor exponent is at most `3e+1`, and its relative upper break is at most `3e`, as stated in lines 769-771. There is no missing extra one in the manuscript's break bound.

Now `F/Q_2` is Galois, `F` lies in `H`, and `U0>3e` since `e<=D`. For `u>U0`, `G_Q2^u=G_F^(psi_F/Q2(u))`, and `psi_F/Q2(u)>=u>3e`. This proves the absolute assertion in line 772 without multiplying `3e` by an additional field degree. The direction of the Herbrand inequality matters here and is favorable.

The Artin conductor is its tame codimension, at most 2, plus a Swan integral of codimensions at most 2 over an interval of length at most `U0`. Therefore it is at most `2+2U0 <= E0`. This argument allows a nontrivial tame unipotent part; it does not mistakenly require all inertia to have finite image.

At residue prime 2 use `r_5` and the 3-torsion extension. At residue prime 3 use `r_5` and the 5-torsion extension. At residue prime 5 use the identified `r_3` and the 3-torsion extension. Thus each conductor is computed away from its coefficient prime.

## Large primes and product bound

For `p>R`, lines 775-778 correctly use `F/Q_p` of degree at most `D<p`, so it is tame. Since every prime of `S` is at most `R`, A has good reduction over F. Absolute wild inertia is already contained in `G_F`, acts trivially on the Tate module, and acts trivially through beta by the odd-prime argument. The Swan conductor vanishes and the full exponent is at most 2.

Outside `T`, the isogeny factor is the identity on inertia because `L` is unramified, the Tate action is unramified by good reduction, and the cleaned beta is unramified. The exponent is zero. The potentially remaining primes above `R` therefore belong to the squarefree support of `M`. Multiplying local bounds gives

`N <= product_(p<=R) p^E0 * M^2 <= R^(R E0) M^2`.

Small primes in `M` can occur in both displayed factors, but this merely weakens an upper bound. The estimate includes every prime and every conductor exponent once as needed.

## Suggested edit

Use `REPAIR.tex` in place of lines 741-773, or extract its subgroup-rule and dyadic sentences. Its purpose is to expose the normal closure, specify when an absolute ramification group lies inside the local field group, and distinguish a conductor exponent from the largest upper break. The degree, conductor, and final height constants remain unchanged. No upstream source was edited by this reviewer.

## Final-version addendum

The parent incorporated a shorter clarification into the manuscript. I read `work/independent-height-review-20261104/clarifications.diff`, re-read the local conductor passage, and independently computed the current manuscript SHA-256 as `bfc4192de00ef7cfe27df586b9cdb8a9348efe3064495f566258be7152b5dec7`.

The inserted paragraph at current lines 796-809 is mathematically correct. Since `L/Q` is Galois, its completion `F/Q_2` is Galois. The existing degree/different argument with `a=D` bounds its last upper break by `4D^2`. At greater absolute indices the group lies in `G_F`. The stated subgroup identity and `psi(u)>=u` then make beta trivial when `u>max(4D^2,3e)`. This maximum is at most `U0`, since `e<=D` and `G0>=1`. This argument does not incur any factor from `[L':Q]`.

I accept the local ramification and conductor argument in this final version, within the scope stated above. The fuller `REPAIR.tex` is optional exposition; it is not a required mathematical repair after this clarification. The references to lines 741-784 elsewhere in this audit refer to the initial manuscript hash. In the final hash, the local argument begins at line 767, the torsion extension at line 780, and the dyadic explanation at line 791.
