# First closure pass: elementary interfaces and the generator height argument

Review date: 2026-11-05. Reviewer: the root assistant. This is a direct source/application review, not an independent human or second-agent review.

Baseline manuscript: SHA256 `c59598ba474a1512dd03787c2bc9ff093a3c3a8a0604f96d5f8bcfa140c61693`. Lines 1–10557 retain their numbering after the de Rham repair; lines 711–714 replace the de Rham citation. Two additional lines, 277 and 281, move the rank-one sentence after the torsion calculation. Correction on 2026-11-05: that reordering was not mathematically necessary. Full rational 2-torsion and finite generation already give the required rank from the index eight; see the correction to F003 in the findings.

Source versions are the byte-pinned Matiyasevich 1971 English translation and Silverman 2009 second edition listed in the source inventory. No equivalence to a different edition is used.

## A048: universal MRDP predicate

Disposition: **closed for this application**, conditional on the main integer-defining polynomial theorem exactly as the corollary states.

Matiyasevich's definition on printed page 2 concerns predicates in any finite number of positive-integer arguments. The Basic Theorem on page 3 covers every enumerable such predicate. It does not merely assert undecidability.

Choose one effective universal machine enumeration. On positive integers define `H(a,b)` to mean that machine `a-1` halts on input `b-1`. Simulation gives a single partial algorithm with domain H, so H is an enumerable two-place predicate in precisely the source's sense. The Basic Theorem supplies one fixed integer polynomial `R(a,b,y)` with positive-integer existential witnesses y. Substitute `a=e+1`, `b=n+1`. Replace each positive witness `y_i` with `1+sum_j z_ij^2`, with four ordinary integer variables. This is exactly the positive-to-integer conversion on source page 2 and gives a fixed D with integer witnesses for all nonnegative e,n. No pairing function or encoded elliptic coordinates replace the two parameters.

Now substitute the already asserted integer-defining relation P_* for each integer witness z, using a separate rational witness block for each copy. In the sum `D^2+sum P_*^2`, vanishing over Q forces every summand to vanish, since Q is ordered. Conversely, finitely many integer witnesses admit all their separate rational witness blocks. This proves the displayed equivalence at manuscript 6198–6234. Any zero-variable D may receive a dummy existential variable, so the stipulated positive arity causes no difficulty.

The many-one maps at 6250–6273 are also uniform: polynomial specialization and finite coefficient coding are computable; a program enumerating rational tuples and evaluating exactly can be compiled effectively from the finite polynomial code. It ignores its own input, so diagonal halting gives the reverse reduction as written. Invalid codes are explicitly handled. The manuscript correctly does not transfer the bounds for P_* to U.

This closes the enumeration, parameter-domain, and witness-translation obligations. It does not prove the premise that P_* defines the integers.

## A055: four-square interfaces

Disposition: **closed for the stated source/application interface**. The source is now identified: Matiyasevich 1971, printed page 2, states Lagrange's theorem for every nonnegative integer and applies the same four-square witness conversion. The classical theorem is an external input; this review does not claim a new proof of it.

At lines 190–197, for positive `1/s=a/b` with a,b positive integers, choose integers u_i with `sum u_i^2=ab`. Then `z_i=u_i/b` gives `s sum z_i^2=1`. Conversely this equation makes the sum nonzero and nonnegative, so s is positive. It never infers integrality from a sum of rational squares.

At lines 199–201, a nonnegative rational is a sum of four rational squares by the same construction, with zero handled by four zeros. Thus `a=sum z_i^2` and `a^2=x^2` are equivalent to `a=|x|`.

At lines 350–357, the four inputs are first forced into the integer-index model by the multiplication relation. Soundness therefore makes their squared indices ordinary integer squares. Completeness and Lagrange's theorem represent every nonnegative index. This consumes multiplication soundness/completeness and the model's addition contract, as explicitly acknowledged by the manuscript; four-square representation over Q alone is not being used as a definition of the integers.

## A059: finite generation and the two reduction primes

Disposition: **closed for this application**, consuming the index-8 two-isogeny conclusion from A058.

The precise references in Silverman 2009 are VIII Theorem 6.7, printed p.239, and VII Proposition 3.1, printed p.192. The former gives finite generation over a number field. The latter gives injectivity of prime-to-residue-characteristic torsion under good reduction.

The independent exact script `check_generator_arithmetic.py` uses both an explicit list of affine pairs and the quadratic-character point count. At `(17,s-6)` and `(23,s-5)`, s satisfies its defining polynomial modulo the indicated prime, d is nonzero, and the discriminant `64 d^6` is nonzero. The resulting group orders, including the identity, are respectively 20 and 24. The complete pairs and residues are in `generator-arithmetic.json`.

For a torsion prime different from 17 and 23, its primary subgroup injects into both reductions and its order divides gcd(20,24)=4. The 17-primary subgroup injects at 23 and is zero because 17 does not divide 24. The 23-primary subgroup injects at 17 and is zero because 23 does not divide 20. Consequently the total torsion order divides 4. The four displayed rational two-torsion points attain that bound. Independently of the total torsion order, finite generation and `|E[2](K_0)|=4` give `|E/2E|=2^(rank+2)`: for every finite abelian torsion group T, `|T/2T|=|T[2]|`. The separately established index 8 therefore forces rank one. No rank oracle is used, and this is not yet a proof that the chosen point generates the free part.

## A060: canonical height normalization and exhaustive small-height search

Disposition: **closed for this application**, consuming the PID and rank/torsion conclusions from A058/A059.

Use Silverman 2009, VIII Theorem 9.1, the definition immediately following it, Remark 9.2 and Theorem 9.3, printed pp.247–249. With f=x of degree 2 the normalization is `2 hhat(T)=lim 4^-m h_x(2^m T)`, exactly as in manuscript line 300. The theorem gives quadraticity, invariance under torsion translation, and positivity on nontorsion points. Using the doubled normalization without adjusting this factor would be wrong.

Here is a direct check of the numerical height bound, so no unidentified height constant is imported. Write `delta=3-s`, `s^2=2`, and `x=a/b` with a,b primitive in the PID Z[s]. At either real embedding `1<delta^2<25`. Thus

`max(|a|,|b|)^4 <= max(|(a^2+delta^2 b^2)^2|, |4ab(a^2-delta^2 b^2)|) <= 676 max(|a|,|b|)^4`.

For the upper bound, the two entries are at most `26^2 M^4` and `104 M^4`. For the lower bound, the first entry alone is at least M^4. These arguments work for real a,b of either sign.

No common prime divisor of the two duplication forms lies away from 2 delta: reduction modulo such a prime would give both `a^2=-delta^2 b^2` and either `ab=0` or `a^2=delta^2 b^2`, contradicting primitivity. At the prime (delta), a unit a gives no common factor; if a is divisible by delta and b is a unit, the first form has valuation at most 4. In the equality case `v_delta(a)=1`, this uses that -1 is a nonsquare in F_7.

At (s), if only one of a,b is a unit the first form is a unit. If both are units, put `u=a/(delta b)=A+Bs` in Z_2[s], with A odd. If B is even then `v_s(u^2+1)=2`; if B is odd it is 3. Indeed the constant term `A^2+2B^2+1` has valuation 2 or at least 4, while `2ABs` has valuation at least 5 or exactly 3, respectively. Hence the first duplication form has valuation at most 6.

The common ideal therefore has norm at most `2^6 7^4=392^2`. Dividing logarithms by `[K_0:Q]=2` gives

`4 h_x(T)-log 392 <= h_x(2T) <= 4 h_x(T)+log 676`.

The projective identity point is included; the height uses the homogeneous pair, so a zero denominator does not invalidate this estimate. Telescoping gives `h_x(T)<=2 hhat(T)+log(392)/3` and `2 hhat(T)<=h_x(T)+log(676)/3`.

The exact replay gives `x(2R)=(57-28s)/8`. Its primitive minimal polynomial is `64 X^2-912 X+1681`. Both real roots exceed 1: for the smaller root it suffices that `49>28 sqrt(2)`, whose squared comparison is `2401>1568`. Its multiplicative Mahler measure is therefore 1681 and its absolute logarithmic height is log 41. If `R=mS+T` with torsion T and |m|>=3, quadraticity now gives exactly the inequality at line 305. The strict comparison was replayed using only integers.

For any quadratic alpha of height less than log 9 with primitive minimal polynomial `aX^2+bX+c`, a positive, its Mahler measure M satisfies `M=exp(2h(alpha))<81`. The identity follows from the product formula and multiplicativity of the nonarchimedean polynomial Gauss norm. The elementary symmetric functions give `a<=M`, `|c|<=M`, `|b|<=2M`. These imply the manuscript's slightly larger closed bounds. For alpha in Q(sqrt(2)) but not Q, the discriminant is `2k^2` with a positive integer k. The coefficient bounds imply `2k^2<=162^2+4*81^2`, hence `k<=162`. Rational alpha has coprime numerator/denominator with maximum less than 9; the manuscript's closed box up to 9 is again a valid over-enumeration.

The exact replay enumerated all 7,004 primitive quadratics in that box, their 14,008 distinct roots, and all 111 rational candidates. Its necessary-and-sufficient square test found precisely the seven stated abscissas. For v nonzero, a square `(a+bs)^2=u+vs` has `a^2-b^2*2=+/-sqrt(u^2-2v^2)` and `a^2=(u+t)/2`, giving the tested criterion; v=0 and a=0 are handled separately. Every returned root is substituted back exactly.

The replay also verified that the four nontorsion abscissas are exactly those of R translated by the four two-torsion points, and verified the coordinate change sending 2R to P0. Points with the same abscissa are negatives, which have the same canonical height. Thus a smaller free generator S in this search would have height hhat(R), contradicting `hhat(R)=m^2 hhat(S)>0`. This completes the bounded generator-saturation application without changing the paper's constants.

## A009 and A056 remain separately tracked

The de Rham replacement has been inserted into the working TeX and its published source statements have been located, including the previously missing algebraic/analytic comparisons. The manuscript rebuild passed with no TeX errors or unresolved references. Separate acceptance of the repair is still pending.

Silverman III Exercise 3.7 has a visible plus sign in its displayed omega formula on p.105. The repository uses `psi_(2n)/(2 psi_n^4)` instead. Its recurrences match the source, and the suspected source typo is being checked against the author's errata before the final convention note is written. Neither this issue nor a finite computational check is silently treated as a proof of an unchecked general formula.
