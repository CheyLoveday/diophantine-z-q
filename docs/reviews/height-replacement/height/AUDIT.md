# Independent review of the CM branch and height transfer

Reviewed 2026-11-04. This review does not edit the manuscript.

## Frozen source and scope

Source: `outputs/diophantine-zq-fable-followup-2026-11-04.tex`.

SHA-256 independently checked: `3f0b79f3d4a074a47ca8165f1d6075f167e51f0d764b774a294cdb8c04e56aa8`.

The review covers lines 557–606, the transfer in lines 787–832, the constants at lines 363–385, and the elementary consumption of the resulting bound at lines 846–873. The author report and replacement files were read as claims. The cited primary publications were independently opened. This review does not certify the intervening construction of the Galois representation, its modularity, or its conductor estimate. In the non-CM branch it assumes those steps supply the stated common constituent over L', N ≤ Q M², and [L':Q] ≤ Q M.

Verdict: **pass within this scope**. I found no missing hypothesis or numerical error in the CM branch or the quantitative height transfer. The exponent 24 and the existing B_cm, C_cm, and H_6 constants survive. No mathematical repair is required in these portions. The non-CM conclusion remains conditional on the separately audited antecedents just listed.

## Primary-source checks

1. [Fowler, publisher full text](https://www.cambridge.org/core/journals/mathematical-proceedings-of-the-cambridge-philosophical-society/article/some-uniform-effective-results-on-andreoort-for-sums-of-powers-in-mathbbcn/A72ABDB14BEB62DE7E9B47953B77DBDC), Proposition 2.7, article-relative pp. 9–10, printed pp. 615–616. It applies to every negative order discriminant Δ with h(Δ) ≤ k and gives sqrt(|Δ|) ≤ 2k² exp(21000k²). Unlike Proposition 2.5, it has no exceptional-field exclusion. Its proof uses the unconditional bound in Proposition 2.6 and the order class-number formula, and separately handles fundamental discriminants −3 and −4. This supports lines 564–569 exactly.

2. [Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri, published article](https://tylergenao.com/wp-content/uploads/2017/09/faltings-heights-of-cm-elliptic-curves-and-special-gamma-values.pdf), p. 1 and equation (6.2), pp. 13–14. The metric is the original Faltings metric. Equation (6.2) uses the analytic discriminant (2π)^12 η(τ)^24. It is the general elliptic discriminant formula, attributed there to Silverman, Proposition 1.1. The Q(j)-coefficient restriction of the surrounding Proposition 6.1 is used later in that proof, not in this formula. Lines 572–588 use only the general formula. The paper also explicitly proves potential good reduction for CM elliptic curves in its proof of Theorem 1.3, p. 15.

3. [Javanpeykar, published article](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf), Theorem 1.1.1, printed p. 90. The upper bound is 13·10^6 g deg_B(X)^5. Section 2.1 uses the differential metric (i/2)∫ω∧conjugate(ω), and Section 2.3, printed p. 98, identifies its height with the stable height of the Jacobian. Thus there is no normalization shift in lines 797–803. The modular-curve discussion at printed pp. 92–93 also bounds Belyi degree by subgroup index.

4. [Gaudron–Rémond, published article](https://lmbp.uca.fr/~gaudron/art13.pdf), introduction, printed pp. 2058–2060, and Section 9, printed pp. 2098 and 2101–2102. Their κ(A) is ((14g)^(64g²) [k:Q] max(h_F(A),log[k:Q],1)²)^(1024g³), with original stable Faltings normalization. Theorem 1.4 gives isogenies in both directions with this degree bound. It imposes no principal-polarization hypothesis. Section 9 explicitly uses the Bost lower bound h_F(C) ≥ −3 dim(C)/2. This supplies the estimates in lines 591–595 and 805–822 without any extra field extension or maximal-order replacement.

## CM reasoning and constants

Lines 558–563 are valid. An idempotent e_11 in End_L^0(A) defines the elliptic image E of an integral multiple. The complementary idempotent defines another elliptic image. The two off-diagonal matrix units provide inverse rational isogenies between these images. Consequently E² and A are L-isogenous. The corner algebra e_11 M_2(k)e_11 is k, so E has CM by an order of k. The CM class polynomial is irreducible over Q of degree h(Δ); since j(E) belongs to L, h(Δ) ≤ [L:Q] ≤ D. No bound on the degree of the initial E²-to-A isogeny is needed.

For each complex embedding, a reduced CM period has y = sqrt(|Δ|)/(2a) for a positive integer a. Hence sqrt(3)/2 ≤ y ≤ sqrt(|Δ|)/2. All conjugates have the same full endomorphism-order discriminant. After passing to a good-reduction field, the finite discriminant term vanishes. Expanding η in the formula checked above gives the exact expression at lines 577–580.

Here is an independent estimate of the error term. For ρ = exp(−2πy),

    −2 Σ_n log|1 − q^n|
      ≤ 2 Σ_n ρ^n/(1 − ρ^n)
      ≤ 2ρ/(1 − ρ)².

Since ρ ≤ exp(−π sqrt(3)) < 1/100, the right side is less than 200/9801. Also −(1/2)log y < 1/10. Discarding −log(2π) and enlarging their sum to 1 proves h_F(E) ≤ π sqrt(|Δ|)/12 + 1. Substitution of Fowler's inequality gives

    h_F(E) ≤ (π/6) D² exp(21000D²) + 1
           ≤ D² 3^(21000D²) + 1 = B_cm.

For source E², the dimension-two specialization of κ is exactly

    (28^256 d max(h_F(E²),log d,1)²)^8192.

Additivity gives h_F(E²) ≤ 2B_cm; log d ≤ D ≤ 2B_cm. Thus lines 594–600 follow from height variation by at most half the logarithmic isogeny degree. In particular the factor 4096 is correct. Finally,

    log(2B_cm) ≤ log 4 + 2 log D + 21000D² log 3
               ≤ 2 + 2D + 42000D²,

and 256 log 28 < 1024. The parenthesis is at most 1028 + 5D + 84000D², which is precisely C_cm as defined. The isogeny theorem is applied over L, not over the auxiliary good-reduction field. Stable-height invariance fully justifies this separation.

## Non-CM transfer and the exponent 24

Lines 788–794 are valid given the common-constituent assertion. Invariants in a finite-dimensional Hom space commute with extending the coefficient field: the invariant space is the intersection of kernels of linear operators, and finitely many of these kernels already define that intersection. Thus a nonzero invariant after coefficient extension yields a nonzero invariant before extension. Faltings then gives a nonzero L'-homomorphism A → J. Absolute simplicity makes its kernel finite. Poincaré reducibility gives an L'-isogeny A × Z → J, with g ≥ 2.

For the group Γ_1(N), the index in SL_2(Z) is N² times a product of factors (1 − p^−2), hence at most N². The map to X(1), followed by the usual j/1728 coordinate, is Belyi. Its degree is at most this index; quotienting by the central sign can only reduce the degree. Riemann–Hurwitz also bounds the genus by the degree. Therefore the use of g ≤ N² and deg_B ≤ N², and hence h_F(J) ≤ 13·10^6 N^12, is justified at lines 795–800.

The constants have ample slack but preserve the desired power of M. From Q ≥ 10^12, M ≥ 1, and N ≤ QM²:

    h_F(J) ≤ Q^13 M^24,
    g ≤ Q^3 M^4,
    d' ≤ QM.

The first follows because 13·10^6 ≤ Q; the genus inequality deliberately enlarges Q² to Q³. With T = QM^4, one has

    log(14g) ≤ log 14 + 3log Q + 4log M ≤ 5T,
    log d' ≤ log Q + log M ≤ 2T,
    log max(h_F(J),log d',1) ≤ 13log Q + 24log M ≤ 19T.

For the third inequality, max(h_F(J),log d',1) ≤ Q^13 M^24. The bounds log Q ≤ Q and log M ≤ M^4/4 suffice. Thus the parenthesis in line 810 is at most

    320 Q^7 M^12 + 40 Q M^4 ≤ 360 Q^7 M^12.

Multiplication by 1024g³ ≤ 1024Q^9M^12 gives exactly 368640Q^16M^24. Since 368640 ≤ Q, line 817 follows. This explicitly verifies the power 24; no factor depending polynomially on g has been omitted.

For the complement, h_F(Z) ≥ −3 dim(Z)/2 ≥ −2g, including Z of dimension zero. Additivity and isogeny height variation therefore yield the first inequality at lines 824–825. The last absorption amounts to

    Q^(−4) + 2Q^(−14) M^(−20) ≤ 1/2,

which holds for Q ≥ 10^12 and M ≥ 1. Since Q^17M^24 ≥ 1, the same bound holds for max(1,h_F(A)).

## Consumption by the six-contact estimate

Combining the CM and non-CM cases gives the exact bound at lines 829–831. The CM estimate is independent of M, and multiplying its constant by M^24 is valid because M ≥ 1. No change to the six contact values or to M_S is involved.

The elementary arithmetic in lines 847–873 is consistent with this output: X_D ≤ 3X, log(X_D+2) ≤ 2X_D for X_D ≥ 1, and the displayed theta bound imply h([z_m]) ≤ 10000·2^24 X. Moreover,

    40·10000·2^24 + 96 = 6,710,886,400,096 < 10^13.

Thus the retained downstream comparison consumes the reviewed bound with H_6/2. This paragraph checks that comparison's numerical use; it does not independently re-audit the cited theta-coordinate theorem or the preceding geometric construction.

## Proposed changes

No change is necessary to repair a mathematical gap within the reviewed scope. Optional expository additions would be to name the Γ_1(N)-to-X(1) map as j/1728, display the intermediate 360Q^7M^12 estimate, and cite Silverman's general discriminant formula alongside equation (6.2). These would make already valid transitions easier to inspect. They would change no hypothesis or constant.
