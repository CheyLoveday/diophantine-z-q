# Third closure pass: height variation and Selmer corank

Review date: 2026-11-05. Reviewer: root assistant. Direct source and application review, not an independent second review. The two applications below consume their separately listed geometric and arithmetic premises.

## A006: the needed direction of height variation and product additivity

Disposition: closed for the actual manuscript applications. The previous inventory over-specified a two-sided absolute height bound. Both displayed consumers need only the upper bound on the target height for an isogeny in its indicated direction. No assertion that an unused stronger bound has been checked is made here.

The pinned Faltings 1983 PDF was visually inspected on printed p.358, Lemma 5. For an isogeny phi:A1->A2 of semiabelian models with proper generic fibers, it states

    h(A2) = h(A1) + log(deg(phi))/2
            - log(# e^* Omega^1_(ker(phi)/O_K)) / [K:Q].

The final cardinality is a positive integer, at least one. Therefore h(A2)<=h(A1)+log(deg(phi))/2. The preceding text and Lemma 1 allow the generic-fiber isogeny to be extended to the semiabelian models. For stable heights, first pass to a common finite extension where both varieties have semistable reduction. The degree of the isogeny is unchanged and the normalized stable heights are unchanged. No degree bound on this auxiliary extension is used. In particular, this does not change the number-field degree fed into the earlier isogeny-existence estimate.

The metric definition was also visually inspected on printed p.351. In absolute norm its integral factor is 2^(-g) times the absolute integral of a top differential wedged with its conjugate. For a product, the determinant of the invariant differentials is the tensor product of the two determinant lines. Fubini's formula gives multiplication of the absolute integrals, and 2^(-(g1+g2))=2^(-g1)2^(-g2). The reordering sign of the exterior forms does not change the absolute norm. At finite places the determinant lattices have the same tensor-product identification. Arithmetic degree therefore adds, giving h_F(A1 x A2)=h_F(A1)+h_F(A2). This is the original Faltings normalization used in the two consumers, not the later shifted theta-height normalization.

In the CM consumer, the isogeny is E^2->A, so the formula gives h_F(A)<=2h_F(E)+log(deg(phi))/2. In the other consumer it is J->A x Z, so it gives h_F(A)<=h_F(J)+log(deg(phi))/2-h_F(Z). The separately sourced lower bound h_F(Z)>=-2g then gives the displayed +2g term. The argument does not assume h_F(Z)>=0. The zero-dimensional complement contributes height zero.

The 1984 erratum changes the height-tower assertion in Satz 2, not Lemma 5 or the determinant metric. The source interface used here is therefore not weakened by that correction. This review does not establish the existence or stated degree bound of either isogeny; those are other application records.

## A019: finite Kummer sequence, primary group and corank

Disposition: closed for this application, conditional on the manuscript's separately proved hypothesis dim_F2 Sel_2=3.

The precise finite Kummer source is Silverman 2009, X Theorem 4.2(a), printed p.333, with phi=[2]. It gives

    0 -> E(Q)/2E(Q) -> Sel_2(E/Q) -> Sha(E/Q)[2] -> 0.

Mordell-Weil finite generation is VIII Theorem 6.7. Full rational two-torsion makes dim E(Q)/2E(Q)=r+2, including any higher two-power torsion in the finite torsion group. Thus r+dim Sha[2]=1. In particular A=Sha[2^infinity] has at most two elements killed by 2.

Here is a direct group argument that avoids assuming finite Sha or using an unstated finite-cotype decomposition. For every n, multiplication by 2 maps A[2^(n+1)] into A[2^n] with kernel A[2] of size at most two. Induction makes each A[2^n] finite. A finite abelian 2-group with at most two elements killed by 2 is cyclic. Hence the A[2^n] form an increasing sequence of finite cyclic groups. If their orders are bounded, the sequence stabilizes and A is a finite cyclic group. If their orders are unbounded, their union is the quasicyclic group Q_2/Z_2. The zero group is included in the first case. This supplies all the structure actually needed in the present rank-one situation.

In the corrected author version of Poonen-Stoll, Corollary 4 identifies the obstruction of a genus-one Jacobian with Pic^0, which has its rational identity point, so that the obstruction c is zero. Corollary 7 gives alternation; Theorem 8(3), printed p.11 of that author version, makes the order of Sha_nd[2] a square. The suffix nd means quotient by the maximal divisible subgroup, not quotient by every group of finite index. Its nondegeneracy is described in Section 3. A finite nonzero cyclic 2-primary group would contribute exactly two elements to Sha_nd[2], contradicting Theorem 8(3). Thus A is either zero or Q_2/Z_2. Other primary components do not affect this 2-torsion conclusion.

If A=0 then r=1. If A=Q_2/Z_2 then r=0. To identify the infinite Selmer corank, use X Theorem 4.2(a) with [2^n] and take the filtered direct limit. On E(Q)/2^nE(Q) the transition is multiplication by 2; on Sha[2^n] it is inclusion. This is the Kummer diagram induced by the identity on the first E and multiplication by 2 on the second E in the short multiplication sequence. Filtered direct limits are exact, yielding

    0 -> E(Q) tensor Q_2/Z_2 -> Sel_(2^infinity) -> A -> 0.

The finite torsion in E(Q) vanishes in the tensor product. In the two cases above the sequence identifies Sel_(2^infinity) with Q_2/Z_2 directly: either its right term is zero and its left term has corank one, or its left term is zero and its right term is Q_2/Z_2. In either case its Z_2-corank is exactly one. This verifies the manuscript's conclusion without assuming the restricted converse, without finite Sha, and without claiming that the pairing restricted to F[2] is perfect.
