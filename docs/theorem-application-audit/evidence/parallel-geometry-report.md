# Geometry application audit

Date: 2026-11-05. Scope: A001, A002, A078, A079 only.

Consumer: `work/github-research-upload-20261104/repository/diophantine_zq.tex`, SHA256 `a17e021ea3a6b90f861d87aff048f905b1dc31226e3445caf273739f7659e51e`. Line numbers below refer to that version. No shared files were changed.

I recommend closing these four mathematical application obligations after incorporating the source locators and bridges below. I found missing citations and an omitted basis, but no false geometry conclusion requiring a change to the degree, excluded primes, field bound, or endomorphism classification. `PATCH.diff` supplies two explanatory manuscript additions. A078 can be closed with this evidence and the three new source entries; the manuscript already supplies its local proof.

## Sources and versions

I regenerated the four PDF text extractions in this folder from the pinned PDFs, rather than treating earlier reports as evidence. Their SHA256 values matched the inventory:

| Source | SHA256 | Relevant pages |
|---|---|---|
| Baba–Granath, 17 March 2005 preprint | `b049ce64f9b662af0e078f4faa9e5325cc7a99bf2d6ccda0a31a84719d031c32` | Printed/PDF pp.3–7, 11–12 |
| Buzzard, original 13 May 1996, corrections 14 June 2002 | `4854cb4adc99fec7eac47596dea86832e2e468f3c80d78726afeb98d2404b915` | Printed/PDF pp.3–7 |
| Lin–Yang, arXiv:1807.00466v1 | `773518a4a30e4f4acac650b7f7c5f19decfb1f893431e6d04f4cfd0205919038` | Printed/PDF pp.3, 5–6 |
| Milne, Abelian Varieties v2.00, 2008 | `f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef` | Printed p.14 / PDF p.20 |

The inventory gives the original public URLs. Public searches for corrections led to the same corrected Buzzard author PDF and the MPIM record for the Baba–Granath preprint. No separate erratum to the particular statements used here was identified. This is not a claim that no correction exists anywhere, or that a later publication is byte-identical to the pinned preprint.

Three additional primary reference pages were read in full and downloaded into this folder. `additional-source-pins.json` records their URLs, hashes, and retrieval date:

* [Stacks tag 07S7, Lemma 66.14.2](https://stacks.math.columbia.edu/tag/07S7), free finite locally free group actions and scheme quotients.
* [Stacks tag 0E97, Lemma 109.24.2](https://stacks.math.columbia.edu/tag/0E97), uniqueness of a stable model over a DVR.
* [Stacks tag 0EYG, Lemma 58.31.5](https://stacks.math.columbia.edu/tag/0EYG), the étale local Kummer form for tame covers along a regular divisor.

## A001: polarization, quotient, and all components

Consumer lines 397–423 and 515–525.

Baba–Granath §3, p.6 fixes exactly `i²=2`, `j²=-3`, `ij=-ji`, the order `Z[i,(1+j)/2]`, and `mu=2j+ij`. It identifies the two twisting rings with square roots of 2 and 3. Its Theorem 1, p.4, identifies the forgetful polarized moduli space with the quotient by the twisting subgroup. In this discriminant that subgroup is the entire four-element Atkin–Lehner group. Lemma 2, p.7 identifies the quotient with the rational projective line. Proposition 10, pp.11–12 fixes the coordinate so that the three images are 0, infinity, and -16/27. The order-two and order-three elliptic points described on p.6 acquire a further order-two quotient ramification; the remaining involution-fixed orbit has order two. Thus the orbifold indices are 4, 6, 2, respectively.

The Riemann-form convention needs care. Baba–Granath's displayed form in §2.1 is not literally the inverse-mu form used by the manuscript. Lin–Yang equation (3), p.5, is the matching inverse-mu form. Its Lemma 3, pp.5–6, gives the positivity test. The source locator `(2),(14)` in A001 omits this actual input. Equation (2), p.3 instead supports the displayed Igusa-coordinate map at manuscript lines 521–522.

Here is a direct check independent of that notational issue. Use the ordered lattice basis

`e=(1,i,(1+j)/2,(i+ij)/2)`.

Quaternion multiplication gives `mu²=-6`, `mu^-1=-mu/6`, and the matrix of `Trd(mu^-1 x bar(y))` is exactly

```
 0  0 -1  1
 0  0  1 -2
 1 -1  0  0
-1  2  0  0
```

Its determinant is one because its upper-right block has determinant one. This proves integrality and unimodularity on the actual lattice. For a real embedding take `i=diag(sqrt(2),-sqrt(2))` and `j=[[0,-sqrt(3)],[sqrt(3),0]]`. The lower-left entry of mu is `(2-sqrt(2))*sqrt(3)>0`, so Lin–Yang's positivity criterion applies. Cyclicity of reduced trace gives Rosati `a -> mu^-1 bar(a) mu`; using `mu²=-6` removes the apparent inverse-placement ambiguity. This is the positive involution fixed in Baba–Granath. Buzzard §1, p.3 states uniqueness of the principal polarization inducing the fixed involution. Thus the polarized moduli datum, rather than an unexamined equality of source formulas, is what identifies the two descriptions.

For the additional adelic argument, at a split prime an order normalizer is the center times `GL2(Z_l)`. At each division prime, valuation modulo the valuation of a central uniformizer contributes a group of order two. Therefore `N/(A_f^* K0)` has order four. The kernel on replacing K0 by K3 is a quotient of `(O/3O)^*`, so the total group has order at most `4*81=324`. This bounds the order of the acting group, not only the degree of a selected connected cover.

A central finite idele can be multiplied by a rational number to make all valuations zero. Its residue at 3 is in `F3^*={1,-1}`; changing the rational scalar's sign makes that residue one. It then lies in K3. This proves the central action is trivial without discarding a determinant component. K0/K3 acts transitively on the level structures over the level-zero object, and the four normalizer classes then give the stated quotient. The full determinant components are included throughout. The canonical level-forgetting maps and normalizer maps are defined over Q; this also agrees with Baba–Granath's Q-rational Atkin–Lehner involutions on p.5.

Conclusion: close A001, correct its source locator, and name the lattice basis. The patch does this without changing the matrix or quotient.

## A002: the integral fine moduli construction

Consumer lines 426–461.

Buzzard p.4–5 requires three properties: full determinant image, maximal level at every division prime, and containment in V1(N) for N at least four and prime to the discriminant. For U=V1(5), diagonal matrices with lower-right entry one show the determinant condition directly. This level changes only the split prime 5, so it is maximal at 2 and 3. The remaining condition holds with N=5 and discriminant 6. Theorem 2.1, p.5 gives proper smooth relative dimension one; Corollary 2.3, p.7 gives a regular projective scheme. The corrected author version is the one checked.

The theorem is NOT reapplied at level three. That would violate its division-prime hypothesis. Instead, on the existing universal abelian scheme over Z[1/30], A[3] and A[5] are finite étale. Their O-linear Isom sheaves are finite étale: étale locally the finite groups and all the finitely many action maps are constant, and the desired isomorphisms form a subset of a finite constant set. Refining a V1(5)-marking to a full marking is precisely the torsor construction of Buzzard §1, pp.3–4, with all choices retained.

Nonemptiness at three is not an assertion that O/3O is a matrix algebra. The quaternion algebra at 3 is division. The rational Tate module has Q3-dimension four and a faithful unital B3 action, hence dimension one over the division algebra B3. If Lambda is any full O3-stable lattice in B3, choose x of minimal division valuation in Lambda. For each y in Lambda, y*x^-1 belongs to O3, so Lambda is contained in O3*x. Stability gives the reverse inclusion. This verifies freeness with the correct left-module convention. In every allowed characteristic, the same dimension argument works for V3(A); alternatively, local constancy transfers the verified module type.

Forgetting five is a genuinely free action after adding three. A stabilizing group element gives an O-linear automorphism of A preserving its canonical principal polarization and its full three-marking. Its order is finite because the polarized automorphism group is finite. On T3(A) it belongs to `1+3M4(Z3)`, which has no nontrivial torsion. Faithfulness of the Tate action forces the automorphism to be the identity, after which the five-marking forces the original group element to be identity. This also holds on geometric fibers in positive characteristic. The group G5 is a constant finite étale group scheme, even at residue characteristics dividing its numerical order. Tameness is not needed for this free quotient.

Stacks tag 07S7 now applies to projective X35 and this free finite group action. Its scheme quotient is a G5-torsor, therefore finite étale. Smoothness and properness descend; an ample line bundle descends after tensoring all its translates, so the quotient is projective. The universal polarized abelian scheme, action, and three-marking have the canonical descent datum because changing five leaves them unchanged. Effective descent can also be read as the moduli interpretation: on a base carrying the three-marked object, its sheaf of five-markings is the covering torsor, and forgetting its trivialization reconstructs that object. No extra level-five multiplicity survives.

Conclusion: close A002. Its final quotient really has the full-three generic fiber and includes all determinant components.

## A078: extension, branch persistence, and normalized pullback

Consumer lines 463–513.

The unlevelled norm-one orbifold has genus zero and two points of each order 2 and 3, hence Euler characteristic `2-2(1-1/2)-2(1-1/3)=-1/3`. The full-three subgroup is torsion-free by the same integral congruence argument. Every connected cover therefore has negative Euler characteristic and genus at least two. Over a strictly henselian DVR at p>324 the smooth proper model separates into connected components, each with geometrically connected generic fiber. Stacks 0E97 applies to these smooth, hence stable, genus-at-least-two models. It extends every generic automorphism and every permutation between components uniquely, and uniqueness preserves the group law.

The order of the full acting group is at most 324 by A001. Thus its order is invertible at p. On each component, replace the action by its effective quotient. A prime-to-p finite-order automorphism reducing to identity is identity: a first nonzero term in its displacement modulo the uniformizer, on iteration through its order, would be multiplied by a unit and could not vanish. This is the standard separated-adic argument on the completed local rings. At a fixed special point, the analogous first-term argument in a local parameter proves that the stabilizer acts faithfully on the tangent line. Consequently it is cyclic, and a nontrivial eigenvalue has eigenvalue-minus-one a unit.

For clarity, the fixed-lift argument concerns the whole stabilizer, not unrelated generic orbits. A generator's fixed equation has invertible derivative and so a unique Hensel lift. Every other stabilizer element fixes that lift. Conversely a special fixed point lifts to a generic fixed point. If two generic ramification sections meet at a special point, both inertia groups lie in its cyclic stabilizer; their nonidentity elements have the same unique fixed lift. The two sections were therefore the same. This proves both absence of new branch points and noncollision. It does not infer noncollision merely from preservation of genus.

After translating to the common fixed section, averaging the parameter against the inverse tangent character gives a parameter z on which a generator acts by `z -> zeta*z`. Thus the invariant complete ring is `R[[z^e]]`. Quotient smoothness follows locally, and the three branch sections retain their inertia orders 4,6,2. The sections are individually Qp-rational on the generic fiber because their j-values are; properness extends them over Zp and the preceding result makes them disjoint. A smooth genus-zero curve with an ordered disjoint triple has the unique coordinate taking it to `(0,infinity,-16/27)`. The differences and denominators involved are units at these p. Uniqueness on the generic fiber identifies this coordinate with j, so no additional denominator prime enters.

I independently checked `G^6-97200F^2=H^2` by exact integer polynomial arithmetic and computed all discriminants and pairwise resultants of F,G,H1,H2,H3. `algebra-checks.json` records the results. Their prime supports are all contained in {2,3,5}; leading coefficients introduce only 7,11,13. Hence the manuscript's bound 13 is safe, including the behavior at infinity. The contact multiplicities over the three j-values are 2,6,2. None of F,G,H has repeated roots or shares a root at p>324.

The local cover before pullback is Kummer along a regular section, as in Stacks 0EYG. Units can be removed after an étale extension, since all ramification indices are invertible. If `t=z^e` and `t=s^a`, write `g=gcd(e,a)`, `e=g*e'`, `a=g*a'`. The normalization splits into g branches after adjoining the relevant roots of unity; on each branch `s=w^e'`, `z=xi*w^a'`. This proves the new index is e/g, rather than multiplying the degree by deg(J). Applied to (e,a)=(4,2),(6,6),(2,2), it leaves 2,1,1. These models are smooth over R. Away from those disjoint sections the pullback is étale; at infinity it is also étale. The integral normalization is finite because the projective R-schemes here are excellent. Its local models glue uniquely, it remains proper, and it maps to the old Y3 model. Pulling back the universal abelian scheme along that map supplies the claimed abelian scheme.

Near a surviving contact the equation is `s=w²`, where s=u-c. For a rational specialization with positive even valuation, adjoining w requires at most an unramified extension: write s=pi^(2m)*v and extract the square root of the unit v after an unramified residue extension. For negative valuation use the unbranched chart at infinity. Contacts have pairwise unit differences outside S, so a positive contact valuation singles out one contact. Thus every point of the fiber is unramified outside S and the odd-contact support. Its splitting field is also unramified there. A finite étale Q-algebra of dimension at most 324 has a normal splitting field of degree at most 324!, by its action on its geometric points. Finally, properness extends a K-point of the cover over each valuation ring above p outside S; its pulled-back abelian scheme gives good reduction even when K/Q ramifies there. These are different conclusions and neither assumes the other.

Conclusion: close A078 with the attached exact source pins and the preceding global-to-local justification. No missing additional bad prime, degree factor, or good-reduction hypothesis was found.

## A079: rational Hodge endomorphisms and the two algebras

Consumer lines 547–553.

The exact analytic bridge is Milne, Part I, Theorems 2.8–2.9, printed p.14 / PDF p.20. It says that polarizable complex tori are abelian varieties and that their complex-analytic group homomorphisms are exactly the algebraic homomorphisms. Part I Theorem 12.1(a), cited elsewhere in this manuscript for étale cohomology, is not the bridge. Its existing separate use should not be deleted.

Fix an embedding of the number field of A into C. The left B-action identifies H1(A,Q) with the one-dimensional left B-module B: both have Q-dimension four. Its complex structure commutes with the left action, so it is right multiplication by J in B_R, with J²=-1. The canonical map `B tensor B^op -> End_Q(B)`, `a tensor b -> (x -> a*x*b)`, is an isomorphism, and remains an isomorphism after real scalar extension. Choose a Q-basis for the left factor. Commutation with right J then forces each right coefficient separately to commute with J; there is no cancellation between left-basis coefficients.

The centralizer of J in B_R=M2(R) is R[J], a copy of C. Its intersection C_J with B contains Q. If it contains a noncentral element b, the quadratic minimal polynomial of b has negative discriminant, and its centralizer in the quaternion algebra is exactly Q(b). Thus C_J is either Q or an imaginary quadratic field k. The rational commutant is consequently B or `B tensor k`. In the latter case the embedding k into B makes k a maximal subfield and splits B, so `B tensor k=M2(k)`.

Every rational map in that commutant preserves the homology lattice after multiplication by a nonzero integer. It is then complex linear and gives an analytic homomorphism of the torus. Milne's exact Hom equivalence makes it algebraic. Conversely every algebraic endomorphism commutes with J. This proves the asserted equality for End_C^0(A), not merely an inclusion in a candidate algebra.

There is also no enlargement caused by using C in place of Qbar. For an integral endomorphism over C and any automorphism sigma of C/Qbar, f and its sigma-conjugate agree on every torsion point: these points and their images are Qbar-rational. Torsion is Zariski dense, so the morphisms agree. Descent of their equations gives definition over Qbar. Clearing denominators gives the same conclusion for quasi-endomorphisms. This supplies the geometric-field translation used by the manuscript.

Conclusion: close A079 after adding the exact Milne citation and the denominator/field bridge. `PATCH.diff` does so. The split CM algebra M2(k), the nonsplit non-CM algebra B, and their coefficient fields are correct.

## Deliverables

* `PATCH.diff`: proposed additions only; not applied to the shared manuscript.
* `proposed-application-updates.json`: scoped status and locator proposals. The main inventory may use its own status vocabulary.
* `additional-source-pins.json`, `07S7.html`, `0E97.html`, `0EYG.html`: new exact source evidence.
* `algebra-checks.json`: exact polynomial identity, discriminants, and pairwise resultants.
* `babagranath.txt`, `buzzard.txt`, `linyang.txt`, `milne-av.txt`: fresh page-labelled extractions of the pinned PDFs.

These conclusions are restricted to the four assigned geometry applications. They do not certify later modularity, height, or definability arguments.
