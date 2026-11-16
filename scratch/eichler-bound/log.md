# eichler-bound results log

Task: prove `GR56.R5fpCountLe` (the only half of `gonzalezRotgerProp56X6` the chain reads) without Eichler's
formula, for the maximal order O of B = (2,-3 | Q).

## Plan (2026-11-16 13:xx)
Target theorem: `#(OptEmb k R / O^x) <= 2^{inertCount6 k} * #Pic(R)` for R of conductor prime to 6, by an
explicit injection `Quot (ConjRel R) -> Pic R x T`, `#T = 2^b`, where T = types at 2 and 3
(`Phi(omega) - Phi0(omega)` in the two-sided prime P_l of O). Ingredients: class number one of O (Euclidean
algorithm), the intertwiner lattice `J = {c in O : c Phi0(a) = Phi(a) c}`, and a "Key" lemma
(J O = O = O J when types agree) proved prime by prime:
* l not dividing 6: polynomial certificate (6 * minor in the ideal of coords of conj(c) d, c conj(d)) + descent;
* l | 6: P_l = pi O = O pi (pi = i, j), conjugation by pi = quaternion conjugation mod P_l.

## Findings
* VERIFIED (sympy, cert_L.py): each 2x2 minor a_i b_j - a_j b_i of the O-coordinates of c, d is a rational
  linear combination, with denominators dividing 6, of the 8 O-coordinates of conj(c)*d and c*conj(d).
* VERIFIED (python, checkP.py, |n_i| <= 3 exhaustive / random): P_2 = {n0, n2 even} = {2 | nrd},
  P_3 = {n0 = n2, n1 = n3 mod 3} = {3 | nrd}; conj(pi) z pi - nrd(pi) conj(z) in l*P_l; commutators in P_2, P_3.

## Compile log (modules under ZInQKernel/Contrib/OneProof/EichlerBound/, lake build)
* Order.lean (part A: norm/trace, l*O, P_2 = iO, P_3 = jO, frob, minor certificate, Euclid/principal): compiles, no sorry. VERIFIED.
* Quadratic.lean (part C: R = Z + Z omega for conductor prime to 6; ramified element; Lemma D at 2): compiles. VERIFIED.
* Embed.lean (embeddings, conjugation sk, centralizer, intertwiners J, Skolem-Noether-lite): compiles. VERIFIED.
* Unit.lean (Bad, conjugation trick Bad => Bad'): compiles. VERIFIED.
* Crit.lean (unit criterion J O = O and O J = O from no bad prime, via principal_of_lattice): compiles. VERIFIED.
