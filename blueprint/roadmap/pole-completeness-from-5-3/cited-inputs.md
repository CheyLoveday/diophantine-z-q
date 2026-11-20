---
article_id: af_da5f38b69bfe3d6aee9db599
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Manuscript.PoleS12.CasselsTatePairingCurves, ZInQ.Manuscript.PoleS12.BCDTThmA, ZInQ.Manuscript.PoleS12.KolyvaginThm1
---

# The cited inputs: the Cassels–Tate pairing, modularity and Kolyvagin's theorem

Write $E_\ell:y^2=x(x-\ell)(x+3\ell)$. The derivation of Theorem 5.2 from Theorem 5.3 uses three cited
statements besides Theorem 5.3.

- **The Cassels–Tate pairing on the curves $E_\ell$.** For every positive squarefree $\ell\equiv11\pmod{12}$
  there is a biadditive pairing $Ш(E_\ell/\mathbb Q)\times Ш(E_\ell/\mathbb Q)\to\mathbb Q/\mathbb Z$ that is
  alternating and whose kernel is the maximal divisible subgroup of $Ш(E_\ell/\mathbb Q)$. This is Cassels'
  theorem, as Poonen and Stoll state it; the manuscript cites it in the proof of Lemma 5.4.
- **Modularity** (Breuil, Conrad, Diamond and Taylor, Theorem A): every elliptic curve over $\mathbb Q$ is
  modular, in the sense that the Dirichlet coefficients of its L-function are the $q$-expansion
  coefficients of a weight-two cusp form on $\Gamma_0(N)$ for some $N>0$.
- **Kolyvagin's theorem, the case $r=1$**: a modular elliptic curve over $\mathbb Q$ whose L-function
  vanishes to order exactly $1$ at $s=1$ has rank $1$ and a finite Tate–Shafarevich group. Kolyvagin's
  Theorem 1 assumes a weak Weil parametrization; this statement follows from it through Shimura's
  construction and Faltings' isogeny theorem, so it is a consequence of the print, not the printed
  statement.

None of the three is proved here. `ZInQ.OneProof.frozenTarget` takes Theorem 5.3, the pairing, modularity
and this consequence of Kolyvagin's theorem as its hypotheses `hRC`, `hCT`, `hB` and `hK`.

## Depends on

None.

## Sources

- [Lemma 5.4](../../sources/manuscript.md#lemma-54)
- [Lemma 5.5](../../sources/manuscript.md#lemma-55)
