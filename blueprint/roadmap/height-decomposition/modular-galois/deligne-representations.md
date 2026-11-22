---
article_id: af_51dfcd18479cbca8bce85948
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves76.dsThm965AtPrimes
---

# Deligne's Galois representations of eigenforms

The *Deligne statement* is the following assertion. Let $f\in S_k(N,\chi)$ be a normalized eigenform
of weight $k\ge2$ whose coefficient field $K_f$ is a number field, and $\lambda$ a prime of $K_f$
above a prime $\ell$, with completion $K_{f,\lambda}$. Then there is a continuous representation
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(K_{f,\lambda})$ with the following property for every prime
$p\nmid N\ell$ and every maximal ideal $\mathfrak p$ of the ring $\overline{\mathbb Z}$ of algebraic
integers lying over $p$. Every $\sigma\in G_{\mathbb Q}$ that maps $\mathfrak p$ to itself and acts
trivially on $\overline{\mathbb Z}/\mathfrak p$ has $\rho(\sigma)=1$; and every $\sigma$ that maps
$\mathfrak p$ to itself and acts on $\overline{\mathbb Z}/\mathfrak p$ as $x\mapsto x^p$ has
characteristic polynomial $x^2-a_p(f)x+\chi(p)p^{k-1}$ for $\rho(\sigma)$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. Diamond and Shurman's theorem prints the characteristic
equation of $\rho(\mathrm{Frob}_{\mathfrak p})$ for every maximal ideal $\mathfrak p$ over $p$, with
inertia and Frobenius as in their §9.3. The statement drops the irreducibility of $\rho$, which the
theorem also asserts, and assumes that $K_f$ is a number field, which the theorem presupposes. The
bound $k\ge2$ is this project's restriction, not a hypothesis of the print. It is a hypothesis, not
proved here.

## Depends on

None.

## Sources

- [Deligne representations](../../../sources/height-decomposition-locators.md#deligne-representations)
