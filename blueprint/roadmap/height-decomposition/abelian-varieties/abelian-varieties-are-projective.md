---
article_id: af_8a21aad21aec22642dee01dc
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenAddedLeaves31.milneThm71Projective
---

# Every abelian variety is projective

For every field $K$ and every abelian variety $A$ over $K$ there are $N$ and a closed immersion
$A\to\mathbb P^N_K$ over $K$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
It is Milne's Theorem 7.1 in his survey in *Arithmetic Geometry*. Milne calls a variety projective
when it has a very ample linear system (citing Hartshorne II 7.8.2), which gives the closed
immersion. His proof treats an algebraically closed field first and then descends to any field. Here
$\mathbb P^N_K$ is the base change of $\mathbb P^N_{\mathbb Z}$ (EGA II (4.1.1), (4.1.3)). Taking
the closure of $A$ in $\mathbb P^N$ over the integers of a finite extension of $\mathbb Q_p$ gives a
proper model of $A$, which Colmez's theorem below assumes. The page and wording of the 1986 printing
were not checked; the author's retyped edition was read. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Milne 1986 Thm 7.1](../../../sources/height-decomposition-locators.md#milne-1986-thm-71)
