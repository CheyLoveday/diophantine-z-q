---
article_id: af_b51f3a8c62c8657c806add15
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves81.serreRigidityLevel3
---

# Serre's rigidity lemma at level 3

Let $\mathcal A$ be an abelian scheme of relative dimension $2$ over a scheme $S$ with a ring
homomorphism $\iota:\mathcal O\to\operatorname{End}_S(\mathcal A)$, and $\theta$ an automorphism of
$\mathcal A$ over $S$ commuting with $\iota(a)$ for every $a\in\mathcal O$. Let
$s:\operatorname{Spec}k\to S$ be a geometric point whose field has characteristic neither $2$ nor
$3$, and $P\in\mathcal A_s(k)$ a point such that $a\mapsto\iota(a)P$ is a bijection from
$\mathcal O/3\mathcal O$ onto the $3$-torsion of $\mathcal A_s(k)$. If $\theta$ fixes $P$, then
$\theta$ fixes every point of $\mathcal A_s(k)$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. A consequence of printed statements, not a single
print. Since $\iota(0)=0$, $\theta$ fixes the zero section, so on the fibre it is a homomorphism
(Milne, Corollary 2.2); commuting with $\mathcal O$ and fixing $P$, it is the identity on the
$3$-torsion. Buzzard states that $\mathcal A_s$ has a unique principal polarization $\lambda$ whose
Rosati involution induces $x\mapsto t^{-1}\bar xt$ on $\mathcal O$, for a fixed $t\in\mathcal O$
with $t^2=-6$; then $\theta^\vee\lambda\theta$ is another such polarization, so $\theta$ preserves
$\lambda$. That step is not printed and is written out in the notes accompanying the Lean proof.
Milne's Proposition 17.5(b) at $n=3$, in characteristic other than $3$, ends the argument. In
characteristic $p$ Buzzard's uniqueness is printed with a sketched proof. It is a hypothesis, not
proved here.

## Depends on

None.

## Sources

- [Serre rigidity at level 3](../../../sources/height-decomposition-locators.md#serre-rigidity-at-level-3)
