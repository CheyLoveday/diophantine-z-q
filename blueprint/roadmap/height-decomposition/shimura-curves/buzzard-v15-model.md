---
article_id: af_de893e3e5df73352097d4933
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves81.buzzardThm21Cor23V15
---

# Buzzard's model at level V₁(5) over ℤ[1/30]

The *$V_1(5)$ model statement* is the following assertion. Let $e=3+2ij\in\mathcal O$; it has
reduced trace $6$ and reduced norm $-15$, so it reduces to an idempotent of rank one in
$\mathcal O/5\mathcal O$. For a scheme $S$ and an abelian scheme $\mathcal A$ of relative dimension
$2$ over $S$ with a ring homomorphism $\iota:\mathcal O\to\operatorname{End}_S(\mathcal A)$, a
*$V_1(5)$-structure* is a section $Q$ of $\mathcal A$ over $S$ with $5Q=0$ and $\iota(e)Q=0$ that is
nonzero at every geometric point of $S$. There are a scheme $X$ over $\mathbb Z[1/30]$, proper and
smooth of relative dimension $1$, with a closed immersion into some $\mathbb P^N_{\mathbb Z[1/30]}$
over $\mathbb Z[1/30]$, and such an $(\mathcal A,\iota)$ over $X$ with a $V_1(5)$-structure $Q$,
with the following property. For every scheme $S$ over $\mathbb Z[1/30]$ and every such
$(\mathcal A',\iota')$ over $S$ with a $V_1(5)$-structure $Q'$, there is exactly one morphism
$g:S\to X$ over $\mathbb Z[1/30]$ for which some cartesian square from $\mathcal A'\to S$ to
$\mathcal A\to X$ over $g$ commutes with the actions of $\mathcal O$ and carries $Q'$ to $Q$; and
that square is unique.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is Buzzard's Theorem 2.1 with Corollary 2.3 at the
level $U=V_1(5)$, for which $\mathbb Z[1/M_Ud]=\mathbb Z[1/30]$: the moduli stack $X_D(U)$ is proper
and smooth of relative dimension $1$ over $\mathbb Z[1/30]$, it is the stack associated to a scheme,
and that scheme is projective. Three steps are not printed and are written out in the notes
accompanying the Lean proof. Buzzard defines $V_1(5)$ through an isomorphism
$\kappa:\mathcal O\otimes R\to\mathrm M_2(R)$, $R=\prod_{p\nmid6}\mathbb Z_p$, fixed once and for
all; the statement takes $\kappa$ with $\kappa(e)\equiv\operatorname{diag}(1,0)\bmod5$, and for that
choice his $V_1(5)$-structures are the sections $Q$ above. Uniqueness of the square is the absence
of automorphisms established in the proof of Corollary 2.3, through Lemma 2.2. Projectivity over the
affine base gives the closed immersion. The polarization is not part of the data, and $\iota$ is not
asked to be injective, which it is automatically over a nonempty base. It is a hypothesis, not
proved here.

## Depends on

None.

## Sources

- [Buzzard Thm 2.1 and Cor 2.3 at V1(5)](../../../sources/height-decomposition-locators.md#buzzard-thm-21-and-cor-23-at-v15)
